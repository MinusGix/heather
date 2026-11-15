//! Moving a module delta onto another dependency world: the early cutoff for
//! an upstream edit the module never observed
//! (`docs/infrastructure/module-interface-cutoff-design.md`).
//!
//! A delta's Ψ references are de Bruijn indices counted from the Ψ length a
//! term is scoped at, so the same module elaborated over a world with one
//! more theorem in `nat` differs from the stored one only in the indices that
//! cross that theorem. [`ModuleDelta::relocate`] rewrites exactly those,
//! through a map from old dependency positions to new ones that the caller
//! builds (by content identity; the elaborator does not know the hashes).
//!
//! The one thing this file must get right is the **scope** of every kernel
//! payload: the Ψ length its free globals count from. The inventory, by
//! `DeltaEvent` variant, is the match in [`Mover::event`]; every variant is
//! named there, so a new event kind fails to compile until its payloads are
//! classified. The guard copies of a declaration's lowering, which the
//! registry compares raw, record the Ψ length they were cut at
//! (`DeltaEvent::GenTyCode`'s `at`): no other position says it.
//!
//! Nothing here is trusted. A relocated delta goes through
//! [`crate::Elaborator::replay_module_delta`] like any decoded image: the
//! kernel (or the verdict store, by content key) judges every binding, and
//! the registry events face the same preflight.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use heather_kernel::rc::Rc;

use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalRef, LocalVar, SealedProof, Term, Type};

use crate::gendefs::{GenDef, SpineCodes, TyCodeFn, WfSlots};
use crate::metaprograms::MetaDef;
use crate::module_delta::{DeltaEvent, ModuleDelta, ModuleDependencyIdentity};
use crate::names::Scope;
use crate::resolve::DerivedInst;

/// Why a delta could not be moved. Always an ordinary miss for the caller:
/// the module is elaborated instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelocationRefusal(pub &'static str);

impl fmt::Display for RelocationRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl std::error::Error for RelocationRefusal {}

/// The world a delta is moved onto.
pub struct RelocationTarget<'a> {
    /// The new dependency prefix, already accepted.
    pub dependency_psi: GlobalCtx,
    /// Its loader identity, as [`crate::Elaborator::replay_module_delta`]
    /// will compare it.
    pub dependencies: ModuleDependencyIdentity,
    /// Old dependency position (below the delta's old base) to new position.
    /// `None` refuses the move.
    pub map: &'a mut dyn FnMut(usize) -> Option<usize>,
}

const NO_COUNTERPART: RelocationRefusal =
    RelocationRefusal("a referenced dependency binding has no counterpart in the new world");

struct Mover<'a> {
    old_base: usize,
    new_base: usize,
    map: &'a mut dyn FnMut(usize) -> Option<usize>,
    /// `D#shape`'s position per tag, from this delta's own `GenDef` events:
    /// the scope of the `Wf` slot guard's decoded copy.
    shape_at: HashMap<u32, u32>,
}

impl Mover<'_> {
    fn abs(&mut self, a: usize) -> Option<usize> {
        if a >= self.old_base {
            Some(a - self.old_base + self.new_base)
        } else {
            (self.map)(a)
        }
    }

    /// A position the module itself bound (a registration's, a generated
    /// definition's): it moves with the module's base.
    fn own(&self, a: u32) -> Result<u32, RelocationRefusal> {
        let a = a as usize;
        if a < self.old_base {
            return Err(RelocationRefusal("a registration names a position below the module"));
        }
        u32::try_from(a - self.old_base + self.new_base).map_err(|_| RelocationRefusal("Ψ position overflows"))
    }

    /// A Ψ length a payload is scoped at. Every scoped payload of a module's
    /// own events was built while the module was being elaborated, so its
    /// scope is at or past the module's base.
    fn scope(&self, p: usize) -> Result<usize, RelocationRefusal> {
        if p < self.old_base {
            return Err(RelocationRefusal("a payload is scoped below the module"));
        }
        Ok(p - self.old_base + self.new_base)
    }

    fn scope32(&self, p: u32) -> Result<u32, RelocationRefusal> {
        u32::try_from(self.scope(p as usize)?).map_err(|_| RelocationRefusal("Ψ position overflows"))
    }

    /// The free index `i` of a term scoped at old length `p`, at new length
    /// `p2`: through the absolute position it names.
    fn index(&mut self, p: usize, p2: usize, i: u32) -> Option<u32> {
        let a = p.checked_sub(1)?.checked_sub(i as usize)?;
        let a2 = self.abs(a)?;
        u32::try_from(p2.checked_sub(1)?.checked_sub(a2)?).ok()
    }

    /// [`Self::index`] for either spelling: a constant is the absolute
    /// position already, and moves to its counterpart's.
    fn reference(&mut self, p: usize, p2: usize, r: GlobalRef) -> Option<GlobalRef> {
        match r {
            GlobalRef::Var(i) => self.index(p, p2, i).map(GlobalRef::Var),
            GlobalRef::Const(a) => Some(GlobalRef::Const(u32::try_from(self.abs(a as usize)?).ok()?)),
        }
    }

    fn ty(&mut self, p: usize, t: &Type) -> Result<Type, RelocationRefusal> {
        let p2 = self.scope(p)?;
        t.reindex_global(&mut |r| self.reference(p, p2, r)).ok_or(NO_COUNTERPART)
    }

    fn tm(&mut self, p: usize, t: &Term) -> Result<Term, RelocationRefusal> {
        let p2 = self.scope(p)?;
        t.reindex_global(&mut |r| self.reference(p, p2, r)).ok_or(NO_COUNTERPART)
    }

    /// A payload of the dependency prefix, scoped at its old position `p`
    /// there: an opened proof.
    fn dependency_tm(&mut self, p: usize, t: &Term) -> Result<Term, RelocationRefusal> {
        let p2 = self.abs(p).ok_or(NO_COUNTERPART)?;
        t.reindex_global(&mut |r| self.reference(p, p2, r)).ok_or(NO_COUNTERPART)
    }

    fn binding(&mut self, p: usize, b: &GlobalBinding) -> Result<GlobalBinding, RelocationRefusal> {
        let p2 = self.scope(p)?;
        b.reindex_global(&mut |r| self.reference(p, p2, r)).ok_or(NO_COUNTERPART)
    }

    fn event(&mut self, e: &DeltaEvent) -> Result<DeltaEvent, RelocationRefusal> {
        Ok(match e {
            DeltaEvent::Global { abs, registration, is_axiom, direct_dependencies } => DeltaEvent::Global {
                abs: self.own(*abs)?,
                registration: registration.clone(),
                is_axiom: *is_axiom,
                direct_dependencies: direct_dependencies.clone(),
            },
            DeltaEvent::GenDef { key, abs } => DeltaEvent::GenDef { key: *key, abs: self.own(*abs)? },
            // The guard copies are scoped at the Ψ length they were cut at,
            // which the event records (`register_ty_code`): they are
            // committed after the definitions minted from them, so no
            // position in the delta says it.
            DeltaEvent::GenTyCode { tag, inline, level, at } => DeltaEvent::GenTyCode {
                tag: *tag,
                inline: Rc::new(self.ty(*at as usize, inline)?),
                level: level.clone(),
                at: self.scope32(*at)?,
            },
            DeltaEvent::GenTyCodeFn { tag, entry, at } => DeltaEvent::GenTyCodeFn {
                tag: *tag,
                entry: TyCodeFn {
                    template: Rc::new(self.ty(*at as usize, &entry.template)?),
                    stmt: Rc::new(self.ty(*at as usize, &entry.stmt)?),
                    ..entry.clone()
                },
                at: self.scope32(*at)?,
            },
            DeltaEvent::GenSpineCodes { tag, codes, at } => {
                let mut moved = |parts: &[(Rc<Type>, heather_kernel::level::Level)]| {
                    parts
                        .iter()
                        .map(|(ty, l)| Ok((Rc::new(self.ty(*at as usize, ty)?), l.clone())))
                        .collect::<Result<Vec<_>, RelocationRefusal>>()
                };
                let ctors = moved(&codes.ctors)?;
                let nodes = moved(&codes.nodes)?;
                DeltaEvent::GenSpineCodes { tag: *tag, codes: SpineCodes { ctors, nodes }, at: self.scope32(*at)? }
            }
            // The inline copy and the arity are cut from the lowering, like
            // the copies above; the decoded copy is `El` of `D#shape`'s body,
            // scoped at that definition's own position
            // (`Elaborator::wf_slot_refs`).
            DeltaEvent::GenWfSlots { tag, slots, at } => {
                let Some(&shape_at) = self.shape_at.get(tag) else {
                    return Err(RelocationRefusal("a Wf slot guard has no shape code in its module"));
                };
                DeltaEvent::GenWfSlots {
                    tag: *tag,
                    slots: WfSlots {
                        shape: Rc::new(self.ty(*at as usize, &slots.shape)?),
                        shape_decoded: Rc::new(self.ty(shape_at as usize, &slots.shape_decoded)?),
                        arity: Rc::new(self.tm(*at as usize, &slots.arity)?),
                        level: slots.level.clone(),
                    },
                    at: self.scope32(*at)?,
                }
            }
            DeltaEvent::Derived(info) => DeltaEvent::Derived(DerivedInst {
                abs: self.own(info.abs)?,
                ty: self.ty(info.at as usize, &info.ty)?,
                at: self.scope32(info.at)?,
                ..info.clone()
            }),
            DeltaEvent::Meta { module, name, slot, definition } => DeltaEvent::Meta {
                module: module.clone(),
                name: name.clone(),
                slot: *slot,
                definition: MetaDef {
                    term: Rc::new(self.tm(definition.psi_len as usize, &definition.term)?),
                    stmt: Rc::new(self.ty(definition.psi_len as usize, &definition.stmt)?),
                    psi_len: self.scope32(definition.psi_len)?,
                    order: definition.order.clone(),
                },
            },
            // Levels, tags, names and surface syntax: nothing positional.
            DeltaEvent::Name { .. }
            | DeltaEvent::GenFamLevels { .. }
            | DeltaEvent::Inductive { .. }
            | DeltaEvent::Class { .. }
            | DeltaEvent::Instance { .. }
            | DeltaEvent::Designation { .. }
            | DeltaEvent::Evidence(_)
            | DeltaEvent::Registered { .. }
            | DeltaEvent::Interface { .. }
            | DeltaEvent::Repr { .. }
            | DeltaEvent::Impl { .. }
            | DeltaEvent::Access { .. }
            | DeltaEvent::InternalAccess { .. } => e.clone(),
        })
    }
}

fn shape_positions(events: &[DeltaEvent]) -> HashMap<u32, u32> {
    events
        .iter()
        .filter_map(|e| match e {
            DeltaEvent::GenDef { key: GenDef::ShapeCode(tag), abs } => Some((*tag, *abs)),
            _ => None,
        })
        .collect()
}

impl ModuleDelta {
    /// This delta over another dependency world: every Ψ position it holds
    /// moved through `to.map` (dependency positions) or with the module's
    /// base (its own). Refused when a referenced position has no
    /// counterpart, or a payload's scope is not one this file knows.
    ///
    /// The result is as untrusted as a decoded image, and is installed only
    /// through [`crate::Elaborator::replay_module_delta`].
    pub fn relocate(&self, to: RelocationTarget<'_>) -> Result<ModuleDelta, RelocationRefusal> {
        let old_base = self.dependency_psi.bindings.len();
        let mut m = Mover {
            old_base,
            new_base: to.dependency_psi.bindings.len(),
            map: to.map,
            shape_at: shape_positions(&self.events),
        };
        let extension = self
            .extension
            .iter()
            .enumerate()
            .map(|(i, b)| m.binding(old_base + i, b))
            .collect::<Result<Vec<_>, _>>()?;
        // A sealed proof is its theorem's body, scoped like the binding.
        let sealed = self
            .sealed
            .iter()
            .map(|(i, proof)| Ok((*i, Rc::new(SealedProof::new(Rc::new(m.tm(old_base + i, proof.term())?))))))
            .collect::<Result<Vec<_>, RelocationRefusal>>()?;
        // A dependency's proof as it was opened, scoped at its theorem's
        // position like any sealed proof; the replay compares it, byte for
        // byte, with the proof now at the moved position.
        let opened_dependencies = self
            .opened_dependencies
            .iter()
            .map(|(a, proof)| Ok((m.abs(*a).ok_or(NO_COUNTERPART)?, Rc::new(SealedProof::new(Rc::new(m.dependency_tm(*a, proof.term())?))))))
            .collect::<Result<Vec<_>, RelocationRefusal>>()?;
        let items = self
            .items
            .iter()
            .map(|slice| {
                let mut slice = slice.clone();
                slice.unsealed = slice
                    .unsealed
                    .iter()
                    .map(|a| m.abs(*a).ok_or(NO_COUNTERPART))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(slice)
            })
            .collect::<Result<Vec<_>, RelocationRefusal>>()?;
        let events = self.events.iter().map(|e| m.event(e)).collect::<Result<Vec<_>, _>>()?;
        Ok(ModuleDelta {
            module: self.module.clone(),
            dependencies: to.dependencies,
            dependency_psi: to.dependency_psi,
            extension,
            sealed,
            opened_dependencies,
            scope: self.scope.clone(),
            events,
            items,
            warnings: self.warnings.clone(),
            scope_at_entry: self.scope_at_entry.clone(),
        })
    }

    /// The same delta over another dependency prefix of the same length,
    /// unrewritten: for an image decoded against a placeholder prefix
    /// (`docs/infrastructure/module-dag-design.md` §4) when the world it is loaded into puts
    /// every module of its closure where its own canonical world did, so the
    /// move is the identity. The caller vouches for that; the replay
    /// rechecks every binding against the prefix it is given either way.
    /// `None` when the lengths differ.
    pub fn over_prefix(&self, dependency_psi: GlobalCtx) -> Option<ModuleDelta> {
        (dependency_psi.bindings.len() == self.dependency_psi.bindings.len()).then(|| ModuleDelta {
            dependency_psi,
            ..self.clone()
        })
    }

    /// Every dependency position (below the module's base) the delta refers
    /// to anywhere: bindings, sealed proofs, registry payloads, opened
    /// proofs. What a relocation must find a counterpart for, and the only
    /// part of the old world a later relocation needs to know about.
    pub fn dependency_references(&self) -> Result<BTreeSet<usize>, RelocationRefusal> {
        let mut refs = BTreeSet::new();
        self.relocate(RelocationTarget {
            dependency_psi: self.dependency_psi.clone(),
            dependencies: self.dependencies.clone(),
            map: &mut |a| {
                refs.insert(a);
                Some(a)
            },
        })?;
        Ok(refs)
    }

    /// The module's contribution a dependent observes through the
    /// elaborator's registries, as opposed to through names: everything but
    /// its `Name` and `Global` events, and its scope. See [`RegistryPart`].
    pub fn registry_part(&self) -> RegistryPart {
        RegistryPart {
            known: true,
            scope: self.scope.clone(),
            events: self
                .events
                .iter()
                .filter(|e| !matches!(e, DeltaEvent::Name { .. } | DeltaEvent::Global { .. }))
                .cloned()
                .collect(),
        }
    }
}

/// Content identities a [`RegistryPart`] projection is taken over, supplied
/// by the caller (the elaborator does not hash): a Ψ binding's, and a kernel
/// payload's at the Ψ length it is scoped at, both independent of where in Ψ
/// anything sits.
pub trait WorldHasher {
    fn binding(&mut self, abs: usize) -> Option<[u8; 32]>;
    fn ty(&mut self, scope: usize, t: &Type) -> Option<[u8; 32]>;
    fn tm(&mut self, scope: usize, t: &Term) -> Option<[u8; 32]>;
}

/// A module's registry contribution, kept beside the session so its
/// position-independent projection can be taken once the hashes of the
/// world under it are known.
#[derive(Clone)]
pub struct RegistryPart {
    /// False for a module whose contribution the caller could not see (one
    /// checked under `--only`, which keeps no delta): it has no projection.
    known: bool,
    scope: Scope,
    events: Vec<DeltaEvent>,
}

impl RegistryPart {
    /// A module whose registry contribution is not known: every digest that
    /// covers it is unavailable, so nothing is moved over it.
    pub fn unknown() -> Self {
        Self { known: false, scope: Scope::new(""), events: Vec::new() }
    }

    /// No registry events: a module of plain `fn`s and `theorem`s.
    pub fn is_inert(&self) -> bool {
        self.known && self.events.is_empty()
    }

    /// The bytes a registry digest is taken over: the scope and each event's
    /// interface encoding with its positions blanked, followed by the content
    /// hashes of what those positions named. Two modules with equal
    /// projections offer a dependent's elaboration the same registry entries,
    /// wherever in Ψ either sits. `None` when a hash is unavailable.
    pub fn projection(&self, h: &mut dyn WorldHasher) -> Option<Vec<u8>> {
        if !self.known {
            return None;
        }
        let shape_at = shape_positions(&self.events);
        let mut out = crate::module_image::encode_interface_scope(&self.scope);
        let mut hashes = Vec::new();
        for e in &self.events {
            let blank = match e {
                DeltaEvent::GenDef { key, abs } => {
                    hashes.push(h.binding(*abs as usize)?);
                    DeltaEvent::GenDef { key: *key, abs: 0 }
                }
                DeltaEvent::GenTyCode { tag, inline, level, at } => {
                    hashes.push(h.ty(*at as usize, inline)?);
                    DeltaEvent::GenTyCode { tag: *tag, inline: Rc::new(Type::Nat), level: level.clone(), at: 0 }
                }
                DeltaEvent::GenTyCodeFn { tag, entry, at } => {
                    hashes.push(h.ty(*at as usize, &entry.template)?);
                    hashes.push(h.ty(*at as usize, &entry.stmt)?);
                    DeltaEvent::GenTyCodeFn {
                        tag: *tag,
                        entry: TyCodeFn { template: Rc::new(Type::Nat), stmt: Rc::new(Type::Nat), ..entry.clone() },
                        at: 0,
                    }
                }
                DeltaEvent::GenSpineCodes { tag, codes, at } => {
                    let blank = |parts: &[(Rc<Type>, heather_kernel::level::Level)]| {
                        parts.iter().map(|(_, l)| (Rc::new(Type::Nat), l.clone())).collect::<Vec<_>>()
                    };
                    for (ty, _) in codes.ctors.iter().chain(&codes.nodes) {
                        hashes.push(h.ty(*at as usize, ty)?);
                    }
                    DeltaEvent::GenSpineCodes {
                        tag: *tag,
                        codes: SpineCodes { ctors: blank(&codes.ctors), nodes: blank(&codes.nodes) },
                        at: 0,
                    }
                }
                DeltaEvent::GenWfSlots { tag, slots, at } => {
                    let shape_at = *shape_at.get(tag)? as usize;
                    hashes.push(h.ty(*at as usize, &slots.shape)?);
                    hashes.push(h.ty(shape_at, &slots.shape_decoded)?);
                    hashes.push(h.tm(*at as usize, &slots.arity)?);
                    DeltaEvent::GenWfSlots {
                        tag: *tag,
                        slots: WfSlots {
                            shape: Rc::new(Type::Nat),
                            shape_decoded: Rc::new(Type::Nat),
                            arity: Rc::new(Term::Var(LocalVar(0))),
                            level: slots.level.clone(),
                        },
                        at: 0,
                    }
                }
                DeltaEvent::Derived(info) => {
                    hashes.push(h.binding(info.abs as usize)?);
                    hashes.push(h.ty(info.at as usize, &info.ty)?);
                    DeltaEvent::Derived(DerivedInst { abs: 0, at: 0, ty: Type::Nat, ..info.clone() })
                }
                DeltaEvent::Meta { module, name, slot, definition } => {
                    let at = definition.psi_len as usize;
                    hashes.push(h.tm(at, &definition.term)?);
                    hashes.push(h.ty(at, &definition.stmt)?);
                    DeltaEvent::Meta {
                        module: module.clone(),
                        name: name.clone(),
                        slot: *slot,
                        definition: MetaDef {
                            term: Rc::new(Term::Var(LocalVar(0))),
                            stmt: Rc::new(Type::Nat),
                            psi_len: 0,
                            order: definition.order.clone(),
                        },
                    }
                }
                _ => e.clone(),
            };
            out.extend_from_slice(&crate::module_image::encode_events(std::slice::from_ref(&blank), true));
        }
        for hash in hashes {
            out.extend_from_slice(&hash);
        }
        Some(out)
    }
}

/// What a module's elaboration could observe of the world's names, for the
/// identifiers it might have looked up: [`NameWorld::observations`].
pub struct NameObservations {
    /// The names, their declaring modules and kinds, and each global's
    /// surface signature, in a canonical order.
    pub bytes: Vec<u8>,
    /// The Ψ positions of the observed globals, in the same order: their
    /// content hashes belong in the digest too, and the elaborator does not
    /// hash.
    pub globals: Vec<usize>,
}

/// The identifiers a source text could name: maximal runs of alphanumeric
/// characters, `_` and `'`. A superset of the names its elaboration looks up
/// by what it wrote, and the filter [`NameWorld::observations`]
/// applies to the last segment of each declared name.
pub fn source_identifiers(src: &str) -> BTreeSet<String> {
    src.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect()
}

/// The world's names as they stood at one moment, kept so that what a
/// module's elaboration could observe of them is computed over the world
/// *under* the module once the elaboration has said what it looked up
/// (`docs/infrastructure/module-interface-cutoff-design.md` §2).
pub struct NameWorld(crate::names::Names);

impl crate::Elaborator {
    /// The world's names now: a snapshot sharing every sealed table.
    pub fn name_world(&self) -> NameWorld {
        NameWorld(self.names.semantic_snapshot())
    }
}

impl NameWorld {
    /// Every name in the world whose last `::` segment `wanted` accepts,
    /// with what it resolves to: its declaring modules and kinds, and for a
    /// global its signature and Ψ position. An upstream edit that changes
    /// none of this for the names a module wrote or looked up did not change
    /// how that module's names resolve.
    pub fn observations(&self, wanted: &dyn Fn(&str) -> bool) -> NameObservations {
        let names = &self.0;
        let observed: BTreeMap<String, Vec<(String, String, u8)>> = names.observe(&|name| {
            wanted(name.rsplit("::").next().unwrap_or(name))
        });
        let mut bytes = Vec::new();
        let mut globals = Vec::new();
        let put = |bytes: &mut Vec<u8>, s: &str| {
            bytes.extend_from_slice(&(s.len() as u64).to_le_bytes());
            bytes.extend_from_slice(s.as_bytes());
        };
        for (name, entries) in &observed {
            put(&mut bytes, name);
            bytes.extend_from_slice(&(entries.len() as u64).to_le_bytes());
            for (module, origin, kind) in entries {
                put(&mut bytes, module);
                put(&mut bytes, origin);
                bytes.push(*kind);
                if let Some(info) = names.global(&crate::names::qkey(origin, name)) {
                    bytes.push(1);
                    globals.push(info.abs as usize);
                    let signature = crate::module_image::encode_interface_signature(
                        &info.params,
                        names.surface_decl(name),
                    );
                    bytes.extend_from_slice(&(signature.len() as u64).to_le_bytes());
                    bytes.extend_from_slice(&signature);
                } else {
                    bytes.push(0);
                }
            }
        }
        NameObservations { bytes, globals }
    }
}
