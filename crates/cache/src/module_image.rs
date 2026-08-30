//! Content-addressed persistent storage for checked semantic module images.
//!
//! This layer owns filesystem and rebuild policy; `heather-elab` owns only
//! the semantic bytes and their bounded inert decoder. A cache hit is still
//! replayed through the kernel before publication.

use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use heather_elab::{
    Lint, LintFix, LintProfile, ModuleDelta, ModuleDependencyIdentity, ModuleImageDecodeError,
    ModuleImageLimits, Span, Warning,
};
use heather_kernel::term::GlobalCtx;

use crate::sha256::{Sha256, hex, sha256};
use crate::{ELABORATOR_SEMANTICS, KERNEL_SEMANTICS};

const MAGIC: &[u8; 8] = b"HTHCACH\x02";
const DOMAIN_KEY: &[u8] = b"heather/module-cache-key/1\0";
const DOMAIN_INTERFACE: &[u8] = b"heather/module-artifact-interface/1\0";
const HEADER: usize = 8 + 32 + 32 + 8 + 8;
const CHECKSUM: usize = 32;
static TEMP_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ModuleCacheKey([u8; 32]);

impl ModuleCacheKey {
    pub fn for_source(
        module: &str,
        source: &str,
        dependencies: &ModuleDependencyIdentity,
        lint_profile: LintProfile,
    ) -> Self {
        let mut h = Sha256::new();
        h.update(DOMAIN_KEY);
        put_bytes(&mut h, ELABORATOR_SEMANTICS.as_bytes());
        put_bytes(&mut h, KERNEL_SEMANTICS.as_bytes());
        put_bytes(&mut h, module.as_bytes());
        h.update(&sha256(source.as_bytes()));
        h.update(&[match lint_profile {
            LintProfile::Default => 0,
            LintProfile::Stdlib => 1,
        }]);
        h.update(&(dependencies.ordered_interface_hashes().len() as u64).to_le_bytes());
        for dependency in dependencies.ordered_interface_hashes() {
            h.update(dependency);
        }
        Self(h.finish())
    }

    pub fn bytes(self) -> [u8; 32] {
        self.0
    }
}

fn put_bytes(h: &mut Sha256, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

pub struct LoadedModule {
    pub delta: ModuleDelta,
    pub warnings: Vec<Warning>,
    /// V1 conservatively identifies the complete semantic artifact. A later
    /// interface projection can stop proof-only edits invalidating consumers
    /// without changing the loader/storage boundary.
    pub interface_hash: [u8; 32],
}

#[derive(Debug)]
pub enum ModuleCacheError {
    Io(std::io::Error),
    Corrupt(&'static str),
    Decode(ModuleImageDecodeError),
}

impl fmt::Display for ModuleCacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "{e}"),
            Self::Corrupt(why) => write!(f, "{why}"),
            Self::Decode(e) => write!(f, "semantic image was rejected: {e}"),
        }
    }
}

impl std::error::Error for ModuleCacheError {}

impl From<std::io::Error> for ModuleCacheError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

pub struct ModuleImageCache {
    dir: PathBuf,
    limits: ModuleImageLimits,
}

impl ModuleImageCache {
    pub fn new(cache_dir: PathBuf) -> Self {
        Self {
            dir: cache_dir.join("modules-v1"),
            limits: ModuleImageLimits::default(),
        }
    }

    pub fn with_limits(cache_dir: PathBuf, limits: ModuleImageLimits) -> Self {
        Self {
            dir: cache_dir.join("modules-v1"),
            limits,
        }
    }

    pub fn path(&self, key: ModuleCacheKey) -> PathBuf {
        self.dir.join(format!("{}.hmi", hex(&key.0)))
    }

    pub fn interface_hash(delta: &ModuleDelta) -> [u8; 32] {
        artifact_interface(&delta.to_image_bytes())
    }

    /// Absence is an ordinary miss. An existing but unusable artifact is
    /// distinguished so callers can report corruption before rebuilding.
    pub fn load(
        &self,
        key: ModuleCacheKey,
        dependency_psi: GlobalCtx,
        source_len: usize,
    ) -> Result<Option<LoadedModule>, ModuleCacheError> {
        let path = self.path(key);
        let file = match std::fs::File::open(&path) {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        let max_file = self.limits.max_bytes.saturating_add(HEADER + CHECKSUM);
        // A metadata preflight alone has a TOCTOU hole: the file can grow
        // before the read. Cap the read itself and reject the sentinel byte.
        let mut bytes = Vec::new();
        file.take(max_file.saturating_add(1) as u64)
            .read_to_end(&mut bytes)?;
        if bytes.len() > max_file {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact exceeds the byte limit",
            ));
        }
        if bytes.len() < HEADER + CHECKSUM || &bytes[..8] != MAGIC {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact has an invalid header",
            ));
        }
        if bytes[8..40] != key.0 {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact has the wrong cache key",
            ));
        }
        let mut interface_hash = [0; 32];
        interface_hash.copy_from_slice(&bytes[40..72]);
        let semantic_len = u64::from_le_bytes(bytes[72..80].try_into().unwrap());
        let semantic_len = usize::try_from(semantic_len)
            .map_err(|_| ModuleCacheError::Corrupt("module cache artifact length overflows"))?;
        let warning_count = u64::from_le_bytes(bytes[80..88].try_into().unwrap());
        let warning_count = usize::try_from(warning_count)
            .map_err(|_| ModuleCacheError::Corrupt("module warning count overflows"))?;
        if warning_count > self.limits.max_sequence {
            return Err(ModuleCacheError::Corrupt("module warning count exceeds the limit"));
        }
        let semantic_end = HEADER
            .checked_add(semantic_len)
            .ok_or(ModuleCacheError::Corrupt(
                "module cache artifact length overflows",
            ))?;
        let checksum_at = bytes.len() - CHECKSUM;
        if semantic_end > checksum_at {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact length does not match",
            ));
        }
        if sha256(&bytes[..checksum_at]) != bytes[checksum_at..] {
            return Err(ModuleCacheError::Corrupt(
                "module cache artifact checksum does not match",
            ));
        }
        let semantic = &bytes[HEADER..semantic_end];
        if artifact_interface(semantic) != interface_hash {
            return Err(ModuleCacheError::Corrupt(
                "module cache interface identity does not match",
            ));
        }
        let delta = ModuleDelta::from_image_bytes(semantic, dependency_psi, self.limits)
            .map_err(ModuleCacheError::Decode)?;
        let warnings = decode_warnings(
            &bytes[semantic_end..checksum_at],
            warning_count,
            source_len,
            self.limits,
        )?;
        Ok(Some(LoadedModule {
            delta,
            warnings,
            interface_hash,
        }))
    }

    /// Publish through a unique temporary sibling and atomic rename. Leaving
    /// a temporary file after a crash is harmless: readers name only the
    /// content-addressed final path.
    pub fn publish(
        &self,
        key: ModuleCacheKey,
        delta: &ModuleDelta,
        warnings: &[Warning],
    ) -> Result<[u8; 32], ModuleCacheError> {
        let semantic = delta.to_image_bytes();
        if semantic.len() > self.limits.max_bytes {
            return Err(ModuleCacheError::Corrupt(
                "semantic image exceeds the byte limit",
            ));
        }
        let interface_hash = artifact_interface(&semantic);
        if warnings.len() > self.limits.max_sequence {
            return Err(ModuleCacheError::Corrupt("module warning count exceeds the limit"));
        }
        let mut bytes = Vec::with_capacity(HEADER + semantic.len() + CHECKSUM);
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(&key.0);
        bytes.extend_from_slice(&interface_hash);
        bytes.extend_from_slice(&(semantic.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&(warnings.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&semantic);
        encode_warnings(&mut bytes, warnings, self.limits)?;
        if bytes.len() > HEADER.saturating_add(self.limits.max_bytes) {
            return Err(ModuleCacheError::Corrupt("module cache artifact exceeds the byte limit"));
        }
        let checksum = sha256(&bytes);
        bytes.extend_from_slice(&checksum);

        std::fs::create_dir_all(&self.dir)?;
        let final_path = self.path(key);
        let temp_path = temporary_sibling(&final_path);
        if let Err(error) = std::fs::write(&temp_path, bytes)
            .and_then(|()| std::fs::rename(&temp_path, &final_path))
        {
            let _ = std::fs::remove_file(&temp_path);
            return Err(error.into());
        }
        Ok(interface_hash)
    }
}

fn encode_warnings(
    out: &mut Vec<u8>,
    warnings: &[Warning],
    limits: ModuleImageLimits,
) -> Result<(), ModuleCacheError> {
    for warning in warnings {
        out.push(match warning.lint {
            Lint::UnreachableMatchArm => 0,
            Lint::MatchFunctionApplication => 1,
            Lint::TightNegationSpacing => 2,
            Lint::StdlibUnicodeSpelling => 3,
            Lint::NestedCall => 4,
            Lint::UnusedPatternBinder => 5,
            Lint::OperatorFallback => 6,
            Lint::RedundantMatchMotive => 7,
        });
        put_warning_string(out, &warning.msg, limits)?;
        put_span(out, warning.span);
        match &warning.fix {
            None => out.push(0),
            Some(fix) => {
                out.push(1);
                put_span(out, fix.span);
                put_warning_string(out, &fix.replacement, limits)?;
            }
        }
    }
    Ok(())
}

fn put_warning_string(
    out: &mut Vec<u8>,
    value: &str,
    limits: ModuleImageLimits,
) -> Result<(), ModuleCacheError> {
    if value.len() > limits.max_string_bytes {
        return Err(ModuleCacheError::Corrupt("module warning string exceeds the limit"));
    }
    out.extend_from_slice(&(value.len() as u64).to_le_bytes());
    out.extend_from_slice(value.as_bytes());
    Ok(())
}

fn put_span(out: &mut Vec<u8>, span: Span) {
    out.extend_from_slice(&(span.start as u64).to_le_bytes());
    out.extend_from_slice(&(span.end as u64).to_le_bytes());
}

fn decode_warnings(
    bytes: &[u8],
    count: usize,
    source_len: usize,
    limits: ModuleImageLimits,
) -> Result<Vec<Warning>, ModuleCacheError> {
    let mut reader = WarningReader { bytes, at: 0, source_len, limits };
    let mut warnings = Vec::with_capacity(count);
    for _ in 0..count {
        let lint = match reader.byte()? {
            0 => Lint::UnreachableMatchArm,
            1 => Lint::MatchFunctionApplication,
            2 => Lint::TightNegationSpacing,
            3 => Lint::StdlibUnicodeSpelling,
            4 => Lint::NestedCall,
            5 => Lint::UnusedPatternBinder,
            6 => Lint::OperatorFallback,
            7 => Lint::RedundantMatchMotive,
            _ => return Err(ModuleCacheError::Corrupt("module warning has an invalid lint tag")),
        };
        let msg = reader.string()?;
        let span = reader.span()?;
        let fix = match reader.byte()? {
            0 => None,
            1 => Some(LintFix { span: reader.span()?, replacement: reader.string()? }),
            _ => return Err(ModuleCacheError::Corrupt("module warning has an invalid fix tag")),
        };
        warnings.push(Warning { lint, msg, span, fix });
    }
    if reader.at != bytes.len() {
        return Err(ModuleCacheError::Corrupt("module warning payload has trailing bytes"));
    }
    Ok(warnings)
}

struct WarningReader<'a> {
    bytes: &'a [u8],
    at: usize,
    source_len: usize,
    limits: ModuleImageLimits,
}

impl WarningReader<'_> {
    fn take(&mut self, len: usize) -> Result<&[u8], ModuleCacheError> {
        let end = self
            .at
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(ModuleCacheError::Corrupt("module warning payload is truncated"))?;
        let value = &self.bytes[self.at..end];
        self.at = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, ModuleCacheError> {
        Ok(self.take(1)?[0])
    }

    fn usize(&mut self) -> Result<usize, ModuleCacheError> {
        let value = u64::from_le_bytes(self.take(8)?.try_into().unwrap());
        usize::try_from(value)
            .map_err(|_| ModuleCacheError::Corrupt("module warning integer overflows"))
    }

    fn string(&mut self) -> Result<String, ModuleCacheError> {
        let len = self.usize()?;
        if len > self.limits.max_string_bytes {
            return Err(ModuleCacheError::Corrupt("module warning string exceeds the limit"));
        }
        let bytes = self.take(len)?;
        let value = std::str::from_utf8(bytes)
            .map_err(|_| ModuleCacheError::Corrupt("module warning string is not UTF-8"))?;
        Ok(value.to_string())
    }

    fn span(&mut self) -> Result<Span, ModuleCacheError> {
        let start = self.usize()?;
        let end = self.usize()?;
        if start > end || end > self.source_len {
            return Err(ModuleCacheError::Corrupt("module warning span is outside its source"));
        }
        Ok(Span { start, end })
    }
}

fn artifact_interface(semantic: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(DOMAIN_INTERFACE);
    h.update(semantic);
    h.finish()
}

fn temporary_sibling(path: &Path) -> PathBuf {
    let id = TEMP_ID.fetch_add(1, Ordering::Relaxed);
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("module.hmi");
    path.with_file_name(format!(".{name}.{}.{}.tmp", std::process::id(), id))
}
