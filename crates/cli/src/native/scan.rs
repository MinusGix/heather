//! Bounded scanner bodies: source decisions and arithmetic, with a reusable
//! input/cursor/fuel loop. Unsupported syntax is refused before publication.
use super::*;
use heather_syntax::{Expr as SourceExpr, ExprKind, Block as SourceBlock, Stmt, Item};
use std::collections::BTreeMap;

#[derive(Clone)]
enum Word { Byte, Value, Literal(u64), Binary(&'static str, Box<Word>, Box<Word>) }
impl Word {
    fn size(&self) -> usize { match self { Self::Binary(_,a,b) => 1+a.size()+b.size(), _ => 1 } }
    fn source(&self) -> String {
        match self {
            Self::Byte => "byte".into(), Self::Value => "value".into(),
            Self::Literal(n) => format!("bitvec::ofNat(64, {n})"),
            Self::Binary(op, a, b) => format!("bitvec::{op}(64, {}, {})", a.source(), b.source()),
        }
    }
}
#[derive(Clone)]
enum Tree { Stop, Overflow, Next(Word), Branch(Word, Word, Box<Tree>, Box<Tree>) }
impl Tree {
    fn source(&self) -> String {
        match self {
            Self::Stop => "Stop".into(), Self::Overflow => "Overflow".into(),
            Self::Next(w) => format!("Next({})", w.source()),
            Self::Branch(a,b,yes,no) => format!("match bitvec::unsigned_lt_bit(64, {}, {}) {{ True => {}, False => {} }}", a.source(), b.source(), yes.source(), no.source()),
        }
    }
}
fn call(expr: &SourceExpr) -> Option<(&str, &[SourceExpr])> {
    match &expr.kind {
        ExprKind::App { head, args, named, .. } if named.is_empty() =>
            if let ExprKind::Var(name) = &head.kind { Some((name, args)) } else { None },
        _ => None,
    }
}
fn word(expr: &SourceExpr, locals: &BTreeMap<String,Word>, budget: &mut usize) -> Result<Word,String> {
    if *budget == 0 { return Err("scanner body exceeds its 256-node source limit".into()); }
    *budget -= 1;
    if let ExprKind::Var(name) = &expr.kind {
        let value = locals.get(name).ok_or_else(|| format!("unsupported scanner value `{name}`"))?;
        if value.size() > *budget { return Err("scanner alias expansion exceeds its 256-node source limit".into()); }
        *budget -= value.size();
        return Ok(value.clone());
    }
    if let Some((name, args)) = call(expr) {
        if args.len() == 2 && name == "bitvec::ofNat" && matches!(args[0].kind, ExprKind::Num(64)) {
            if let ExprKind::Num(n) = args[1].kind { return Ok(Word::Literal(n)); }
        }
        if args.len() == 3 && matches!(args[0].kind, ExprKind::Num(64)) {
            let op = match name { "bitvec::add" => "add", "bitvec::sub" => "sub", "bitvec::band" => "band", "bitvec::bor" => "bor", "bitvec::bxor" => "bxor", _ => return Err("unsupported scanner word operation".into()) };
            return Ok(Word::Binary(op, Box::new(word(&args[1], locals, budget)?), Box::new(word(&args[2], locals, budget)?)));
        }
    }
    Err("scanner values require word inputs, literals, or supported bitvector arithmetic".into())
}
fn block(block: &SourceBlock, locals: &BTreeMap<String,Word>, budget: &mut usize) -> Result<Tree,String> {
    if !block.ons.is_empty() { return Err("scanner proof discharges are outside the source fragment".into()); }
    let mut locals = locals.clone();
    for stmt in &block.stmts {
        let Stmt::Let { name, expr, .. } = stmt else { return Err("scanner bodies support only scalar let bindings".into()); };
        let value = word(expr, &locals, budget)?; locals.insert(name.clone(), value);
    }
    tree(&block.result, &locals, budget)
}
fn tree(expr: &SourceExpr, locals: &BTreeMap<String,Word>, budget: &mut usize) -> Result<Tree,String> {
    if *budget == 0 { return Err("scanner body exceeds its 256-node source limit".into()); }
    *budget -= 1;
    match &expr.kind {
        ExprKind::Block(body) => return block(body, locals, budget),
        ExprKind::Var(name) if name == "Stop" => return Ok(Tree::Stop),
        ExprKind::Var(name) if name == "Overflow" => return Ok(Tree::Overflow),
        ExprKind::Match { scrut, arms, .. } => {
            let ("bitvec::unsigned_lt_bit", args) = call(scrut).ok_or("scanner conditions require unsigned word comparison")? else { return Err("scanner conditions require unsigned word comparison".into()); };
            if args.len() != 3 || !matches!(args[0].kind, ExprKind::Num(64)) || arms.len() != 2 || arms.iter().any(|a| !a.binders.is_empty() || a.default) { return Err("unsupported scanner match".into()); }
            let yes = arms.iter().find(|a| a.ctor == "True").ok_or("missing True arm")?;
            let no = arms.iter().find(|a| a.ctor == "False").ok_or("missing False arm")?;
            return Ok(Tree::Branch(word(&args[1],locals,budget)?, word(&args[2],locals,budget)?, Box::new(tree(&yes.body,locals,budget)?), Box::new(tree(&no.body,locals,budget)?)));
        }
        _ => {}
    }
    if let Some(("Next", args)) = call(expr) {
        if args.len() == 1 { return Ok(Tree::Next(word(&args[0],locals,budget)?)); }
    }
    Err("scanner branches must return Stop, Overflow, or Next(word)".into())
}


struct BodyCompiler<'a> { elab: &'a Elaborator, proof: &'a mut Module, prefix: String, next: usize }
struct Body { name: String, instructions: Vec<Instruction>, yes: Option<Box<Body>>, no: Option<Box<Body>>, outcome: u8 }
impl BodyCompiler<'_> {
    fn lower(&mut self, tree: &Tree) -> Result<Body,String> {
        let name = format!("{}_node_{}", self.prefix, self.next); self.next += 1;
        let (code, instructions, yes, no, outcome, proof) = match tree {
            Tree::Stop => ("ScanStop".into(), vec![], None, None, 1, "refl".into()),
            Tree::Overflow => ("ScanOverflow".into(), vec![], None, None, 2, "refl".into()),
            Tree::Next(word) => {
                let helper = format!("{name}_word");
                let declaration = format!("fn {helper}(byte, value: BitVec(64)) -> BitVec(64) {{ {} }}", word.source());
                self.proof.raw(declaration.clone());
                let (instructions, result_proof) = match word {
                    Word::Byte => (vec![Instruction::MovRR { destination:Gpr::Rax,source:Gpr::Rdi }], "refl".into()),
                    Word::Value => (vec![Instruction::MovRR { destination:Gpr::Rax,source:Gpr::Rsi }], "refl".into()),
                    Word::Literal(n) => (vec![Instruction::MovRI { destination:Gpr::Rax,immediate:*n }], "refl".into()),
                    Word::Binary(..) => {
                        let mut elab = self.elab.fork();
                        elab.elab_module_source("scan_expressions", &format!("import bitvec; {declaration}")).map_err(|e| e.render(&declaration))?;
                        let emission = function_ir_source::generate_elaborated_x86(&elab, &helper, &format!("scan_expressions::{helper}"), [Gpr::Rdi,Gpr::Rsi], &[Gpr::Rax,Gpr::Rcx,Gpr::Rdx], Gpr::Rax).map_err(|e| e.to_string())?;
                        self.proof.raw(emission.text.replace("import scan_expressions;", "").replace("scan_expressions::", ""));
                        elf::valuation_with_parameters(self.proof, &format!("{helper}_input"), &helper, &emission.reflected.region,
                            [Expr::raw("bitvec::ofNat(width, bitvec::toNat(64, left))"),Expr::raw("bitvec::ofNat(width, bitvec::toNat(64, right))")], &[("left","BitVec(64)"),("right","BitVec(64)")])?;
                        let l = "read_gpr(Rdi, before.gprs)"; let r = "read_gpr(Rsi, before.gprs)";
                        let values = format!("{helper}_input_values({l}, {r})");
                        let result = format!("trans({helper}_refines_function_ir({values}, before, bitvec::ofNat_toNat(64, {l}), bitvec::ofNat_toNat(64, {r}), {helper}_input_entry_graph({l}, {r})), trans({helper}_denotes_source({values}, {helper}_input_entry_graph({l}, {r})), trans(cong_fn<BitVec(64), BitVec(64)>(λ left => {helper}(left, {values}(64, 1)), bitvec::ofNat_toNat(64, {l})), cong_fn<BitVec(64), BitVec(64)>(λ right => {helper}({l}, right), bitvec::ofNat_toNat(64, {r})))))");
                        (emission.instructions, result)
                    }
                };
                let ins = instructions.iter().map(|i| i.heather_expr().render()).collect::<Vec<_>>().join(", ");
                (format!("ScanNext([{ins}])"), instructions, None, None, 0,
                    format!("cong_fn<BitVec(64), ScanStep>(λ value => Next(value), {result_proof})"))
            }
            Tree::Branch(left,right,yes,no) => {
                let atom = |word:&Word, destination| -> Result<Instruction,String> { Ok(match word {
                    Word::Byte => Instruction::MovRR{destination,source:Gpr::Rdi},
                    Word::Value => Instruction::MovRR{destination,source:Gpr::Rsi},
                    Word::Literal(immediate) => Instruction::MovRI{destination,immediate:*immediate},
                    _ => return Err("scanner comparison operands currently require inputs or literals".into()),
                }) };
                let instructions = vec![atom(left,Gpr::Rax)?,atom(right,Gpr::Rcx)?,Instruction::CmpRR{left:Gpr::Rax,right:Gpr::Rcx}];
                let yes = self.lower(yes)?; let no = self.lower(no)?;
                let ins = instructions.iter().map(|i| i.heather_expr().render()).collect::<Vec<_>>().join(", ");
                let after = format!("execute_block_normal([{ins}], before)");
                let proof = format!("scan_choose_congr(({after}).flags.cf, scan_body({}(), {after}), scan_body({}(), {after}), {}_source(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)), {}_source(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)), {}_correct({after}), {}_correct({after}))",yes.name,no.name,yes.name,no.name,yes.name,no.name);
                (format!("ScanBranch([{ins}], {}(), {}())",yes.name,no.name),instructions,Some(Box::new(yes)),Some(Box::new(no)),3,proof)
            }
        };
        self.proof.raw(format!("fn {name}() -> ScanCode {{ {code} }}\nfn {name}_source(byte, value: BitVec(64)) -> ScanStep {{ {} }}",tree.source()));
        let frame = format!("λ before => {}", (0..13).fold("refl".to_string(), |tail,_| format!("⟨refl, {tail}⟩")));
        let frame = if let Tree::Branch(left,right,_,_) = tree {
            let instructions = instructions.iter().map(|i|i.heather_expr().render()).collect::<Vec<_>>().join(", ");
            let after = format!("execute_block_normal([{instructions}], before)");
            let substitute = |word:&Word| word.source().replace("byte", "read_gpr(Rdi, before.gprs)").replace("value", "read_gpr(Rsi, before.gprs)");
            let head = format!("λ before => scan_compare_frame(before, {}, {}, ({after}).flags, ({after}).rip)",substitute(left),substitute(right));
            format!("scan_branch_frame<M>([{instructions}], {}(), {}(), {head}, {}_frame<M>(), {}_frame<M>())",yes.as_ref().unwrap().name,no.as_ref().unwrap().name,yes.as_ref().unwrap().name,no.as_ref().unwrap().name)
        } else if outcome == 0 { frame } else { "trivial".into() };
        self.proof.raw(format!("theorem {name}_frame<M>(): ScanCodeFrame<M>({name}()) {{ {frame} }}"));
        self.proof.raw(format!("theorem {name}_correct<M>(before: MachineState<M>): scan_body({name}(), before) = {name}_source(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)) {{ {proof} }}"));
        Ok(Body { name,instructions,yes,no,outcome })
    }
}

impl Body {
    fn size(&self) -> usize {
        encode(&self.instructions).len() + if self.outcome == 3 { 11 + self.yes.as_ref().unwrap().size() + self.no.as_ref().unwrap().size() } else { 5 }
    }
    fn bytes(&self, offset: usize, advance: usize, done: usize, overflow: usize) -> Vec<u8> {
        let mut bytes = encode(&self.instructions);
        let branch = offset + bytes.len();
        if self.outcome == 3 {
            let yes = self.yes.as_ref().unwrap(); let no = self.no.as_ref().unwrap();
            let yes_start = branch + 11; let no_start = yes_start + yes.size();
            bytes.extend(jcc(0x82, branch, yes_start)); bytes.extend(jump(branch+6, no_start));
            bytes.extend(yes.bytes(yes_start, advance, done, overflow));
            bytes.extend(no.bytes(no_start, advance, done, overflow));
        } else { bytes.extend(jump(branch, match self.outcome { 0 => advance, 1 => done, _ => overflow })); }
        bytes
    }
}
fn jump(offset: usize, target: usize) -> Vec<u8> {
    let mut bytes = vec![0xe9]; bytes.extend(((target as i64 - offset as i64 - 5) as i32).to_le_bytes()); bytes
}
fn jcc(opcode: u8, offset: usize, target: usize) -> Vec<u8> {
    let mut bytes = vec![0x0f,opcode]; bytes.extend(((target as i64 - offset as i64 - 6) as i32).to_le_bytes()); bytes
}
fn mov(destination:Gpr, source:Gpr) -> Instruction { Instruction::MovRR{destination,source} }
fn imm(destination:Gpr, immediate:u64) -> Instruction { Instruction::MovRI{destination,immediate} }
fn cmp(left:Gpr,right:Gpr) -> Instruction { Instruction::CmpRR{left,right} }

fn source_tree(source_text:&str, symbol:&str) -> Result<Tree,String> {
    let file = heather_syntax::parse_file(source_text).map_err(|e| format!("{e:?}"))?;
    let d = file.items.iter().find_map(|item| match item { Item::Decl(d) if d.name == symbol => Some(d), _ => None }).ok_or("scanner source function not found")?;
    if d.params.len() != 2 || !d.tyvars.is_empty() || d.is_meta || d.kind != heather_syntax::DeclKind::Fn { return Err("scanner bodies require two word parameters".into()); }
    let locals = [(d.params[0].name.clone(),Word::Byte),(d.params[1].name.clone(),Word::Value)].into_iter().collect();
    block(&d.body,&locals,&mut 256)
}

pub(super) fn preflight(source_text:&str, symbol:&str) -> Result<(),String> {
    source_tree(source_text,symbol).map(|_| ())
}

pub(super) fn generate(elab: &Elaborator, proof:&mut Module, prefix:&str, source_name:&str, source_text:&str) -> Result<Vec<u8>,String> {
    let tree = source_tree(source_text,source_name.rsplit("::").next().unwrap())?;
    proof.raw(format!("import byte_scan;\nimport x86_64_scan_body;\nimport x86_64_scan_gate;\nimport x86_64_buffer_cursor;\nimport {};", source_name.rsplit_once("::").unwrap().0));
    let mut compiler = BodyCompiler {elab,proof,prefix:prefix.into(),next:0};
    let body = compiler.lower(&tree)?;
    let name = &body.name;
    proof.raw(format!("theorem {prefix}_source(byte, value: BitVec(64)): {name}_source(byte, value) = {source_name}(byte, value) {{ refl }}"));
    proof.raw(format!("theorem {prefix}_body_correct<M>(before: MachineState<M>): scan_body({name}(), before) = {source_name}(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs)) {{ trans({name}_correct(before), {prefix}_source(read_gpr(Rdi, before.gprs), read_gpr(Rsi, before.gprs))) }}"));
    proof.raw(format!("theorem {prefix}_bounded_refinement<M>(fuel: Nat, before: MachineState<M>, length: BitVec(64), at: BitVec(64) -> BitVec(8), cursor: BitVec(64)): scan(fuel, length, at, cursor, λ byte value => scan_body({name}(), scan_inputs(before, byte, value))) = scan(fuel, length, at, cursor, {source_name}) {{ scan_run_congr(fuel, length, at, λ byte value => scan_body({name}(), scan_inputs(before, byte, value)), {source_name}, λ byte value => scan_body_inputs({name}(), {source_name}, λ state => {prefix}_body_correct(state), before, byte, value), cursor, bitvec::zero(64), False) }}"));
    const FUEL:u64 = 256;
    let advance = 62 + body.size(); let done = advance+24; let overflow = done+49; let limit = done+64; let finish = done+74;
    if finish+6 > 4096 { return Err("scanner exceeds its 4096-byte code limit".into()); }
    let mut bytes = encode(&[mov(Gpr::R8,Gpr::Rdi),mov(Gpr::R9,Gpr::Rsi),mov(Gpr::R10,Gpr::Rdx),imm(Gpr::R11,FUEL),imm(Gpr::Rsi,0),cmp(Gpr::R10,Gpr::R9)]);
    bytes.extend(jcc(0x83,32,done));
    bytes.extend(encode(&[imm(Gpr::Rax,0),cmp(Gpr::R11,Gpr::Rax)])); bytes.extend(jcc(0x84,51,limit));
    bytes.extend([0x4b,0x0f,0xb6,0x3c,0x10]);
    bytes.extend(body.bytes(62,advance,done,overflow));
    bytes.extend(encode(&[mov(Gpr::Rsi,Gpr::Rax),imm(Gpr::Rax,1),Instruction::AddRR{destination:Gpr::R10,source:Gpr::Rax},Instruction::SubRR{destination:Gpr::R11,source:Gpr::Rax}])); bytes.extend(jump(advance+19,29));
    bytes.extend(encode(&[imm(Gpr::Rax,FUEL),cmp(Gpr::R11,Gpr::Rax)])); bytes.extend(jcc(0x84,done+13,done+34));
    for (status,offset) in [(0,done+29),(1,done+44),(2,done+59)] { bytes.extend(encode(&[imm(Gpr::Rcx,status)])); bytes.extend(jump(offset,finish)); }
    bytes.extend(encode(&[imm(Gpr::Rcx,3),mov(Gpr::Rax,Gpr::Rsi),mov(Gpr::Rdx,Gpr::R10)]));
    assert_eq!(bytes.len(),finish+6);
    // Physical bounds/fuel branches and the permitted byte load, from offset 29.
    // The repeated loop/body/back-edge invariant remains a separate obligation.
    let d = format!("scan_relative(38, {done})"); let l = format!("scan_relative(57, {limit})");
    proof.raw(format!("theorem {prefix}_guarded_entry<M>(access: BufferAccess<M>, before: MachineState<M>, allowed: ScanGateReadable(access, before)): ScanGateExecution<M>(access, {d}, {l}, before, scan_gate(access, {d}, {l}, before)) {{ scan_gate_safe(access, {d}, {l}, before, allowed) }}"));
    proof.raw(format!("theorem {prefix}_entry_frame<M>(access: BufferAccess<M>, before: MachineState<M>): ScanGateFrame(before, scan_gate_state(scan_gate(access, {d}, {l}, before))) {{ scan_gate_frame(access, {d}, {l}, before) }}"));
    proof.raw(format!("theorem {prefix}_end_target<M>(before: MachineState<M>): (scan_bounds_edge(False, {d}, before)).rip = next_rip(before.rip, {}) {{ scan_end_rip({d}, {}, refl, before) }}", done-29, done-38));
    proof.raw(format!("theorem {prefix}_limit_target<M>(before: MachineState<M>): (scan_fuel_edge(True, {l}, scan_bounds_edge(True, {d}, before))).rip = next_rip(before.rip, {}) {{ scan_limit_rip({d}, {l}, {}, refl, before) }}", limit-29, limit-57));
    proof.raw(format!("theorem {prefix}_body_entry_target<M>(access: BufferAccess<M>, before: MachineState<M>): (scan_load(access, scan_fuel_edge(False, {l}, scan_bounds_edge(True, {d}, before)))).rip = next_rip(before.rip, 33) {{ scan_ready_rip(access, {d}, {l}, before) }}"));
    let (body_bytes, body_proof) = body.certify_bytes(proof,&bytes,62,advance,done,overflow);
    let head = format!("{prefix}_head"); let tail = format!("{prefix}_tail");
    byte_chain(proof,&head,&bytes[..62]); byte_chain(proof,&tail,&bytes[advance..]);
    proof.raw(format!("theorem {head}_encoding(): scan_prefix_bytes({FUEL}, {done}, {limit}) = {head}() {{ refl }}"));
    proof.raw(format!("theorem {tail}_encoding(): scan_suffix_bytes({FUEL}, {advance}) = {tail}() {{ refl }}"));
    let hm = format!("scan_prefix_bytes({FUEL}, {done}, {limit})");
    let bm = format!("scan_body_bytes({name}(), 62, {advance}, {done}, {overflow})");
    let tm = format!("scan_suffix_bytes({FUEL}, {advance})");
    proof.raw(format!("fn {prefix}_published_bytes() -> List<BitVec(8)> {{ {head}() ++ {body_bytes} ++ {tail}() }}"));
    proof.raw(format!("theorem {prefix}_exported_bytes(): scan_program_bytes({name}(), {FUEL}) = {prefix}_published_bytes() {{ scan_bytes_join({hm}, {head}(), ({bm} ++ {tm}), ({body_bytes} ++ {tail}()), {head}_encoding(), scan_bytes_join({bm}, {body_bytes}, {tm}, {tail}(), {body_proof}, {tail}_encoding())) }}"));
    Ok(bytes)
}

impl Body {
    fn certify_bytes(&self, proof:&mut Module, bytes:&[u8], offset:usize, advance:usize, done:usize, overflow:usize) -> (String,String) {
        let published = format!("{}_published",self.name);
        let certified = format!("{}_encoding",self.name);
        let expected = format!("scan_body_bytes({}(), {offset}, {advance}, {done}, {overflow})",self.name);
        if self.outcome != 3 {
            byte_chain(proof,&published,&bytes[offset..offset+self.size()]);
            proof.raw(format!("theorem {certified}(): {expected} = {published}() {{ refl }}"));
        } else {
            let head = encode(&self.instructions).len()+11;
            let yes = self.yes.as_ref().unwrap(); let no = self.no.as_ref().unwrap();
            let yes_start = offset+head; let no_start = yes_start+yes.size();
            let (y,yp) = yes.certify_bytes(proof,bytes,yes_start,advance,done,overflow);
            let (n,np) = no.certify_bytes(proof,bytes,no_start,advance,done,overflow);
            let prefix = format!("{}_prefix",self.name); byte_chain(proof,&prefix,&bytes[offset..yes_start]);
            let instructions = self.instructions.iter().map(|i|i.heather_expr().render()).collect::<Vec<_>>().join(", ");
            let branch = yes_start-11;
            let prefix_model = format!("canonical_block_bytes([{instructions}]) ++ scan_jcc(0x82, {branch}, {yes_start}) ++ scan_jump({}, {no_start})",branch+6);
            proof.raw(format!("theorem {prefix}_encoding(): {prefix_model} = {prefix}() {{ refl }}"));
            proof.raw(format!("fn {published}() -> List<BitVec(8)> {{ {prefix}() ++ {y} ++ {n} }}"));
            let ym = format!("scan_body_bytes({}(), {yes_start}, {advance}, {done}, {overflow})",yes.name);
            let nm = format!("scan_body_bytes({}(), {no_start}, {advance}, {done}, {overflow})",no.name);
            proof.raw(format!("theorem {certified}(): {expected} = {published}() {{ scan_bytes_join(({prefix_model}), {prefix}(), ({ym} ++ {nm}), ({y} ++ {n}), {prefix}_encoding(), scan_bytes_join({ym}, {y}, {nm}, {n}, {yp}, {np})) }}"));
        }
        (format!("{published}()"),format!("{certified}()"))
    }
}
