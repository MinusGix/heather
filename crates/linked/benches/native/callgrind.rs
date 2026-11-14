//! Instructions counted exactly: callgrind over this binary's `count`
//! mode, and the counted addresses joined with `objdump`'s disassembly of
//! the same file to say what kind of instruction each was. Exact,
//! repeatable and machine independent, which is why the optimizer's
//! counter is this and not a time.
//!
//! Without `valgrind` (or `objdump`, for the breakdown) a count is `None`
//! and the table says "not measured"; it never fails the run.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::process::Command;

pub fn available() -> bool {
    Command::new("valgrind").arg("--version").output().is_ok_and(|o| o.status.success())
}

/// One callgrind run: every instruction's count by address, their sum, and
/// where the executable was mapped (to find an address in the file).
pub struct Counted {
    pub total: u64,
    pub by_address: HashMap<u64, u64>,
    /// The load bias: an address minus this is the file's virtual address.
    pub bias: u64,
}

/// Run `count <case> <n>` under callgrind. With `toggle`, only what runs
/// inside that function (and what it calls) is counted; without, all of it.
pub fn run(case: &str, n: u64, toggle: Option<&str>, work: &Path) -> Option<Counted> {
    let exe = std::env::current_exe().ok()?;
    let out = work.join(format!("callgrind.{case}.{n}.out"));
    let mut command = Command::new("valgrind");
    command.args(["--tool=callgrind", "--dump-instr=yes", "--dump-line=no"]);
    if let Some(function) = toggle {
        command.arg("--collect-atstart=no").arg(format!("--toggle-collect={function}"));
    }
    command.arg(format!("--callgrind-out-file={}", out.display()));
    command.arg(&exe).args(["count", case, &n.to_string()]);
    let output = command.output().ok()?;
    if !output.status.success() {
        eprintln!("callgrind over `count {case}` failed:\n{}", String::from_utf8_lossy(&output.stderr));
        return None;
    }
    let stderr = String::from_utf8_lossy(&output.stderr);
    let bias = stderr
        .lines()
        .find_map(|l| {
            let mut f = l.strip_prefix("mapped\t")?.split('\t');
            let start = u64::from_str_radix(f.next()?, 16).ok()?;
            let offset = u64::from_str_radix(f.next()?, 16).ok()?;
            Some(start - offset)
        })
        .unwrap_or(0);
    let text = std::fs::read_to_string(&out).ok()?;
    let _ = std::fs::remove_file(&out);
    let (total, by_address) = parse(&text)?;
    Some(Counted { total, by_address, bias })
}

/// A number as callgrind writes one: hexadecimal with `0x`, else decimal.
fn number(s: &str) -> Option<u64> {
    match s.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => s.parse().ok(),
    }
}

/// The self cost of every instruction, from a callgrind file written with
/// `--dump-instr=yes --dump-line=no` (one position, the address; one event,
/// `Ir`). A `calls=` line is followed by the call's inclusive cost, which is
/// not this instruction's own and is skipped, but its position still moves
/// the relative ones after it. The sum is held to the file's own total.
fn parse(text: &str) -> Option<(u64, HashMap<u64, u64>)> {
    let mut by_address: HashMap<u64, u64> = HashMap::new();
    let mut last: u64 = 0;
    let mut inclusive_next = false;
    let mut declared = None;
    for line in text.lines() {
        let Some(first) = line.chars().next() else { continue };
        if line.starts_with("calls=") {
            inclusive_next = true;
            continue;
        }
        if let Some(rest) = line.strip_prefix("summary:").or_else(|| line.strip_prefix("totals:")) {
            declared = rest.trim().parse::<u64>().ok();
            continue;
        }
        if !(first.is_ascii_digit() || first == '+' || first == '-' || first == '*') {
            continue;
        }
        let mut fields = line.split_whitespace();
        let position = fields.next()?;
        let address = match position.as_bytes()[0] {
            b'+' => last + number(&position[1..])?,
            b'-' => last - number(&position[1..])?,
            b'*' => last,
            _ => number(position)?,
        };
        last = address;
        let cost = fields.next().map_or(Some(0), number)?;
        if inclusive_next {
            inclusive_next = false;
            continue;
        }
        *by_address.entry(address).or_default() += cost;
    }
    let total: u64 = by_address.values().sum();
    if let Some(declared) = declared {
        if declared != total {
            eprintln!("callgrind: the file's total is {declared} and its lines sum to {total}");
            return None;
        }
    }
    Some((total, by_address))
}

/// The kinds the table breaks the compression's instructions into, in the
/// order it prints them.
pub const KINDS: [&str; 13] = [
    "frame loads/stores",
    "register moves",
    "small immediates",
    "64-bit immediates",
    "byte loads/stores",
    "other memory",
    "shifts",
    "logic",
    "adds",
    "compares",
    "jumps",
    "call/ret/frame",
    "other",
];

/// The kind of one instruction, from objdump's Intel spelling
/// (`mov QWORD PTR [rsp+0x8],rcx`).
fn kind(mnemonic: &str, operands: &str) -> &'static str {
    let memory = operands.contains('[');
    let frame = operands.contains("[rsp");
    match mnemonic {
        "call" | "ret" => "call/ret/frame",
        "add" | "sub" if operands.starts_with("rsp,") => "call/ret/frame",
        "movabs" => "64-bit immediates",
        "mov" | "movzx" | "movsx" | "movsxd" if frame => "frame loads/stores",
        "mov" | "movzx" | "movsx" | "movsxd" if memory && operands.contains("BYTE") => "byte loads/stores",
        "mov" | "movzx" | "movsx" | "movsxd" | "bswap" if memory => "other memory",
        "mov" | "movzx" | "movsx" | "movsxd" => {
            let source = operands.rsplit(',').next().unwrap_or("");
            if source.starts_with("0x") || source.chars().all(|c| c.is_ascii_digit()) { "small immediates" } else { "register moves" }
        }
        "shl" | "shr" | "sar" | "rol" | "ror" => "shifts",
        "and" | "or" | "xor" | "not" => "logic",
        "add" | "sub" | "inc" | "dec" | "neg" | "lea" | "imul" => "adds",
        "cmp" | "test" => "compares",
        m if m.starts_with("set") || m.starts_with("cmov") => "compares",
        m if m.starts_with('j') => "jumps",
        _ => "other",
    }
}

/// What the counted instructions were, by kind, and the calls among them:
/// the counted addresses found in `objdump -d -M intel` of this executable.
/// `None` without `objdump`.
pub fn breakdown(counted: &Counted) -> Option<(BTreeMap<&'static str, u64>, u64)> {
    // Callgrind writes an address in a position-independent executable as
    // the file's own (valgrind 3.22) or as where it ran; whichever finds
    // the counted instructions in the file is the one.
    [0, counted.bias]
        .into_iter()
        .filter_map(|bias| breakdown_at(counted, bias))
        .max_by_key(|(_, _, found)| *found)
        .map(|(kinds, calls, _)| (kinds, calls))
}

/// The breakdown with addresses read as `bias` above the file's, and how
/// many of the counted instructions were found in the disassembly.
fn breakdown_at(counted: &Counted, bias: u64) -> Option<(BTreeMap<&'static str, u64>, u64, u64)> {
    let exe = std::env::current_exe().ok()?;
    let addresses: Vec<u64> = counted.by_address.keys().filter_map(|a| a.checked_sub(bias)).collect();
    let low = *addresses.iter().min()?;
    let high = *addresses.iter().max()? + 16;
    let output = Command::new("objdump")
        .args(["-d", "-M", "intel", "--no-show-raw-insn"])
        .arg(format!("--start-address={low:#x}"))
        .arg(format!("--stop-address={high:#x}"))
        .arg(&exe)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let mut kind_of: HashMap<u64, (&'static str, bool)> = HashMap::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let Some((address, rest)) = line.trim_start().split_once(":\t") else { continue };
        let Ok(address) = u64::from_str_radix(address, 16) else { continue };
        let mut words = rest.trim().splitn(2, ' ');
        let mnemonic = words.next().unwrap_or("");
        let operands = words.next().unwrap_or("").trim();
        kind_of.insert(address, (kind(mnemonic, operands), mnemonic == "call"));
    }
    let mut kinds: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut calls = 0;
    let mut found = 0;
    for (address, count) in &counted.by_address {
        let known = address.checked_sub(bias).and_then(|a| kind_of.get(&a)).copied();
        if known.is_some() {
            found += count;
        }
        let (k, call) = known.unwrap_or(("other", false));
        *kinds.entry(k).or_default() += count;
        if call {
            calls += count;
        }
    }
    Some((kinds, calls, found))
}
