//! `--limits <spec>` and `HEATHER_LIMITS`: resource limits the process sets
//! on itself, so a development run does not need a shell's `ulimit` around
//! it (issues/limits-flag.md).
//!
//! Off unless asked for: a user's `heather check` runs with whatever limits
//! its shell gave it, as before. The limits exist for development, where a
//! runaway normalization or a deep conversion can take a whole machine's
//! memory and not only the process's (CLAUDE.md's rails).
//!
//! A spec is a comma-separated list, read left to right, so a later item
//! loosens or tightens an earlier one:
//!
//! - `dev`: the rail every direct development run takes, `memory=8G,cpu=120,core=0`
//!   (what `ulimit -v 8388608 -t 120 -c 0` sets).
//! - `memory=<size>`: the process's address space (`RLIMIT_AS`, what `ulimit
//!   -v` sets). Address space, not resident memory: it counts every
//!   reservation, so it is always the larger number.
//! - `cpu=<seconds>`: CPU time over every thread (`RLIMIT_CPU`, `ulimit -t`).
//!   The process is killed with `SIGKILL` when it is reached, as under
//!   `ulimit -t`, so a run that dies at the rail reads as `signal 9`.
//! - `core=<size>`: the largest core file (`RLIMIT_CORE`, `ulimit -c`).
//!   `core=0` keeps a run killed at the memory rail from writing a core of
//!   its full size.
//! - `off`: none of the above, forgetting the items before it.
//!
//! A size is a whole number of bytes, or one with `K`, `M`, `G` or `T`
//! after it (powers of 1024). `--limits` wins over `HEATHER_LIMITS`, so
//! `--limits off` runs a command unlimited under an environment that sets
//! them.
//!
//! Each limit is set as both the soft and the hard limit, as `ulimit` does,
//! and only ever lowered: a limit above the one the process already has
//! keeps the one it has. The limits are the process's from then on and its
//! children's, and a run that executes itself again keeps them, with the
//! CPU time it has used.
//!
//! The limits are set as `main` starts, once the arguments are read, where
//! a shell's `ulimit` is set before the process exists. At the sizes a rail
//! is (gibibytes) the two behave the same, and a run that reaches the
//! memory rail aborts on an allocation it was refused either way. A memory
//! limit below what the process reserves before `main` (the allocator's
//! first arena, about a gibibyte) is not a rail but a crash, and which
//! allocation meets it first depends on timing.

/// What a spec asks for; `None` leaves the process's limit as it is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Limits {
    /// Address space, in bytes.
    pub memory: Option<u64>,
    /// CPU time, in seconds.
    pub cpu: Option<u64>,
    /// Largest core file, in bytes.
    pub core: Option<u64>,
}

/// The `dev` preset: CLAUDE.md's rail for a direct `heather` run.
pub const DEV: Limits = Limits { memory: Some(8 << 30), cpu: Some(120), core: Some(0) };

impl Limits {
    pub fn is_empty(&self) -> bool {
        self.memory.is_none() && self.cpu.is_none() && self.core.is_none()
    }

    /// The limits a spec asks for (the module's grammar).
    pub fn parse(spec: &str) -> Result<Limits, String> {
        let mut limits = Limits::default();
        let mut any = false;
        for item in spec.split(',').map(str::trim).filter(|item| !item.is_empty()) {
            any = true;
            match item.split_once('=') {
                None if item == "dev" => limits = DEV,
                None if item == "off" => limits = Limits::default(),
                Some(("memory", size)) => limits.memory = Some(parse_size(size)?),
                Some(("cpu", secs)) => limits.cpu = Some(parse_seconds(secs)?),
                Some(("core", size)) => limits.core = Some(parse_size(size)?),
                _ => return Err(format!("`{item}` is not a limit; a limit is `dev`, `off`, `memory=<size>`, `cpu=<seconds>` or `core=<size>`")),
            }
        }
        if !any {
            return Err("no limit given; a limit is `dev`, `off`, `memory=<size>`, `cpu=<seconds>` or `core=<size>`".into());
        }
        Ok(limits)
    }

    /// Lowers the process's limits to these.
    pub fn apply(&self) -> Result<(), String> {
        if self.is_empty() {
            return Ok(());
        }
        apply(self)
    }
}

/// A whole number of bytes, or of KiB, MiB, GiB or TiB with `K`, `M`, `G`
/// or `T` after it.
fn parse_size(text: &str) -> Result<u64, String> {
    let (digits, shift) = match text.as_bytes().last() {
        Some(b'K' | b'k') => (&text[..text.len() - 1], 10),
        Some(b'M' | b'm') => (&text[..text.len() - 1], 20),
        Some(b'G' | b'g') => (&text[..text.len() - 1], 30),
        Some(b'T' | b't') => (&text[..text.len() - 1], 40),
        _ => (text, 0),
    };
    let bad = || format!("`{text}` is not a size; a size is a number of bytes, or one with `K`, `M`, `G` or `T` after it");
    let n: u64 = digits.parse().map_err(|_| bad())?;
    n.checked_mul(1u64 << shift).ok_or_else(bad)
}

/// A whole number of seconds, with or without an `s` after it.
fn parse_seconds(text: &str) -> Result<u64, String> {
    let digits = text.strip_suffix('s').unwrap_or(text);
    digits.parse().map_err(|_| format!("`{text}` is not a number of seconds"))
}

/// Removes every `--limits <spec>` and `--limits=<spec>` from `args`, up to
/// a `--`, and returns what they ask for together, or `None` where there
/// was none. The flag is taken out before the subcommand reads its
/// arguments, so it is accepted in any place and by every subcommand.
pub fn take_flag(args: &mut Vec<String>) -> Result<Option<Limits>, String> {
    let mut specs: Vec<String> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--" {
            break;
        }
        if let Some(spec) = args[i].strip_prefix("--limits=") {
            specs.push(spec.to_string());
            args.remove(i);
        } else if args[i] == "--limits" {
            if i + 1 >= args.len() {
                return Err("--limits needs a value: `dev`, `off`, or a list such as `memory=8G,cpu=120,core=0`".into());
            }
            specs.push(args.remove(i + 1));
            args.remove(i);
        } else {
            i += 1;
        }
    }
    if specs.is_empty() {
        return Ok(None);
    }
    Limits::parse(&specs.join(",")).map(Some).map_err(|why| format!("--limits: {why}"))
}

/// The limits this run asks for: `--limits` where given (taken out of
/// `args`), else `HEATHER_LIMITS` where set, else none.
pub fn choose(args: &mut Vec<String>) -> Result<Limits, String> {
    if let Some(limits) = take_flag(args)? {
        return Ok(limits);
    }
    match std::env::var("HEATHER_LIMITS") {
        Ok(spec) if !spec.trim().is_empty() => Limits::parse(&spec).map_err(|why| format!("HEATHER_LIMITS: {why}")),
        _ => Ok(Limits::default()),
    }
}

#[cfg(unix)]
fn apply(limits: &Limits) -> Result<(), String> {
    for (name, resource, value) in [
        ("memory", libc::RLIMIT_AS, limits.memory),
        ("cpu", libc::RLIMIT_CPU, limits.cpu),
        ("core", libc::RLIMIT_CORE, limits.core),
    ] {
        if let Some(value) = value {
            lower(resource, value).map_err(|err| format!("could not set the {name} limit: {err}"))?;
        }
    }
    Ok(())
}

#[cfg(not(unix))]
fn apply(_: &Limits) -> Result<(), String> {
    Err("resource limits are set with `setrlimit`, which this platform does not have".into())
}

/// Sets `resource`'s soft and hard limit to `value`, or to the hard limit
/// the process already has where that is lower.
///
/// The one place the crate's `unsafe_code = "deny"` is lifted
/// (`Cargo.toml`): `getrlimit` and `setrlimit` are foreign functions.
#[cfg(unix)]
#[allow(unsafe_code)]
fn lower(resource: RlimitResource, value: u64) -> std::io::Result<()> {
    let mut now = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    // SAFETY: `now` is a valid, writable `rlimit` for the call's duration,
    // and `resource` is one of libc's own constants.
    if unsafe { libc::getrlimit(resource, &mut now) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    let wanted = libc::rlim_t::try_from(value).unwrap_or(libc::RLIM_INFINITY);
    let at = if now.rlim_max == libc::RLIM_INFINITY { wanted } else { wanted.min(now.rlim_max) };
    let new = libc::rlimit { rlim_cur: at, rlim_max: at };
    // SAFETY: `new` is a valid `rlimit` for the call's duration; it never
    // raises the hard limit, which is all the call could refuse.
    if unsafe { libc::setrlimit(resource, &new) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

/// The type libc gives the resource argument: glibc's is an enum of its
/// own, every other libc's an `int`.
#[cfg(all(unix, target_os = "linux", target_env = "gnu"))]
type RlimitResource = libc::__rlimit_resource_t;
#[cfg(all(unix, not(all(target_os = "linux", target_env = "gnu"))))]
type RlimitResource = libc::c_int;

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|arg| arg.to_string()).collect()
    }

    #[test]
    fn a_spec_reads_left_to_right() {
        assert_eq!(Limits::parse("dev"), Ok(DEV));
        assert_eq!(Limits::parse("dev,cpu=600"), Ok(Limits { cpu: Some(600), ..DEV }));
        assert_eq!(Limits::parse("dev,off"), Ok(Limits::default()));
        assert_eq!(Limits::parse("off,memory=6G"), Ok(Limits { memory: Some(6 << 30), ..Limits::default() }));
        assert_eq!(Limits::parse(" memory = 512M "), Err("`memory = 512M` is not a limit; a limit is `dev`, `off`, `memory=<size>`, `cpu=<seconds>` or `core=<size>`".into()));
        assert_eq!(Limits::parse("memory=512M, cpu=30s ,core=0"), Ok(Limits { memory: Some(512 << 20), cpu: Some(30), core: Some(0) }));
        assert_eq!(Limits::parse("memory=4096"), Ok(Limits { memory: Some(4096), ..Limits::default() }));
        assert!(Limits::parse("").is_err());
        assert!(Limits::parse("rss=1G").is_err());
        assert!(Limits::parse("memory=1.5G").is_err());
        assert!(Limits::parse("memory=99999999999T").is_err());
        assert!(Limits::parse("cpu=two").is_err());
    }

    #[test]
    fn the_flag_is_taken_out_of_any_place() {
        let mut list = args(&["check", "--limits", "dev", "--cache", "--limits=cpu=600", "f.hthr"]);
        assert_eq!(take_flag(&mut list), Ok(Some(Limits { cpu: Some(600), ..DEV })));
        assert_eq!(list, args(&["check", "--cache", "f.hthr"]));
        // Nothing after `--` is the binary's.
        let mut list = args(&["eval", "--", "--limits", "dev"]);
        assert_eq!(take_flag(&mut list), Ok(None));
        assert_eq!(list.len(), 4);
        let mut list = args(&["check", "f.hthr", "--limits"]);
        assert!(take_flag(&mut list).is_err());
        let mut list = args(&["check", "--limits", "bogus", "f.hthr"]);
        assert!(take_flag(&mut list).unwrap_err().starts_with("--limits: `bogus`"));
    }
}
