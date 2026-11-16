//! `--limits` and `HEATHER_LIMITS`: the resource limits a development run
//! sets on itself (`crates/cli/src/limits.rs`). The grammar is the binary's
//! unit tests'; these are the process: a limit is applied, the flag wins
//! over the environment, and a spec that is not one is refused before any
//! work.

use std::process::{Command, Output};

fn fixtures() -> std::path::PathBuf {
    std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"))
}

fn heather(args: &[&str], env: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_heather"));
    command.current_dir(fixtures()).args(args);
    match env {
        Some(spec) => command.env("HEATHER_LIMITS", spec),
        None => command.env_remove("HEATHER_LIMITS"),
    };
    command.output().expect("run heather")
}

fn shown(result: &Output) -> String {
    format!("status: {:?}\nstdout: {}\nstderr: {}", result.status,
        String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr))
}

/// The `dev` rail, given either way, leaves a good check as it was; the
/// suite's own rail is lower, and a limit is only ever lowered, so this is
/// also a check that asking for more than the process has is not an error.
#[test]
fn a_good_module_checks_under_the_dev_rail() {
    for (args, env) in [(&["check", "--limits", "dev", "good.hthr"][..], None),
                        (&["check", "--limits=dev,cpu=600", "good.hthr"][..], None),
                        (&["--limits", "dev", "check", "good.hthr"][..], None),
                        (&["check", "good.hthr"][..], Some("dev"))] {
        let result = heather(args, env);
        assert_eq!(result.status.code(), Some(0), "{args:?} with HEATHER_LIMITS={env:?}\n{}", shown(&result));
    }
}

/// The process's limits as `/proc/<pid>/limits` states them: address
/// space, CPU time and core size, each as its (soft, hard) text.
#[cfg(target_os = "linux")]
fn limits_of(pid: &str) -> Vec<(String, String)> {
    let text = std::fs::read_to_string(format!("/proc/{pid}/limits")).expect("read the limits");
    ["Max address space", "Max cpu time", "Max core file size"].iter().map(|name| {
        let line = text.lines().find(|line| line.starts_with(name)).expect("a limit's line");
        let mut words = line[name.len()..].split_whitespace();
        (words.next().unwrap().to_string(), words.next().unwrap().to_string())
    }).collect()
}

/// `heather check` of a module it reads from a FIFO, so the process waits
/// with its limits set (they are set before anything else) while this
/// test reads them; then the module is written and the check must pass.
#[cfg(target_os = "linux")]
fn limits_while_checking(name: &str, args: &[&str], env: Option<&str>) -> Vec<(String, String)> {
    use std::os::unix::fs::OpenOptionsExt;
    let dir = std::env::temp_dir().join(format!("heather-limits-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let fifo = dir.join("m.hthr");
    assert!(Command::new("mkfifo").arg(&fifo).status().expect("run mkfifo").success());
    let mut command = Command::new(env!("CARGO_BIN_EXE_heather"));
    command.arg("check").args(args).arg(&fifo)
        .stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped());
    match env {
        Some(spec) => command.env("HEATHER_LIMITS", spec),
        None => command.env_remove("HEATHER_LIMITS"),
    };
    let mut child = command.spawn().expect("run heather");
    // The reader has the FIFO open once a non-blocking open for writing
    // succeeds; by then the limits are set.
    let started = std::time::Instant::now();
    let mut writer = loop {
        match std::fs::File::options().write(true).custom_flags(libc::O_NONBLOCK).open(&fifo) {
            Ok(file) => break file,
            Err(_) if started.elapsed().as_secs() < 60 => {
                if let Some(status) = child.try_wait().unwrap() {
                    panic!("heather ended before it read the module: {status:?}\n{}", shown(&child.wait_with_output().unwrap()));
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            Err(err) => panic!("heather never opened the module: {err}"),
        }
    };
    let limits = limits_of(&child.id().to_string());
    use std::io::Write;
    writer.write_all("fn f() → Nat { 1 }\n".as_bytes()).unwrap();
    drop(writer);
    let result = child.wait_with_output().unwrap();
    assert_eq!(result.status.code(), Some(0), "{args:?} with HEATHER_LIMITS={env:?}\n{}", shown(&result));
    let _ = std::fs::remove_dir_all(&dir);
    limits
}

/// The limits asked for are the process's, soft and hard alike; the flag
/// wins over the environment, and `--limits off` leaves the limits the
/// process was started with. The values are below the suite's own rails,
/// which a limit can only lower.
#[cfg(target_os = "linux")]
#[test]
fn the_limits_asked_for_are_the_process_s() {
    let pair = |n: &str| (n.to_string(), n.to_string());
    let asked = vec![pair("3221225472"), pair("77"), pair("0")];
    assert_eq!(limits_while_checking("flag", &["--limits", "memory=3G,cpu=77,core=0"], None), asked);
    assert_eq!(limits_while_checking("env", &[], Some("memory=3G,cpu=77s,core=0")), asked);
    assert_eq!(limits_while_checking("wins", &["--limits", "dev,memory=3G,cpu=77"], Some("memory=64M")), asked);
    assert_eq!(limits_while_checking("off", &["--limits", "off"], Some("memory=64M")), limits_of("self"));
}

/// A spec that is not one is a usage error (exit 2) naming what was wrong,
/// from the flag or the environment.
#[test]
fn a_spec_that_is_not_one_is_refused() {
    let flag = heather(&["check", "--limits", "rss=1G", "good.hthr"], None);
    assert_eq!(flag.status.code(), Some(2), "{}", shown(&flag));
    assert!(String::from_utf8_lossy(&flag.stderr).contains("--limits: `rss=1G` is not a limit"), "{}", shown(&flag));
    let env = heather(&["check", "good.hthr"], Some("memory=lots"));
    assert_eq!(env.status.code(), Some(2), "{}", shown(&env));
    assert!(String::from_utf8_lossy(&env.stderr).contains("HEATHER_LIMITS: `lots` is not a size"), "{}", shown(&env));
    let bare = heather(&["check", "good.hthr", "--limits"], None);
    assert_eq!(bare.status.code(), Some(2), "{}", shown(&bare));
}
