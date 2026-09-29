//! `heather check --timings` — the attribution the primary command never had
//! (`docs/instrumentation-design.md`).

use std::process::{Command, Output};

fn heather(dir: &std::path::Path, args: &[&std::ffi::OsStr]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("run heather")
}

fn fixtures() -> std::path::PathBuf {
    std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"))
}

struct Table {
    columns: Vec<String>,
    rows: Vec<Vec<String>>,
}

impl Table {
    fn read(path: &std::path::Path) -> Table {
        let text = std::fs::read_to_string(path).expect("the timings table");
        let mut lines = text.lines();
        let columns: Vec<String> =
            lines.next().expect("a header").split('\t').map(str::to_string).collect();
        let rows: Vec<Vec<String>> = lines
            .map(|line| line.split('\t').map(str::to_string).collect::<Vec<_>>())
            .collect();
        for row in &rows {
            assert_eq!(row.len(), columns.len(), "ragged row {row:?}");
        }
        Table { columns, rows }
    }

    fn at(&self, row: &[String], column: &str) -> u64 {
        let i = self.columns.iter().position(|c| c == column).unwrap_or_else(|| {
            panic!("no column `{column}` in {:?}", self.columns);
        });
        row[i].parse().unwrap_or(0)
    }

    fn of_kind<'a>(&'a self, kind: &'a str) -> impl Iterator<Item = &'a Vec<String>> {
        self.rows.iter().filter(move |r| r[0] == kind)
    }

    fn total(&self, kind: &str, column: &str) -> u64 {
        self.of_kind(kind).map(|r| self.at(r, column)).sum()
    }
}

/// One declaration row per declaration, a module row, a run row, and the
/// columns a "re-measure first" next action actually needs: parse separated
/// from elaboration, the kernel gate, conversion hits, evaluator steps.
#[test]
fn check_attributes_a_module_by_declaration() {
    let out = std::env::temp_dir().join(format!("heather-timings-{}.tsv", std::process::id()));
    let _ = std::fs::remove_file(&out);
    let result = heather(
        &fixtures(),
        &["check".as_ref(), "--timings".as_ref(), out.as_os_str(), "good.hthr".as_ref()],
    );
    assert_eq!(
        result.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&result.stderr)
    );

    let table = Table::read(&out);
    assert_eq!(&table.columns[..5], ["scope", "module", "item", "total_ns", "other_ns"]);

    let items: Vec<_> = table.of_kind("item").collect();
    assert!(!items.is_empty(), "a module with declarations has declaration rows");
    assert!(items.iter().all(|r| !r[2].is_empty()), "a declaration row is named");
    assert!(
        items.iter().any(|r| table.at(r, "kernel_gate_ns") > 0),
        "the kernel gate is timed per declaration",
    );

    let modules: Vec<_> = table.of_kind("module").collect();
    assert!(!modules.is_empty(), "one row per module of the closure");
    assert!(
        modules.iter().any(|r| table.at(r, "parse_ns") > 0),
        "parse time is separated from elaboration",
    );

    let runs: Vec<_> = table.of_kind("run").collect();
    assert_eq!(runs.len(), 1, "exactly one run row");
    let run = runs[0];
    assert!(table.at(run, "total_ns") > 0);
    assert!(
        table.at(run, "prelude_ns") > 0,
        "`with_prelude` is a named timer, not an unattributed constant",
    );
    assert!(
        table.at(run, "conv_shortcut_hits") + table.at(run, "conv_memo_hits") > 0,
        "conversion *hits* are counted, not only misses",
    );
    assert!(table.at(run, "eval_steps") > 0, "so are evaluator steps");
    assert!(
        table.at(run, "total_ns")
            >= table.of_kind("module").map(|r| table.at(r, "total_ns")).sum::<u64>(),
        "a run row is inclusive of its modules",
    );

    // Exclusive timers: no row can claim more phase time than it took.
    for row in &table.rows {
        let phases: u64 = table
            .columns
            .iter()
            .enumerate()
            .filter(|(_, c)| c.ends_with("_ns") && *c != "total_ns" && *c != "other_ns")
            .map(|(i, _)| row[i].parse::<u64>().unwrap_or(0))
            .sum();
        let total: u64 = row[3].parse().unwrap_or(0);
        assert!(phases <= total, "row {row:?} claims {phases}ns of {total}ns");
    }

    let _ = std::fs::remove_file(&out);
}

/// The replay phases the fast lane's premise rests on
/// (`issues/semantic-replay-phase-attribution.md`): a warm run decodes an
/// image, kernel-rechecks it, and both are columns. A cold run publishes.
#[test]
fn replay_phases_are_attributed() {
    let dir = std::env::temp_dir().join(format!("heather-replay-timings-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let cache = dir.join("cache");
    let cold = dir.join("cold.tsv");
    let warm = dir.join("warm.tsv");
    let fixtures = fixtures();

    let run = |timings: &std::path::Path| {
        heather(
            &fixtures,
            &[
                "check".as_ref(),
                "--cache-dir".as_ref(),
                cache.as_os_str(),
                "--timings".as_ref(),
                timings.as_ref(),
                "good.hthr".as_ref(),
            ],
        )
    };

    let first = run(&cold);
    assert_eq!(first.status.code(), Some(0), "{}", String::from_utf8_lossy(&first.stderr));
    let cold_table = Table::read(&cold);
    assert!(
        cold_table.total("module", "image_publish_ns") > 0,
        "a cold module publishes its image",
    );
    assert!(
        cold_table.total("run", "cache_hash_ns") > 0,
        "and the declaration cache's hashing is timed, not just counted",
    );
    assert!(cold_table.total("run", "cache_hashes") > 0);
    assert!(cold_table.total("run", "merkle_walk_ns") > 0);

    let second = run(&warm);
    assert_eq!(second.status.code(), Some(0), "{}", String::from_utf8_lossy(&second.stderr));
    let warm_table = Table::read(&warm);
    assert!(warm_table.total("module", "image_decode_ns") > 0, "a warm module decodes");
    assert!(
        warm_table.total("module", "image_recheck_ns") > 0,
        "and the decoded delta is kernel-rechecked, which is the phase that must be visible",
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A run killed mid-check (the CPU rail's SIGXCPU or SIGKILL) still leaves
/// its table: the header and every closed scope's row, and beside it
/// `<stem>.open.tsv` naming the scopes that were open, the running
/// declaration last (`issues/native-build-no-partial-diagnostics.md`).
#[test]
fn a_killed_run_leaves_its_rows_and_what_was_running() {
    let dir = std::env::temp_dir().join(format!("heather-killed-timings-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let tsv = dir.join("t.tsv");
    let open = dir.join("t.open.tsv");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    // The standard library: long enough, unit tests' profile, to be caught
    // with one declaration done and another running.
    let mut child = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["check".as_ref(), "--timings".as_ref(), tsv.as_os_str(), "lib/std".as_ref()])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("run heather");
    // Look only at a stopped process, so what is seen is what the kill finds:
    // a declaration can close between a look and a kill.
    let pid = child.id().to_string();
    let signal = |name: &str| {
        let sent = Command::new("kill").args([name, &pid]).status().expect("kill");
        assert!(sent.success(), "kill {name}");
    };
    // Stopped when a declaration is running whose name has no row yet (names
    // repeat: `bool` has several `instance Decide`), with another done.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(120);
    let (seen_table, seen_open) = loop {
        if let Some(status) = child.try_wait().unwrap() {
            panic!("the check ended ({status}) before a declaration was seen running");
        }
        signal("-STOP");
        let table = std::fs::read_to_string(&tsv).unwrap_or_default();
        let open_scopes = std::fs::read_to_string(&open).unwrap_or_default();
        let running = open_scopes.lines().last().and_then(|l| l.strip_prefix("item\t"));
        let has_row = |name: &str| table.lines().any(|l| l.strip_prefix("item\t").is_some_and(|r| r.starts_with(&format!("{name}\t"))));
        if table.lines().any(|l| l.starts_with("item\t")) && running.is_some_and(|name| !has_row(name)) {
            break (table, open_scopes);
        }
        signal("-CONT");
        if std::time::Instant::now() > deadline {
            let _ = child.kill();
            panic!("no declaration was seen running within the deadline");
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    };
    child.kill().unwrap();
    child.wait().unwrap();

    // What the kill left is what stood when it landed: nothing was waiting in
    // a buffer.
    assert_eq!(std::fs::read_to_string(&tsv).unwrap(), seen_table, "the table as it stood");
    assert_eq!(std::fs::read_to_string(&open).expect("the open scopes, beside the table"), seen_open);
    let table = Table::read(&tsv);
    assert_eq!(&table.columns[..5], ["scope", "module", "item", "total_ns", "other_ns"]);
    assert!(table.of_kind("item").next().is_some(), "the declarations that closed have rows");
    assert!(table.of_kind("run").next().is_none(), "the run never closed, so it has no row");
    let scopes: Vec<Vec<&str>> = seen_open.lines().map(|l| l.split('\t').collect()).collect();
    assert_eq!(scopes[0], ["scope", "module", "item"]);
    assert_eq!(scopes[1], ["run", "", ""], "outermost first");
    assert_eq!(scopes[2][0], "module", "{seen_open}");

    let _ = std::fs::remove_dir_all(&dir);
}

/// Attribution is opt-in: without the flag nothing is written and the output
/// is byte-for-byte what it always was.
#[test]
fn no_flag_no_table_and_no_change_in_output() {
    let plain = heather(&fixtures(), &["check".as_ref(), "good.hthr".as_ref()]);
    assert_eq!(plain.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&plain.stdout), "good.hthr: ok\n");
    assert!(plain.stderr.is_empty(), "{}", String::from_utf8_lossy(&plain.stderr));
}
