//! Small ANSI styling layer for the human-facing CLI.
//!
//! The elaborator deliberately returns plain diagnostic text: editors, tests,
//! and other callers should not have to remove terminal escapes. The binary
//! adds color at its final output boundary only when that stream is a terminal.

use std::io::IsTerminal;

#[derive(Clone, Copy)]
pub(crate) enum Severity {
    Error,
    Warning,
}

pub(crate) fn stderr_enabled() -> bool {
    std::io::stderr().is_terminal() && environment_allows_color()
}

pub(crate) fn stdout_enabled() -> bool {
    std::io::stdout().is_terminal() && environment_allows_color()
}

fn environment_allows_color() -> bool {
    std::env::var_os("NO_COLOR").is_none()
        && std::env::var_os("TERM").is_none_or(|term| term != "dumb")
}

pub(crate) fn diagnostic(text: &str, severity: Severity, enabled: bool) -> String {
    if !enabled {
        return text.to_string();
    }
    let severity_code = match severity {
        Severity::Error => "1;31",
        Severity::Warning => "1;33",
    };
    let label = match severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
    };
    let mut out = String::with_capacity(text.len() + 96);
    for (i, line) in text.split_inclusive('\n').enumerate() {
        if i == 0 && line.starts_with(label) {
            out.push_str(&paint(label, severity_code));
            out.push_str(&line[label.len()..]);
            continue;
        }
        if let Some(at) = line.find("-->") {
            out.push_str(&line[..at]);
            out.push_str(&paint(&line[at..].trim_end_matches('\n'), "36"));
            if line.ends_with('\n') {
                out.push('\n');
            }
            continue;
        }
        if let Some(bar) = line.find('|') {
            let after_bar = bar + 1;
            out.push_str(&paint(&line[..after_bar], "2;36"));
            let rest = &line[after_bar..];
            if let Some(caret) = rest.find('^') {
                out.push_str(&rest[..caret]);
                let end = rest[caret..]
                    .find(|c| c != '^')
                    .map_or(rest.len(), |n| caret + n);
                out.push_str(&paint(&rest[caret..end], severity_code));
                out.push_str(&rest[end..]);
            } else {
                out.push_str(rest);
            }
            continue;
        }
        out.push_str(line);
    }
    out
}

pub(crate) fn error_label(enabled: bool) -> String {
    styled("error", "1;31", enabled)
}

pub(crate) fn internal_error_label(enabled: bool) -> String {
    styled("internal error", "1;31", enabled)
}

pub(crate) fn warning_count(text: &str, enabled: bool) -> String {
    styled(text, "1;33", enabled)
}

pub(crate) fn error_count(text: &str, enabled: bool) -> String {
    styled(text, "1;31", enabled)
}

pub(crate) fn success(text: &str, enabled: bool) -> String {
    styled(text, "1;32", enabled)
}

fn styled(text: &str, code: &str, enabled: bool) -> String {
    if enabled { paint(text, code) } else { text.to_string() }
}

fn paint(text: &str, code: &str) -> String {
    format!("\x1b[{code}m{text}\x1b[0m")
}

#[cfg(test)]
mod tests {
    use super::{diagnostic, Severity};

    const PLAIN: &str = "warning: something useful\n  --> f.hthr:2:5\n  |\n2 |     old\n  |     ^^^\n";

    #[test]
    fn disabled_color_is_byte_for_byte_plain() {
        assert_eq!(diagnostic(PLAIN, Severity::Warning, false), PLAIN);
    }

    #[test]
    fn warning_diagnostics_style_structure_but_not_source() {
        let styled = diagnostic(PLAIN, Severity::Warning, true);
        assert!(styled.starts_with("\x1b[1;33mwarning\x1b[0m: something useful"), "{styled:?}");
        assert!(styled.contains("\x1b[36m--> f.hthr:2:5\x1b[0m"), "{styled:?}");
        assert!(styled.contains("2 |\x1b[0m     old"), "{styled:?}");
        assert!(styled.contains("\x1b[1;33m^^^\x1b[0m"), "{styled:?}");
        assert!(styled.contains("    old"), "source text remains readable: {styled:?}");
    }

    #[test]
    fn errors_use_red() {
        let styled = diagnostic(&PLAIN.replacen("warning", "error", 1), Severity::Error, true);
        assert!(styled.starts_with("\x1b[1;31merror\x1b[0m"), "{styled:?}");
        assert!(styled.contains("\x1b[1;31m^^^\x1b[0m"), "{styled:?}");
    }
}
