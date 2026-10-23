//! Temporary explicit driver, not a stable Heather command or derivation syntax.
use heather_cli::loader;
use heather_elab::{
    Elaborator,
    relational_context::{Fixed, Operation, Outcome, Request, RewriteRequest, derive, rewrite},
};
use std::path::Path;

fn run() -> Result<bool, String> {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "success".into());
    if ![
        "success",
        "missing-observer",
        "supplied-observer",
        "length",
        "rewrite",
        "rewrite-missing-observer",
        "rewrite-supplied-observer",
        "rewrite-mismatch",
        "rewrite-length",
    ]
    .contains(&mode.as_str())
    {
        return Err("expected success, missing-observer, supplied-observer, length, rewrite, rewrite-missing-observer, rewrite-supplied-observer, rewrite-mismatch, or rewrite-length".into());
    }
    let rewrite_mode = mode.starts_with("rewrite");
    let path = Path::new(if rewrite_mode {
        "docs/showcase/contextual_rewrite_input.hthr"
    } else {
        "docs/showcase/relational_generator_input.hthr"
    });
    let input_module = path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or("invalid input path")?;
    let contexts = Path::new("lib/std/tactic/relation_context.hthr");
    let modules = loader::load_many(&[path, contexts], &["lib/std".into()]).map_err(|e| e.msg)?;
    let mut environment = Elaborator::with_prelude().map_err(|e| format!("{e:?}"))?;
    let mut input = None;
    for module in modules {
        if module.name == input_module {
            input = Some(module.src);
        } else {
            environment
                .elab_module_source(&module.name, &module.src)
                .map_err(|e| e.render(&module.src))?;
        }
    }
    let same = "SameMembers<A>".to_string();
    let function = match mode.as_str() {
        "success" => "receive",
        "length" => "counted",
        _ => "observed",
    };
    let mut request = Request {
        function: function.into(),
        variable: "incoming".into(),
        input: same.clone(),
        output: same.clone(),
        generated_name: format!("{function}_generated"),
        operations: vec![Operation {
            head: "++".into(),
            function: "append<A>".into(),
            inputs: vec![same.clone(), same.clone()],
            output: same.clone(),
            certificate: Some("append_same_members<A>".into()),
        }],
        fixed: vec![Fixed {
            term: "known".into(),
            relation: same.clone(),
            evidence: "same_members_refl(known)".into(),
        }],
    };
    if !rewrite_mode && mode != "success" {
        let length = mode == "length";
        if length {
            request.output = "RelId<Nat>".into();
        }
        request.operations.push(Operation {
            head: if length { "list_len" } else { "observe" }.into(),
            function: if length { "list_len<A>" } else { "observe<A>" }.into(),
            inputs: vec![same],
            output: request.output.clone(),
            certificate: (mode == "supplied-observer")
                .then(|| "preserves_relation_id(SameMembers<A>)".into()),
        });
    }
    let mut input = input.ok_or("missing demo source")?;
    let outcome = if rewrite_mode {
        if mode.contains("observer") || mode == "rewrite-length" {
            let length = mode == "rewrite-length";
            input = input.replace(
                "SameMembers<A>(known ++ (xs ++ xs), known ++ (ys ++ ys))",
                if length {
                    "RelId<Nat>(list_len(known ++ (xs ++ xs)), list_len(known ++ (ys ++ ys)))"
                } else {
                    "SameMembers<A>(observe(known ++ (xs ++ xs)), observe(known ++ (ys ++ ys)))"
                },
            );
            request.operations.push(Operation {
                head: if length { "list_len" } else { "observe" }.into(),
                function: if length { "list_len<A>" } else { "observe<A>" }.into(),
                inputs: vec!["SameMembers<A>".into()],
                output: if length {
                    "RelId<Nat>"
                } else {
                    "SameMembers<A>"
                }
                .into(),
                certificate: (mode == "rewrite-supplied-observer")
                    .then(|| "preserves_relation_id(SameMembers<A>)".into()),
            });
        }
        if mode == "rewrite-mismatch" {
            input = input.replace("known ++ (ys ++ ys)", "xs ++ (ys ++ ys)");
        }
        rewrite(
            &environment,
            "rewrite_demo",
            &input,
            &RewriteRequest {
                theorem: "rewrite_receive".into(),
                proof: "h".into(),
                operations: request.operations,
                fixed: request.fixed,
            },
        )?
        .outcome
    } else {
        derive(&environment, "context_demo", &input, &request)?
    };
    match outcome {
        Outcome::Checked { source } => {
            print!("{source}");
            Ok(true)
        }
        Outcome::Blocked { obligations } => {
            for goal in obligations {
                eprintln!(
                    "{} (bytes {}..{}):\n{}",
                    goal.reason, goal.at.start, goal.at.end, goal.declaration
                );
            }
            Ok(false)
        }
    }
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(true) => std::process::ExitCode::SUCCESS,
        Ok(false) => std::process::ExitCode::from(1),
        Err(error) => {
            eprintln!("{error}");
            std::process::ExitCode::from(2)
        }
    }
}
