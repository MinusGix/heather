//! Temporary explicit driver, not a stable Heather command or derivation syntax.
use heather_cli::loader;
use heather_elab::{
    Elaborator,
    relational_context::{Fixed, Operation, Outcome, Request, derive},
};
use std::path::Path;

fn run() -> Result<bool, String> {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "success".into());
    if !["success", "missing-observer", "supplied-observer", "length"].contains(&mode.as_str()) {
        return Err("expected success, missing-observer, supplied-observer, or length".into());
    }
    let path = Path::new("docs/showcase/relational_generator_input.hthr");
    let contexts = Path::new("lib/std/relation_context.hthr");
    let modules = loader::load_many(&[path, contexts], &["lib/std".into()]).map_err(|e| e.msg)?;
    let mut environment = Elaborator::with_prelude().map_err(|e| format!("{e:?}"))?;
    let mut input = None;
    for module in modules {
        if module.name == "relational_generator_input" {
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
    if mode != "success" {
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
    match derive(
        &environment,
        "context_demo",
        &input.ok_or("missing demo source")?,
        &request,
    )? {
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
