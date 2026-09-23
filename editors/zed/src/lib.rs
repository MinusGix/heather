use zed_extension_api::{self as zed, LanguageServerId, Result};

struct HeatherExtension;

impl zed::Extension for HeatherExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        let command = worktree.which("heather-lsp").ok_or_else(|| {
            "heather-lsp is not on PATH; install it with `cargo install --path crates/lsp`"
                .to_string()
        })?;
        Ok(zed::Command {
            command,
            args: Vec::new(),
            env: Default::default(),
        })
    }
}

zed::register_extension!(HeatherExtension);
