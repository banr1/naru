//! naru の Zed 拡張(IDEAL.md C17)。
//!
//! シンタックスハイライトは `extension.toml` の tree-sitter 文法(`editors/tree-sitter-naru`、`rev` のコミット)と
//! `languages/naru/highlights.scm` が担い、このクレートは言語サーバー(`naru lsp`)の起動だけを受け持つ。
//! `naru` 実行ファイルは次の順で探す。
//!
//! 1. Zed の設定 `lsp.naru.binary.path`(引数は `lsp.naru.binary.arguments`、省略時は `["lsp"]`)。
//! 2. `PATH` 上の `naru`。
//! 3. ワークツリー直下の `.lake/build/bin/naru`(このリポジトリを開いて `lake build naru` した場合)。
//!
//! 診断はすべてコンパイラが `naru lsp` を通して出す(IDEAL.md「不変条件」)。この glue は naru の意味論・検査・生成に
//! 関与しない。

use zed_extension_api::{self as zed, settings::LspSettings, LanguageServerId, Result};

/// 言語サーバーの識別子(`extension.toml` の `[language_servers.naru]`)。
const SERVER_ID: &str = "naru";

struct NaruExtension;

impl zed::Extension for NaruExtension {
    fn new() -> Self {
        NaruExtension
    }

    fn language_server_command(
        &mut self,
        language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        let env = worktree.shell_env();

        // 1. Zed の設定 `lsp.naru.binary.path` で明示されたパス。
        if let Ok(settings) = LspSettings::for_worktree(SERVER_ID, worktree) {
            if let Some(binary) = settings.binary {
                if let Some(path) = binary.path {
                    let args = binary
                        .arguments
                        .unwrap_or_else(|| vec!["lsp".to_string()]);
                    let mut env = env;
                    if let Some(extra) = binary.env {
                        env.extend(extra);
                    }
                    return Ok(zed::Command {
                        command: path,
                        args,
                        env,
                    });
                }
            }
        }

        // 2. PATH 上の naru。
        if let Some(path) = worktree.which("naru") {
            return Ok(zed::Command {
                command: path,
                args: vec!["lsp".to_string()],
                env,
            });
        }

        // 3. ワークツリー内でビルドした naru。
        if let Some(path) = local_build(worktree) {
            return Ok(zed::Command {
                command: path,
                args: vec!["lsp".to_string()],
                env,
            });
        }

        Err(format!(
            "`{}` が見つかりません。`lake build naru` の成果物 .lake/build/bin/naru を PATH に置くか、\
             Zed の設定 `lsp.naru.binary.path` にそのパスを書いてください。",
            language_server_id.as_ref()
        ))
    }
}

/// ワークツリー直下の `.lake/build/bin/naru` のパスを返す。
///
/// 存在の確認はしない。拡張はワークツリーのファイルを `read_text_file` でしか覗けず、これはワークツリーの走査が
/// 終わる前(セッション復元の直後など)には失敗する。存在の判定に使うと、そのときだけ「naru が見つかりません」で
/// 言語サーバーの起動に失敗し、Zed はそのセッションのあいだ二度と起動を試みない(ハイライトだけが効いて診断が
/// 出ないまま終わる)。パスを返して起動は Zed に任せ、実際に無ければ Zed が起動失敗として報告する。
/// ワークツリーが無い(単独のファイルを開いた)ときだけ `None` を返す。
fn local_build(worktree: &zed::Worktree) -> Option<String> {
    let root = worktree.root_path();
    if root.is_empty() {
        return None;
    }
    Some(format!("{root}/.lake/build/bin/naru"))
}

zed::register_extension!(NaruExtension);
