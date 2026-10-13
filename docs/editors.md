# エディタ対応(tree-sitter 文法と Zed 拡張)

`editors/tree-sitter-naru/` の tree-sitter 文法、`editors/zed-naru/` の Zed 拡張、文法を変えた周回の `rev` の付け替え。
言語サーバーは [cli.md](cli.md)、検査(`naru_test grammar` / `zed` / `lsp` / `zed-install`)は [testing.md](testing.md)。

## tree-sitter 文法

`editors/tree-sitter-naru/grammar.js` は、[language.md](language.md) とパーサを正本として追従させるハイライト用の第二のパーサ(IDEAL.md「不変条件」)。
意味検査(型・phase・停止性)は持たず、診断はすべて `naru lsp` を通してコンパイラが出す。**構文を増やす周回は、`docs/language.md`・`Parser.lean` と
同じ周回で `grammar.js` も直し、`tree-sitter generate` で `src/`(追跡対象。手で編集しない)を作り直して `lake exe naru_test grammar` を通す。**
`tests/accept/editors_syntax.naru` は全構文の受理例なので、新しい構文はここにも足し(`lake exe naru compile` が exit 0 のまま)、
捕捉の期待値 `tests/accept/editors_syntax.captures`(行番号・捕捉名・字句)も直す。

### 正本との既知の差

ハイライト用なので広く受理する側に倒してある: 入れ子のブロックコメントは深さ 9 まで(字句が正規表現のため)、
予約語 `in` は構文に現れないので予約できない(他の 28 語は予約)、`match` の腕の `,` は常に省略可、`if` / `match` の頭部の `Name { … }` は
GLR で record literal とブロックの両方を試す。

### node の名前

`queries/highlights.scm` が使う: 宣言は `<kind>_declaration`(`name` 欄)、型は `type_identifier` / `named_type` /
`tuple_type` / `function_type`、大域経路は `path_expression`(前置の段は `type_identifier`、最後の段は `constructor_identifier` か
`identifier`)、record literal は `record_literal`(`type_path` + `field_initializer` / `base_initializer`)、欄は `field_identifier`、
メソッドは `method_call_expression`(`method_identifier`)、構築子は `constructor_identifier`、モジュール経路は `module_identifier`、
`derive` の capability は `capability`。scenario の本体は `scenario_body`(`input_binding`(`name` / `parameters` = `binding_parameters` /
`value`)、`let_statement`、`observe_statement`(`value`))。予約語 `observe` と `input_binding` の捕捉(`@keyword` / `name` の `@function` /
`binding_parameters` の `@variable.parameter`)は、Zed 拡張の `rev` がこの文法を指す周回で `highlights.scm` に足す(下の「`rev` の付け替え」)。

## Zed 拡張

`editors/zed-naru/`(C17)は、文法を `extension.toml` の `rev`(このリポジトリのコミット SHA)から取り、`naru lsp` を起動して診断を表示する(ホバー・定義ジャンプ・補完・リネームも `naru lsp` が返す。Zed は既定で保存時に言語サーバーの整形 `textDocument/formatting`(C33)を呼ぶので、整形済みの `specs/consensus/` と `tests/accept/` のファイルは保存しても本文が変わらない: [cli.md](cli.md)「言語サーバー」の整形の規則)。
Dev Extension として入れる検査が `lake exe naru_test zed-install`(C19)。

## `rev` の付け替え

文法を変えた周回は `rev` を動かせない(その周回のコミットがまだ無い)。その周回では `highlights.scm` を `rev` の文法でもロードできる形に保ち(新しい node を
参照する捕捉は次の周回に回す)、次の周回で `rev` を直前の周回のコミット(`git log -1 --format=%H -- editors/tree-sitter-naru`)に付け替えて
`lake exe naru_test zed` を通す(IDEAL.md「前提」の「周回の運び」)。
