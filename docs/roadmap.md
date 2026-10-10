# まだ無いもの

現時点の naru に無いものの一覧。言語の現状は [language.md](language.md)、実装の構成は [architecture.md](architecture.md)。

- E007(runtime 条件の classical 依存。[diagnostics.md](diagnostics.md))
- `protocol` 宣言の意味と stdlib の generic な `Event` / `Run`([language.md](language.md)「scenario と observer」)
- `import` の意味(現状は全ファイルが 1 つの大域表。backend は参照からモジュールの依存を計算する)
- 型引数付きのユーザ宣言(`record R<T>`)
- 関数を返す fn と関数を持つ record(関数型は仮引数にだけ)
- `let` のパターン(`let (a, b) = …`)
- Constants と interface binding の構文(C15 の `generated/Statements/Review.lean`)
- naru で書いた stdlib(現状は [language.md](language.md) の表と Lean 側の `NaruStd`)
- Statements 用の stdlib(Safety / Liveness の一般概念・条件・regime。型引数が入るまでは `specs/consensus/Consensus/Spec/` に monomorphic に書いてある)
- `derive finite` / `derive repr` の生成
- enum / Option / Bool / tuple の match の網羅性検査(Lean に任せている)
- Bool の値が要る位置に置いた Prop(量化・spec 宣言の呼出し)の診断(いまは Lean が拒否する)
- `Set` / `Table` の不変条件の型への取り込み([architecture.md](architecture.md)「Statements backend」の既知の制限。コンパイラ意味論保存を Set / Table へ広げるときの方針は同「後続拡張の設計判断」)
- Surface AST → Core の意味保存(C49〜C51): AST の独立した意味論(C48。[architecture.md](architecture.md)「Surface AST の意味論と適格性」)と Core の意味の対応(値の対応・命題の同値)の一般定理、実際の frontend の入力 AST・出力 Core・実生成宣言を合成した接続検査、frontend 側の負の検体(C52)と文書(C53)
- コンパイラ意味論保存の次の段階(関数呼出しと input、再帰とコレクション、状態機械の一ステップ …。[architecture.md](architecture.md)「後続拡張の設計判断」、IDEAL.md「延期」)
