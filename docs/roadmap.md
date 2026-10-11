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
- コンパイラ意味論保存の関数呼出しと input の段階の残り(C55〜C58): 呼出し・名前付き引数・UFCS を含む runtime の独立 lowering、その全域性とCoreの型保存、現在17関数の実AST/Coreの構造的一致は検査する。同じ署名を守る関数・input環境と文脈に対応する局所環境の下で、全runtime式のAST/Core評価保存も一般定理と17関数への適用で検査する。spec の lowering の一般保存と双方向同値、Surface/Core の宣言群の意味の合成、Surfaceから実生成Leanまでの合成は未完了。inputのみ別モジュールからの任意解釈と、別モジュールのfn/spec呼出し先への実生成接続、spec 側の呼出し・input 誤配線等の負の検体は検査する。式の一般同値 `Call.Sem_denote`、現在の10 spec の prefix 読みへの接続と `Call.interp_prop_agree` による宣言群の命題同値の合成・論理の取り違えの負の検体は実装済み。独立意味論・適格性・意味が定まること(Core と Surface AST)・宣言群の引用(C54)と、runtime の Core → 実生成 Model の保存(読み `Call.denoteN`、一般定理 `Call.denote_sound`、宣言群の意味と実生成定数の一致 `Call.interp_agree`、実際の宣言群の接続と負の検体。C55〜C57 の runtime 側)は [architecture.md](architecture.md)「関数・input の保存対象の意味論」
- コンパイラ意味論保存のその先の段階(再帰とコレクション、状態機械の一ステップ …。[architecture.md](architecture.md)「後続拡張の設計判断」、IDEAL.md「延期」)

呼出しruntime本体は、同じ環境のほか、署名に合う引数で呼出し結果が一致する別々の関数/input環境でもAST/Coreの評価を保つ。
`Surf.Call.lower_eval_agree` / `lower_denote_sound` はその対応証拠を前提として評価とCoreの読みへ合成し、現在17 fnで検査する。
型外の引数での閉包の等式は要求しない。Surface/Coreの宣言群から環境対応を導く証明、spec loweringの双方向同値、Surface宣言群から実生成Leanへの合成は未完了である。

呼出しを含むspecの独立した `Surf.Call.lowerS` の全域性とCoreへの型保存は、任意の宣言表・文脈・適格な式に対する `Surf.Call.lowerS_typed` でkernel検査する。現在10宣言の実AST/実Core一致と、この一般定理の適用を含む90証拠を検査・公理監査する。命題のlet・Bool値・量化・ガードを区別し、型が合う誤callee・名前付き引数・UFCS・input・命題letの5検体を拒否する。specの双方向同値とSurface/Core宣言群から実生成Leanまでの合成は未完了である。

呼出しspecの値・命題のlet列には、子式と末尾の双方向の意味対応を明示した証明書からCoreのlet列への意味対応を合成する局所証明がある。同名の値・命題の再束縛も検査する。全spec式の一般同値と宣言群から実生成LeanまでのSurface合成は未完了である。
