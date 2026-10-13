# まだ無いもの

現時点の naru に無いものの一覧。言語の現状は [language.md](language.md)、実装の構成は [architecture.md](architecture.md)。

- E007(runtime 条件の classical 依存。[diagnostics.md](diagnostics.md))
- `naru lsp` の編集支援(ホバー C29・定義ジャンプ C30・補完 C31・リネーム C32・整形 C33 は実装済み。[cli.md](cli.md)「言語サーバー」。未対応のリクエストには `MethodNotFound` を返す)を人間の Zed で観測する C62。補完の局所名の有効範囲は位置の前後での近似(ブロックの終わりで消えない)。リネームは宣言名と欄名だけ(variant・局所名・モジュール名は対象外)。整形は字句の間の改行の有無を保つ(行を分ける・つなぐ整形、行の長さの制限、`textDocument/rangeFormatting` は無い)
- 依存グラフ `naru deps`(C63〜C67: `naru.toml` の `deps`、`docs/deps/deps.json` と閲覧用 `index.html`、`naru_test deps`)
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
- コンパイラ意味論保存の関数呼出しと input の段階の残り(C55〜C58): 呼出し・名前付き引数・UFCS を含む runtime の独立 lowering、その全域性とCoreの型保存、現在17関数の実AST/Coreの構造的一致は検査する。同じ署名を守る関数・input環境と文脈に対応する局所環境の下で、全runtime式のAST/Core評価保存も一般定理と17関数への適用で検査する。Surface/Core の宣言群の意味の合成と Surface から実生成 Model / Statements への接続も達成した(`SurfaceCallProg.lean` と検査プログラム `SurfaceCallStatementsCheck.lean`。spec の lowering の一般保存と双方向同値も達成)。残るのは C36 / C53 / C59 の最終状態の確認と、呼出しの合成に対する意味上の負検体の拡充。inputのみ別モジュールからの任意解釈と、別モジュールのfn/spec呼出し先への実生成接続、spec 側の呼出し・input 誤配線等の負の検体は検査する。式の一般同値 `Call.Sem_denote`、現在の10 spec の prefix 読みへの接続と `Call.interp_prop_agree` による宣言群の命題同値の合成・論理の取り違えの負の検体は実装済み。独立意味論・適格性・意味が定まること(Core と Surface AST)・宣言群の引用(C54)と、runtime の Core → 実生成 Model の保存(読み `Call.denoteN`、一般定理 `Call.denote_sound`、宣言群の意味と実生成定数の一致 `Call.interp_agree`、実際の宣言群の接続と負の検体。C55〜C57 の runtime 側)は [architecture.md](architecture.md)「関数・input の保存対象の意味論」
- コンパイラ意味論保存のその先の段階(再帰とコレクション、状態機械の一ステップ …。[architecture.md](architecture.md)「後続拡張の設計判断」、IDEAL.md「延期」)

呼出しruntime本体は、同じ環境のほか、署名に合う引数で呼出し結果が一致する別々の関数/input環境でもAST/Coreの評価を保つ。
`Surf.Call.lower_eval_agree` / `lower_denote_sound` はその対応証拠を前提として評価とCoreの読みへ合成し、現在17 fnで検査する。
型外の引数での閉包の等式は要求しない。Surface/Coreの宣言群から環境対応を導く証明とSurface宣言群から実生成Model/Statementsへの接続は後述の `SurfaceCallProg.lean` が与えた(spec loweringの双方向同値は後述の `SurfaceCallLowerSpecSemAll.lean` が与えた)。

呼出しを含むspecの独立した `Surf.Call.lowerS` の全域性とCoreへの型保存は、任意の宣言表・文脈・適格な式に対する `Surf.Call.lowerS_typed` でkernel検査する。現在10宣言の実AST/実Core一致と、この一般定理の適用を含む100証拠を検査・公理監査する。命題のlet・Bool値・量化・ガードを区別し、型が合う誤callee・名前付き引数・UFCS・input・命題letの5検体を拒否する。specの双方向同値は `SurfaceCallLowerSpecSemAll.lean` が与えた(後述)。Surface/Core宣言群からのcallee環境の対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecの値・命題のlet列には、子式と末尾の双方向の意味対応を明示した証明書からCoreのlet列への意味対応を合成する局所証明がある。同名の値・命題の再束縛も検査する。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた(後述)。宣言群からのcallee環境の対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecのガード付きmatchにも、各腕のガード・本体の双方向意味対応を明示した `SpecArmsBridge` から腕列の意味を合成する局所証明がある。Bool/Propガード、Nat/Boolパターン、同名束縛と後続腕への復帰を保ち、意味のないガードや空の腕列に意味を補わない。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた(後述)。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecの量化には、本体の双方向対応を拡張後の任意環境で要求し、任意長のNat/Bool束縛列を同じ全量化範囲で運ぶ局所保存がある。`Surf.Call.lowerS_quant_sem_iff` は束縛の名前・順序・同名shadowingと実lowering出力を照合する。本体の対応と意味の存在をこの局所定理だけから導くものではない(全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた)。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecの論理演算(`&&` / `||` / `implies`)・否定・ifには、子式の双方向対応から親式の意味証人を合成する局所保存がある。公開入口は適格性と独立loweringの実出力を照合する。ifは独立意味論に従い両分岐の意味を要求し、未選択分岐の意味が欠けても成功にしない。子式の対応を一般帰納から導く全spec同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。

呼出しspecのNat/Bool値の比較とNat値の等値には、runtimeの一般評価保存を使う局所双方向対応がある。Bool値と命題を含む等値は、子式の `SpecSemEquiv` と左辺がNatを評価しない局所前提を使い、値の等値と命題の同値を区別する。公開入口は適格性・変換の分岐・独立loweringの実出力を照合する。全spec式の一般同値は `SurfaceCallLowerSpecSemAll.lean` が与えた。Surface/Core宣言群の環境対応と実生成Model/StatementsへのSurfaceからの接続は `SurfaceCallProg.lean` が与えた(後述)。


呼出し葉の双方向対応は `SurfaceCallCallSem.lean` の `Surf.Call.lowerArgs_arrange_eval` / `lowerS_call_sem_iff` / `lowerS_ufcs_sem_iff` / `lowerS_call_equiv` / `lowerS_ufcs_equiv` が扱う。通常呼出しとUFCSの式全体の適格性・独立loweringの実出力から、引数の一般runtime評価保存と仮引数順の並べ替えを合成する。位置・名前付き・修飾名・ゼロ引数、fn/inputのBool値をtrueへ写す境界、同じ任意のspec解釈を保ち、子SpecSemEquivやspec解釈の存在を仮定しない。spec解釈の不在も両側の意味不在として保持する。関数/input環境は署名を守ること、値/命題の束縛環境は型付け文脈と一致することを前提にする。
`SurfaceCallCallSemExamples.lean` の35公開検体は任意解釈の対応、非空虚な意味証人、名前付き/UFCS引数順、Bool値境界、ゼロ引数、spec解釈不在、同名の局所隠蔽と不正引数の拒否をkernel検査する。同型の引数交換は適格でも意味を保存しない反例を含む。5一般補題と35検体をroot公理監査・`requiredTheorems`へ登録し、欠落を失敗にする。`checkCallLeafConnection` の `CallLeafControl.lean` は正しい接続と交換したCoreの型・4監査を通し、`CallLeafWrong.lean` は名前付き/UFCSの接続2行だけの型不一致を要求する。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。
これは同じcallee解釈での呼出し葉の保存であり、全spec式の相互帰納保存は `SurfaceCallLowerSpecSemAll.lean` がこれを子式の対応に使って与えた。Surface/Core宣言群からcallee環境の対応を導く証明と、Surfaceから実生成Model/Statementsへの接続は `SurfaceCallProg.lean` が与えた(後述)。手組AST/Coreの検体を実naru/compiler経路の接続や一般保証全体の代用にはしない。


呼出しを含む全spec式の一般双方向同値は `SurfaceCallLowerSpecSemAll.lean` の `Surf.Call.lowerS_sem_all` / `lowerS_equiv` / `lowerS_sem_iff` / `lowerS_Sem` / `Sem_lowerS` / `lowerS_sem_exists_iff` が扱う。`Surf.Call.wtS.mutual_induct` で式・let列・腕列・腕を同時に帰納し、let列 `SpecLetsBridge`(`lowerStmtsS_bridge`)・腕列 `SpecArmsBridge`(`lowerArmsS_bridge`)・量化・論理/否定/if・比較/値等値/命題等値・通常呼出し/UFCSの葉の局所合成を、これまで前提にしていた子式の `SpecSemEquiv` を帰納結果で満たして結ぶ。命題等値の左子式がNatを評価しないことは `eval_not_nat_of_wtS`(spec解釈をすべて補った環境での意味の存在 `Sem_exists` と `Sem_not_nat`。評価はspec解釈に依らない)で導く。任意の宣言表・文脈で論理の位置で適格なspec式と独立 `lowerS` の実出力について、署名を守る任意の関数/input解釈・任意のspec解釈(不在を含む)・型付け文脈と一致する任意の環境で、同じ命題がSurfaceの意味であることとCoreの意味であることは同値であり、意味の存在(不在)も両側で一致する。`lowerS_denote` / `lowerS_denoteP` はC44/C55のCore→実生成Leanの読み `Call.denoteP` まで合成する(読みの環境との対応 `FEnv.Agree` / `PEnv.Agree` は前提)。
`SurfaceCallLowerSpecSemAllExamples.lean` の18公開検体は、命題のlet・Natの量化・呼出しのscrutinee・ガード付きmatch・名前付きspec呼出し・UFCSのinput呼出し・否定・命題等値・論理演算を1式に重ねた合成式について、子式の対応を仮定しない任意解釈の双方向対応、意味の存在の一致、Natに評価されないこと、2つの腕へ進む非空虚な意味証人(すべての値calleeがfalse / trueを返す解釈)とそのCore側・読みへの合成、否定を落とした同型の誤Coreが適格でも正しいloweringでなく意味を保存しないことをkernel検査する。11一般定理と18検体をroot公理監査・`requiredTheorems`へ登録し、欠落を失敗にする。`naru_test semantics` は現在10specの `sssem_*`(`lowerS_sem_iff` を実AST/実Coreへ適用した任意解釈・任意環境の双方向同値)を `SurfaceCallLowerSpecCheck.lean` に加え、計100証拠の監査と欠落検査を行う。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。
これは式の意味の対応であり、Surface/Core宣言群の意味 `interp` からcallee環境 `Φ` / `Ψ` の対応を導く証明と、現在の実生成Model/Statements宣言へのSurfaceからの接続証拠は `SurfaceCallProg.lean` と `SurfaceCallStatementsCheck.lean` が与えた(後述)。手組AST/Coreの検体を実naru/compiler経路の接続や一般保証全体の代用にはしない。

Surface/Core宣言群の意味の対応と実生成Model/Statementsへの合成は `SurfaceCallProg.lean` の `Surf.Call.interp_lower_agree` / `interpFrom_lower_agree` / `spec_sem_denote` が扱う。宣言ごとの対応 `Surf.Call.DeclLower`(鍵と署名が同じで、fn/spec宣言の本体はその宣言より前の宣言の表での独立lowering `lower` / `lowerS` の実出力、inputは本体なし)の列 `ProgLower` と、適格な両宣言群・inputの署名を守る任意の同じ解釈 `I` から、宣言群の帰納法で `Surf.Call.interp I P` と `Call.interp I C` のcallee環境の一致(`FEnv.Agree`: 型の合う任意の実引数で同じ値、`PEnv.Agree`: 型の合う任意の実引数で双方向同値)を導く。fnの段はruntimeの一般評価保存 `lower_eval_agree`、spec宣言の段は全spec式の一般双方向同値を読み `Call.denoteP` 経由で(`lowerS_denote` / `lowerS_denoteP` と `Call.Sem_denote_self` / `Sem_denoteP`)それまでの対応に合成し、inputの段は同じ解釈を運ぶ。翻訳の正しさや呼出し先の正しさは仮定しない。prefixの表の署名はCoreのprefix署名の畳み込みに等しく(`Δ_take_eq`)、宣言群全体の署名に含まれる(`Δ_full_eq` / `Δ_take_subV`)。`spec_sem_denote` は既存のCore→実生成環境の対応(`Call.interp_agree` / `interp_prop_agree` の結論)と推移(`FEnv.Agree.trans` / `PEnv.Agree.trans`)で結び、Surfaceの宣言群の意味の下でのspec本体の意味が実生成環境での読みと同値であること(読み自体が意味、任意の意味は読みと同値)を与える。`naru_test semantics` は `SurfaceCallStatementsCheck.lean` に、現在31宣言の対応 `splower_call`(鍵・署名は `decide`、本体は `slow_*` / `sslower_*`)、宣言群の意味の一致 `sagree_call` と実生成環境との一致 `sgen_call` / `sinputs_connect`、現在17fnの `sfn_*`(Surfaceの宣言群の意味の下でのfn本体の評価 = 実生成Modelの値)、現在10specの `ssΔ_*`(prefix署名の一致)/ `ssurf_*`(読みが意味)/ `ssiff_*`(任意の意味は読みと同値)/ `sstmt_*`(実生成Statementsの命題がSurface ASTの意味)/ `sstmt_iff_*`(任意の意味は実生成Statementsの命題と同値)を、任意の署名を守るinput解釈(実生成と同じinput)と任意の仮引数について書き、kernel検査・公理監査・欠落検査する。負の検体 `SurfaceCallStatementsWrong.lean` は、違う宣言の実生成Statements(`specUfcs`)を `specNamed` のASTと組み合わせた接続と、同じ署名の別の呼出し先へ置換した型の合うCoreを宣言群の対応に使う検体が、対照の成功の下で接続の2行だけで失敗することを要求する。再実行は `lake build NaruSem` / `lake exe naru_test semantics` / `lake exe naru_test regression`。これは現在の実生成物への接続であり、構文解析・モジュール全体・claim bundle全体の保存、再帰・コレクションは含めない。
