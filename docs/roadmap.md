# まだ無いもの

現時点の naru に無いものの一覧。言語の現状は [language.md](language.md)、実装の構成は [architecture.md](architecture.md)。

- E007(runtime 条件の classical 依存。[diagnostics.md](diagnostics.md))
- `naru lsp` の編集支援(ホバー C29・定義ジャンプ C30・補完 C31・リネーム C32・整形 C33 は実装済み。[cli.md](cli.md)「言語サーバー」。未対応のリクエストには `MethodNotFound` を返す)を人間の Zed で観測する C62。補完の局所名の有効範囲は位置の前後での近似(ブロックの終わりで消えない)。リネームは宣言名と欄名だけ(variant・局所名・モジュール名は対象外)。整形は字句の間の改行の有無を保つ(行を分ける・つなぐ整形、行の長さの制限、`textDocument/rangeFormatting` は無い)
- 依存グラフ `naru deps`(C63〜C66: `naru.toml` の `deps`、`docs/deps/deps.json` と閲覧用 `index.html`、`naru_test deps`)は実装済み([cli.md](cli.md)「依存グラフ」、
  [architecture.md](architecture.md)「依存グラフ」)。残るのはブラウザでの実画面観測 C67。推論された依存(欄アクセスの record、呼出し結果の型、input の署名を通したもの)を
  グラフに含めること、生成 Lean や Lean 側(compiler / semantics / stdlib / naru_test)の依存グラフ、グラフからのソース編集やエディタ統合、import 行を実際の参照に合わせて
  書き直すこと(差は報告するだけ)は対象外(IDEAL.md「対象外」)
- プロトコル証明の分離基盤(C68〜C72)の基盤(C68〜C70: Lake ライブラリ `Proofs`、`obligations.json`、束縛 hash と失効、`naru proofs`)と書き手の案内(C72: `proofs/README.md`)は
  実装済み([cli.md](cli.md)「証明状況」、[architecture.md](architecture.md)「Proofs」)。残るのは C71: consensus の 14 件の証明(いまは `constants` / `nested` / `finalizedMonotone` / `certificatesAccountable` / `finalizedAccountable` / `finalizedSafe` / `honestNeverSlashed` の 7 件が証明済みで、`naru proofs` は残り 7 件を `missing` と表示する。
  `naru_test proofs` は証明済みの件名が `proved` のままであることを検査し、証明が揃った周回で 14 件すべて証明済みの検査にする。残りの liveness 系の claim の
  共有の足場 — 包含から活性への generic な還元、未来の提案の不在、時計と tree の不変条件(`proofs/Proofs/Consensus/Liveness.lean` / `NoFutureRead.lean` /
  `Clocks.lean` / `TreeInv.lean`)と、`available` の結論 `SafeFrom` を欄の事実(記録の時刻をまたぐ一致・記録と finalized の交差の互換・finalized の一致)に
  還元する足場(`ConfirmationRecords.lean` / `RecordGrowth.lean` / `Outputs.lean`。stable の記録 ⪯ 確認の記録は store の不変条件として `RecordOrder.lean` が前提なしに示す)と、
  `AvailableAt` を残る 5 つの事実から組み立て、`t0 ≠ 0` の finalized の一致を `finalizedSafe` から出す `Available.lean`、確認の候補を書く fork choice と得点の
  最初の層(`ghost` の降下補題 `ghost_reaches`・結果は anchor を延ばし適格・得点は祖先ほど大きい・`updateConfirmationWith` が書く確認の記録の形 `latestConfirmed_shape`)の
  `Goldfish.lean`、投票の pool の不変条件(pool の投票は committee の投票で、増えるだけ)の `Votes.lean`、確認の門 `lateCount < 2 · score` の honest 過半の数え上げ
  (支持の投票は投票者ごとに 1 つで equivocator は無い。honest な committee の要素がすべて遅い投票の参加者なら門を通るブロックには honest な支持者がいる。honest な
  committee の要素がみな `B` 以下に投票していれば(`HonestSupport`)`B` とその祖先は門を通り、門を通るどのブロックも `B` と互換)の `Majority.lean`、honest な投票の発行(投票は投票の時刻の tick の務めが出し、投票者ごと・slot ごとに 1 つで、honest な committee の要素は horizon までの各 slot で
  投票を発行し、Δ > 0 なら投票の head は発行の tick の前の発行者の store に時計を合わせたものの fork choice の head(cache は `onPhaseTick` で進めたもの))の `Voting.lean`、投票の配送の層の入口(投票は `PartialSynchrony` から honest な受信者が締切
  `max t tGST + Δ` より前に扱い、その経路は自分の発行・配送・運ぶブロックの受理の 3 つで、配送された投票は投票者が committee の要素・受信者の slot が `u.slot` か `u.slot + 1`・同じ投票者の
  投票が pool にまだ 2 つ無いときに pool に入って以後も残る)の `Delivery.lean`、受信の直前の slot の窓(時計は添字について単調で、GST 以後に発行された投票の発行の時刻以後で締切より前の
  配送の直前の受信者の slot はちょうど投票の slot)の `Window.lean`、pool の投票の由来(どのノードの pool の投票もそのノードが処理した投票か処理したブロックが運ぶ投票で、
  `UnforgeableSignatures` の下で honest な投票者の pool の投票はその投票者が出した投票なので、`ScheduleWellFormed` も合わせて同じ honest な投票者・同じ slot の pool の投票は 1 つ)の `PoolFrom.lean`、honest な投票者は pool で equivocate せず、GST 以後の honest な投票の honest な受信者への締切より前の
  配送の後に投票が受信者の pool にある(`UnforgeableSignatures` / `ScheduleWellFormed` / Δ > 0 の下で)の `Equivocation.lean`、同じ仮定の下で honest なノードの tick が出した投票は以後そのノードの
  pool にあり、GST 以後の honest な投票を発行の時刻以後・締切より前に扱えば扱った直後の pool に入るか投票を運ぶブロックが tree に新しく入るの `OwnVote.lean`、ブロックが運ぶ投票は新しく受理したノードの
  pool に入り(tick がブロックを出すのは提案の時刻だけなので、締切より前の経路 (3) は配送だけ)、GST 以後の honest な投票は締切が horizon 以内なら締切より前に honest な各ノードの pool に届く(添字はノードごと)
  `Carried.lean`、pool の投票の受信の印は以後変わらず、GST 以後の honest な投票は honest な各ノードの pool に受信の印が `supportCutoff` より前のまま入る `Stamps.lean`、tree のブロックの受信の印は以後変わらず event の時刻で抑えられ、投票と head のブロックの 2 つの印から
  解決の印 `storeTau` が締切より前になる `BlockStamps.lean`、`onBlockUsing` の受理の守り(`Admits`)と名前付きの親・attestation の round の守りの下で配送されたブロックが受信者の tree(新しければ bodies)に入り、
  配送の時刻が締切より前なら受信の印も締切より前になる `BlockReceipt.lean`、提案の務め・tick が出すブロックの名前付きの親が提案者の bodies にあり、提案者が `proposer' (slot)` で
  round の守りを通り、honest な受信者への発行より後の配送の直前の slot がブロックの slot 以上になる `Proposal.lean`、tree のブロックの slot が store の slot 以下で
  発行されたブロックの親の slot がブロックの slot より小さい `ParentSlot.lean`、配送の前提 `DeliveryWellFormed` から親が受信者の tree にあり、
  発行されたブロックが `preceq st.f b` だけを仮定に配送の後の受信者の tree に入る `DeliveredBlock.lean`、store の `f ⪯ j` が run を通して保たれ、
  発行されたブロックが提案者の `f` を延ばすので `preceq st.f b` が受信者と提案者の finalized の順序に還元される `ProposerFinality.lean`、
  `f` が run の添字について単調で FG root が `f` を延ばすので、発行されたブロックが honest な受信者に発行より後、締切より前に配送され、締切の時刻の読みの受信者の FG root が
  そのブロックの祖先なら(setup と run の前提の下で)その読みの tree にある `ReceiverFinality.lean`、配送の event を `PartialSynchrony` から取り出し、
  ブロックの提案者(発行者)でない honest な受信者について(setup と run の前提の下で)締切の読みの FG root の事実だけでその読みの tree に入れる `BlockSynchrony.lean`、
  提案者自身は提案の tick の中で自分のブロックを受理するので、すべての honest な受信者について同じ結論を出す `ProposerReceipt.lean`、
  発行されたブロックが発行の tick の直前の提案者の FG root を延ばすので、締切の読みの FG root の仮定を、受信者の FG root が提案者の FG root かブロックの親の祖先であることに還元する `ProposerRoot.lean`、
  run のどの読みの FG root も(前提なし)bodies のどれかの導出の `j` か `f` で tree にある bodies の消去の祖先であることを示す `JustifiedCarrier.lean`、`f` の分岐を justified な祖先の導出の `j` に言い換えて FG root を常に bodies のどれかの導出の `j` にする `FinalizedSource.lean`、その `j` の justification の証明書に(定足数に honest な署名者がいれば。regime の重みの多数からそれを出す補題を含む)honest な署名者がいて、その署名者が FG root に当たる行を読みの時刻より前に出したことを示す `JustificationCertificate.lean`、行の height pair `Vote h entry nu` がその行を出した tick の中の store の FG source(tree にあり、bodies の名前付きブロックの消去)の chain 状態の高さと `tH` の根であることを示す `AttestationSource.lean`、どの名前付きブロックにも導出の高さが等しく消去が導出の `tH` の祖先があることを示す `EntryHeight.lean`、それらを結んで FG root の honest な行の署名者の務めの FG source の祖先に高さ `hJ` で根が FG root の根のブロックがあることを示す `RootEntry.lean`、根の衝突なしの下でそのブロックが読みの主の bodies の FG root の名前付きブロックと同じであることを示す `RootWitness.lean`(務めの store の chain 状態でも FG source と FG root の `(h, tH)` が `(hJ, FG root)`) は既にあり、残るのは
  `SleepyRegime` の下で `HonestSupport` の前提(honest な tick が `voteTime` に出す投票の head が honest な提案 `B` を延ばして slot が `s` 以下で、
  `ExecutionValid` / `PartialSynchrony` で投票とブロック `B` が `supportCutoff` までに届く)と、2 つの honest なノードの読みの間の
  正準性(手書きの `eligible_compatible` の筋: 一方の支持の投票が他方の遅い投票に入れば、同じ slot に両ノードで門を通る 2 ブロックは互換)で確認の記録の
  一致・確認の記録と finalized の交差の互換・GST-zero の枝(`t0 = 0`)の finalized の一致(stable の記録と grade の候補の分岐についても同じ)を結ぶことと、honest な提案が適格な子の一意な最大になって `ghost_reaches` で選ばれること
  (`IncludedFrom`)を示す `available` の本体、finalized の包含、`stableIncludedFast`、`stableAsynchronyResilient` の本体)。bridge の形式証明、手書きライブラリ(`DecoupledConsensus*`)の import、証明の自動生成、`naru proofs` による
  義務の雛形の生成、レビュー面 / エディタへの証明状況の表示は対象外
- 有界検査(C73 / C74。[testing.md](testing.md)「有界検査」、`proofs/README.md` 10 節)の残り: 周回 197 で置いたのは共通の run の記述からの run の生成(`tests/properties/`)、
  前提の有界版(`SetupWellFormed` / `RunDomain` / `ExecutionValid` / `PartialSynchrony` / `FullParticipation` / `HonestCommittees` / `BelowOneThird` / `MultiProposerRecurrence`)、
  中間命題の検査器 2 つ(`hreadBound`: 判定 0・違反 0(手書きの期限 `a(D)` ≥ 3858 が horizon に収まる run は予算の外。期限を外した診断では全読みで成立)、
  `IncludedFrom`(confirmed / stable): 判定 60 / 22・違反 0)、負の検体 9 件、`naru_test properties`(38 項目。まだ回帰一式には入れていない)。残るのは
  6 claim の前提・結論の検査器と `WindowMajority` / `FreshMajority` / `SlashableBound` / `RecoveredBy` の有界版、他の中間命題、scenario が fn で公開する run、
  共通の run の記述からの手書き側(golden)への写しと C10 の拡充、C74 の theorem、C75(前提を満たす具体的な run の kernel 検査。native の FinalityLiveness は
  horizon 100 / 200 / 400 で 28 ms / 0.4 秒 / 7.4 秒と約 4 乗で増え、全 horizon 33,730 は実行不能)
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
