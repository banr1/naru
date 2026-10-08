/-!
# NaruStd.Observe — scenario の観測(`naru simulate` の出力)

backend は scenario を `List Observation` の `def` に落とす(`observe e;` → `observe` / `observeList` の cons)。
`naru simulate` が書く `generated/Simulate.lean` の `main` が `runScenario` で表示する。
値の表示は `Repr`(backend がすべての record / enum に生成し、`Set` / `Table` もここで持つ)。
IO はこのファイルだけ(Model 本体は純粋なまま)。
-/

namespace NaruStd

/-- 1 つの `observe`: 表示用のラベル(ソースの式)と、値の行。observer の戻り型が `List` なら 1 要素 1 行。 -/
structure Observation where
  label : String
  lines : List String
  /-- `observeList` で作った(`List` の観測)か。空のリストと 1 要素のリストを scalar と区別して表示する。 -/
  isList : Bool

/-- 値を 1 行に表示する(`Repr` の `Format` を折り返さずに描く)。 -/
def render [Repr α] (x : α) : String := (repr x).pretty 1000000

def observe [Repr α] (label : String) (x : α) : Observation := ⟨label, [render x], false⟩

def observeList [Repr α] (label : String) (xs : List α) : Observation := ⟨label, xs.map render, true⟩

/-- scenario の観測を表示する: `scenario <name>`、scalar は `  <label> = <value>`、`List` は `  <label>:` の下に
1 要素 1 行(空なら `[]`)。 -/
def runScenario (name : String) (obs : List Observation) : IO Unit := do
  IO.println s!"scenario {name}"
  for o in obs do
    if o.isList then
      if o.lines.isEmpty then
        IO.println s!"  {o.label}: []"
      else
        IO.println s!"  {o.label}:"
        for l in o.lines do IO.println s!"    {l}"
    else
      for l in o.lines do IO.println s!"  {o.label} = {l}"

end NaruStd
