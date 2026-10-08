/-!
# 診断(エラー報告)

naru コンパイラのすべての検査はこの `Diagnostic` を返す。
出力形式は `file:line:col: error[E0xx]: message` で固定し、
IDEAL.md の検証(`E001` 等を出力する)はこの文字列で確かめる。
-/

namespace Naru

/-- ソース上の位置(1 始まり)。 -/
structure Span where
  line : Nat := 0
  col : Nat := 0
deriving Repr, Inhabited, BEq

structure Diagnostic where
  file : String
  span : Span
  code : String
  msg : String
deriving Repr, Inhabited

def Diagnostic.render (d : Diagnostic) : String :=
  s!"{d.file}:{d.span.line}:{d.span.col}: error[{d.code}]: {d.msg}"

/-! エラー番号。E001〜E007 は IDEAL.md が名指しする静的検査。E01x はフロントエンド共通の誤り。 -/
namespace Code
/-- runtime 宣言が spec 宣言に依存した(phase leak)。 -/
def phaseLeak := "E001"
/-- 停止性を確認できない再帰。 -/
def nonTotal := "E002"
/-- 無条件の選択(choose / pick / set.first / set.toList …)。 -/
def choose := "E003"
/-- 順序指定の無い Set → List 変換。 -/
def orderLoss := "E004"
/-- capability(eq / order / …)の無い型への演算。 -/
def missingCapability := "E005"
/-- Model 内の無限量化による分岐。 -/
def infiniteQuantification := "E006"
/-- runtime 条件の classical な命題への依存。 -/
def classicalDecision := "E007"
/-- 字句・構文の誤り。 -/
def syntaxError := "E010"
/-- 解決できない名前。 -/
def unresolved := "E011"
/-- 同名の宣言の重複。 -/
def duplicate := "E012"
/-- 型の位置に型でない宣言が現れた。 -/
def notAType := "E013"
/-- 型の不一致・推論できない型・値でないものの値としての使用。 -/
def typeMismatch := "E014"
/-- 無い欄・無いメソッド・引数の数や名前の不一致。 -/
def arity := "E015"
/-- claim bundle の項目が claim(または入れ子の claim bundle)でない。 -/
def notAClaim := "E016"
/-- 生成モジュールの構造の誤り: モジュール同士の循環参照、同名のモジュール(backend)。 -/
def moduleStructure := "E017"
/-- match の腕の形: 最後の腕のガード、Nat / Int / String の match に無条件の腕が無い(網羅性の穴)。 -/
def matchShape := "E018"
/-- コンテナ(Option / List / Set / Table / Result / tuple)越しに自分を参照する record / enum。 -/
def nestedRecursion := "E019"
end Code

end Naru
