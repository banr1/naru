; naru のハイライト(tree-sitter-naru)。`editors/zed-naru/languages/naru/highlights.scm` と同一に保つ(C16)。
; 捕捉名は Zed のテーマが知っている名前(keyword / type / constructor / comment / string / number / function /
; property / boolean / operator / punctuation / attribute / variable)。同じ node を 2 つの捕捉で取らないように、
; 文法側で field / method / constructor / type を別の node 名にしてある。

(comment) @comment
(string) @string
(number) @number
(boolean) @boolean

[
  "module" "import" "type" "record" "state" "enum" "derive" "input" "fn" "observer"
  "predicate" "condition" "regime" "property" "claim" "bundle" "protocol" "scenario" "observe"
  "let" "if" "else" "match" "forall" "exists" "implies"
] @keyword

(type_identifier) @type
(module_identifier) @type
(constructor_identifier) @constructor
(field_identifier) @property
(capability) @attribute

(function_declaration name: (identifier) @function)
(observer_declaration name: (identifier) @function)
(input_declaration name: (identifier) @function)
(predicate_declaration name: (identifier) @function)
(condition_declaration name: (identifier) @function)
(regime_declaration name: (identifier) @function)
(property_declaration name: (identifier) @function)
(claim_declaration name: (identifier) @function)
(scenario_declaration name: (identifier) @function)
; scenario の本体の `input f(x) = e;`(束縛する input の名前と仮引数。周回 16 の文法から)
(input_binding name: (identifier) @function)
(binding_parameters (identifier) @variable.parameter)

(call_expression function: (identifier) @function)
(call_expression function: (path_expression (identifier) @function))
(method_call_expression method: (method_identifier) @function.method)

(parameter name: (identifier) @variable.parameter)
(binder name: (identifier) @variable.parameter)
(named_argument name: (identifier) @variable.parameter)
(let_statement name: (identifier) @variable)

[
  "=>" "->" "=" "==" "!=" "<" "<=" ">" ">=" "+" "-" "*" "/" "%" "!" "&&" "||" "|" ".."
] @operator

["(" ")" "[" "]" "{" "}"] @punctuation.bracket
["," ";" ":" "."] @punctuation.delimiter
