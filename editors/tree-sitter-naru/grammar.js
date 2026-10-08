// tree-sitter 文法 for naru(`.naru`)。
//
// これは naru の正本ではない。正本は `compiler/Naru/Parser.lean` と `compiler/SYNTAX.md` で、この文法は
// エディタ(Zed)のシンタックスハイライトと括弧対応のための第二のパーサとして正本に追従させる(IDEAL.md C16)。
// 意味検査(型・phase・停止性)は持たない。診断はすべて `naru lsp` を通してコンパイラが出す。
//
// 正本との既知の差(ハイライト用なので、正本より広く受理する側に倒してある):
// - 入れ子のブロックコメントは深さ MAX_COMMENT_DEPTH(= 8。`/*` を 9 重まで)で打ち切る。tree-sitter の字句は正規表現なので
//   無限の入れ子は外部スキャナ(手書きの C)が要るが、`src/` を `tree-sitter generate` の生成物だけに保つためにここでは
//   有界の正規表現で表す。
// - 予約語 `in` は構文に現れないので予約できない(tree-sitter の `reserved` は文法中のトークンに限る)。他の 28 語は予約する。
// - `match` の腕の区切り `,` は省略できる(正本は本体がブロックのときだけ省略を許す)。
// - `if` / `match` の頭部の `Name { … }` は GLR で record literal とブロックの両方を試し、続く字句で決める
//   (正本は頭部で record literal を読まない)。
// - 局所名の大文字始まり(E010)、record literal の `..base` の位置などの細則は検査しない。
// - 名前の大文字 / 小文字は正本と同じく「式の先頭の段」と「パターンの 1 段の名前」でだけ区別する(大文字始まりは大域経路、
//   小文字は値 / 変数)。欄名・メソッド名・名前付き引数・2 段目以降の経路・enum の variant は大小を問わない。
//
// 変更したら `tree-sitter generate` で `src/` を作り直し(`src/` は追跡対象で、手で編集しない)、
// `lake exe naru_test grammar` を通す。構文を増やす周回は `SYNTAX.md`・パーサと同じ周回でここも直す。

const MAX_COMMENT_DEPTH = 8;

const PREC = {
  lambda: -1,
  implies: 1,
  or: 2,
  and: 3,
  equality: 4,
  comparison: 5,
  additive: 6,
  multiplicative: 7,
  unary: 8,
  postfix: 9,
  method: 10,
};

// `compiler/Naru/Lexer.lean` の `keywords` から `in`(構文に現れない)を除いたもの。
const KEYWORDS = [
  'module', 'import', 'type', 'record', 'enum', 'derive', 'input', 'fn', 'state',
  'protocol', 'predicate', 'condition', 'regime', 'property', 'claim', 'bundle',
  'scenario', 'observer', 'let', 'if', 'else', 'match', 'forall', 'exists',
  'implies', 'true', 'false',
];

function sep1(rule, separator) {
  return seq(rule, repeat(seq(separator, rule)));
}

// `,` 区切り、末尾の `,` を許す(正本の `parseCommaList` と同じ)。
function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)), optional(','));
}

function commaSep(rule) {
  return optional(commaSep1(rule));
}

// `/* … */`(入れ子は maxDepth 段まで)。正本の `Lexer.skipBlock` と同じく、`/*` は常に 1 段開き、`*/` は常に 1 段閉じる。
// 本文は `/*` と `*/` を含まない文字列で、`*` の列は次が `/` 以外、`/` の列は次が `*` 以外のときだけ本文。
function blockComment(maxDepth) {
  const text = '[^*/]|\\*+[^*/]|/+[^*/]';
  let comment = '/\\*(' + text + ')*\\*+/';
  for (let depth = 1; depth <= maxDepth; depth++) {
    comment = '/\\*(' + text + '|/*' + comment + ')*\\*+/';
  }
  return new RegExp(comment);
}

module.exports = grammar({
  name: 'naru',

  word: $ => $.identifier,

  extras: $ => [/\s/, $.comment],

  reserved: {
    global: $ => KEYWORDS,
  },

  conflicts: $ => [
    // `Name` の後の `.` / `{`: 大域経路の続き・record literal・値としての経路のどれかは次の字句で決まる(GLR)。
    [$.path_expression, $._record_type_path],
    [$.path_expression, $._path_segment],
    [$._path_segment_dot, $._record_type_path],
  ],

  rules: {
    // ── モジュール ──

    source_file: $ => seq(
      $.module_declaration,
      repeat(choice($.import_declaration, $._declaration)),
    ),

    module_declaration: $ => seq('module', field('name', $.module_path), optional(';')),
    import_declaration: $ => seq('import', field('name', $.module_path), optional(';')),
    module_path: $ => sep1($._module_segment, '.'),
    _module_segment: $ => choice(
      alias($._upper_identifier, $.module_identifier),
      alias($.identifier, $.module_identifier),
    ),

    // ── 宣言 ──

    _declaration: $ => choice(
      $.type_declaration,
      $.record_declaration,
      $.state_declaration,
      $.enum_declaration,
      $.input_declaration,
      $.function_declaration,
      $.observer_declaration,
      $.predicate_declaration,
      $.condition_declaration,
      $.regime_declaration,
      $.property_declaration,
      $.claim_declaration,
      $.claim_bundle_declaration,
      $.protocol_declaration,
      $.scenario_declaration,
    ),

    // 型・record・enum・protocol・claim bundle の名前(慣例は大文字始まり)。
    _type_name: $ => choice(
      alias($._upper_identifier, $.type_identifier),
      alias($.identifier, $.type_identifier),
    ),
    // fn・input・observer・spec 宣言・scenario の名前(慣例は小文字始まり。predicate は大文字でもよい)。
    _value_name: $ => choice(
      $.identifier,
      alias($._upper_identifier, $.identifier),
    ),

    type_declaration: $ => seq(
      'type', field('name', $._type_name), '=', field('type', $._type), optional(';'),
    ),

    record_declaration: $ => seq(
      'record', field('name', $._type_name), field('body', $.field_declaration_list),
      optional(field('derive', $.derive_clause)),
    ),
    state_declaration: $ => seq(
      'state', field('name', $._type_name), field('body', $.field_declaration_list),
      optional(field('derive', $.derive_clause)),
    ),
    field_declaration_list: $ => seq('{', commaSep($.field_declaration), '}'),
    field_declaration: $ => seq(
      field('name', $._field_name), ':', field('type', $._type),
    ),
    _field_name: $ => choice(
      alias($.identifier, $.field_identifier),
      alias($._upper_identifier, $.field_identifier),
    ),

    enum_declaration: $ => seq(
      'enum', field('name', $._type_name), field('body', $.variant_list),
      optional(field('derive', $.derive_clause)),
    ),
    variant_list: $ => seq('{', commaSep($.variant), '}'),
    variant: $ => seq(
      field('name', choice(
        alias($._upper_identifier, $.constructor_identifier),
        alias($.identifier, $.constructor_identifier),
      )),
      optional(field('arguments', $.variant_arguments)),
    ),
    variant_arguments: $ => seq('(', commaSep($._type), ')'),

    derive_clause: $ => seq('derive', sep1($.capability, ',')),
    capability: $ => $.identifier,

    input_declaration: $ => seq(
      'input', field('name', $._value_name), field('parameters', $.parameters),
      '->', field('return_type', $._type), optional(';'),
    ),
    function_declaration: $ => seq(
      'fn', field('name', $._value_name), field('parameters', $.parameters),
      '->', field('return_type', $._type), field('body', $.block),
    ),
    observer_declaration: $ => seq(
      'observer', field('name', $._value_name), field('parameters', $.parameters),
      '->', field('return_type', $._type), field('body', $.block),
    ),
    parameters: $ => seq('(', commaSep($.parameter), ')'),
    parameter: $ => seq(field('name', $.identifier), ':', field('type', $._type)),

    predicate_declaration: $ => seq(
      'predicate', field('name', $._value_name), optional(field('parameters', $.parameters)), field('body', $.block),
    ),
    condition_declaration: $ => seq(
      'condition', field('name', $._value_name), optional(field('parameters', $.parameters)), field('body', $.block),
    ),
    regime_declaration: $ => seq(
      'regime', field('name', $._value_name), optional(field('parameters', $.parameters)), field('body', $.block),
    ),
    property_declaration: $ => seq(
      'property', field('name', $._value_name), optional(field('parameters', $.parameters)), field('body', $.block),
    ),
    claim_declaration: $ => seq(
      'claim', field('name', $._value_name), optional(field('parameters', $.parameters)), field('body', $.block),
    ),
    claim_bundle_declaration: $ => seq(
      'claim', 'bundle', field('name', $._type_name), field('body', $.bundle_item_list),
    ),
    bundle_item_list: $ => seq('{', commaSep($.bundle_item), '}'),
    bundle_item: $ => seq(
      field('name', $._field_name),
      optional(seq(':', field('value', $._expression))),
    ),

    protocol_declaration: $ => seq(
      'protocol', field('name', $._type_name), '{', repeat($._declaration), '}',
    ),
    scenario_declaration: $ => seq(
      'scenario', field('name', $._value_name), field('body', $.block),
    ),

    // ── 型 ──

    _type: $ => choice($.named_type, $.tuple_type, $.function_type),

    // `Nat` / `Option<T>` / `A.B.Name`
    named_type: $ => seq(field('name', $.type_path), optional(field('arguments', $.type_arguments))),
    type_path: $ => sep1($._type_segment, '.'),
    _type_segment: $ => choice(
      alias($._upper_identifier, $.type_identifier),
      alias($.identifier, $.type_identifier),
    ),
    // 正本の `parseCommaList` は空(`List<>`)も読む(型検査で E014)
    type_arguments: $ => seq('<', commaSep($._type), '>'),

    // `()` は Unit、`(T)` は T、`(T1, T2)` は tuple
    tuple_type: $ => seq('(', commaSep($._type), ')'),

    // `(T1, T2) -> U`(first-order の関数値。仮引数・closure の引数・`let` の注釈にだけ書ける: 検査は型検査の段)
    function_type: $ => seq(
      field('parameters', alias($.tuple_type, $.parameter_types)), '->', field('return_type', $._type),
    ),

    // ── 式 ──

    _expression: $ => choice(
      $.number,
      $.string,
      $.boolean,
      $.unit,
      $.identifier,
      $.path_expression,
      $.record_literal,
      $.list_literal,
      $.tuple_expression,
      $.parenthesized_expression,
      $.block,
      $.if_expression,
      $.match_expression,
      $.quantifier_expression,
      $.lambda_expression,
      $.call_expression,
      $.method_call_expression,
      $.field_expression,
      $.unary_expression,
      $.binary_expression,
    ),

    boolean: $ => choice('true', 'false'),
    unit: $ => seq('(', ')'),

    // 大文字始まりの大域経路: `Some` / `None` / `Phase.Tick` / `A.B.Ctor`(最後の段が構築子)/ `Set.empty`(最後の段が小文字)。
    // 正本(`parseIdentExpr`)は先頭が大文字なら以降の段の大小を問わず 1 つの経路に読むので、2 段目以降は小文字(モジュール名)も
    // 許す。小文字始まりは `identifier` + `field_expression` の連鎖。`Set.empty()` / `A.b.c(1)` / `Phase.Tick.foo` は
    // 「短い経路 + メソッド / 欄」ではなく「できるだけ長い経路」に読む(正本の `parsePathSpans` と同じ)ので、
    // 動的優先度を段の数に比例させてある(GLR の両方の読みが生き残ったとき、段の多い経路が勝つ)。
    path_expression: $ => choice(
      alias($._upper_identifier, $.constructor_identifier),
      prec.dynamic(1, seq(
        alias($._upper_identifier, $.type_identifier), '.',
        repeat($._path_segment_dot),
        choice(
          alias($._upper_identifier, $.constructor_identifier),
          $.identifier,
        ),
      )),
    ),
    _path_segment_dot: $ => prec.dynamic(1, seq($._path_segment, '.')),
    _path_segment: $ => choice(
      alias($._upper_identifier, $.type_identifier),
      alias($.identifier, $.module_identifier),
    ),

    // `Block { slot: 1, parent: None }` / `Store { head: b, ..st }` / `Store { ..st }`
    record_literal: $ => seq(
      field('type', alias($._record_type_path, $.type_path)),
      field('body', $.field_initializer_list),
    ),
    _record_type_path: $ => seq(
      alias($._upper_identifier, $.type_identifier),
      repeat(seq('.', $._path_segment)),
    ),
    field_initializer_list: $ => seq(
      '{',
      repeat(seq($.field_initializer, ',')),
      optional(choice($.field_initializer, $.base_initializer)),
      '}',
    ),
    field_initializer: $ => seq(
      field('name', $._field_name),
      optional(seq(':', field('value', $._expression))),
    ),
    base_initializer: $ => seq('..', field('base', $._expression), optional(',')),

    list_literal: $ => seq('[', commaSep($._expression), ']'),
    tuple_expression: $ => seq('(', $._expression, ',', optional(commaSep1($._expression)), ')'),
    parenthesized_expression: $ => seq('(', $._expression, ')'),

    // `{ let x = e; f(x); x + 1 }`
    block: $ => seq('{', repeat($._statement), optional(field('tail', $._expression)), '}'),
    _statement: $ => choice($.let_statement, $.expression_statement),
    let_statement: $ => seq(
      'let', field('name', $.identifier), optional(seq(':', field('type', $._type))),
      '=', field('value', $._expression), ';',
    ),
    expression_statement: $ => seq($._expression, ';'),

    if_expression: $ => seq(
      'if', field('condition', $._expression), field('consequence', $.block),
      'else', field('alternative', choice($.block, $.if_expression)),
    ),

    match_expression: $ => seq('match', field('value', $._expression), field('body', $.match_arm_list)),
    match_arm_list: $ => seq('{', repeat(seq($.match_arm, optional(','))), '}'),
    match_arm: $ => seq(
      field('pattern', $._pattern),
      optional(field('guard', $.match_guard)),
      '=>',
      field('value', $._expression),
    ),
    match_guard: $ => seq('if', field('condition', $._expression)),

    // `forall b: Block, t: Time { … }` / `exists t { … }`(spec 専用: runtime では E006)
    quantifier_expression: $ => seq(
      field('quantifier', choice('forall', 'exists')),
      sep1($.binder, ','),
      field('body', $.block),
    ),
    binder: $ => seq(field('name', $.identifier), optional(seq(':', field('type', $._type)))),

    // `|x, y| x + y` / `|| 0`。本体は右に伸びる(`|x| x + 1` は `|x| (x + 1)`)。
    lambda_expression: $ => prec.right(PREC.lambda, seq(
      field('parameters', $.lambda_parameters),
      field('body', $._expression),
    )),
    lambda_parameters: $ => choice('||', seq('|', commaSep($.binder), '|')),

    call_expression: $ => prec(PREC.postfix, seq(
      field('function', $._expression),
      field('arguments', $.arguments),
    )),
    // `x.f(args)`: `f` がユーザ宣言の大域名なら UFCS、無ければ stdlib のメソッド(どちらも型検査の段で決まる)。
    // 名前の大小は正本と同じく問わない(`x.Twice()` は fn `Twice` の UFCS)。
    method_call_expression: $ => prec(PREC.method, seq(
      field('receiver', $._expression),
      '.',
      field('method', choice(
        alias($.identifier, $.method_identifier),
        alias($._upper_identifier, $.method_identifier),
      )),
      field('arguments', $.arguments),
    )),
    arguments: $ => seq('(', commaSep(choice($.named_argument, $._expression)), ')'),
    named_argument: $ => seq(
      field('name', choice($.identifier, alias($._upper_identifier, $.identifier))),
      '=', field('value', $._expression),
    ),

    field_expression: $ => prec(PREC.postfix, seq(
      field('value', $._expression),
      '.',
      field('field', $._field_name),
    )),

    unary_expression: $ => prec(PREC.unary, seq(
      field('operator', choice('!', '-')),
      field('operand', $._expression),
    )),

    binary_expression: $ => choice(
      prec.right(PREC.implies, seq(field('left', $._expression), field('operator', 'implies'), field('right', $._expression))),
      prec.left(PREC.or, seq(field('left', $._expression), field('operator', '||'), field('right', $._expression))),
      prec.left(PREC.and, seq(field('left', $._expression), field('operator', '&&'), field('right', $._expression))),
      prec.left(PREC.equality, seq(field('left', $._expression), field('operator', choice('==', '!=')), field('right', $._expression))),
      prec.left(PREC.comparison, seq(field('left', $._expression), field('operator', choice('<', '<=', '>', '>=')), field('right', $._expression))),
      prec.left(PREC.additive, seq(field('left', $._expression), field('operator', choice('+', '-')), field('right', $._expression))),
      prec.left(PREC.multiplicative, seq(field('left', $._expression), field('operator', choice('*', '/', '%')), field('right', $._expression))),
    ),

    // ── パターン ──

    _pattern: $ => choice(
      $.identifier,          // 変数(小文字)と `_`
      $.number,
      $.string,
      $.boolean,
      $.tuple_pattern,
      $.constructor_pattern,
    ),
    tuple_pattern: $ => seq('(', commaSep($._pattern), ')'),
    // `Some(x)` / `None` / `Enum.Variant(p1, p2)`。正本(`parsePattern`)は 1 段の小文字だけを変数に読み、2 段以上の経路は
    // 各段の大小を問わず構築子に読む(`a.b.E.c(y)` も可)ので、1 段なら大文字、2 段以上なら大小を問わない。
    constructor_pattern: $ => choice(
      seq(
        field('constructor', alias($._upper_identifier, $.constructor_identifier)),
        optional(field('arguments', $.pattern_arguments)),
      ),
      seq(
        repeat1(seq($._path_segment, '.')),
        field('constructor', choice(
          alias($._upper_identifier, $.constructor_identifier),
          alias($.identifier, $.constructor_identifier),
        )),
        optional(field('arguments', $.pattern_arguments)),
      ),
    ),
    pattern_arguments: $ => seq('(', commaSep($._pattern), ')'),

    // ── 字句 ──

    // 小文字か `_` 始まり。末尾の `?` を許す(`find?` / `eventObject?`)。
    identifier: $ => /[a-z_][A-Za-z0-9_]*\??/,
    // 大文字始まり(型・モジュール・enum・構築子)。
    _upper_identifier: $ => /[A-Z][A-Za-z0-9_]*\??/,
    number: $ => /[0-9]+/,
    // `"…"`(`\n` `\t` `\"` `\\`)
    string: $ => token(seq('"', repeat(choice(/[^"\\\n]/, /\\[nt"\\]/)), '"')),
    comment: $ => token(choice(
      seq('//', /[^\n]*/),
      blockComment(MAX_COMMENT_DEPTH),
    )),
  },
});
