// Heather's CST is maintained here. Fixed words and symbols are mirrored in
// syntax-inventory.json and checked against the Rust lexer/parser by
// scripts/check-tree-sitter; do not grow a second lexical inventory here.

const PREC = {
  IFF: 1,
  ARROW: 2,
  OR: 3,
  AND: 4,
  COMPARE: 5,
  BOOL_OR: 6,
  BOOL_AND: 7,
  ADD: 8,
  MUL: 9,
  PREFIX: 10,
  POSTFIX: 11,
};

module.exports = grammar({
  name: 'heather',

  extras: $ => [/\s/, $.comment],

  word: $ => $.identifier,

  supertypes: $ => [$._item, $._expression, $._pattern],

  conflicts: $ => [
    [$._expression, $.lambda_binder],
    [$.parameter_name, $.lambda_binder],
    [$.quote_expression, $.contextual_identifier],
    [$.calc_expression, $.contextual_identifier],
    [$.j_expression, $.contextual_identifier],
    [$.refl_expression, $.contextual_identifier],
  ],

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice(
      $.import_declaration,
      $.function_declaration,
      $.theorem_declaration,
      $.inductive_declaration,
      $.record_declaration,
      $.class_declaration,
      $.instance_declaration,
      $.designation_declaration,
      $.datarepr_declaration,
      $.impl_declaration,
    ),

    import_declaration: $ => seq(
      'import', field('module', $.identifier),
      optional(seq('::', '{', commaSep1(field('name', $.identifier)), optional(','), '}')),
      ';',
    ),

    function_declaration: $ => seq(
      optional('meta'), 'fn', field('name', $.qualified_identifier),
      optional($.type_parameters), optional($.requires_clause),
      field('parameters', $.parameter_list),
      optional(seq('for', $.slot_path)),
      '->', field('return_type', $._declaration_type), field('body', $.block),
    ),

    theorem_declaration: $ => seq(
      'theorem', field('name', $.qualified_identifier),
      optional($.type_parameters), optional($.requires_clause),
      field('parameters', $.parameter_list),
      ':', field('return_type', $._declaration_type), field('body', $.block),
    ),

    inductive_declaration: $ => seq(
      'inductive', field('name', $.identifier), optional($.type_parameters),
      optional($.value_parameters), optional(seq(':', field('index', $._expression))),
      field('body', $.constructor_list),
    ),

    record_declaration: $ => seq(
      'record', field('name', $.identifier), optional($.type_parameters),
      optional($.value_parameters), field('body', $.field_list),
    ),

    class_declaration: $ => seq(
      'class', field('name', $.identifier), optional($.type_parameters),
      optional($.value_parameters),
      optional(seq('extends', commaSep1($.class_reference))),
      field('body', $.field_list),
    ),

    instance_declaration: $ => seq(
      'instance', optional($.type_parameters), optional($.value_parameters),
      field('class', $.class_reference), optional($.requires_clause),
      field('body', $.instance_body),
    ),

    designation_declaration: $ => seq(
      'designation', optional('prefix'), optional($.type_parameters),
      field('operator', $.operator), 'at', field('carrier', $._expression),
      ':=', field('value', $._expression), optional(';'),
    ),

    datarepr_declaration: $ => seq(
      'datarepr', field('name', $.identifier), 'for', field('type', $._expression),
      choice(seq(':=', field('value', $._expression), optional(';')), $.repr_clause_block),
    ),

    impl_declaration: $ => seq(
      'impl', field('name', $.identifier), 'for', field('representation', $.identifier),
      choice(seq(':=', field('value', $._expression), optional(';')), $.repr_clause_block),
    ),

    type_parameters: $ => seq('<', commaSep1($.type_parameter), '>'),
    type_parameter: $ => seq(
      field('name', $.identifier),
      optional(seq(':', commaSep1($._expression, '+'))),
    ),
    requires_clause: $ => seq('requires', commaSep1($.parameter)),
    value_parameters: $ => seq('(', commaSep1($.parameter), optional(','), ')'),
    parameter_list: $ => seq('(', commaSep($.parameter), optional(','), ')'),
    parameter: $ => choice(
      seq('{', $.parameter_run, '}'),
      $.parameter_run,
    ),
    parameter_run: $ => seq(
      commaSep1($.parameter_name), ':', field('type', $._expression),
      optional(seq(':=', 'infer')),
    ),
    parameter_name: $ => seq(optional('self'), field('name', $.identifier), optional(seq('as', $.operator))),
    binder_group: $ => seq('(', commaSep1($.parameter_run), ')'),
    implicit_binder_group: $ => seq('{', commaSep1($.parameter_run), '}'),

    class_reference: $ => seq(
      field('name', $.qualified_identifier), field('arguments', $.type_arguments),
      optional(field('indices', $.argument_list)),
    ),
    // Expression/type application is adjacent in Heather (`List<Nat>`). The
    // immediate opener keeps spaced comparisons such as `n < Succ(m)` out of
    // the speculative type-argument path, matching the compiler's lexer span
    // check and substantially improving edit recovery.
    type_arguments: $ => prec.dynamic(2, seq(token.immediate('<'), commaSep1($._expression), '>')),
    slot_path: $ => seq($.identifier, '.', $.identifier),

    constructor_list: $ => seq('{', commaSep($.constructor), optional(','), '}'),
    constructor: $ => seq(
      field('name', $.identifier), optional($.field_parameters),
      optional(seq(':', field('result', $._expression))),
    ),
    field_parameters: $ => seq('(', commaSep($.field), optional(','), ')'),
    field_list: $ => seq('{', commaSep($.field), optional(','), '}'),
    field: $ => seq(field('name', $.identifier), ':', field('type', $._expression)),

    instance_body: $ => seq('{', choice(
      repeat1(choice($.function_declaration, $.theorem_declaration)),
      seq(commaSep($.assignment), optional(',')),
    ), '}'),
    assignment: $ => seq(field('name', $.identifier), ':=', field('value', $._expression)),
    repr_clause_block: $ => seq('{', commaSep($.repr_clause), optional(','), '}'),
    repr_clause: $ => seq(optional('mk'), field('name', $.identifier), ':=', field('value', $._expression)),

    block: $ => choice(
      seq('{', '}'),
      seq('{', repeat($.let_statement), choice($.split_statement, field('result', $._expression)), repeat($.on_statement), '}'),
    ),
    let_statement: $ => seq(
      'let', choice(field('name', $.identifier), $.destructure_pattern),
      optional(seq(':', field('type', $._expression))), '=', field('value', $._expression), ';',
    ),
    destructure_pattern: $ => seq('{', commaSep1($.identifier), optional(','), '}'),
    split_statement: $ => seq(
      'split', optional(seq(field('equation', $.identifier), ':')),
      field('value', $._expression), optional(seq('as', field('motive', $._expression))), ';',
    ),
    on_statement: $ => seq(
      'on', choice($.goal_reference, seq('_', ':', $._expression), $._pattern),
      ':=', field('value', $._expression), ';',
    ),
    goal_reference: $ => seq($.hole, optional(seq('.', $.number))),

    _head_expression: $ => choice(
      $.identifier, $.qualified_identifier, $.number, $.hole, $.argument_slot,
      $.builtin_type, $.universe, seq('(', $._head_expression, ')'), $.vector_expression,
      $.head_call_expression, $.head_member_expression, $.head_type_application,
      $.head_prefix_expression, $.head_binary_expression,
    ),
    head_call_expression: $ => prec.left(PREC.POSTFIX, seq($._head_expression, $.argument_list)),
    head_member_expression: $ => prec.left(PREC.POSTFIX, seq($._head_expression, choice('.', '::'), $.identifier, optional($.argument_list))),
    head_type_application: $ => prec.left(PREC.POSTFIX, seq(choice($.identifier, $.qualified_identifier), $.type_arguments)),
    head_prefix_expression: $ => prec(PREC.PREFIX, seq(choice('-', '¬'), $._head_expression)),
    head_binary_expression: $ => choice(
      ...headBinary($, ['↔', '<->'], PREC.IFF, 'right'),
      ...headBinary($, ['∨'], PREC.OR, 'right'),
      ...headBinary($, ['∧'], PREC.AND, 'right'),
      ...headBinary($, ['=', '≠', '<=', '<'], PREC.COMPARE, 'left'),
      ...headBinary($, ['||'], PREC.BOOL_OR, 'left'),
      ...headBinary($, ['&&'], PREC.BOOL_AND, 'left'),
      ...headBinary($, ['+', '-', '++'], PREC.ADD, 'left'),
      ...headBinary($, ['*', '∙'], PREC.MUL, 'left'),
    ),

    // A declaration body starts with `{`, which is also record-literal
    // postfix syntax. The compiler deliberately suppresses record literals
    // in this one context. Keeping that boundary explicit gives Tree-sitter
    // the same decision and avoids swallowing the body during recovery.
    _declaration_type: $ => choice(
      $._type_atom,
      $.declaration_function_type,
      $.declaration_binary_type,
      $.declaration_quantified_type,
      $.declaration_prefix_type,
    ),
    _type_atom: $ => choice(
      $.identifier,
      $.contextual_identifier,
      $.qualified_identifier,
      $.builtin_type,
      $.number,
      $.hole,
      $.universe,
      $.vector_type,
      seq('(', $._declaration_type, ')'),
      seq(choice($.identifier, $.qualified_identifier, $.builtin_type), $.type_arguments),
      $.declaration_call_type,
      $.declaration_member_type,
    ),
    declaration_call_type: $ => prec.left(PREC.POSTFIX, seq(
      choice($.identifier, $.qualified_identifier, $.builtin_type),
      optional($.type_arguments), repeat1($.argument_list),
    )),
    declaration_member_type: $ => prec.left(PREC.POSTFIX, seq(
      choice($.identifier, $.qualified_identifier, seq('(', $._declaration_type, ')')),
      repeat1(seq('.', $.identifier, optional($.argument_list))),
    )),
    declaration_function_type: $ => prec.right(PREC.ARROW, seq(
      choice($.binder_group, $.implicit_binder_group, $._type_atom), '->', $._declaration_type,
    )),
    declaration_binary_type: $ => choice(
      ...typeBinary($, ['↔', '<->'], PREC.IFF, 'right'),
      ...typeBinary($, ['∨'], PREC.OR, 'right'),
      ...typeBinary($, ['∧'], PREC.AND, 'right'),
      ...typeBinary($, ['=', '≠', '<=', '<'], PREC.COMPARE, 'left'),
      ...typeBinary($, ['||'], PREC.BOOL_OR, 'left'),
      ...typeBinary($, ['&&'], PREC.BOOL_AND, 'left'),
      ...typeBinary($, ['+', '-', '++'], PREC.ADD, 'left'),
      ...typeBinary($, ['*', '∙'], PREC.MUL, 'left'),
    ),
    declaration_quantified_type: $ => prec.right(seq(
      choice('∀', '∃'), $.identifier, ':', $._declaration_type, ',', $._declaration_type,
    )),
    declaration_prefix_type: $ => prec(PREC.PREFIX, seq(choice('-', '¬'), $._declaration_type)),

    _expression: $ => choice(
      $.identifier,
      $.contextual_identifier,
      $.qualified_identifier,
      $.builtin_type,
      $.number,
      $.hole,
      $.argument_slot,
      $.universe,
      $.parenthesized_expression,
      $.vector_type,
      $.vector_expression,
      $.block_expression,
      $.lambda_expression,
      $.quantified_expression,
      $.sequent_expression,
      $.if_expression,
      $.if_let_expression,
      $.match_expression,
      $.match_code_expression,
      $.quote_expression,
      $.splice_expression,
      $.calc_expression,
      $.j_expression,
      $.refl_expression,
      $.explicit_call_expression,
      $.record_expression,
      $.call_expression,
      $.member_expression,
      $.type_application_expression,
      $.prefix_expression,
      $.binary_expression,
      $.function_type,
    ),

    parenthesized_expression: $ => seq('(', $._expression, ')'),
    builtin_type: _ => choice('Code', 'Ctx', 'TyCode'),
    universe: $ => prec.right(PREC.POSTFIX, seq('Type', optional(seq('<', $.number, '>')))),
    vector_type: $ => seq('[', field('element', $._expression), ';', field('length', $._expression), ']'),
    vector_expression: $ => seq('[', commaSep($._expression), optional(','), ']'),
    block_expression: $ => $.block,

    lambda_expression: $ => prec.right(seq(
      choice('λ', 'fun'), repeat1($.lambda_binder), '=>', field('body', $._expression),
    )),
    lambda_binder: $ => choice(
      $.identifier,
      seq('(', $.identifier, ':', $._expression, ')'),
      seq('{', $.identifier, optional(seq(':', $._expression)), '}'),
    ),
    quantified_expression: $ => prec.right(seq(
      choice('∀', '∃'), field('name', $.identifier), ':', field('type', $._expression),
      ',', field('body', $._expression),
    )),
    sequent_expression: $ => prec.right(seq(repeat1($.lambda_binder), choice('⊢', '|-'), $._expression)),

    if_expression: $ => prec.right(seq(
      'if', optional(seq(field('evidence', $.identifier), ':')),
      field('condition', $._head_expression), field('consequence', $.block),
      'else', field('alternative', $.block),
    )),
    if_let_expression: $ => prec.right(seq(
      'if', 'let', optional(seq(field('evidence', $.identifier), ':')),
      field('pattern', $._pattern), '=', field('value', $._head_expression),
      field('consequence', $.block), 'else', field('alternative', $.block),
    )),
    match_expression: $ => seq(
      'match', optional(seq(field('equation', $.identifier), ':')),
      field('value', $._head_expression), optional(seq('as', field('motive', $._motive_expression))),
      field('body', $.match_body),
    ),
    match_code_expression: $ => seq(
      'match', 'code', field('value', $._head_expression), 'as', field('type', $._declaration_type),
      field('body', $.match_body),
    ),
    _motive_expression: $ => choice($.motive_lambda_expression, $._head_expression),
    motive_lambda_expression: $ => prec.right(seq(
      choice('λ', 'fun'), repeat1($.lambda_binder), '=>', field('body', $._declaration_type),
    )),
    match_body: $ => seq('{', commaSep($.match_arm), optional(','), '}'),
    match_arm: $ => seq(field('pattern', $._pattern), '=>', field('body', $._expression)),
    _pattern: $ => choice($.identifier, $.constructor_pattern),
    constructor_pattern: $ => seq(field('constructor', choice($.identifier, $.qualified_identifier)), '(', commaSep(choice($.named_pattern, $._pattern)), optional(','), ')'),
    named_pattern: $ => seq(field('field', $.identifier), ':=', field('pattern', $._pattern)),

    quote_expression: $ => seq('code', $.block),
    splice_expression: $ => prec(PREC.PREFIX, seq('$', choice($.identifier, seq('{', $._expression, '}')))),
    calc_expression: $ => seq('calc', '{', $.calc_first_step, repeat(seq(',', $.calc_next_step)), optional(','), '}'),
    calc_first_step: $ => seq($._expression, '=', $._expression, ':=', $._expression),
    calc_next_step: $ => seq('=', $._expression, ':=', $._expression),
    j_expression: $ => seq('j', '(', $._expression, ',', $._expression, ',', $._expression, ')'),
    refl_expression: _ => 'refl',

    explicit_call_expression: $ => prec(PREC.POSTFIX, seq('@', $.qualified_identifier, optional($.type_arguments), $.argument_list)),
    call_expression: $ => prec.left(PREC.POSTFIX, seq(
      field('function', $._expression), repeat1(field('arguments', $.argument_list)),
    )),
    argument_list: $ => seq('(', commaSep(choice(
      $.named_argument,
      $.operator,
      $._expression,
    )), optional(','), ')'),
    named_argument: $ => seq(field('name', $.identifier), ':=', field('value', $._expression)),
    member_expression: $ => prec.left(PREC.POSTFIX, seq(field('value', $._expression), choice('.', '::'), field('member', $.identifier), optional($.argument_list))),
    type_application_expression: $ => prec.dynamic(4, prec.left(PREC.POSTFIX, seq(
      field('value', choice($.identifier, $.qualified_identifier, $.member_expression)),
      $.type_arguments,
    ))),
    record_expression: $ => prec(PREC.POSTFIX, seq(
      field('type', choice($.identifier, $.qualified_identifier)), optional($.type_arguments),
      '{', commaSep1($.record_field), optional(','), '}',
    )),
    record_field: $ => seq(field('name', $.identifier), ':', field('value', $._expression)),

    function_type: $ => prec.right(PREC.ARROW, seq(
      choice($.binder_group, $.implicit_binder_group, $._expression), '->', $._expression,
    )),
    prefix_expression: $ => prec(PREC.PREFIX, seq(choice('-', '¬'), $._expression)),
    binary_expression: $ => choice(
      ...binary($, ['↔', '<->'], PREC.IFF, 'right'),
      ...binary($, ['∨'], PREC.OR, 'right'),
      ...binary($, ['∧'], PREC.AND, 'right'),
      // The compiler rejects comparison chains semantically. Left association
      // here gives incomplete edits a stable CST instead of a grammar conflict.
      ...binary($, ['=', '≠', '<=', '<'], PREC.COMPARE, 'left'),
      ...binary($, ['||'], PREC.BOOL_OR, 'left'),
      ...binary($, ['&&'], PREC.BOOL_AND, 'left'),
      ...binary($, ['+', '-', '++'], PREC.ADD, 'left'),
      ...binary($, ['*', '∙'], PREC.MUL, 'left'),
    ),

    operator: _ => choice('+', '-', '++', '*', '&&', '||', '∙', '<=', '<'),
    // These words introduce a special form only with their fixed follower in
    // Heather's parser (`j(`, `code {`, `calc {`). Elsewhere they are ordinary
    // names, so preserve that recovery-friendly contextual reading.
    contextual_identifier: $ => choice(
      alias('j', $.identifier),
      alias('code', $.identifier),
      alias('calc', $.identifier),
      alias('refl', $.identifier),
    ),
    // Lower lexical precedence lets a plain name remain `identifier` wherever
    // either node is valid, while declaration/name positions also accept it.
    qualified_identifier: _ => token(prec(-1, /[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*/)),
    identifier: _ => /[A-Za-z_][A-Za-z0-9_]*/,
    number: _ => /[0-9]+/,
    hole: _ => token(/\?[A-Za-z_][A-Za-z0-9_]*|\?/),
    argument_slot: _ => token(/·[₀₁₂₃₄₅₆₇₈₉]*/),
    comment: _ => token(seq('//', /[^\n]*/)),
  },
});

function commaSep(rule, separator = ',') {
  return optional(commaSep1(rule, separator));
}

function commaSep1(rule, separator = ',') {
  return seq(rule, repeat(seq(separator, rule)));
}

function binary($, operators, precedence, associativity) {
  const wrap = associativity === 'right' ? prec.right : associativity === 'left' ? prec.left : prec;
  return operators.map(operator => wrap(precedence, seq(
    field('left', $._expression), field('operator', operator), field('right', $._expression),
  )));
}

function typeBinary($, operators, precedence, associativity) {
  const wrap = associativity === 'right' ? prec.right : prec.left;
  return operators.map(operator => wrap(precedence, seq(
    field('left', $._declaration_type), field('operator', operator), field('right', $._declaration_type),
  )));
}

function headBinary($, operators, precedence, associativity) {
  const wrap = associativity === 'right' ? prec.right : prec.left;
  return operators.map(operator => wrap(precedence, seq(
    field('left', $._head_expression), field('operator', operator), field('right', $._head_expression),
  )));
}
