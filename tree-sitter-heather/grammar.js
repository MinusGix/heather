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
  // `-x ^ 2` is `-(x ^ 2)` and `x⁻¹ ^ 2` is `(x⁻¹) ^ 2`, as in the compiler.
  POWER: 11,
  POSTFIX: 12,
};

// Words that introduce a special form only before their fixed follower
// (`contextual_identifier` below); elsewhere they are names.
const CONTEXTUAL_WORDS = ['j', 'code', 'calc', 'apply', 'give', 'refl', 'by', 'have', 'with'];

module.exports = grammar({
  name: 'heather',

  extras: $ => [/\s/, $.comment],

  word: $ => $.identifier,

  supertypes: $ => [$._item, $._expression, $._pattern],

  conflicts: $ => [
    [$._expression, $.lambda_binder],
    [$.parameter_name, $.lambda_binder],
    [$.quote_expression, $.contextual_identifier],
    // `match code { … }` and `match code as M { … }` are ordinary matches on a
    // variable named `code`: `{` and `as` cannot begin the analysis form's
    // scrutinee, so there was never one there. The compiler's parser decides
    // this by that exact follow-token rule (parser.rs `match_expr`,
    // issues/match-scrutinee-named-code.md); here the two readings fork and the
    // one that consumes the arm block wins.
    [$.match_code_expression, $.contextual_identifier],
    [$.calc_expression, $.contextual_identifier],
    [$.apply_expression, $.contextual_identifier],
    [$.j_expression, $.contextual_identifier],
    [$.refl_expression, $.contextual_identifier],
    [$.requirement_class_reference],
  ],

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice(
      $.import_declaration,
      $.export_declaration,
      $.function_declaration,
      $.theorem_declaration,
      $.axiom_declaration,
      $.inductive_declaration,
      $.record_declaration,
      $.class_declaration,
      $.instance_declaration,
      $.designation_declaration,
      $.datarepr_declaration,
      $.impl_declaration,
      $.assuming_declaration,
      $.section_declaration,
      $.generate_declaration,
      $.value_declaration,
      $.prefixed_declaration,
    ),

    import_declaration: $ => seq(
      'import', field('module', $.identifier),
      optional(seq('::', '{', commaSep1(field('name', $.identifier)), optional(','), '}')),
      ';',
    ),

    export_declaration: $ => seq(
      'export', field('module', $.identifier),
      '::', '{', commaSep1(field('name', $._qualified_name)), optional(','), '}', ';',
    ),

    function_declaration: $ => seq(
      optional('meta'), 'fn', field('name', $._qualified_name),
      optional($.type_parameters), optional($.requires_clause),
      field('parameters', $.parameter_list),
      optional(seq('for', $.slot_path)),
      choice('->', '→'), field('return_type', $._declaration_type),
      optional($.decreases_clause), field('body', $.block),
    ),

    theorem_declaration: $ => seq(
      optional('evidence'), 'theorem', field('name', $._qualified_name),
      optional($.type_parameters), optional($.requires_clause),
      field('parameters', $.parameter_list),
      ':', field('return_type', $._declaration_type),
      optional($.decreases_clause), field('body', $.block),
    ),

    axiom_declaration: $ => seq(
      'axiom', field('name', $._qualified_name),
      optional($.type_parameters), optional($.requires_clause),
      field('parameters', $.parameter_list),
      ':', field('return_type', $._declaration_type), ';',
    ),

    inductive_declaration: $ => seq(
      choice('inductive', 'codata'), field('name', $.identifier), optional($.type_parameters),
      optional($.value_parameters), optional($.varies_clause),
      optional(seq(':', field('index', $._expression))),
      field('body', $.constructor_list),
    ),

    record_declaration: $ => seq(
      'record', field('name', $.identifier), optional($.type_parameters),
      optional($.value_parameters), optional($.varies_clause), field('body', $.field_list),
    ),

    // `varies A`: the parameter a type constructor over the declaration
    // abstracts (docs/lambda-carrier-instances-design.md §7.1).
    varies_clause: $ => seq('varies', field('parameter', $.identifier)),

    class_declaration: $ => seq(
      'class', field('name', $.identifier), optional($.type_parameters),
      optional($.value_parameters),
      optional(seq('extends', commaSep1($.parent_class_reference))),
      field('body', $.field_list),
    ),

    parent_class_reference: $ => seq(
      field('class', $.class_reference),
      optional(seq('as', field('tag', $.identifier))),
    ),

    instance_declaration: $ => seq(
      'instance', optional($.type_parameters), optional($.value_parameters),
      field('class', $.class_reference), optional($.requires_clause),
      field('body', $.instance_body),
    ),

    designation_declaration: $ => seq(
      'designation', optional(choice('prefix', 'postfix')), optional($.type_parameters),
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

    // `def five: Nat = 5;`, `def six = Succ(five);` — a value definition
    // (docs/value-definitions-design.md §2). The annotation stops at `=`, as
    // a `let`'s does.
    value_declaration: $ => seq(
      'def', field('name', $._qualified_name), optional($.type_parameters),
      optional(seq(':', field('type', $._annotation_type))), '=', field('value', $._expression), ';',
    ),

    // `runtime fn f(…)`, `regex def is_hex = "…";` — a declaration under a
    // prefix generator (docs/value-definitions-design.md §3).
    prefixed_declaration: $ => seq(
      field('generator', $.identifier), optional(field('arguments', $.argument_list)),
      field('declaration', choice($.function_declaration, $.theorem_declaration, $.value_declaration)),
    ),

    // `generate congruences(Tm);` — a generator's declarations, published
    // here (docs/host-elaboration-interface-design.md §19).
    generate_declaration: $ => seq('generate', field('generator', $._expression), ';'),

    assuming_declaration: $ => seq(
      'assuming', commaSep1($.assumption),
      field('body', seq('{', repeat($._item), '}')),
    ),
    // `section<A: C>(x: A) { fn … theorem … }` — a head spliced into every
    // member's (docs/sections-design.md).
    section_declaration: $ => seq(
      'section', optional($.type_parameters), optional($.requires_clause),
      optional(field('parameters', $.parameter_list)),
      field('body', seq('{', repeat(choice($.function_declaration, $.theorem_declaration, $.section_declaration)), '}')),
    ),
    assumption: $ => choice(
      seq(field('name', $.identifier), ':', field('type', $._declaration_type)),
      field('type', $._declaration_type),
    ),

    type_parameters: $ => seq('<', commaSep1($.type_parameter), '>'),
    type_parameter: $ => seq(
      field('name', $.identifier),
      optional(seq(':', commaSep1($._expression, '+'))),
    ),
    requires_clause: $ => seq('requires', commaSep1($.requirement)),

    // `decreases e` — a termination measure between the result type and the
    // body (docs/termination-measures-design.md).
    // The measure is read with the declaration-type sub-grammar, which is the
    // expression grammar minus the forms that would swallow the body's `{`.
    decreases_clause: $ => seq('decreases', $._declaration_type),
    requirement: $ => choice(
      field('class', $.requirement_class_reference),
      seq(field('name', $.identifier), ':', field('class', $.requirement_class_reference)),
    ),
    requirement_class_reference: $ => seq(
      field('name', alias($._requirement_name, $.qualified_identifier)),
      field('arguments', $.type_arguments),
      optional(field('indices', $.class_index_arguments)),
    ),
    _requirement_name: $ => seq($.identifier, repeat(seq('::', $.identifier))),
    value_parameters: $ => seq('(', commaSep1($.parameter), optional(','), ')'),
    parameter_list: $ => seq('(', commaSep($.parameter), optional(','), ')'),
    parameter: $ => choice(
      seq('{', $.parameter_run, '}'),
      $.parameter_run,
    ),
    parameter_run: $ => seq(
      commaSep1($.parameter_name), ':', field('type', $._expression),
      optional(seq(':=', choice('infer', field('default', $._expression)))),
    ),
    // A binder's name is a plain identifier even when it is a contextual
    // word: after `(` in a type, `(j: Nat) →` could still begin `j(…)`, so
    // the lexer reads the word and the name has to accept it.
    parameter_name: $ => seq(optional('self'), field('name', choice($.identifier, ...contextualWords($))), optional(seq('as', $.operator))),
    binder_group: $ => seq('(', commaSep1($.parameter_run), ')'),
    implicit_binder_group: $ => seq('{', commaSep1($.parameter_run), '}'),

    class_reference: $ => seq(
      field('name', $._qualified_name), field('arguments', $.type_arguments),
      // In a `requires C<A> (x: A)` head the following parentheses are the
      // declaration's binder list. Prefer reducing the class reference there;
      // an actual `C<A>(index)` remains the only valid parse when its contents
      // are expressions rather than binders.
      optional(field('indices', $.class_index_arguments)),
    ),
    class_index_arguments: $ => seq('(', commaSep1($._expression), optional(','), ')'),
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
    field: $ => seq(
      field('name', $.identifier), ':', field('type', $._expression),
      optional(seq(':=', field('default', $._expression))),
    ),

    instance_body: $ => seq('{', choice(
      repeat1(choice($.function_declaration, $.theorem_declaration)),
      seq(commaSep($.assignment), optional(',')),
    ), '}'),
    assignment: $ => seq(field('name', $.identifier), ':=', field('value', $._expression)),
    repr_clause_block: $ => seq('{', commaSep($.repr_clause), optional(','), '}'),
    repr_clause: $ => seq(optional('mk'), field('name', $.identifier), ':=', field('value', $._expression)),

    block: $ => choice(
      seq('{', '}'),
      seq('{', repeat(choice($.let_statement, $.have_statement, $.expression_statement, $.assignment_statement, $.statement_form, $.exit_statement)), choice(
        $.goal_combinators,
        seq(choice($.split_statement, field('result', $._expression)), repeat($.on_statement)),
      ), '}'),
      // A statement body ends in a statement and has no result
      // (docs/sequencing-surface-design.md §4).
      seq('{', repeat(choice($.let_statement, $.have_statement, $.expression_statement, $.assignment_statement, $.statement_form, $.exit_statement)),
        choice(seq(field('name', $.identifier), ':=', field('value', $._expression)), $.statement_form,
          'break', 'continue', seq('return', field('value', $._expression))), '}'),
    ),
    // `let x = e;`, and the binding statement `let x <- e;` (`←` too,
    // docs/sequencing-surface-design.md §3.1).
    let_statement: $ => seq(
      'let', optional('mut'), choice(field('name', $.identifier), $.destructure_pattern),
      optional(seq(':', field('type', $._annotation_type))), choice('=', '<-', '←'), field('value', $._expression), ';',
    ),
    // `x := e;` reassigns a `let mut` local (§4).
    assignment_statement: $ => seq(field('name', $.identifier), ':=', field('value', $._expression), ';'),
    // A statement `if`/`match`: its bodies are statements, and it needs no
    // `;` (§5.1).
    statement_form: $ => choice($.if_expression, $.match_expression, $.for_statement, $.while_statement),
    // `for x in xs { body }` (§5.2): `in` is contextual.
    // `a..b` is a range, written only in a `for` header.
    for_statement: $ => seq('for', field('binder', $.identifier), 'in', field('iterable', $._head_expression),
      optional(seq('..', field('end', $._head_expression))), field('body', $.block)),
    // `while c decreases m { body }` (§5.3): a recursive function over the
    // locals the body assigns, `m` its measure.
    while_statement: $ => seq('while', field('condition', $._head_expression), 'decreases', field('measure', $._head_expression), field('body', $.block)),
    // `break;`, `continue;`, `return e;` in a `for` body (§5.2): contextual
    // words, statements only before `;` or `}`.
    exit_statement: $ => choice(seq('break', ';'), seq('continue', ';'), seq('return', field('value', $._expression), ';')),
    // `e;` discards a computation's result in a block over a carrier.
    expression_statement: $ => seq(field('value', $._expression), ';'),
    // `have x = e;` binds opaquely (docs/have-design.md): one name, never a
    // pattern. `have` stays a contextual word, so `have(x)` is still a call.
    have_statement: $ => seq(
      'have', field('name', $.identifier),
      optional(seq(':', field('type', $._annotation_type))), '=', field('value', $._expression), ';',
    ),
    destructure_pattern: $ => seq(
      '{', commaSep1(choice($.identifier, $.named_destructure_field)), optional(','), '}',
    ),
    named_destructure_field: $ => seq(
      field('field', $.identifier), ':=', field('name', $.identifier),
    ),
    split_statement: $ => seq(
      'split', optional(seq(field('equation', $.identifier), ':')),
      field('value', $._expression), optional(seq('as', field('motive', $._expression))), ';',
    ),
    goal_combinators: $ => seq(
      'split_all', ';', 'all_goals', field('body', $.block),
    ),
    on_statement: $ => seq(
      'on', choice(seq('decreasing', $.identifier), $.goal_reference, seq('_', ':', $._expression), $._pattern),
      ':=', field('value', $._expression), ';',
    ),
    goal_reference: $ => seq($.hole, optional(seq('.', $.number))),

    _head_expression: $ => choice(
      // A head position is where a match scrutinee lives, so the contextual
      // words have to be ordinary names here too — `match code { … }` is an
      // ordinary match on a variable named `code`.
      $.identifier, $.contextual_identifier, $.qualified_identifier, $.number, $.character, $.string, $.hole, $.argument_slot,
      $.builtin_type, $.universe, seq('(', $._head_expression, ')'), $.vector_expression,
      $.anonymous_constructor_expression,
      $.boolean_reflection_expression,
      $.explicit_call_expression,
      $.head_call_expression, $.head_member_expression, $.head_type_application,
      $.head_index_expression,
      $.head_propagation_expression,
      $.head_inverse_expression,
      $.head_prefix_expression, $.head_binary_expression,
    ),
    head_propagation_expression: $ => prec.left(PREC.POSTFIX, seq($._head_expression, token.immediate('?'))),
    head_inverse_expression: $ => prec.left(PREC.POSTFIX, seq($._head_expression, '⁻¹')),
    head_call_expression: $ => prec.left(PREC.POSTFIX, seq($._head_expression, $.argument_list)),
    head_member_expression: $ => prec.left(PREC.POSTFIX, seq($._head_expression, choice('.', '::'), $.identifier, optional($.argument_list))),
    head_type_application: $ => prec.left(PREC.POSTFIX, seq(choice($.identifier, $.qualified_identifier), $.type_arguments)),
    head_index_expression: $ => prec.left(PREC.POSTFIX, seq(
      field('value', $._head_expression), '[', field('index', $._expression), ']',
    )),
    head_prefix_expression: $ => prec(PREC.PREFIX, seq(choice('-', '!', '¬', '↑'), $._head_expression)),
    head_binary_expression: $ => choice(
      ...headBinary($, ['↔', '<->'], PREC.IFF, 'right'),
      ...headBinary($, ['∨'], PREC.OR, 'right'),
      ...headBinary($, ['∧'], PREC.AND, 'right'),
      ...headBinary($, ['=', '≠', '≈', '<=', '<'], PREC.COMPARE, 'left'),
      ...headBinary($, ['||'], PREC.BOOL_OR, 'left'),
      ...headBinary($, ['&&'], PREC.BOOL_AND, 'left'),
      ...headBinary($, ['+', '-', '++', '⊔'], PREC.ADD, 'left'),
      ...headBinary($, ['*', '∙'], PREC.MUL, 'left'),
      ...headBinary($, ['^'], PREC.POWER, 'right'),
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
      $.declaration_big_operator_type,
      $.declaration_prefix_type,
      $.match_expression,
    ),
    _type_atom: $ => choice(
      $.identifier,
      $.contextual_identifier,
      $.qualified_identifier,
      $.builtin_type,
      $.number,
      $.character,
      $.string,
      $.hole,
      $.universe,
      $.vector_type,
      $.vector_expression,
      $.squash_type,
      $.boolean_reflection_expression,
      seq('(', $._expression, ')'),
      $.declaration_type_application,
      $.declaration_call_type,
      $.declaration_member_type,
      $.declaration_index_type,
      $.declaration_inverse_type,
      $.explicit_call_expression,
    ),
    declaration_type_application: $ => prec.dynamic(4, prec.left(PREC.POSTFIX, seq(
      field('value', $._type_atom), $.type_arguments,
    ))),
    declaration_inverse_type: $ => prec.left(PREC.POSTFIX, seq(field('value', $._type_atom), '⁻¹')),
    declaration_call_type: $ => prec.left(PREC.POSTFIX, seq(
      field('function', $._type_atom), repeat1($.argument_list),
    )),
    declaration_member_type: $ => prec.left(PREC.POSTFIX, seq(
      field('value', $._type_atom), choice('.', '::'), field('member', $.identifier), optional($.argument_list),
    )),
    declaration_index_type: $ => prec.left(PREC.POSTFIX, seq(
      field('value', $._type_atom), '[', field('index', $._expression), ']',
    )),
    declaration_function_type: $ => prec.right(PREC.ARROW, seq(
      choice($.binder_group, $.implicit_binder_group, $._type_atom), choice('->', '→'), $._declaration_type,
    )),
    declaration_binary_type: $ => choice(
      ...typeBinary($, ['↔', '<->'], PREC.IFF, 'right'),
      ...typeBinary($, ['∨'], PREC.OR, 'right'),
      ...typeBinary($, ['∧'], PREC.AND, 'right'),
      ...typeBinary($, ['=', '≠', '≈', '<=', '<'], PREC.COMPARE, 'left'),
      ...typeBinary($, ['||'], PREC.BOOL_OR, 'left'),
      ...typeBinary($, ['&&'], PREC.BOOL_AND, 'left'),
      ...typeBinary($, ['+', '-', '++', '⊔'], PREC.ADD, 'left'),
      ...typeBinary($, ['*', '∙'], PREC.MUL, 'left'),
      ...typeBinary($, ['^'], PREC.POWER, 'right'),
    ),
    declaration_quantified_type: $ => prec.right(seq(
      choice('∀', '∃'), $.identifier, ':', $._declaration_type, ',', $._declaration_type,
    )),
    declaration_big_operator_type: $ => prec.right(PREC.BOOL_OR, seq(
      choice('∑', '∏'), field('name', $.identifier), '<', field('bound', $._declaration_type),
      ',', field('body', $._declaration_type),
    )),
    declaration_prefix_type: $ => prec(PREC.PREFIX, seq(choice('-', '!', '¬', '↑'), $._declaration_type)),

    // A `let`/`have` annotation runs up to the binder's `=`, so, as in the
    // compiler (parser.rs `no_eq`), it is a declaration type without the
    // comparison rung; a parenthesis is the escape hatch. Read as a plain
    // expression, `let p: A → Type = λ …` gave the codomain the binder's `=`.
    _annotation_type: $ => choice(
      $._type_atom,
      alias($.annotation_function_type, $.declaration_function_type),
      alias($.annotation_binary_type, $.declaration_binary_type),
      alias($.annotation_quantified_type, $.declaration_quantified_type),
      alias($.annotation_big_operator_type, $.declaration_big_operator_type),
      alias($.annotation_prefix_type, $.declaration_prefix_type),
      $.match_expression,
    ),
    annotation_function_type: $ => prec.right(PREC.ARROW, seq(
      choice($.binder_group, $.implicit_binder_group, $._type_atom), choice('->', '→'), $._annotation_type,
    )),
    annotation_binary_type: $ => choice(
      ...typeBinary($, ['↔', '<->'], PREC.IFF, 'right', $._annotation_type),
      ...typeBinary($, ['∨'], PREC.OR, 'right', $._annotation_type),
      ...typeBinary($, ['∧'], PREC.AND, 'right', $._annotation_type),
      ...typeBinary($, ['||'], PREC.BOOL_OR, 'left', $._annotation_type),
      ...typeBinary($, ['&&'], PREC.BOOL_AND, 'left', $._annotation_type),
      ...typeBinary($, ['+', '-', '++', '⊔'], PREC.ADD, 'left', $._annotation_type),
      ...typeBinary($, ['*', '∙'], PREC.MUL, 'left', $._annotation_type),
      ...typeBinary($, ['^'], PREC.POWER, 'right', $._annotation_type),
    ),
    annotation_quantified_type: $ => prec.right(seq(
      choice('∀', '∃'), $.identifier, ':', $._declaration_type, ',', $._annotation_type,
    )),
    annotation_big_operator_type: $ => prec.right(PREC.BOOL_OR, seq(
      choice('∑', '∏'), field('name', $.identifier), '<', field('bound', $._annotation_type),
      ',', field('body', $._annotation_type),
    )),
    annotation_prefix_type: $ => prec(PREC.PREFIX, seq(choice('-', '!', '¬', '↑'), $._annotation_type)),

    _expression: $ => choice(
      $.identifier,
      $.contextual_identifier,
      $.qualified_identifier,
      $.builtin_type,
      $.number,
      $.character,
      $.string,
      $.hole,
      $.argument_slot,
      $.universe,
      $.parenthesized_expression,
      $.vector_type,
      $.squash_type,
      $.vector_expression,
      $.anonymous_constructor_expression,
      $.boolean_reflection_expression,
      $.block_expression,
      $.lambda_expression,
      $.quantified_expression,
      $.big_operator_expression,
      $.sequent_expression,
      $.if_expression,
      $.if_let_expression,
      $.match_expression,
      $.match_code_expression,
      $.quote_expression,
      $.splice_expression,
      $.calc_expression,
      $.apply_expression,
      $.j_expression,
      $.squash_ind_expression,
      $.refl_expression,
      $.by_expression,
      $.explicit_call_expression,
      $.record_expression,
      $.record_update_expression,
      $.call_expression,
      $.decreasing_expression,
      $.member_expression,
      $.index_expression,
      $.propagation_expression,
      $.inverse_expression,
      $.type_application_expression,
      $.prefix_expression,
      $.bind_expression,
      $.binary_expression,
      $.function_type,
    ),

    parenthesized_expression: $ => seq('(', $._expression, ')'),
    builtin_type: _ => choice('Code', 'Ctx', 'TyCode'),
    universe: $ => prec.right(PREC.POSTFIX, seq('Type', optional(seq('<', $.number, '>')))),
    vector_type: $ => seq('[', field('element', $._expression), ';', field('length', $._expression), ']'),
    squash_type: $ => choice(
      seq('∥', field('type', $._declaration_type), '∥'),
      seq('Squash', '<', field('type', $._declaration_type), '>'),
    ),
    vector_expression: $ => seq('[', commaSep($._expression), optional(','), ']'),
    anonymous_constructor_expression: $ => choice(
      seq('⟨', commaSep($._expression), optional(','), '⟩'),
      seq('⟨', field('value', $._expression), '|', '⟩'),
      seq('⟨', '|', field('value', $._expression), '⟩'),
    ),
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
    // `∑ k < n, e`: the body runs over arithmetic and stops at a relation,
    // as in the compiler, so its precedence sits just above COMPARE.
    big_operator_expression: $ => prec.right(PREC.BOOL_OR, seq(
      choice('∑', '∏'), field('name', $.identifier), '<', field('bound', $._expression),
      ',', field('body', $._expression),
    )),
    sequent_expression: $ => prec.right(seq(repeat1($.lambda_binder), choice('⊢', '|-'), $._expression)),

    if_expression: $ => prec.right(seq(
      'if', optional(seq(field('evidence', $.identifier), ':')),
      field('condition', $._head_expression), field('consequence', $.block),
      // A statement `if` may omit its `else`, and chains with `else if`.
      optional(seq('else', field('alternative', choice($.block, $.if_expression)))),
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
    _pattern: $ => choice($.identifier, $.constructor_pattern, $.anonymous_constructor_pattern),
    constructor_pattern: $ => seq(field('constructor', choice($.identifier, $.qualified_identifier)), '(', commaSep(choice($.named_pattern, $._pattern)), optional(','), ')'),
    anonymous_constructor_pattern: $ => choice(
      seq('⟨', commaSep(choice($.named_pattern, $._pattern)), optional(','), '⟩'),
      seq('⟨', field('value', $._pattern), '|', '⟩'),
      seq('⟨', '|', field('value', $._pattern), '⟩'),
    ),
    named_pattern: $ => seq(field('field', $.identifier), ':=', field('pattern', $._pattern)),

    boolean_reflection_expression: $ => seq(
      '⟦', field('value', $._expression), '⟧',
    ),

    quote_expression: $ => seq('code', $.block),
    splice_expression: $ => prec(PREC.PREFIX, seq('$', choice($.identifier, seq('{', $._expression, '}')))),
    // Each step names its relation; the compiler composes mixed `=`, `≈`,
    // `<=` and `<` steps (docs/calc-order-chains.md).
    calc_expression: $ => seq('calc', '{',
      $.calc_first_step, repeat(seq(',', $.calc_next_step)),
      optional(','), '}'),
    // The relation is an inline choice, not a hidden rule: a rule would need
    // a reduction right after the token, where the comparison rung shifts.
    calc_first_step: $ => seq($._expression, choice('=', '≈', '<=', '<'), $._expression, ':=', $._expression),
    calc_next_step: $ => seq(choice('=', '≈', '<=', '<'), $._expression, ':=', $._expression),
    apply_expression: $ => prec.right(seq(
      'apply', field('function', $._expression), ';',
      repeat(seq('give', field('argument', $._expression), ';')),
      field('argument', $._expression),
    )),
    j_expression: $ => seq('j', '(', $._expression, ',', $._expression, ',', $._expression, ')'),
    squash_ind_expression: $ => seq('squash_ind', '(', $._expression, ',', $._expression, ',', $._expression, ')'),
    refl_expression: _ => 'refl',

    // `by t` runs the tactic `t` (docs/host-elaboration-interface-design.md §7);
    // the compiler reads it only when a name follows, so `by` stays a name.
    by_expression: $ => prec.right(PREC.POSTFIX, seq('by', field('tactic', choice(
      $._qualified_name,
      alias($.by_tactic_call, $.call_expression),
    )))),
    by_tactic_call: $ => prec.left(PREC.POSTFIX, seq(
      field('function', $._qualified_name), repeat1(field('arguments', $.argument_list)),
    )),

    explicit_call_expression: $ => prec(PREC.POSTFIX, seq('@', $._qualified_name, optional($.type_arguments), $.argument_list)),
    propagation_expression: $ => prec.left(PREC.POSTFIX, seq(field('value', $._expression), token.immediate('?'))),
    decreasing_expression: $ => prec.left(PREC.POSTFIX, seq(field('call', $._expression), 'decreasing', field('label', $.identifier))),
    inverse_expression: $ => prec.left(PREC.POSTFIX, seq(field('value', $._expression), '⁻¹')),
    call_expression: $ => prec.left(PREC.POSTFIX, seq(
      field('function', $._expression), repeat1(field('arguments', $.argument_list)),
    )),
    argument_list: $ => seq('(', commaSep(choice(
      $.named_argument,
      $.operator,
      $._expression,
    )), optional(','), ')'),
    // Contextual words remain ordinary names away from their fixed followers;
    // `Char(code := n)` is a named argument, not a half-written `code { … }`.
    named_argument: $ => seq(
      field('name', choice($.identifier, $.contextual_identifier)),
      ':=', field('value', $._expression),
    ),
    member_expression: $ => prec.left(PREC.POSTFIX, seq(field('value', $._expression), choice('.', '::'), field('member', $.identifier), optional($.argument_list))),
    index_expression: $ => prec.left(PREC.POSTFIX, seq(
      field('value', $._expression), '[', field('index', $._expression), ']',
    )),
    type_application_expression: $ => prec.dynamic(4, prec.left(PREC.POSTFIX, seq(
      field('value', choice($.identifier, $.qualified_identifier, $.member_expression)),
      $.type_arguments,
    ))),
    record_expression: $ => prec(PREC.POSTFIX, seq(
      field('type', choice($.identifier, $.qualified_identifier)), optional($.type_arguments),
      '{', commaSep1($.record_field), optional(','), '}',
    )),
    record_field: $ => seq(field('name', $.identifier), ':', field('value', $._expression)),
    // `s with { f = v, … }` — functional record update; `with` is a word only
    // before the `{`.
    record_update_expression: $ => prec.left(PREC.POSTFIX, seq(
      field('value', $._expression), 'with', '{', commaSep1($.record_update_field), optional(','), '}',
    )),
    record_update_field: $ => seq(field('name', $.identifier), '=', field('value', $._expression)),

    function_type: $ => prec.right(PREC.ARROW, seq(
      choice($.binder_group, $.implicit_binder_group, $._expression), choice('->', '→'), $._expression,
    )),
    prefix_expression: $ => prec(PREC.PREFIX, seq(choice('-', '!', '¬', '↑'), $._expression)),
    // `<- e`, a nested bind: it takes the whole expression after it.
    bind_expression: $ => prec.right(0, seq(choice('<-', '←'), field('value', $._expression))),
    binary_expression: $ => choice(
      ...binary($, ['↔', '<->'], PREC.IFF, 'right'),
      ...binary($, ['∨'], PREC.OR, 'right'),
      ...binary($, ['∧'], PREC.AND, 'right'),
      // The compiler rejects comparison chains semantically. Left association
      // here gives incomplete edits a stable CST instead of a grammar conflict.
      ...binary($, ['=', '≠', '≈', '<=', '<'], PREC.COMPARE, 'left'),
      ...binary($, ['||'], PREC.BOOL_OR, 'left'),
      ...binary($, ['&&'], PREC.BOOL_AND, 'left'),
      ...binary($, ['+', '-', '++', '⊔'], PREC.ADD, 'left'),
      ...binary($, ['*', '∙'], PREC.MUL, 'left'),
      ...binary($, ['^'], PREC.POWER, 'right'),
    ),

    operator: _ => choice('+', '-', '!', '++', '*', '&&', '||', '∙', '⊔', '≈', '<=', '<', '^', '⁻¹'),
    // These words introduce a special form only with their fixed follower in
    // Heather's parser (`j(`, `code {`, `calc {`, `apply f;`). Elsewhere they are ordinary
    // names, so preserve that recovery-friendly contextual reading.
    contextual_identifier: $ => choice(...contextualWords($)),
    // Keep plain and namespace-qualified names lexically disjoint. Declaration
    // name positions alias either spelling to the stable qualified-name node.
    _qualified_name: $ => alias(choice($.identifier, $.qualified_identifier), $.qualified_identifier),
    qualified_identifier: _ => token(/[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)+/),
    identifier: _ => /[A-Za-z_][A-Za-z0-9_]*/,
    // A decimal point starts a fraction only before a digit (`1.foo` and
    // `1..2` keep their meaning), and a hex point only when a `p` exponent
    // follows (`0xff.f()` stays a method call): crates/syntax/src/lexer.rs.
    number: _ => token(choice(
      /0x[0-9A-Fa-f][0-9A-Fa-f_]*((\.[0-9A-Fa-f][0-9A-Fa-f_]*)?[pP][+-]?[0-9][0-9_]*)?/,
      /0o[0-7][0-7_]*|0b[01][01_]*/,
      /[0-9][0-9_]*(\.[0-9][0-9_]*)?([eE][+-]?[0-9][0-9_]*)?/,
    )),
    // Match the lexer's closed escape set; scalar-value validation stays in
    // the compiler. Tokens keep spaces and comment markers inside literals.
    character: _ => token(seq("'", choice(/[^'\\\r\n]/, /\\[ntr\\'"0]/, /\\u\{[0-9A-Fa-f]+\}/), "'")),
    string: _ => token(seq('"', repeat(choice(/[^"\\\r\n]/, /\\[ntr\\'"0]/, /\\u\{[0-9A-Fa-f]+\}/)), '"')),
    hole: _ => token(/\?[A-Za-z_][A-Za-z0-9_]*|\?/),
    argument_slot: _ => token(/·[₀₁₂₃₄₅₆₇₈₉]*/),
    comment: _ => token(seq('//', /[^\n]*/)),
  },
});

function contextualWords($) {
  return CONTEXTUAL_WORDS.map(word => alias(word, $.identifier));
}

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

function typeBinary($, operators, precedence, associativity, operand = $._declaration_type) {
  const wrap = associativity === 'right' ? prec.right : prec.left;
  return operators.map(operator => wrap(precedence, seq(
    field('left', operand), field('operator', operator), field('right', operand),
  )));
}

function headBinary($, operators, precedence, associativity) {
  const wrap = associativity === 'right' ? prec.right : prec.left;
  return operators.map(operator => wrap(precedence, seq(
    field('left', $._head_expression), field('operator', operator), field('right', $._head_expression),
  )));
}
