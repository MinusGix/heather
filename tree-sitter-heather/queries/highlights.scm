(comment) @comment
(number) @number
(hole) @variable.special
(argument_slot) @variable.special
(universe) @type.builtin
(builtin_type) @type.builtin
(refl_expression) @constant.builtin

[
  "import" "inductive" "record" "class" "instance" "designation"
  "datarepr" "impl" "fn" "theorem" "meta" "requires" "extends"
  "for" "at" "prefix" "mk" "let" "split" "on" "match" "if"
  "else" "as" "code" "calc" "self" "infer"
] @keyword

[
  "λ" "fun" "∀" "∃"
] @keyword.function

[
  "+" "-" "++" "*" "<" "<=" "=" "≠" "&&" "||" "∙"
  "¬" "∧" "∨" "↔" "<->" "->" "=>" "⊢" "|-" ":="
] @operator

(inductive_declaration name: (identifier) @type)
(record_declaration name: (identifier) @type)
(class_declaration name: (identifier) @type)

(function_declaration name: (qualified_identifier) @function)
(theorem_declaration name: (qualified_identifier) @function)
(designation_declaration value: (identifier) @function)

(constructor name: (identifier) @constructor)
(constructor_pattern constructor: (_) @constructor)
(match_arm pattern: (identifier) @constructor)
(type_parameter name: (identifier) @type)
(parameter_name name: (identifier) @variable.parameter)
(field name: (identifier) @property)
(record_field name: (identifier) @property)
(named_argument name: (identifier) @property)
(member_expression member: (identifier) @property)
(head_member_expression (identifier) @property)

(call_expression function: (identifier) @function.call)
(explicit_call_expression (qualified_identifier) @function.call)
(identifier) @variable
