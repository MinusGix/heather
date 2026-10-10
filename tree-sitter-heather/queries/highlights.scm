(comment) @comment
(number) @number
(character) @string
(string) @string
(hole) @variable.special
(argument_slot) @variable.special
(universe) @type.builtin
(builtin_type) @type.builtin
(refl_expression) @constant.builtin

[
  "import" "export" "inductive" "record" "class" "instance" "designation"
  "datarepr" "impl" "fn" "theorem" "axiom" "meta" "evidence" "requires" "assuming" "extends" "decreases" "decreasing" "with"
  "for" "at" "prefix" "mk" "let" "have" "split" "on" "match" "if"
  "else" "as" "code" "calc" "self" "infer" "squash_ind"
] @keyword

(squash_type) @type.builtin

[
  "λ" "fun" "∀" "∃"
] @keyword

[
  "+" "-" "++" "*" "<" "<=" "=" "≠" "&&" "||" "∙" "⊔" "≈"
  "!" "¬" "∧" "∨" "↔" "<->" "→" "->" "=>" "⊢" "|-" ":=" "⟨" "⟩" "|" "⟦" "⟧"
] @operator

; Default names conservatively to variables. More specific, later patterns
; override this fallback in Zed.
(identifier) @variable
(qualified_identifier) @variable

; Heather conventionally capitalizes types and constructors. This also gives
; useful highlighting to references whose role cannot be inferred from the CST.
((identifier) @type
  (#match? @type "^[A-Z]"))
((qualified_identifier) @type
  (#match? @type "(^|::)[A-Z]"))

(inductive_declaration name: (identifier) @type)
(record_declaration name: (identifier) @type)
(class_declaration name: (identifier) @type)
(datarepr_declaration name: (identifier) @type)
(class_reference name: (_) @type)
(record_expression type: (_) @type)
(type_application_expression value: (_) @type)
(head_type_application (_) @type)

(function_declaration name: (qualified_identifier) @function)
(theorem_declaration name: (qualified_identifier) @function)
(axiom_declaration name: (qualified_identifier) @function)
(designation_declaration value: (identifier) @function)
(impl_declaration name: (identifier) @function)

(constructor name: (identifier) @constructor)
(constructor_pattern constructor: (_) @constructor)
(type_parameter name: (identifier) @type)
(parameter_name name: (identifier) @variable.parameter)
(lambda_binder (identifier) @variable.parameter)
(quantified_expression name: (identifier) @variable.parameter)
(field name: (identifier) @property)
(record_field name: (identifier) @property)
(named_argument name: (identifier) @property)
(named_pattern field: (identifier) @property)
(assignment name: (identifier) @property)
(repr_clause name: (identifier) @property)
(member_expression member: (identifier) @property)
(head_member_expression (identifier) @property)

(call_expression function: (identifier) @function)
(call_expression function: (qualified_identifier) @function)
(explicit_call_expression (qualified_identifier) @function)
(head_call_expression (identifier) @function)
(head_call_expression (qualified_identifier) @function)
(member_expression
  member: (identifier) @function
  (argument_list))
(head_member_expression
  (identifier) @function
  (argument_list))

; Constructor calls are syntactically calls, so recover the more precise role
; using Heather's capitalization convention after the general call captures.
((call_expression function: (identifier) @constructor)
  (#match? @constructor "^[A-Z]"))
((call_expression function: (qualified_identifier) @constructor)
  (#match? @constructor "(^|::)[A-Z]"))

; Goal-oriented words get tactic-like keyword styling even when the CST sees
; an ordinary identifier. This is intentionally lexical: `apply(x)` and a
; user binding named `give` may be highlighted the same way as the syntax.
[
  "apply" "give"
] @keyword @preproc
((identifier) @keyword @preproc
  (#any-of? @preproc "apply" "give"))

(propagation_expression "?" @operator)
(head_propagation_expression "?" @operator)
