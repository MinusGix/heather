(function_declaration
  name: (_) @name) @item

(theorem_declaration
  name: (_) @name) @item

[
  (inductive_declaration name: (identifier) @name)
  (record_declaration name: (identifier) @name)
  (class_declaration name: (identifier) @name)
  (instance_declaration class: (class_reference name: (_) @name))
  (datarepr_declaration name: (identifier) @name)
  (impl_declaration name: (identifier) @name)
] @item
