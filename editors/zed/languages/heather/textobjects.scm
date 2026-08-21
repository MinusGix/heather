(function_declaration
  body: (block) @function.inside) @function.around

(theorem_declaration
  body: (block) @function.inside) @function.around

[
  (inductive_declaration body: (constructor_list) @class.inside)
  (record_declaration body: (field_list) @class.inside)
  (class_declaration body: (field_list) @class.inside)
  (instance_declaration body: (instance_body) @class.inside)
] @class.around

(comment)+ @comment.around
