Theory compiler
Ancestors
  panLang p4

Definition compile_binop_def:
  compile_binop binop_mul = Panop Mul ∧
  compile_binop binop_add = Op Add ∧
  compile_binop _ = ARB
End
