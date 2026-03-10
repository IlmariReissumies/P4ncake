Theory compiler
Ancestors
  panLang p4

Definition compile_binop_def:
  compile_binop (pan_e1, op, pan_e2) = case op of
    binop_le      => Cmp Lower    (pan_e1) (pan_e2)
  | binop_ge      => Cmp NotLess  (pan_e1) (pan_e2)
  | binop_ge      => Cmp NotLess  (pan_e1) (pan_e2)
  | binop_lt      => Cmp Less     (pan_e1) (pan_e2)
  | binop_gt      => Cmp NotLower (pan_e1) (pan_e2)
  | binop_neq     => Cmp NotEqual (pan_e1) (pan_e2)
  | binop_eq      => Cmp Equal    (pan_e1) (pan_e2)                        
  | binop_mul     => Panop Mul    [pan_e1;  pan_e2]
  | binop_div     => ARB          [pan_e1;  pan_e2]
  | binop_mod     => ARB          [pan_e1;  pan_e2]
  | binop_add     => Op Add       [pan_e1;  pan_e2]
  | binop_sat_add => ARB          [pan_e1;  pan_e2]
  | binop_sub     => Op Sub       [pan_e1;  pan_e2]
  | binop_sat_sub => ARB          [pan_e1;  pan_e2]
  | binop_and     => Op And       [pan_e1;  pan_e2]
  | binop_or      => Op Or        [pan_e1;  pan_e2]
  | binop_xor     => Op Xor       [pan_e1;  pan_e2]
  | binop_bin_and => ARB          [pan_e1;  pan_e2]
  | binop_bin_or  => ARB          [pan_e1;  pan_e2]
  | _ => ARB                   (* ERROR, invalid *)
End

Definition compile_unop_def:
  compile_unop (op, pan_e) = case op of
    unop_neg        => ARB
  | unop_compl      => ARB
  | unop_neg_signed => ARB
  | unop_un_plus    => ARB
  | _ => ARB                   (* ERROR, invalid *)
End

Definition compile_exp_def:
  compile_exp (e_binop e1 op e2) = compile_binop (compile_exp e1, op, compile_exp e2) ∧
  compile_exp (e_unop op e) = compile_unop (op, compile_exp e) ∧
  compile_exp _ = ARB
End

Definition compile_stmt_def:
  compile_stmt (stmt_empty)                = Skip ∧
  compile_stmt (stmt_ass l_val e)          = Assign Global (to_mlstring l_val) (compile_exp e) ∧
  (*
  compile_stmt (stmt_ass l_val e)          =
  (let v = to_mlstring l_val in
    let c = compile_exp e in
        Assign Global v c) ∧
  *)
  compile_stmt (stmt_cond e stmt_t stmt_f) = ARB ∧
  compile_stmt (stmt_block t_scope stmt)   = ARB ∧
  compile_stmt (stmt_ret e)                = ARB ∧
  compile_stmt (stmt_seq stmt1 stmt2)      = ARB ∧
  compile_stmt (stmt_trans e)              = ARB ∧
  compile_stmt (stmt_app x es)             = ARB ∧
  compile_stmt (stmt_ext)                  = ARB ∧
  compile_stmt _ = ARB         (* ERROR, invalid *)
End

Definition to_mlstring_def:
  to_mlstring _ = "TEMPORARY"
End
