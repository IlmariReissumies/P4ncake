Theory compiler
Ancestors
  panLang p4

          
val _ = monadsyntax.temp_add_monadsyntax()
val _ = monadsyntax.enable_monad "option"

                                                       
(*
Definition test:
  foo 0 = SOME [] ∧
  foo (SUC x) =
    if x = 0:num then NONE
    else do
      ys <- foo x;
      return(T::ys)
      od
End                  
*)
                   
(*--AUXILIARY--*)
(*
---TODO:---
fun lookup_var
fun lookup_call_type
fun lookup_field_index
fun morph_calls
-----------
Type yoooooo = “:'a # string”

val test = “(17,"hello") : num yoooooo”

Datatype:
  myrec = <| field1 : 'a; field2 : num |>
End

Type foo = “:num yoooooo myrec”

val test2 = “<| field1 := (17,"hello"); field2 := 12156 |> : foo”
*)

Type word64b = “:64 word”
val ones = “unit bit1 bit1 bit1 bit1 bit1 bit1 word : word64b”
val p_exp_ones = “Const ones”
                   
Type mlstringpair = “:string # mlstring”;

Datatype:
  env = <| signatures : string;
             varnames : mlstringpair |>
End

val test = “<| signatures := "Hi"; varnames := ("oh", strlit "ah") |>” 
                   
(*
Dictionary of either {varn, varname} : {varn, mlstring} or
                     {string, varname} : {string, mlstring}
*)

Definition lval_to_mlstring_def:
  lval_to_mlstring (lval_varname varname)   = strlit "TEMP-VARNAME" ∧
  lval_to_mlstring (lval_null)              = strlit "TEMP-NULL--to_mlstring not finished"  ∧
  lval_to_mlstring (lval_field lval s)      = strlit "TEMP-FIELD-to_mlstring not finished" ∧
  lval_to_mlstring (lval_slice lval e1 e2)  = strlit "TEMP-SLICE-to_mlstring not finished" ∧
  lval_to_mlstring (lval_paren lval)        = strlit "TEMP-PAREN-to_mlstring not finished"
End

Definition varn_to_mlstring_def:
  varn_to_mlstring_def (varn_name s)    = strlit "TEMP-VARNAME" ∧
  varn_to_mlstring_def (varn_star funn) = strlit "TEMP-FUNNAME"
End
  
(*--COMPILATION--*)
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
  | _ => ARB                   (* ERROR, invalid, should not happen *)
End

Definition compile_unop_def:
  compile_unop (op, pan_e) = case op of
    unop_neg        => ARB
  | unop_compl      => ARB
  | unop_neg_signed => ARB
  | unop_un_plus    => ARB
  | _ => ARB                   (* ERROR, invalid, should not happen *)
End

(*TODO: needs redoing with monad*)
Definition compile_exp_def:
  compile_exp (e_binop e1 op e2)  =
  do
    e1' <- compile_exp e1;
    e2' <- compile_exp e2;
    return $ compile_binop (e1', op, e2')
  od ∧       
  compile_exp (e_unop op e)       = compile_unop (op, compile_exp e) ∧
  compile_exp (e_call funn es)    = NONE ∧             (*a stmt in Pancake, also has actions and extern calls*)
  compile_exp (e_list es)         = NONE ∧             (*let cs = map compile es in sequence maybe *)
  compile_exp (e_var varn)        = NONE ∧             (*need check with table*)
  compile_exp (e_v val)           = NONE ∧             (*what can val be*)
  compile_exp (e_acc e field)     = NONE ∧             (*need a helper function "field name to index"*)
  compile_exp (e_cast cast e)     = NONE ∧
  compile_exp (e_struct fields)   = NONE ∧
  compile_exp (e_header b fields) = NONE ∧
  compile_exp (e_select e ss x)   = NONE ∧
  compile_exp (e_slice e1 e2 e3)  = NONE ∧             (*bit-slice*)
  compile_exp (e_concat e1 e2)    = NONE ∧             (*bit_strings*)
  compile_exp _ = NONE          (* ERROR, invalid, should not happen *)
End

(*TODO: throwing of errors*)
Definition compile_stmt_def:
  compile_stmt (stmt_empty)                = NONE ∧
  compile_stmt (stmt_ass l_val e)          =
  do
    e' <- compile_exp e;
    (* get global/local from varname *)
    return $ Assign Global (lval_to_mlstring l_val) (e') 
  od ∧
  compile_stmt (stmt_cond e stmt_t stmt_f) =
  do
    e'  <- compile_exp e;
    pt' <- compile_stmt stmt_t;
    pf' <- compile_stmt stmt_f;
    return $ If e' pt' pf'
  od ∧
  compile_stmt (stmt_block t_scope stmt)   = ARB ∧
  compile_stmt (stmt_ret e)                =
  do
    e' <- (compile_exp e);
    return $ Return e'
  od ∧
  compile_stmt (stmt_seq stmt1 stmt2)      =
  do
    p1' <- compile_stmt stmt1;
    p2' <- compile_stmt stmt2;
    return $ Seq p1' p2'
  od ∧
  compile_stmt (stmt_trans e)              = ARB ∧
  compile_stmt (stmt_app x es)             = ARB ∧            (* Method call *)
  compile_stmt (stmt_ext)                  = ARB ∧
  compile_stmt _ = ARB         (* ERROR, invalid, should not happen *)
End

(*
Definition pre_pass_def:
  pre_pass_def =
  do
    
  od
End
*)

(*Entry*)(*
Definition compile_def:
  compile_def =
  do
    env = pre_pass    
    pancake_program = compile_prog  
    some_pancake_function pancake_program
  od
End
*)

(* Prepass needs:
   - Type of functions (tail, etc..)       table
   - Variables and their varkind           table
   - Structs to store fieldnames indecies  table
   - Global vars/funs                      table
   - Store calls in P4 to change to stmts     -- are there more complicaded calls in P4 than Pancake
   - Direction translations
*)
