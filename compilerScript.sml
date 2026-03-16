(*
P4 to Pancake transpiler, "P4ncake".  It assumes well-typed P4 programs.
*)

Theory compiler
Ancestors
  panLang
  p4
  finite_map
          
val _ = monadsyntax.temp_add_monadsyntax()
val _ = monadsyntax.enable_monad "option"
                  
(*
---TODO:---
fun lookup_var
fun lookup_call_type
fun lookup_field_index
fun morph_calls
-----------
---EXAMPLES:---
Type yoooooo = “:'a # string”

val test = “(17,"hello") : num yoooooo”

Datatype:
  myrec = <| field1 : 'a; field2 : num |>
End

Type foo = “:num yoooooo myrec”

val test2 = “<| field1 := (17,"hello"); field2 := 12156 |> : foo”

Type mlstringpair = “:string # mlstring”;

Definition test:
  foo 0 = SOME [] ∧
  foo (SUC x) =
    if x = 0:num then NONE
    else do
      ys <- foo x;
      return(T::ys)
      od
End 
---------------
*)
                   
(*--AUXILIARY--*)            
Type scope_dict  = “:varname |-> varkind”
Type state_dict = “:varname |-> ('a prog list)”
Type scope_kv   = “:finitemap # varkind”
Type state_kv   = “:varname # ('a state_dict)”

Datatype:
  env_rec = <| scopes : 'a ; states : 'b|>
End
                  

 
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
(*
Assumes that Pancake deals with overflowing values (for the saturated ADD and SUB).
        
Paramethers: op : unop in P4, pan_eX is a (compiled P4) Pancake expression
*)
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
  | binop_sat_add => Op Add       [pan_e1;  pan_e2]
  | binop_sub     => Op Sub       [pan_e1;  pan_e2]
  | binop_sat_sub => Op Sub       [pan_e1;  pan_e2]
  | binop_and     => Op And       [pan_e1;  pan_e2]
  | binop_or      => Op Or        [pan_e1;  pan_e2]
  | binop_xor     => Op Xor       [pan_e1;  pan_e2]
  | binop_bin_and => Op And       [pan_e1;  pan_e2]
  | binop_bin_or  => Op Or        [pan_e1;  pan_e2]
  | _ => NONE                                          (* ERROR, invalid, should not happen *)
End

(*
Since the transpiler only considers well-typed programs, this defintion only considers the cases of
those.  Thus, cases if which the expressions don't conform to the correct units/values/types are ignored
and could create silent errors.

The following P4 exp. are the unitary operators (in order):
   - boolean negation
   - binary compliment
   - signed negation
   - unary plus (NO-OP)

Paramethers: op : unop in P4, pan_e is a (compiled P4) Pancake expression
*)
Definition compile_unop_def:
  compile_unop (op, pan_e) = case op of
    unop_neg        =>
      let one    = 0x0000000000000001w : word64 in
        let one_e  = Const one in
          Op Xor [pan_e; one_e]
  | unop_compl      =>
      let ones   = 0xFFFFFFFFFFFFFFFFw : word64 in
        let ones_e = Const ones in
          Op Xor [pan_e; ones_e]
  | unop_neg_signed =>
      let ones   = 0xFFFFFFFFFFFFFFFFw : word64 in
        let ones_e = Const ones in
          Op Add [Op Xor [pan_e; ones_e]; ones_e]                      
  | unop_un_plus    =>
      let zero   = 0x0000000000000000w : word64 in
        let zero_e = Const zero in
          Op Add [pan_e; zero_e]
End

Definition compile_exp_def:
  compile_exp (e_binop e1 op e2)  =
  do
    e1' <- compile_exp e1;
    e2' <- compile_exp e2;
    return $ compile_binop (e1', op, e2')
  od ∧       
  compile_exp (e_unop op e)       =
  do
    e' <- compile_exp e;
    return $ compile_unop (op, e')
  od ∧
  compile_exp (e_call funn es)    = NONE ∧             (*a stmt in Pancake, also has actions and extern calls*)
  compile_exp (e_list es)         = NONE ∧             (*let cs = map compile es in sequence maybe *)
  compile_exp (e_var varn)        = NONE ∧             (*need check with table*)
  compile_exp (e_v val)           = NONE ∧             (*what can val be*)
  compile_exp (e_acc e field)     = NONE ∧             (*need a helper function "field name to index"*)
  compile_exp (e_cast cast e)     = NONE ∧
  compile_exp (e_struct fields)   = NONE ∧
  compile_exp (e_header b fields) = NONE ∧             (*fields are (string#exp). Similar to a struct*)
  compile_exp (e_select e ss s)   = NONE ∧             (*switch*)
  compile_exp (e_slice e1 e2 e3)  = NONE ∧             (*bit-slice*)
  compile_exp (e_concat e1 e2)    = NONE ∧             (*bit_strings*)
  compile_exp _ = NONE                                 (* ERROR, invalid, should not happen *)
End

Definition compile_stmt_def:
  compile_stmt (stmt_empty)                = NONE ∧
  compile_stmt (stmt_ass l_val e)          =
  do
    e' <- compile_exp e;
    (* get global/local from varname *)
    return $ Assign Global (lval_to_mlstring l_val) (e')  (*Are there local functions*)
  od ∧
  compile_stmt (stmt_cond e stmt_t stmt_f) =
  do
    e'  <- compile_exp e;
    pt' <- compile_stmt stmt_t;
    pf' <- compile_stmt stmt_f;
    return $ If e' pt' pf'
  od ∧
  compile_stmt (stmt_block t_scope stmt)   = NONE ∧    
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
  compile_stmt (stmt_trans e)              = NONE ∧       (* I reduces to parser state name "st" *)
  compile_stmt (stmt_app x es)             = NONE ∧       (* Method call *)
  compile_stmt (stmt_ext)                  = NONE ∧
  compile_stmt _ = NONE                                   (* ERROR, invalid, should not happen *)
End

Definition compile_parser_def:
  compile_parser env = NONE
End

Definition compile_control_def:
  compile_control env = NONE
End

Definition compile_pblock_def:
  compile_pblock env (pbl_type, sd_list, b_func_map, t_scope, pars_map, tbl_map) =
    case pbl_type of
      pbl_type_parser => return $ compile_parser env
    | pbl_type_control => return $ compile_control env
End

Definition compile_pblocks_def:
  compile_pblocks env [] = return $ env ∧
  compile_pblocks env (pblock::pblocks) =
  do
    env' <- compile_pblock env pblock;
    env'' <- compile_pblocks env' pblocks;
    return $ env''
  od
End

(*---PRE-PASS & SETUP---*)
(* Records the state blocks' code into a (prog list) so that the
 states blocks can be collapsed.  Also, renames any variables that
 shadow previous variables. *)
Definition states_pass_def:
  states_pass_def = NONE
End
        
(*
Definition pre_pass_def:
  pre_pass_def env =
  do
    env' <- make_decls env
    env'' <- scopes_prepass env'
    env''' <- field_to_indices env''
  od
End
*)

Definition env_setup_def:
  env_setup =
    let dict1 = FEMPTY : scope_dict in
      let dict2 = FEMPTY : word64 state_dict in
        let env = <| scopes := dict1 ; states := dict2  |> in
          return env
End

(*---ENTRY---*)
(*
Definition compile_def:
  compile_def =
  do
    env  <- env_setup
    env' <- pre_pass env   
    (_, pancake_program) <- compile_prog env'
    case pancake_program of
      NONE => "Throw some error"
    | SOME $ some_pancake_function pancake_program
  od
End
*)

(* Prepass needs:
   - Type of function call                 
   - Structs to store fieldnames indecies  
   - Store calls in P4 to change to stmts  
   - Direction translations
   - Actionmap (struct)
*)
