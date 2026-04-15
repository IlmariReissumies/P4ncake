Theory compiler
Ancestors
  panLang
  p4
  finite_map
          
val _ = monadsyntax.temp_add_monadsyntax()
val _ = monadsyntax.enable_monad "option"
                   
(*--AUXILIARY--*)
Type state_dict  = “:varname |-> ('a prog list)” (* To create stmts for the state-machine if-elses *)
Type scope_dict  = “:varname |-> varkind”        (* Global or Local, for funn and varnn *)
Type staten_dict = “:64 exp |-> word64”  

Datatype:
  env_rec = <| states : 'a ; scopes : 'b; state_nums : 'c |>
End

(* TODO *)
Definition lval_to_mlstring_def:
  lval_to_mlstring (lval_varname varname)   = strlit "TEMP-VARNAME" ∧
  lval_to_mlstring (lval_null)              = strlit "TEMP-NULL--to_mlstring not finished"  ∧
  lval_to_mlstring (lval_field lval s)      = strlit "TEMP-FIELD-to_mlstring not finished" ∧
  lval_to_mlstring (lval_slice lval e1 e2)  = strlit "TEMP-SLICE-to_mlstring not finished" ∧
  lval_to_mlstring (lval_paren lval)        = strlit "TEMP-PAREN-to_mlstring not finished"
End

(* TODO *)
Definition varn_to_mlstring_def:
  varn_to_mlstring_def (varn_name s)    = strlit "TEMP-VARNAME" ∧
  varn_to_mlstring_def (varn_star funn) = strlit "TEMP-FUNNAME"
End

       
(* Returns: (word64), (num list) *)
Definition chars_to_word_def:
  chars_to_word [] = (0w, []) ∧
  chars_to_word cs =
  let wrd :word64 = FOLDL (\w (c, shift_n).let c':word64 = (n2w (ORD c)) << shift_n in w ⊕ c') (0w) $ ZIP (TAKE 8 cs, GENLIST (\m.m*8) (8)) in
    (wrd, DROP 8 cs)
End

Definition string_to_chars_def:
  string_to_chars "" = [] ∧
  string_to_chars (STRING c rst) =
  let rst_cs = string_to_chars rst in
    c::rst_cs   
End

Definition string_to_struct_def:
  string_to_struct s =
  do
     cs <<- string_to_chars s;
     wrds_pair <<- REPLICATE 8 (chars_to_word cs);
     pan_wrds <<- MAP (\w.Const w) $ lLEFT wrds_pair;
     Struct $ pan_wrds
  od
End

Definition lLEFT_def:
  lLEFT l = MAP (\(l,r).l) l
End

Definition lRIGHT_def:
  lRIGHT l = MAP (\(l,r).r) l
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
    unop_neg        => Op Xor [pan_e; Const(1w:word64)]
  | unop_compl      => Op Xor [pan_e; Const(0xFFFFFFFFFFFFFFFFw:word64)]
  | unop_neg_signed => Op Add [Op Xor [pan_e; Const(0xFFFFFFFFFFFFFFFFw:word64)]; Const(0xFFFFFFFFFFFFFFFFw:word64)]               
  | unop_un_plus    => Op Add [pan_e; Const(0w:word64)]
End
        
Definition compile_exp_def:
  compile_exp env (e_binop e1 op e2)  =
  do
    (env', e1') <- compile_exp env e1;
    (env', e2') <- compile_exp env e2;
    return (env', compile_binop (e1', op, e2'))
  od                                     ∧       
  compile_exp env (e_unop op e)       =                     (* unop is only called on e=bool or bitv *)
  do
    (env', e') <- compile_exp env e;
    return (env', compile_unop (op, e'))
  od                                     ∧
  compile_exp env (e_call funn es)    = NONE ∧             (*a stmt in Pancake, also has actions and extern calls*)
  compile_exp env (e_list es)         = NONE ∧             (*let cs = map compile es in sequence maybe *)
  compile_exp env (e_var varn)        = (case varn of
    varn_name n  => return $ (env, Var Local (strlit n))
  | varn_star fn => NONE)                   ∧            
  compile_exp env (e_v val)           = (case val of
    v_bool T        => return $ (env, Const(1w:word64))
  | v_bool F        => return $ (env, Const(0w:word64))
  | v_bit (bools,n) =>
      (let
         wrd_indx_list = ZIP ((MAP (\b.case b of T => 1w :word64 | F => 0w :word64) bools), (GENLIST (\m.m) n));
         wrd = FOLDR (\(m,i) c.(m << i) ⊕ c) (0w :word64) wrd_indx_list;
       in
         return $ (env, Const wrd))
  | v_str s         => return (env, string_to_struct s)
  | v_struct svs    => NONE
  | v_header hd svs => NONE
  | v_ext_ref i     => NONE
  | v_bot           => NONE)             ∧
  compile_exp env (e_acc e field)     = NONE ∧             
  compile_exp env (e_cast cast e)     = NONE ∧
  compile_exp env (e_struct fields)   = NONE ∧
  compile_exp env (e_header b fields) = NONE ∧             (*fields are (string#exp). Similar to a struct*)
  compile_exp env (e_select e ss s)   = NONE ∧             (*switch*)
  compile_exp env (e_slice e1 e2 e3)  = NONE ∧             (*bit-slice*)
  compile_exp env (e_concat e1 e2)    = NONE ∧             (*bit_strings*)
  compile_exp _ _ = NONE
End

        
(* TODO
   - input enviroment/enviroment entvienment
   - variables need env-table check for varkind value
   - return should check stack return varaibels? (not needed since type-checked already?)
*)
Definition compile_stmt_def:
  compile_stmt env (stmt_empty)                = return (env, Skip) ∧
  compile_stmt env (stmt_ass l_val e)          =
  do
    (env', e') <- compile_exp env e;
    return (env', Assign Global (lval_to_mlstring l_val) (e'))
  od                                              ∧
  compile_stmt env (stmt_cond e stmt_t stmt_f) =
  do
    (env', e')    <- compile_exp env e;
    (env'', pt')  <- compile_stmt env' stmt_t;
    (env''', pf') <- compile_stmt env' stmt_f;
    return (env', If e' pt' pf')
  od                                              ∧
  compile_stmt env (stmt_block t_scope stmt)   = NONE ∧    
  compile_stmt env (stmt_ret e)                =
  do
    (env', e') <- (compile_exp env e);
    return (env', Return e')
  od                                              ∧
  compile_stmt env (stmt_seq stmt1 stmt2)      =
  do
    (env', p1')  <- compile_stmt env  stmt1;
    (env'', p2') <- compile_stmt env' stmt2;
    return (env'', Seq p1' p2')
  od                                              ∧
  compile_stmt env (stmt_trans e)              =
  do
    (env', pan_e) <- (compile_exp env e);
    wrd <- FLOOKUP env.state_nums pan_e;
        return (env', Seq (Assign Local (strlit "trans") (Const wrd)) Break)    
  od ∧
  compile_stmt env (stmt_app x es)             = NONE ∧       (* Method call *)
  compile_stmt env (stmt_ext)                  = NONE ∧
  compile_stmt _ _ = NONE                  
End

 
(*-------------------------------------------------
Does:
    - Updates enviroment giving every state in block an unique number
    - Compiles each states' stmts
    - Puts those stmts into panLang conditionals (one for each state) with comp. of "trans"-variable and unique number as guard
        
Paramathers:
    - states : ((state_name, stmt) alist)
        
Returns: sequence of panLang conditionals
-------------------------------------------------*)
Definition compile_states_def:
  compile_states env states =
  do
    (env', _, nums) <<- FOLDL (\(e,i,l) (st_name,_). (env with state_nums := (env.state_nums |+ (string_to_struct st_name, i)), i + (1w :word64), i::l) ) (env, (2w :word64), []) states;
    l <- OPT_MMAP (compile_stmt env') (lRIGHT states);
    (seqs :64 prog list) <<- lRIGHT l;
    conds <<- FOLDR (\(num, seq) p. If (Cmp Equal (Var Local (strlit "trans")) (Const num)) seq p :64 prog) Skip (ZIP (nums,seqs));
    return (env', conds)
  od
End


(* TODO:
   - make pr_accept and pr_reject do more than just break
   - make parser be seperate function?
*)
(*-------------------------------------------------
The Parser is a state machine and and is in Pancake translated into a function containing a conditional blocks for every state. Required states are the states: Start, Accept, and Reject.

Returns: pair of; new enviroment and the panLang prog describing the whole parser
-------------------------------------------------*)
Definition compile_parser_def:
  compile_parser env pars_map =
  (let
     e_trans = Const (2w:word64); (* start state will always be first in the list of states and so always get value 2 *)
     e_accept = Const (1w:word64);
     e_reject = Const (0w:word64);
     e_var_trans = (Var Local (strlit "trans"):64 exp);
     pr_accept = Break:64 prog;
     pr_reject = Break:64 prog;
   in
     do
       (env', pr_states) <- compile_states env pars_map;
       pr_if' <<- If ((Cmp Equal) e_var_trans e_reject) pr_reject pr_states;
       pr_if  <<- If ((Cmp Equal) e_var_trans e_accept) pr_accept pr_if';
       return (env', While (Const (1w:word64)) (Dec (strlit "trans") One e_trans pr_if))
     od)
End

(* TODO *)
Definition compile_control_def:
  compile_control env tbl_map = NONE
End

(*-------------------------------------------------
    - pbl_type      : programmable block type
    - sd_list       : list of (in order) 1. sequence of the first-level stmts in the block* 2. all paramathers and their direction
    - b_func_map    :
    - t_scope       :
    - pars_ms       : maps/dictionaries for parser(s), mapping state names and their stmts
    - tbl_map       :

        *For parser blocks this will instead just be the 'invisible' transision to the start state
-------------------------------------------------*)
Definition compile_pblock_def:
  compile_pblock env n (pbl_type, sd_list, b_func_map, t_scope, pars_map, tbl_map) =
  case pbl_type of
    pbl_type_parser =>
          do
            (env', pr) <- compile_parser env pars_map;
            (let
               prms = MAP (\(l,r).(l, One)) sd_list;
               decl =
               <|     name        := strlit n
                    ; inline      := F
                    ; export      := F
                    ; params      := prms
                    ; body        := pr
                    ; return      := One
               |> :64 fun_decl;
             in
               return (env', decl))
          od
  | pbl_type_control => NONE
End


(* Returns (:decl list) *)
Definition compile_pblocks_def:
  compile_pblocks env [] = return (env, []) ∧
  compile_pblocks env (pa::pas) = case pa of (n, pbl) =>
   do
     (env', decl)  <- compile_pblock env n pbl;
     (env'', decls) <- compile_pblocks env' pas;
     return $ (env'', (decl::decls))
   od                   
End

(* TODO *)
Definition compile_archblocks_def:
  compile_archblocks env _ [] = return (env, []) ∧
  compile_archblocks env pblock_ms (ablock::ablocks) = case ablock of
    arch_block_inp => NONE
  | arch_block_pbl _ _ =>
      do
        (env',decls) <- compile_pblocks env pblock_ms;   
        return $ (env',decls)
      od
  | arch_block_ffbl s => NONE
  | arch_block_out => NONE
End

(* (ab_list # pblock_map # 'a ffblock_map # 'a input_f # 'a output_f # 'a copyin_pbl # 'a copyout_pbl # 'a apply_table_f # 'a ext_map # func_map) *)
Definition compile_actx_def:
  compile_actx env (abs, (_, pblock_ms), _, _, _, _, _, _, _, func_map) =
  do
    (env', decls) <- compile_archblocks env pblock_ms abs;
    return (env', decls)
  od
End
(*
(*---PRE-PASS & SETUP---*)
      
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
*)
Definition env_setup_def:
  env_setup =
    let dict1 = FEMPTY : word64 state_dict in
      let dict2 = FEMPTY : scope_dict in
        let dict3 = FEMPTY : staten_dict in
          let env = <| states := dict1 ; scopes := dict2 ; state_nums := dict3 |> in
            return env
End
(*
(*---ENTRY---*)
Definition compile_def:
  compile_def =
  do
    let env = env_setup in
    (_, pancake_program) <- compile_prog env;
    case pancake_program of
      NONE => "Throw some error"
    | SOME => NONE (*some_pancake_function pancake_program*)
  od
End
*)
