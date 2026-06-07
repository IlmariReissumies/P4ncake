Theory compiler
Ancestors
  panLang
  p4
  finite_map
  p4_ebpf
          
val _ = monadsyntax.temp_add_monadsyntax()
val _ = monadsyntax.enable_monad "option"
                   
(*-------------------------------------------------*)
(*                 AUXILIRARY                      *)
(*-------------------------------------------------*)
Type state_dict  = “:varname |-> ('a prog list)” (* To create stmts for the state-machine if-elses *)
Type scope_dict  = “:varname |-> varkind”        (* Global or Local, for funn and varnn *)
Type staten_dict = “:64 exp |-> word64”
Type out_ind_dict = “:varname |-> num list”      (* Name to parameter position *)
Type out_val_dict = “:64 panLang$exp |-> num list”
Type apply_table = “:ebpf_ctrl”

Datatype:
  env_rec = <| states : 'a ; scopes : 'b; state_nums : 'c ; out_s_ind_pairs : 'd ; table : 'e ; ass_var : 'f ; out_ind_val_pairs : 'g ; match_fun : 'h|>
End
      
Definition lLEFT_def:
  lLEFT l = MAP (\(l,r).l) l
End

Definition lRIGHT_def:
  lRIGHT l = MAP (\(l,r).r) l
End

Definition lCOPY_def:
  lCOPY l = FOLDR (\e t. e::t) [] l
End

(* TODO *)
Definition lval_to_mlstring_def:
  lval_to_mlstring (lval_varname varname)   = strlit "TEMP-VARNAME" ∧
  lval_to_mlstring (lval_null)              = strlit "TEMP-NULL--to_mlstring not finished" ∧
  lval_to_mlstring (lval_field lval s)      = strlit "TEMP-FIELD-to_mlstring not finished" ∧
  lval_to_mlstring (lval_slice lval e1 e2)  = strlit "TEMP-SLICE-to_mlstring not finished" ∧
  lval_to_mlstring (lval_paren lval)        = strlit "TEMP-PAREN-to_mlstring not finished"
End

(* TODO *)
Definition lval_to_string_def:
  lval_to_string (lval_varname varname)   = "TEMP-VARNAME" ∧
  lval_to_string (lval_null)              = "TEMP-NULL--to_string not finished" ∧
  lval_to_string (lval_field lval s)      = "TEMP-FIELD-to_string not finished" ∧
  lval_to_string (lval_slice lval e1 e2)  = "TEMP-SLICE-to_string not finished" ∧
  lval_to_string (lval_paren lval)        = "TEMP-PAREN-to_string not finished"
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
  (let
     cs = string_to_chars s;
     wrds_pair = REPLICATE 8 (chars_to_word cs);
     pan_wrds  = MAP (\w.Const w) $ lLEFT wrds_pair;
   in
     Struct $ pan_wrds)
End

Definition bit_v_to_word_def:
  bit_v_to_word bools n =
  (let
     wrd_indx_list = ZIP ((MAP (\b.case b of T => 1w :word64 | F => 0w :word64) bools), (GENLIST (\m.m) n));
     wrd = FOLDR (\(m,i) c.(m << i) ⊕ c) (0w :word64) wrd_indx_list;
   in
        wrd :64 word)
End

(*TODO: all these functions---make unique and properly functioning*)
Definition get_trans_name:
  get_trans_name = strlit "trans"
End

Definition get_fun_name_def:
  get_fun_name s = "fun"
End

Definition get_var_name_def:
  get_var_name s = "var"
End

Definition get_match_fun_name_def:
  get_match_fun_name = strlit "match_fun"
End
        
Definition get_no_name_def:
  get_no_name = strlit ""
End

(* Generates a new, unique (to this compiler!) variable_name *)
(* TODO: to implement a true unique name-generator we need to rename all variable also *)
Definition generate_varname_def:
  generate_varname env = (env, strlit "")
End

(* Generates a list of Varnames, all unique. Empty list results in 'no name' and, thus, returns an empty list. *)
(* TODO: to implement a true unique name-generator we need to rename all variable also *)
Definition generate_varnames_def:
  generate_varnames env l = (env, strlit "")
End

Definition FOLDM_def:
  FOLDM fun a [] = return a ∧
  FOLDM fun a (b::bs) =
  do
    a' <- fun a b;
    FOLDM fun a' bs
  od
End

Theorem FOLDM_CONG[defncong]:
  !l l' b b' (f: 'a->'b->'a option) f'.
    l=l' /\ b=b' /\ (!x a. MEM x l' ==> (f a x = f' a x))
          ==>
    FOLDM f b l = FOLDM f' b' l'
Proof
cheat
  (*Induct
  THEN REWRITE_TAC [FOLDR, MEM]
  THEN REPEAT STRIP_TAC
  THEN REPEAT (PAT_X_ASSUM (Term‘x = y’) (SUBST_ALL_TAC o SYM))
  THEN REWRITE_TAC [FOLDR]
  THEN POP_ASSUM (fn th => MP_TAC (SPEC (Term‘h’) th) THEN ASSUME_TAC th)
  THEN REWRITE_TAC [MEM]
  THEN DISCH_TAC
  THEN MK_COMB_TAC
  THENL [CONV_TAC FUN_EQ_CONV THEN ASM_REWRITE_TAC [],
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []
           THEN REPEAT STRIP_TAC
           THEN FIRST_ASSUM MATCH_MP_TAC
           THEN ASM_REWRITE_TAC [MEM]]*)
QED
        
Definition mlstring_EQ_def:
  mlstring_EQ s1 s2 = T
End

                
(*-------------------------------------------------*)
(*                 eBPF FUNCTIONS                  *)
(*-------------------------------------------------*)
(*
TODO:   - finish
        - make dynamic for architecture used.
*)
Definition match_fun_def:
  match_fun v s = s
End
        
(*-------------------------------------------------*)
(*                    COMPILER                     *)
(*-------------------------------------------------*)
(*
Assumes that Pancake deals with overflowing values (for the saturated ADD and SUB).
        
Paramethers: op : unop in P4, pan_eX is a (compiled P4) Pancake expression

             TODO: fix faulty binpos: lisst cons!
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

(* TODO: termination for the FOLM (lambda) in e_call *)
Definition compile_exp_def:
  compile_exp env (e_binop e1 op e2)  =
  do
    (env',  stmts1, e1') <- compile_exp env e1;
    (env'', stmts2, e2') <- compile_exp env' e2;
    return (env'', stmts1++stmts2, compile_binop (e1', op, e2'))
  od                                     ∧       
  compile_exp env (e_unop op e)       =                     (* unop is only called on e=bool or bitv *)
  do
    (env', stmts, e') <- compile_exp env e;
    return (env', stmts , compile_unop (op, e'))
  od                                     ∧
  compile_exp env (e_call funn es)    =
  do
    case env.ass_var of
      varn_name "" => NONE
    | varn_name x =>
        do
          function_name <<- strlit $ get_fun_name funn;
          (env', sl, args_pan) <- FOLDM (\(e, sl, l) x. do (e', sl', x') <- compile_exp e x; return (e', sl++sl', l++[x']) od) (env, [], []) es;
          out_iv_pairs  <<- ([] : (num # 64 panLang$exp) list); (*(env'.out_ind_value_pairs) function_name;*)
          out_vars      <<- MAP (\i. EL i args_pan) (lLEFT out_iv_pairs);
          out_var_names <- OPT_MMAP (\e. case e of (Var v_kind v_name) => SOME v_name | _ => NONE) out_vars;
          varname <<- strlit (get_var_name x);
          s1   <<- DecCall varname One function_name args_pan Skip; 
          s2   <<- FOLDL (\s (name, v). Seq (Assign Local name v) s) Skip $ ZIP (out_var_names, (lRIGHT out_iv_pairs));
          env'' <<- env' with ass_var := varn_name "";
          return (env'', sl++[Seq s1 s2], Var Local varname)
        od
  od ∧
  compile_exp env (e_list es)         = NONE ∧             
  compile_exp env (e_var varn)        = (case varn of      (* TODO: need lookup! *)
    varn_name n  => return $ (env, [] , Var Local (strlit n))
  | varn_star fn => NONE)                   ∧            
  compile_exp env (e_v val)           = (case val of
    v_bool T        => return $ (env, [], Const(1w:word64))
  | v_bool F        => return $ (env, [], Const(0w:word64))
  | v_bit (bools,n) => (*TODO: bit-arrays longer than 64 bits*)
      (let
         wrd = bit_v_to_word bools n
       in
         return $ (env, [], Const wrd))
  | v_str s         => return (env, [], string_to_struct s)
  | v_struct svs    => NONE
  | v_header b svs  => NONE
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

Definition compile_exps_def:
  compile_exps env [] = return (env, [], []) ∧
  compile_exps env (e::es) =
  do
    (env',  stmts1, e_pan)  <- compile_exp env e;
    (env'', stmts2, e_pans) <- compile_exps env' es;
    return (env'', stmts1++stmts2, e_pan::e_pans)
  od
End

Definition compile_set_exp_def:
  compile_set_exp env es = compile_exps env es
End

(* TODO
   - input enviroment/enviroment entvienment
   - variables need env-table check for varkind value
   - return should check stack return varaibels? (not needed since type-checked already?)
*)
Definition compile_stmt_def:
  compile_stmt env (stmt_empty)                = return (env, Skip) ∧
  compile_stmt env (stmt_ass lval e)           =
  (case env.out_s_ind_pairs of
     [] =>
       do
        (*--IN ASS. STMT---*)
        env' <<- env with ass_var := varn_name $ get_var_name $ lval_to_string lval;
        (env'', stmts, e') <- compile_exp env' e;
        env''' <<- env'' with ass_var := varn_name "";
        (*-----------------*)
        return (env''', FOLDR Seq (Assign Local (strlit (get_var_name (lval_to_string lval))) (e')) stmts)
      od 
   | pairs  =>
       do
        (*--IN ASS. STMT---*)
        name <<- get_var_name $ lval_to_string lval;
        env' <<- env with ass_var := varn_name name;
        (env'', stmts, e_pan) <- compile_exp env' e;
        env''' <<- env'' with ass_var := varn_name "";
        (*-----------------*)
        ind <- FOLDL (\ i (s, ind). if (mlstring_EQ (get_var_name s) (strlit name)) then (SOME ind) else i) NONE pairs;
        env4 <<- env''' with out_ind_val_pairs := env'''.out_ind_val_pairs |+ (ind, e_pan);
        return (env''', FOLDR Seq (Assign Local (strlit name) (e_pan)) stmts)
      od ) ∧
  compile_stmt env (stmt_cond e stmt_t stmt_f) =
  do
    (env', stmts, e')    <- compile_exp env e;
    (env'', pt')  <- compile_stmt env' stmt_t;
    (env''', pf') <- compile_stmt env' stmt_f;
    return (env', FOLDR Seq (If e' pt' pf') stmts)
  od                                              ∧
  compile_stmt env (stmt_block t_scope stmt)   = NONE ∧    
  compile_stmt env (stmt_ret e)                =
  do
    (env', stmts, e') <- (compile_exp env e);
    return (env', FOLDR Seq (Return e') stmts)
  od                                              ∧
  compile_stmt env (stmt_seq stmt1 stmt2)      =
  do
    (env', p1')  <- compile_stmt env  stmt1;
    (env'', p2') <- compile_stmt env' stmt2;
    return (env'', Seq p1' p2')
  od                                              ∧
  compile_stmt env (stmt_trans e)              =
  do
    (env', stmts, pan_e) <- (compile_exp env e);
    wrd <- FLOOKUP env.state_nums pan_e;
    return (env', FOLDR Seq (Seq (Assign Local get_trans_name (Const wrd)) Break) stmts)    
  od ∧
  compile_stmt env (stmt_app x es)             = NONE ∧
  compile_stmt env (stmt_ext)                  = NONE ∧
  compile_stmt _ _ = NONE                  
End


Definition to_seq_def:
  to_seq [] = Skip ∧
  to_seq (s::ss) = Seq s (to_seq ss)
End
 
(*-------------------------------------------------
DOES:
    - Updates enviroment giving every state in block an unique number
    - Compiles each states' stmts
    - Puts those stmts into panLang conditionals (one for each state) with comp. of "trans"-variable and unique number as guard
        
Parameters:
    - states : ((state_name, stmt) alist)
        
Returns: sequence of panLang conditionals
-------------------------------------------------*)
Definition compile_states_def:
  compile_states env states =
  do
    (env', _, nums) <<- FOLDL (\(e,i,l) (st_name,_). (env with state_nums := (env.state_nums |+ (string_to_struct st_name, i)), i + (1w :word64), i::l) ) (env, (2w :word64), []) states;
    l <- OPT_MMAP (compile_stmt env') (lRIGHT states);
    (seqs :64 prog list) <<- lRIGHT l;
    conds <<- FOLDR (\(num, seq) p. If (Cmp Equal (Var Local get_trans_name) (Const num)) seq p :64 prog) Skip (ZIP (nums,seqs));
    return (env', conds)
  od
End



(*-------------------------------------------------
The Parser is a state machine and and is in Pancake translated into a function containing a conditional blocks for every state. Required states are the states: Start, Accept, and Reject.

TODO:   - make pr_accept and pr_reject do more than just break
        - care about specific function call .extract(blah-blah) (puts argument into P4-header structure)  

Returns: pair of; new enviroment and the panLang prog describing the whole parser
-------------------------------------------------*)
Definition compile_parser_def:
  compile_parser env pars_map =
  (let
     e_trans  = Const (2w:word64); (* start state will always be first in the list of states and so get value 2 *)
     e_accept = Const (1w:word64);
     e_reject = Const (0w:word64);
     e_var_trans = (Var Local get_trans_name:64 exp);
     pr_accept = Break:64 prog;
     pr_reject = Break:64 prog;
   in
     do
       (env', pr_states) <- compile_states env pars_map;
       pr_if' <<- If ((Cmp Equal) e_var_trans e_reject) pr_reject pr_states;
       pr_if  <<- If ((Cmp Equal) e_var_trans e_accept) pr_accept pr_if';
       return (env', While (Const (1w:word64)) (Dec get_trans_name One e_trans pr_if))
     od)
End

(* TODO: Shape should depend on type t correctly *)
Definition get_local_vars_def:
  get_local_vars (_, pairs) = FOLDL (\l (t, v). (case t v of (tau_bool,      lval_varname v') => (case v' of (varn_name x) => ((strlit x), (One))::[] | _ => l)
                                                           | (tau_bit st,    lval_varname v') => l
                                                           | (tau_bot,       lval_varname v') => l
                                                           | (tau_xtl st vs, lval_varname v') => l
                                                           | (tau_ext,       lval_varname v') => l )) [] pairs
End

(* TODO: need for specific shapes *)
Definition to_params_def:
  to_params sds = MAP (\(s,d). (s, One)) sds
End

Definition generate_params_def:
  generate_params env [] = (env, []) ∧
  generate_params env (prm::prms) =
  (let
     (env', s) = generate_varname env;
     (env'', ss) = generate_params env' prms
   in
     (env'', (s, One)::ss))
End


(*-------------------------------------------------*)        
(*-------------------------------------------------
Does: Creates a new function (above the control function block in Pancake) for every control-block local function. Saves index for every "out" or "inout" parameter for that function (as name and num-list pair) in enviroment to be used for copy-out during function calls. Adds all control-block local variables as paramathers to the function.


TODO: Make sure list of function declerations match order of those functions declared in memory! (top-to-bottom OR bottom-to-top)

Return: enviroment and list of Pancake function declerations
-------------------------------------------------*)
Definition compile_block_functions_def:
  compile_block_functions env vars [] = return (env, []) ∧
  compile_block_functions env vars ((n, (stmt, ad_list))::b_funcs) =
  do
    prms <<- (to_params (lLEFT ad_list)) ++ vars;
    out_sind_pairs <<- FOLDL (\l ((s, d), ind).  
                             case d of
                               d_out => (s, ind)::l
                             | d_inout => (s, ind)::l
                             | _ => l) [] $ ZIP (ad_list, (GENLIST (\m.m) (LENGTH ad_list)));
    env' <<- env with out_s_ind_pairs := out_sind_pairs;
    (env'', b) <- compile_stmt env' stmt;
    decl <<-
        <|     name   := strlit (get_fun_name n)
             ; inline := F
             ; export := F
             ; params := prms
             ; body   := b
             ; return := One
        |>;
    (*env''' <<- env'' with out_ind_val_pairs := env''.out_ind_val_pairs |+ (strlit (get_fun_name n), lRIGHT out_sind_pairs);*)
    env''' <<- env''; (* TODO: *)
    (env4, decls) <- compile_block_functions env''' vars b_funcs;
    return (env4, decl::decls)
  od                               
End


(*-------------------------------------------------
   DOES: Generates seqence of panLang$prog for matching all parameters to the match_function and ANDs up the result.
        
  TAKES: An enviroment, list of exp_pan and list of the apply_tables keys as exp_pan.

RETURNS: An enviroment, AND-variable keeping current AND from all match-results, stmts for searching (possible finding) one action
-------------------------------------------------*)
Definition generate_action_matching_def:
  generate_action_matching env [] [] = (env, Var Local (strlit ""), Skip) ∧
  generate_action_matching env (v_l::[]) (s_l::[]) = (env, Var Local (strlit ""), Skip) ∧ (*TODO*)
  generate_action_matching env (v_l1::v_ls) (s_l1::s_ls) =
  (let
    (env', AND_s : mlstring) = generate_varname env;
    AND_var       = Var Local AND_s;
    match_funn    = env'.match_fun : mlstring;
    stmt          = DecCall AND_s One match_funn (v_l1::[s_l1]) Skip;
    (env'', prog) = FOLDL (\(e, prev) (v, s). (let (e', RET_s : mlstring) = generate_varname e;
                                                   RET_var = Var Local RET_s
                                               in  
                                                 (e', Seq prev (DecCall RET_s One match_funn (v::[s]) (Assign Local AND_s (Op And ([AND_var]++[RET_var]))))))) (env', stmt) $ ZIP (v_ls, s_ls)
   in
     (env'', AND_var, prog))
End

(*-------------------------------------------------
ASSUMPTIONS: - priority a bit-vector max 1 word long (n ≤ 64).
-------------------------------------------------*)
Definition generate_actions_def:
  generate_actions env (_,_,_,_) [] = (env, Skip) ∧
  generate_actions env (prms, a_s, p_s, found) (((s_ls, a_prio), (a, _))::tbls) =
  (let
     (env', AND_var, p_a) = generate_action_matching env prms s_ls;
     cur_prio = Const (bit_v_to_word a_prio (LENGTH a_prio));
     ass_a    = Assign Local a_s (string_to_struct a);
     ass_prio = Assign Local p_s cur_prio;
     prio_var = Var Local p_s;
     p_false  = Seq ass_a ass_prio;
     p_true   = If (Cmp Lower prio_var cur_prio) (Seq ass_a ass_prio) Skip;
     p_true'  = If found p_true p_false;
     p_false' = Skip;
     p_conds  = Seq (If AND_var p_true' p_false') (Skip);
     (env'', prev) = generate_actions env' (prms, a_s, p_s, found) tbls
   in
     (env'', Seq (Seq p_a p_conds) prev)) 
End

(*-------------------------------------------------
     TODO: - check if theses "set_expression" will ever produce stmts as well, otherwise remove from here
           - replace concatination in the return with a general function
-------------------------------------------------*)
Definition compile_table_variables_def:
  compile_table_variables env [] = return (env, [], []) ∧
  compile_table_variables env (((ss, p), a)::tbls) =
  do
    (env', stmts, es_pan) <- compile_set_exp env ss;
    (env'', stmts', l)   <- compile_table_variables env' tbls;
    return (env'', (stmts++stmts'), l++[((es_pan, p), a)])
  od
End
        
(*-------------------------------------------------
ASSUMTIONS: - priority in tbl for certain action is of type bit-string
      TODO: - fun_end need real return value
            - only Ebpf-architecture specific
            - what to do with params?
-------------------------------------------------*)
Definition compile_action_tables_def:
  compile_action_tables env [] = return (env, []) ∧
  compile_action_tables env ((table_name, (mks, (default_action, es)))::ts) =
  do
    (env', stmts, args :64 exp list) <- compile_exps env es;
    (env'', fun_prms) <<- generate_params env' args;
    tbl <<- env''.table;
    (env''', a_s) <<- generate_varname env'';
    (env4, p_s)   <<- generate_varname env''';
    (env5, f_s)   <<- generate_varname env4;
    found   <<- Var Local f_s;
    (env6, stmts, tbl') <- compile_table_variables env5 tbl;
    start_prog <<- (Dec a_s One (Const (0w :64 word)) $ Dec p_s One (Const (0w :64 word)) $ Dec f_s One (Const (0w :64 word)) Skip);
    pre_prog   <<- to_seq stmts;
    (env7, prog) <<- generate_actions env6 (args, a_s, p_s, found) tbl';
    decl <<-
         <|         name   := strlit (get_fun_name table_name)
                  ; inline := F
                  ; export := F
                  ; params := fun_prms
                  ; body   := Seq (Seq start_prog pre_prog) prog
                  ; return := One
         |>;
    (env8, decls) <- compile_action_tables env7 ts;
    return (env8, decl::decls)
  od
End

(*-------------------------------------------------

-------------------------------------------------*)
Definition compile_control_def:
  compile_control env n b_func_map func_map sd_list tbl_map t_scope =
     do
       vars <<- get_local_vars t_scope;                                       (* TODO: this only gives names, not expressions *)
       prms <<- to_params sd_list;
       (env', decls) <- compile_block_functions env vars b_func_map;          (*important to be before block compilation (dir. depend on stmt-compilation order)*)
       (env'', table_decls) <- compile_action_tables env' tbl_map;
       b <- lookup_block_body n b_func_map;
       (env''', b') <- compile_stmt env' b;
       cntrl_decl <<-
       <|      name   := strlit n
             ; inline := F
             ; export := F
             ; params := prms
             ; body   := b' 
             ; return := One
       |>;
       d <<- table_decls++[cntrl_decl];
       return (env''', decls++d)
     od
End




(*
-------------------------------------------------
    - pbl_type      : programmable block type
    - sd_list       : list of (in order) 1. sequence of the first-level stmts in the block* 2. all paramaters and their direction
    - b_func_map    : maps block-local function names with their bodies and parameters
    - t_scope       :
    - pars_ms       : maps/dictionaries for parser(s), mapping state names and their stmts
    - tbl_map       : table name and, match-kind- ... and paramether, tuple

        *For parser blocks this will instead just be the 'invisible' transision to the start state
-------------------------------------------------
*)
Definition compile_pblock_def:
  compile_pblock env n (pbl_type, sd_list, b_func_map, t_scope, pars_map, tbl_map) func_map =
  case pbl_type of
    pbl_type_parser =>
          do
            (env', pr) <- compile_parser env pars_map;
            (let
               prms = to_params sd_list;
               decl =
               <|     name        := strlit n
                    ; inline      := F
                    ; export      := F
                    ; params      := prms
                    ; body        := pr
                    ; return      := One
               |> :64 fun_decl;
             in
               return (env', decl::[]))
          od
  | pbl_type_control =>
          do
            (env', decls) <- compile_control env n b_func_map func_map sd_list tbl_map t_scope;
            return (env', decls)
          od
End


(* Returns (:decl list) *)
Definition compile_pblocks_def:
  compile_pblocks env [] _  = return (env, []) ∧
  compile_pblocks env ((n, pbl)::pas) func_map =
   do
     (env', decl)  <- compile_pblock env n pbl func_map;
     (env'', decls) <- compile_pblocks env' pas func_map;
     return (env'', (decl ++ decls))
   od                   
End

(* TODO --- all block types *)
Definition compile_archblocks_def:
  compile_archblocks env _ [] _ = return (env, []) ∧
  compile_archblocks env pblock_ms (ablock::ablocks) func_map = case ablock of
    arch_block_inp => NONE
  | arch_block_pbl _ _ =>
      do
        (env',decls) <- compile_pblocks env pblock_ms func_map;   
        return $ (env',decls)
      od
  | arch_block_ffbl s => NONE
  | arch_block_out => NONE
End
        
Definition compile_global_funs_def:
  compile_global_funs env [] = return (env, []) ∧
  compile_global_funs env ((s, (stmt, sd_list))::func_map) =
  do
    (env', body_pan) <- compile_stmt env stmt;
    prms <<- to_params sd_list;
    decl <<-
    <|         name        := (strlit (get_fun_name s))
             ; inline      := F
             ; export      := F
             ; params      := prms
             ; body        := body_pan
             ; return      := One
    |>;
    (env'', decls) <- compile_global_funs env' func_map;
    return (env'', decl::decls)
  od
End

Definition compile_actx_def:
  compile_actx env (abs, (_, pblock_ms), _, _, _, _, _, apply_table, _, func_map) =
  do
    (env', global_decls) <- compile_global_funs env func_map;
    (env'', decls) <- compile_archblocks env' pblock_ms abs func_map;
    return (decls++global_decls)
  od
End


(*-------------------------------------------------*)
(*                    SETUP                        *)
(*-------------------------------------------------*)
Definition env_setup_def:
  env_setup ((_, _, _, tbl :ebpf_ctrl), _, _, _) =
  (let
    dict1 = FEMPTY : word64 state_dict;
    dict2 = FEMPTY : scope_dict;
    dict3 = FEMPTY : staten_dict;
    dict4 = FEMPTY : out_ind_dict;
    dict5 = FEMPTY : out_val_dict;
    pvar = varn_name "";
    env = <| states := dict1 ; scopes := dict2 ; state_nums := dict3 ; out_s_ind_pairs := dict4 ; table := tbl ; ass_var := pvar ; out_ind_val_pairs := dict5 ; match_fun := get_match_fun_name |>;
   in
     return env)
End

(*-------------------------------------------------*)
(*                    ENTRY                        *)
(*-------------------------------------------------*)

(*
   For now, aenv is assumed to have 'a <- ebpf_scope, thus is only for the ebpf architecture.
*)(*
Definition compile_def:
  compile_def actx (aenv, _, _, _) =
  do
    let env = env_setup aenv in
    pancake_program <- compile_prog env actx;
    case pancake_program of
      NONE => "Throw some error"
    | SOME => NONE (*some_pancake_function pancake_program*)
  od
End
*)
