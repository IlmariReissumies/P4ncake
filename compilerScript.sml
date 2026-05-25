Theory compiler
Ancestors
  panLang
  p4
  finite_map
          
val _ = monadsyntax.temp_add_monadsyntax()
val _ = monadsyntax.enable_monad "option"
                   
(*-------------------------------------------------*)
(*                 AUXILIRARY                      *)
(*-------------------------------------------------*)
Type state_dict  = “:varname |-> ('a prog list)” (* To create stmts for the state-machine if-elses *)
Type scope_dict  = “:varname |-> varkind”        (* Global or Local, for funn and varnn *)
Type staten_dict = “:64 exp |-> word64”
Type out_ind_dict = “:varname |-> num list” (* Function to parameter position *)

Datatype:
  env_rec = <| states : 'a ; scopes : 'b; state_nums : 'c ; out_ind : 'd ; table : e' |>
End
      
Definition lLEFT_def:
  lLEFT l = MAP (\(l,r).l) l
End

Definition lRIGHT_def:
  lRIGHT l = MAP (\(l,r).r) l
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

Definition get_fun_name_def:
  get_fun_name s = NONE
End

Definition get_var_name_def:
  get_var_name s = NONE
End

Definition to_no_name_def:
  to_no_name = strlit ""
End

(* Generates a new, unique (to this compiler!) variable_name *)
(* TODO: to implement a true unique name-generator we need to rename all variable also *)
Definition generate_varname_def:
  generate_varname = NONE
End

(* Generates a list of Varnames, all unique. Empty list results in 'no name' and, thus, returns an empty list. *)
(* TODO: to implement a true unique name-generator we need to rename all variable also *)
Definition generate_varnames_def:
  generate_varname [] = []
  generate_varnames l = NONE
End
(*-------------------------------------------------*)
(*                  COMPILER                       *)
(*-------------------------------------------------*)
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
  compile_exp env (e_call funn es)    =
  do
    case env.ass_var of
      strlit "" =>
        do
          (* TODO: do normal call *)
        od
    | var_name  =>
        do
          function_name <- get_fun_name funn;
          args_pan      <- compile_exp es
          out_iv_pair   <- env.out_ind_value_pairs function_name;
          out_vars      <- OPT_MMAP ((\as i. get_element i as) args_pan) (lLEFT out_iv_pair);
          out_var_names <- OPT_MMAP (\e. case e of (Var v_kind v_name) => SOME v_name | _ => NONE) out_vars;
          s1   <<- DecCall var_name One function_name (OPT_MMAP args_pan) Skip;                                          (* TODO: deal with shape! *)
          s2   <<- FOLDL (\s (name, v). Seq (Assign Local name v) s) Skip ZIP (out_vnms, (lRIGHT out_iv_pair));
          env' <<- env with ass_var := get_no_name;
          return (env', Seq s1 s2)
        od
  od ∧
  compile_exp env (e_list es)         = NONE ∧             
  compile_exp env (e_var varn)        = (case varn of      (* TODO: need lookup! *)
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
        env' <- env with ass_var := lval_to_mlstring lval;
        (env'', e') <- compile_exp env' e;
        env''' <- env'' with ass_var := strlit "";
        return (env''', Assign Local (lval_to_mlstring lval) (e'))
      od 
   | pairs  =>
      do
        name <- get_var_name lval;
        env' <<- env with ass_var := name;
        (env'', e_pan) <- compile_exp env' e;
        env''' <<- env'' with ass_var := strlit "";
        ind <- FOLDL ((\n i (s, ind). if ((get_var_name s) == n) then (SOME i) else NONE) name) (SOME 0) pairs;
        env4 <<- env''' with out_ind_val_pairs := env'''.out_ind_val_pairs |+ (ind, e_pan);
        return (env''', Assign Local (name) (e_pan))
      od ) ∧
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
  compile_stmt env (stmt_app x es)             = NONE ∧
  compile_stmt env (stmt_ext)                  = NONE ∧
  compile_stmt _ _ = NONE                  
End

 
(*-------------------------------------------------
Does:
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
    conds <<- FOLDR (\(num, seq) p. If (Cmp Equal (Var Local (strlit "trans")) (Const num)) seq p :64 prog) Skip (ZIP (nums,seqs));
    return (env', conds)
  od
End


(* TODO:
   - make pr_accept and pr_reject do more than just break
   - care about specific function call .extract(blah-blah) (puts argument into P4-header structure)  
*)
(*-------------------------------------------------
The Parser is a state machine and and is in Pancake translated into a function containing a conditional blocks for every state. Required states are the states: Start, Accept, and Reject.

Returns: pair of; new enviroment and the panLang prog describing the whole parser
-------------------------------------------------*)
Definition compile_parser_def:
  compile_parser env pars_map =
  (let
     e_trans  = Const (2w:word64); (* start state will always be first in the list of states and so get value 2 *)
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

        
(*-------------------------------------------------
Does: Creates a new function (above the control function block in Pancake) for every control-block local function. Saves index for every "out" or "inout" parameter for that function (as name and num-list pair) in enviroment to be used for copy-out during function calls. Adds all control-block local variables as paramathers to the function.


TODO: Make sure list of function declerations match order of those functions declared in memory! (top-to-bottom OR bottom-to-top)

Return: enviroment and list of Pancake function declerations
-------------------------------------------------*)
Definition compile_block_functions_def:
  compile_block_functions env vars [] = return (env, []) ∧
  compile_block_functions env vars ((n, (stmt, ad_list))::b_funcs) =
  do
    prms <<- (to_params (lLeft ad_list)) ++ vars;
    out_s_ind_pairs <<- FOLDL (\l ((s, d), ind).  
                             case d of
                               d_out -> (s, ind)::l
                             | d_inout -> (s, ind)::l
                             | _ -> l) [] ZIP (ad_list, (GENLIST (\m.m) m));
    env' <<- env' with out_sinds := out_s_ind_pairs;
    (env'', b) <- compile_stmt env' stmt;
    decl <<-
        <|     name   := get_fun_name n
             ; inline := F
             ; export := F
             ; params := prms
             ; body   := b
             ; return := One
        |>;
    env''' <<- env'' with out_ind_value_pairs := env''.out_ind_value_pairs |+ (get_fun_name n, out_ind_list);
    (env4, decls) <- compile_block_functions env''' vars b_funcs;
    return (env4, decl::decls)
  od                               
End

Definition generate_action_matching_def:
  generate_action_matching env prms =
  do
    (env', x) <<- generate_varname env;
    v_l1::v_ls <<- lCOPY prms;
    (env'', s_l1::s_ls) <- FOLDL (\(e, x_p) x. let (e', x_p') = compile_exp e x in (e', x_p::x_p') ) (env', []) sls;
    
    s <<- DecCall x One env.match_fun [v_l1]::[s_l1] Skip;
    prog <<- FOLDL ((\env prev v. let (env', r) = generate_varname env
                                       in (x, Seq s $ DecCall r One env.match_fun v_l::s_l $ Assign Local x (Op And [r]::[x])))) env'') (x, s) ZIP (v_ls, s_ls);
    return (env'', x, prog)
  od
End
        
(*
Ebpf-architecture specific table matching function (as of yet).
*)
Definition compile_action_tables_def:
  compile_action_tables env vars [] = return (env, []) ∧
  compile_action_tables env vars (table_name, (mks, (default_action, es)))::ts =
  do
    (env', prms) <- FOLDL (\(e, x_p) x. let (e', x_p') = compile_exp e x in (e', x_p::x_p') ) (env, []) es;
    b <<- Skip;

    case env.tbl of
      tbls =>
        do
          (env'', action) <<- generate_varname env';
          (env''', priority) <<- generate_varname env'';
          (env4, found) <<- generate_varname env''';
                 
          s <<- Dec action One (Const w0 :64 word) $ Dec priority One (Const w0 :64 word) $ Dec found One (Const w0 :64 word) Skip;
          fun_end <<- Return TopAddr; (* TODO *)
          tbls' <- FOLDR ((\(e, prev) ((s, p), a). do (e', s'); return ((s',p),a)::prev) env) [] tbls;
          (env5, prog) <<- FOLDL((\v_ls (e, prev) action priority found ((s_ls, prio), a).
                                    (let
                                       (e', x, p_a) = generate_action_matching e v_ls s_ls;
                                       ass_a    = Assign Local action a;
                                       ass_prio = Assign Local priority prio;
                                       p_true   = If (Op (Cmp lower) [priority]::[prio]) (Seq ass_a ass_prio) (Skip);
                                       p_false  = Seq ass_a ass_prio;
                                       p_true'  = If found p_true p_false;
                                       p_false' = Skip;
                                       p_conds  = Seq (If x p_true' p_false') (Skip);
                                     in
                                       (e', Seq (Seq p_a p_conds) prev))) v_ls action priority found) (env4, fun_end) tbls';      
          b <<- prog)
        od
    | [] =>)
    decl <<-
         <|       name   := get_fun_name n
                ; inline := F
                ; export := F
                ; params := prms
                ; body   := b
                ; return := One
         |>;
  od
End

Definition compile_control_def:
  compile_control env n b_func_map func_map sd_list tbl_map t_scope =
     do
       vars <<- get_local_vars t_scope;
       prms <<- to_params sd_list;
       (env', decls) <- compile_block_functions env vars b_func_map;          (*important to be before block compilation (dir. depend on stmt-compilation order)*)
       (env'', table_decls) <- compile_action_tables env' vars tbl_map;
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
       return (env''', decls::(table_decl::cntrl_decl))
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
  compile_global_funs env [] = return (env, [])
  compile_global_funs env (s, (stmt, sd_list))::func_map =
  do
    (env', body_pan) <- compile_stmt stmt env ;
    prms <<- to_params sd_list;
    decl <<-
    <|         name        := get_fun_name s
             ; inline      := F
             ; export      := F
             ; params      := prms
             ; body        := body_pan
             ; return      := One
    |> :64 fun_decl;
    (env'', decls) <- compile_global_funs env' func_map;
    return (env'', decl::decls))
  od
End

Definition compile_actx_def:
  compile_actx env (abs, (_, pblock_ms), _, _, _, _, _, apply_table, _, func_map) =
  do
    (env', global_decls) <- compile_global_funs func_map;
    (env'', decls) <- compile_archblocks env' pblock_ms abs func_map;
    return decls::global_decls
  od
End


(*-------------------------------------------------*)
(*                    SETUP                        *)
(*-------------------------------------------------*)
Definition env_setup_def:
  env_setup ((_, _, _, tbl), _, _, _) =
  (let
    dict1 = FEMPTY : word64 state_dict;
    dict2 = FEMPTY : scope_dict;
    dict3 = FEMPTY : staten_dict;
    dict4 = FEMPTY : word64 out_ind_dict;
    env = <| states := dict1 ; scopes := dict2 ; state_nums := dict3 ; out_ind := dict4 ; table := tbl |>;
   in
     return env)
End

(*-------------------------------------------------*)
(*                    ENTRY                        *)
(*-------------------------------------------------*)

(*
   For now, aenv is assumed to have 'a <- ebpf_scope, thus is only for the ebpf architecture.
*)
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

