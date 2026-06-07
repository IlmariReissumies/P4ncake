Theory compilerProof
Ancestors
  panLang panProps panSem compiler p4 p4_full_bigstep p4_exec_sem p4_ebpf
Libs
  wordsLib


(*----NOTESs----*)
(*
Type scope = ``:((varn, (v # lval option)) alist)``;
Type state = 
    <| locals      : varname |-> 'a v
     ; globals     : varname |-> 'a v
     ; code        : funname |-> ((varname # shape) list # ('a panLang$prog))
                     (* arguments (with shape), body *)
     ; eshapes     : eid |-> shape
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; sh_memaddrs : ('a word) set
     ; clock       : num
     ; be          : bool
     ; ffi         : 'ffi ffi_state
     ; base_addr   : 'a word
     ; top_addr    : 'a word;          

val s = ``(s:('a,'ffi) panSem$state)``
*)


        
(*----VERIFICATIONS----*)
  
(* Semantic properties of the value-relations *)
Inductive v_rel:
  v_rel (e_v (v_bool T)) (Val (Word 1w)) ∧
  v_rel (e_v (v_bool F)) (Val (Word 0w)) ∧
  (*(v_rel (e_v (v_bit (b,l))) (Val (Word wrd)) && MAP (\(x,y).case (x,y) of (T,1) => T | (F,0) => T | (_,_) => F) $ ZIP (b,word_to_bin_list (wrd:word64)))*)
  (*(v_rel (e_v (v_str s)) (Struct vals) && EVERY (\((wrd1, _), Val Word wrd2). case (word_compare wrd1 wrd2) of 1w => T | 0w => F) $ ZIP ((REPLICATE 8 chars_to_word (string_to_chars s)), vals))*)
End

Inductive state_rel:
  s_rel 
End

Theorem compile_exp_correct:
  (∀ e uninit (scope_lists:scope_list) e' (n:num) m env pan_e s.
    bigstep_e_exec uninit (scope_lists:scope_list) (INL (e)) (n:num) = SOME $ (INL e', m) ∧
    is_v e' ∧ compile_exp env e = SOME (env, pan_e) ∧ state_rel scope_lists s ⇒
    ∃ v. eval s pan_e = SOME v ∧
         v_rel e' v ) ∧
  ∀ es uninit (scope_lists:scope_list) es' (n:num) m env pan_e s.
    bigstep_e_exec uninit (scope_lists:scope_list) (INR (es)) (n:num) = SOME $ (INR es', m) ∧
    EVERY is_v es' ∧ EVERY (\x. compile_exp env x = SOME (env, pan_e)) es ∧ state_rel scope_lists s ⇒
    ∃ vs. OPT_MMAP (eval s) pan_es = SOME vs ∧
         LIST_REL v_rel es' vs                     
Proof
  Induct
  >~ [‘e_v _’]
  >- Cases_on ‘n’ >> (rw [compile_exp_def, bigstep_e_exec_def, AllCaseEqs()] >> (rw [eval_def] >> metis_tac [v_rel_rules]))
  >~ [‘e_unop _’]
  >- (rw [compile_unop_def, compile_exp_def, bigstep_e_exec_def, AllCaseEqs()]
  >- (gvs[oneline e_exec_unop_def, AllCaseEqs(), oneline unop_exec_def] >> first_x_assum drule_all >> strip_tac >> rw[eval_def] >> gvs[v_rel_cases] >> gvs[wordLangTheory.word_op_def] >> gvs[wordLangTheory.word_op_def])
  >- (gvs[oneline e_exec_unop_def, AllCaseEqs(), oneline unop_exec_def] >> first_x_assum drule_all >> strip_tac >> rw[eval_def] >> gvs[v_rel_cases] >> fs[bitv_unop_def] >> gvs[wordLangTheory.word_op_def])
  >- (gvs[oneline e_exec_unop_def, AllCaseEqs(), oneline unop_exec_def] >> first_x_assum drule_all >> strip_tac >> rw[eval_def] >> gvs[v_rel_cases] >> fs[bitv_unop_def, AllCaseEqs()] >> gvs[wordLangTheory.word_op_def] >> gvs[v_rel_cases])
  >- (gvs[oneline e_exec_unop_def, AllCaseEqs(), oneline unop_exec_def] >> first_x_assum drule_all >> strip_tac >> rw[eval_def] >> gvs[v_rel_cases] >> gvs[wordLangTheory.word_op_def])
  >- cheat
  >- cheat
  >- cheat
  >- cheat)
  >~ [‘e_binop _’]
  >- cheat
  >~ [‘e_var _’] 
  >- cheat
  >~ [‘e_acc _ _’]
  >- cheat
  >~ [‘e_cast _ _’]
  >- cheat
  >~ [‘e_concat _ _’]
  >- cheat
  >~ [‘e_slice _ _ _’]
  >- cheat
  >~ [‘e_call _ _’]
  >- cheat
  >~ [‘e_select _ _ _’]
  >- cheat
  >~ [‘e_struct _’]
  >- cheat
  >~ [‘e_header _ _’]
  >- cheat
  >~ [‘INR []’]
  >- (rw [bigstep_e_exec_def])
  >~ [‘INR (_::_)’]
  >- cheat >> gvs [compile_exp_def]
QED


        
(*
REDO 
Theorem compile_stmt_correct:

Proof

QED
*)
