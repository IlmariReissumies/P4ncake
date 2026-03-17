Theory test
Ancestors
  panLang panProps compiler p4
Libs
  wordsLib


(* Note the ARB:s --- it's ok for the examples to have holes in them
    so long as it doesn't get in the way of evaluation.

   Here I tried to write

      x = y;
      return x

   in P4 abstract syntax
 *)
Quote example1 = Term:
  stmt_seq
    (stmt_ass (lval_varname (varn_name "x")) (e_var (varn_name "y")))
    (stmt_ret (e_var (varn_name "x")))
End

(* Runs the compiler definitions on example_prog1
    and saves the result as a theorem.
    Note the ^ antiquotation to reference an ML variable in a HOL term quotation
 *)
val example1_compile_thm = EVAL “compile_stmt ^example1”

(* If we wanted to do further processing on the compiler output we could
    extract it from the theorem like this:

val example1_compile_tm = example1_compile_thm |> concl |> rhs |> rand

   ...but the compiler says NONE on this program so it doesn't apply here

 *)

(* Let's try to evaluate a simple Pancake expression that we hand-cooked instead.
   In concrete syntax this would be

      var 1 x = 1 + 1;
      return x;
 *)
Quote example2 = Term:
  Dec «x» One (Op Add [Const 1w; Const(1w:word64)])
    (Return (Var Local «x»))
End

(* More clock lets evaluation proceed further, necessary if you have many
   loop iterations and function calls.
   The state can be specified in more detail if need be, but for this simple
   example ARB sufficed
 *)
val example2_run = EVAL “evaluate (^example2, ARB with clock := 10)”
