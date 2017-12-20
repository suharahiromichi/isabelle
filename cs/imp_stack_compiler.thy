theory "imp_stack_compiler" imports Main begin

(*********************************************)
subsection "Arithmetic Expressions"
(*********************************************)

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>" (* 12 *)
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>" (* 5 *)

(*********************************************)
subsection "Constant Folding"
(*********************************************)

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)"

theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply (auto split: aexp.split)
done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
              apply simp_all (* just for a change from auto *)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))" (* "V ''x''" *)

lemma aval_asimp[simp] : "aval (asimp a) s = aval a s"
  apply (induction a)
    apply simp_all
  done

(*********************************************)
subsection "Stack Machine"
(*********************************************)

type_synonym stack = "val list"

datatype instr = LOADI val | LOAD vname | ADD

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (LOADI n) _ stk  =  n # stk" |
  "exec1 (LOAD x) s stk  =  s(x) # stk" |
  "exec1 ADD _ stk  =  (hd2 stk + hd stk) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stk = stk" |
  "exec (i#is) s stk = exec is s (exec1 i s stk)"

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"

lemma exec_append[simp]:
  "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
  apply (induction is1 arbitrary: stk)
   apply (auto)
  done

(*********************************************)
subsection "Compilation"
(*********************************************)

fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]" |
  "comp (V x) = [LOAD x]" |
  "comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"
  (* "[LOAD ''x'', LOADI 1, ADD, LOAD ''z'', ADD]" *)

theorem exec_comp : "exec (comp a) s stk = aval a s # stk"
  apply (induction a arbitrary: stk)
    apply (auto)
  done

end