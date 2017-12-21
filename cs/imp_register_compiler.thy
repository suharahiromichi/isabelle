(*
Concrete Semantics with Isabelle/HOL
3. Case Study: IMP Expressions
*)

theory "imp_register_compiler" imports Main begin

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

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)" (* 12 *)
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))" (* 12 *)

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

lemma aval_asimp_const : "aval (asimp_const a) s = aval a s"
  apply (induction a)
    apply (auto split: aexp.split)
done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus [simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
              apply simp_all (* just for a change from auto *)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))" (* "V ''x''" *)

lemma aval_asimp [simp] : "aval (asimp a) s = aval a s"
  apply (induction a)
    apply simp_all
  done

(*********************************************)
subsection "Register Machine"
(*********************************************)

type_synonym reg = nat
type_synonym rstate = "reg \<Rightarrow> val"

datatype instr = LDI val reg | LD vname reg | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> reg \<Rightarrow> val" where
  "exec1 (LDI n R) s rs r = (if R = r then n else rs(r))" |
  "exec1 (LD  x R) s rs r = (if R = r then s(x) else rs(r))" |
  "exec1 (ADD R S) s rs r = (if R = r then rs(R) + rs(S) else rs(r))"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> reg \<Rightarrow> val" where
  "exec [] s rs r = rs(r)" |
  "exec (i # is) s rs r = exec is s (exec1 i s rs) r"

value "exec [LDI 5 0, LD ''y'' 1, ADD 0 1] <''x'' := 42, ''y'' := 43> 
<0 := 0, 1 := 0, 2 := 50> 0" (* 48 *)

(*********************************************)
subsection "Compilation"
(*********************************************)

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp (N n) r = [LDI n r]" |
  "comp (V v) r = [LD v r]" |
  "comp (Plus a1 a2) r = (comp a1 r) @ (comp a2 (r + 1)) @ [ADD r (r + 1)]"
 
value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z'')) 0"
 (* "[LD ''x'' 0, LDI 1 1, ADD 0 1, LD ''z'' 1, ADD 0 1]" *)

fun execn :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "execn [] s rs = rs" |
  "execn (i # is) s rs = execn is s (exec1 i s rs)"

lemma exec_execn : "exec is1 s rs r = (execn is1 s rs) r"
  apply (induction is1 arbitrary: rs)
   apply auto  
  done

lemma execn_dist_append : "(execn (is1 @ is2) s rs) = (execn is2 s (execn is1 s rs))"  
  apply (induction is1 arbitrary: rs)
   apply auto
  done

lemma execn_comp_append : "(execn ((comp a r) @ is2) s rs) = (execn is2 s (execn (comp a r) s rs))"
  apply (auto simp add: execn_dist_append)
  done

lemma comp_left_rs_not_changed : "r1 > r \<Longrightarrow> execn (comp a r1) s rs r = rs(r)"
  apply (induction a arbitrary: r r1 rs)
    apply (auto simp add: execn_dist_append)
  done

theorem "exec (comp a r) s rs r = aval a s"
  apply (induction a arbitrary: r rs)
    apply (auto simp add: exec_execn execn_comp_append comp_left_rs_not_changed)
  done

end