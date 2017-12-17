(* GEB MIU Puzzle *)

theory "miu"
  imports Main

begin

datatype miu = M | I | U

inductive_set MIU :: "miu list set" where
  "[M, I] : MIU" |
  "x @ [I] : MIU \<Longrightarrow> x @ [I, U] : MIU" |  (* \<Longrightarrow> abbreviation is "= = >" *)
  "[M] @ x : MIU \<Longrightarrow> [M] @ x @ x : MIU" |
  "x @ [I, I, I] @ y : MIU \<Longrightarrow> x @ [U] @ y : MIU" |
  "x @ [U, U] @ y : MIU \<Longrightarrow> x @ y : MIU"

fun ci :: "miu list \<Rightarrow> nat" where        (* \<Rightarrow> abbreviation is "= >" *)
  "ci [] = 0" |
  "ci (x # xs) = (if x = I then ci xs + 1 else ci xs)"

lemma [rule_format, simp] : "\<forall> y. ci (x @ y) = ci x + ci y"
  apply (induct_tac x)
   apply (auto)
  done
                                              (* \<noteq> abbs "~ =" *)
lemma miu_inv : "x \<in> MIU \<Longrightarrow> ci x mod 3 \<noteq> 0"  (* \<in> abbs "i n" *)
  apply (erule MIU.induct)
      apply (auto)
  apply (arith)
  done

theorem th_miu'' : "[M, U] \<notin> MIU"    (* \<notin> abbs "~ :" *)
  (* \<not> [M, U] \<notin> S \<Longrightarrow> [M, U] \<notin> S *)
  apply (rule classical)
  apply (simp)
  apply (drule miu_inv)
  apply (simp)
  done

theorem th_miu' : "[M, U] \<notin> MIU"
proof (rule classical)  (* \<not> [M, U] \<notin> S \<Longrightarrow> [M, U] \<notin> S *)
  assume "\<not> [M, U] \<notin> MIU"
  from this have 1 : "[M, U] : MIU" by simp
  from this have "ci [M, U] mod 3 \<noteq> 0" by (rule miu_inv)
  from this have  2: "\<not> [M, U] : MIU" by simp
  from 1 and 2 have "False" by simp
  from this show "[M, U] \<notin> MIU" by simp
qed

theorem th_miu : "[M, U] \<notin> MIU"
proof (rule classical)  (* \<not> [M, U] \<notin> S \<Longrightarrow> [M, U] \<notin> S *)
  assume "\<not> [M, U] \<notin> MIU"
  hence 1 : "[M, U] : MIU" by simp
  hence "ci [M, U] mod 3 \<noteq> 0" by (rule miu_inv)
  hence 2: "\<not> [M, U] : MIU" by simp
  from 1 and 2 have "False" by simp
  thus "[M, U] \<notin> MIU" by simp
qed

(* END *)
