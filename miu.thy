theory "miu"
  imports Main
begin

datatype miu = M | I | U

inductive_set S :: "miu list set" where
  "[M, I] : S" |
  "x @ [I] : S ==> x @ [I, U] : S" |
  "[M] @ x : S ==> [M] @ x @ x : S" |
  "x @ [I, I, I] @ y : S ==> x @ [U] @ y : S" |
  "x @ [U, U] @ y : S ==> x @ y : S"

fun ci :: "miu list => nat" where
  "ci [] = 0" |
  "ci (x#xs) = (if x = I then 1 + (ci xs) else ci xs)"

lemma [rule_format,simp]: "ALL y. ci (x @ y) = ci x + ci y"
  apply(induct_tac x)
   apply(auto)
  done

lemma miu_inv: "x : S ==> (ci x) mod 3 ~= 0"
  apply(erule S.induct)
      apply(auto)
  apply(arith)
  done

theorem th_miu : "[M, U] ~: S"
  apply(rule classical)
  apply(simp)
  apply(drule miu_inv)
  apply(simp)
  done

theorem th_miu2 :
  shows "[M, U] ~: S"
proof (rule classical)  (* 1. ¬ [M, U] ∉ S ⟹ [M, U] ∉ S *)
  assume "~ [M, U] ~: S"
  from this have 1 : "[M, U] : S" by simp
  from this have "ci [M, U] mod 3  ~= 0" by (rule miu_inv)
  from this have  2: "~ [M, U] : S" by simp
  from 1 and 2 have  "False" by simp
  from this show "[M, U] ∉ S" by simp
qed

end