(*
  Programming and Proving in Isabelle/HOL 
  4. Isar: A Language for Structured Proofs
*)

theory "prog-prove-sample-4"  (* example codes  *)
  imports Main

begin

lemma test : "\<not> surj (f :: 'a  \<Rightarrow>  'a set)"
proof
assume 0: "surj f"
  from 0 have 1: " \<forall> A. \<exists> a. A = f a" by (simp add: surj_def)
  from 1 have 2: "EX a. {x . x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

(* a sample of the obtain *)

end
