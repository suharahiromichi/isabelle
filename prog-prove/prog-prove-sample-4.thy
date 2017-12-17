(*
  Programming and Proving in Isabelle/HOL 
  4. Isar: A Language for Structured Proofs
*)

theory "prog-prove-sample-4"  (* example codes  *)
  imports Main

begin

lemma sample1 : "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: " \<forall> A. \<exists> a. A = f a" by (simp add: surj_def)
  from 1 have 2: "EX a. {x . x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma sample2 : "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  have 1: " \<forall> A. \<exists> a. A = f a" using 0 by (simp add: surj_def)
  have 2: "EX a. {x . x \<notin> f x} = f a" using 1 by blast
  show "False" using 2 by blast
qed

lemma sample3 : "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists> a. {x . x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

lemma sample4 : "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x . x \<notin> f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed

lemma sample5 :
  fixes f :: " 'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists> a. {x . x \<notin> f x} = f a" using s by (auto simp: surj_def)
  thus "False" by blast
qed

lemma sample6 : "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x . x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x . x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

end
