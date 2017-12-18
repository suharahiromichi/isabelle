(*
  Programming and Proving in Isabelle/HOL 
  4. Isar: A Language for Structured Proofs
*)

(* 4.1 Isar by Example *)

theory "prog-prove-sample-4"
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

(* 4.1.1 this, then, hence and thus *)

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

(* 4.1.2 Structured Lemma Statements: fixes, assumes, shows *)

lemma sample5 :
  fixes f :: " 'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists> a. {x . x \<notin> f x} = f a" using s by (auto simp: surj_def)
  thus "False" by blast
qed

(* 4.2 Proof Patterns *)

lemma sample6 : "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> a. {x . x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x . x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

(* 4.3.3 Raw Proof Blocks *)

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  {
    fix k assume k : "a + b = b * k"
    have "\<exists> k'. a = b * k'"
    proof
      show "a = b * (k - 1)" using k by(simp add: algebra_simps)
    qed
  }
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

(* 4.4 Case Analysis and Induction *)
(* 4.4.1 Datatype Case Analysis *)

lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y # ys"
  thus ?thesis by simp
qed

(* 4.4.2 Structural Induction *)

lemma "\<Sum>{0..n::nat} = n * (n + 1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0 * (0+1) div 2" by simp
next
  fix n assume "\<Sum>{0..n::nat} = n * (n + 1) div 2"
  thus "\<Sum>{0..Suc n} = Suc n * (Suc n + 1) div 2" by simp
qed

lemma "\<Sum>{0..n::nat} = n * (n + 1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

(* 4.4.4 Rule Induction *)

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True" |
  "evn (Suc 0) = False" |
  "evn (Suc(Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0
  show ?case by simp
next
  case evSS
  thus ?case by simp
qed

end
