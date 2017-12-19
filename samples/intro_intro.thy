(* 
introduction of the Isabelle introduction 
https://qiita.com/myuon_myon/items/11bb5bfc2e274fdaea7c
*)

theory "intro_intro"
imports Main
begin

lemma ex:
  fixes n :: nat
  assumes "n \<ge> 2"
  shows "2*n \<le> n^2"
  using assms
  apply (induct n, simp)
  apply simp
  apply (subst Suc_eq_plus1)+
  apply (subst power2_sum)
  apply auto
  done

lemma ex':
  fixes n :: nat
  assumes "n \<ge> 2"
  shows "2 * n \<le> n^2"
  using assms     (* this is "assums" *)

proof (induct n, simp)
  fix n :: nat
  assume a : "2 \<le> n \<Longrightarrow> 2 * n \<le> n^2" and b: "2 \<le> Suc n"
  have "2 * Suc n \<le> 2 * (n + 1)" using a b by simp
  also have "\<dots> \<le> 2 * n + 2" by simp
  also have "\<dots> \<le> n^2 + 2 * n + 1" using b by simp
  also have "\<dots> = (n + 1)^2" using power2_sum [of n 1] by simp
  finally
  show "2 * Suc n \<le> (Suc n)^2" by simp
qed

end