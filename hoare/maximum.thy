theory maximum
  imports "~~/src/HOL/Hoare/Hoare_Logic"
    "~~/src/HOL/Hoare/Arith2"
    "~~/src/HOL/Hoare/List"
begin

(* ******************* *)
(* ******************* *)
(* ******************* *)

definition maximum :: "nat list \<Rightarrow> nat" where
  "maximum l = foldr max l 0"

value "maximum [1,3,5,4,2]"    (* 5 *)
value "maximum []"             (* 0 *)

lemma max0r [simp] : "\<forall>a::nat. max 0 a = a"
  by (simp add: max_def)

lemma max0l [simp] : "\<forall>a::nat. max a 0 = a"
  by (simp add: max_def)

lemma max_assoc [simp] : "\<forall>x y z. max a (max b c) = max (max a b) c"
  apply (simp add: max_def)
  apply auto
  sorry

lemma l_hdtl [simp] : "x \<noteq> [] \<Longrightarrow> hd x # tl x = x"
  apply (induct x)
  by auto

lemma max_nil [simp] : "maximum [] = 0"
  apply (simp add: maximum_def)
  done

lemma max_hdtl_eq [simp] : "l \<noteq> [] \<Longrightarrow> max (hd l) (maximum (tl l)) = maximum l"
  apply (induct l)
  apply (auto)
  apply (simp add: hd_def tl_def maximum_def)
  done

lemma max_sym [simp] : "max a b = max b a"
  apply (simp add: max_def)
  apply auto
  sorry

lemma hdtl_eq [simp] : "x \<noteq> [] \<Longrightarrow> hd x # tl x = x"
proof (induct x)
  assume "[] \<noteq> []"
  thus "hd [] # tl [] = []" by auto
next
  fix a x
  show "hd (a # x) # tl (a # x) = a # x" by auto
qed

(* ******* *)
(* ******* *)
(* ******* *)

lemma l1 [simp] : "max (maximum []) y = maximum l \<Longrightarrow> y = maximum l"
  apply (simp add: maximum_def)
  done  

lemma l2' [simp] : "max (maximum x) y = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> y \<le> hd x \<Longrightarrow> max (maximum (tl x)) (hd x) = maximum l"
proof -
  fix x y l
  assume 1 : "max (maximum x) y = maximum l" and
    2 : "x \<noteq> []" and
    3 : "y \<le> hd x"

  from 3 have 4 : "maximum x = maximum l"
    by (metis "1" "2" dual_order.antisym max.bounded_iff max_def max_hdtl_eq)

  from 2 and 4 have "max (hd x) (maximum (tl x)) = maximum l" by auto     
  thus "max (maximum (tl x)) (hd x) = maximum l" by simp (* max_sym *)
qed

lemma l2 : "max y (maximum x) = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> y \<le> hd x \<Longrightarrow> maximum x = maximum l"
proof -
  fix x y l
  assume 1 : "max y (maximum x) = maximum l" and
    2 : "x \<noteq> []" and
    3 : "y \<le> hd x"

  show "maximum x = maximum l"
    by (metis "1" "2" dual_order.antisym max.bounded_iff max_def max_hdtl_eq)
qed

lemma l3 : "max y (maximum x) = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> \<not> y \<le> hd x \<Longrightarrow> max y (maximum (tl x)) = maximum l"
proof -
  fix x y l
  assume 1 : "max y (maximum x) = maximum l" and
    2 : "x \<noteq> []" and
    3 : "\<not> y \<le> hd x"

  show "max y (maximum (tl x)) = maximum l"
    by (metis "1" "2" "3" max.assoc max_def max_hdtl_eq)
qed

(* ******* *)
(* ******* *)
(* ******* *)

theorem "TRUE
  \<Longrightarrow>
  VARS x y l
  {x = l \<and> y = 0}
  y := 0;
  WHILE x \<noteq> []
  INV {max (maximum x) y = maximum l}
  DO
    IF y \<le> hd x THEN
      y := hd x
    ELSE
      SKIP
    FI;
    x := tl x
  OD
  {y = maximum l}"
  apply vcg_simp
  apply auto
  apply (simp_all add: l1 l2 l3)
  done

end
