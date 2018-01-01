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

lemma max_hdtl_eq [simp] : "l \<noteq> [] \<Longrightarrow> max (hd l) (maximum (tl l)) = maximum l"
  apply (induct l)
  apply (auto)
  apply (simp add: hd_def tl_def maximum_def)
  done

(* ******* *)
(* ******* *)
(* ******* *)

lemma l1 : "max (maximum x) y = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> y \<le> hd x \<Longrightarrow> max (maximum (tl x)) (hd x) = maximum l"
  by (metis max.assoc max.commute max_def max_hdtl_eq)
(*
proof -
  fix x y l
  assume 1 : "max (maximum x) y = maximum l" and
    2 : "x \<noteq> []" and
    3 : "y \<le> hd x"
  show "max (maximum (tl x)) (hd x) = maximum l"
    by (metis "1" "2" "3" max.assoc max.commute max_def max_hdtl_eq)
qed
*)

lemma l2 : "max (maximum x) y = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> \<not> y \<le> hd x \<Longrightarrow> max (maximum (tl x)) y = maximum l"
  by (metis max.assoc max.commute max_def max_hdtl_eq)
(*
proof -
  fix x y l
  assume 1 : "max (maximum x) y = maximum l" and
    2 : "x \<noteq> []" and
    3 : "\<not> y \<le> hd x"
  show "max (maximum (tl x)) y = maximum l"
    by (metis "1" "2" "3" max.assoc max.commute max_def max_hdtl_eq)
qed
*)

lemma l3 : "max (maximum []) y = maximum l \<Longrightarrow> y = maximum l"
  by (simp add: maximum_def) 
(*
proof -
  fix y l
  assume "max (maximum []) y = maximum l"
  thus "y = maximum l" using maximum_def by auto
qed
*)

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
  apply vcg
  apply auto
  apply (simp_all add: l1 l2 l3) 
  done

end

(* END *)