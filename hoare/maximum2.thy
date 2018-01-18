theory maximum2
  imports "~~/src/HOL/Hoare/Hoare_Logic"
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
  apply auto
  by (simp add: maximum_def)

(* ********* *)
(* * lemma * *)
(* ********* *)

(* 3 subgoals, 1., 2., 3. *)
(* 1. *)
lemma l1 : "max (maximum x) y = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> y \<le> hd x \<Longrightarrow> max (maximum (tl x)) (hd x) = maximum l"
  by (metis max.assoc max.commute max_def max_hdtl_eq) (* Sledgehammer *)

(* 2. *)
lemma l2 : "max (maximum x) y = maximum l \<Longrightarrow>
       x \<noteq> [] \<Longrightarrow> \<not> y \<le> hd x \<Longrightarrow> max (maximum (tl x)) y = maximum l"
  by (metis max.assoc max.commute max_def max_hdtl_eq) (* Sledgehammer *)

(* 3. *)
lemma l3 : "max (maximum []) y = maximum l \<Longrightarrow> y = maximum l"
  by (simp add: maximum_def) (* Sledgehammer *)

(* ******** *)
(* * main * *)
(* ******** *)

theorem "VARS x y l
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
  (* 3 subgoals, 1., 2., 3. *)
  by (simp_all add: l1 l2 l3) 

end

(* END *)