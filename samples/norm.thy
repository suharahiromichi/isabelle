theory "norm" imports Main begin

(* 
 * L1 norm
 * The sum of absolute values of each component. 
 *)    
fun L1_norm :: "int*int\<Rightarrow>int" where
  "L1_norm (z1, z2) = abs z1 + abs z2"

(* Prove that L1 is nonnegative. *)
theorem L1_norm_is_non_negative : "L1_norm zz \<ge> 0"
  apply (cases zz)
  by simp

theorem L1_norm_is_non_negative' : "L1_norm zz \<ge> 0"
  by (smt L1_norm.elims)    (* Sledgehammer *)

theorem L1_norm_is_non_negative'' :
  fixes "zz" :: "int*int"
  shows "0 \<le> L1_norm zz"
proof (cases zz)  (* \<And>a b. zz = (a, b) \<Longrightarrow> 0 \<le> L1_norm zz *)
  fix a b
  assume H : "zz = (a, b)"
  have "0 \<le> L1_norm (a, b)" by simp
  thus "0 \<le> L1_norm zz" using H by simp  (* thus = from this show *) 
qed

end
