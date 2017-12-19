(* Practice of Natural Deduction *)
(* http://rainyday.blog.so-net.ne.jp/2017-09-24 *)

theory NaturalDeduction
  imports Main
begin

theorem Example_1_4:
  (*fixes P Q*)
  assumes 1: "P \<and> Q"
  assumes 2: "R"
  shows "Q \<and> R"
proof -
  have 3: "Q" using 1 by (rule conjunct2)
  show 4: "Q \<and> R" using 3 2 by (rule conjI)
qed

find_theorems "\<not>\<not> _ \<Longrightarrow> _"              (* notnotD *)
theorem notnotI: "P \<Longrightarrow> \<not>\<not> P" by auto

theorem Example_1_5:
  assumes 1: "P"
  assumes 2: "\<not>\<not> (Q \<and> R)"
  shows "\<not>\<not> P \<and> R"
proof -
  have 3: "\<not>\<not> P" using 1 by (rule notnotI)
  have 4: "Q \<and> R" using 2 by (rule notnotD)
  have 5: "R" using 4 by (rule conjunct2)
  show 6: "\<not>\<not> P \<and> R" using 3 5 by (rule conjI)
qed

theorem  mp: "(P\<Longrightarrow>Q) \<Longrightarrow> P \<Longrightarrow> Q" by auto
theorem  mt: "(P\<Longrightarrow>Q) \<Longrightarrow> \<not> Q \<Longrightarrow> \<not> P" by auto

theorem Example_1_7:
  assumes 1: "P \<Longrightarrow> (Q \<Longrightarrow> R)"
  assumes 2: "P"
  assumes 3: "\<not> R"
  shows "\<not> Q"
proof -
  have 4: "Q \<Longrightarrow> R" using 1 2 by (rule mp)
  show 5: "\<not> Q" using 4 3 by (rule mt)
qed

theorem Example_1_9:
  assumes 1: "\<not> Q \<Longrightarrow> \<not> P"
  shows "P \<Longrightarrow> \<not>\<not> Q"
proof -
  assume 2: "P"
  have 3: "\<not>\<not> P" using 2 by (rule notnotI)
  show 4: "\<not>\<not> Q" using 1 3 by (rule mt)
qed

theorem Example_1_11:
  shows "(Q \<Longrightarrow> R) \<Longrightarrow> (( \<not> Q \<Longrightarrow> \<not> P) \<Longrightarrow> (P \<Longrightarrow> R))"
proof -
  assume 1: "Q \<Longrightarrow> R"
  show "(\<not> Q \<Longrightarrow> \<not> P) \<Longrightarrow> (P \<Longrightarrow> R)"
  proof -
    assume 2: "\<not> Q \<Longrightarrow> \<not> P"
    show "P \<Longrightarrow> R"
    proof -
      assume 3: "P"
      have 4: "\<not>\<not> P" using 3 by (rule notnotI)
      have 5: "\<not>\<not> Q" using 2 4 by (rule mt)
      have 6: "Q" using 5 by (rule notnotD)
      show 7: "R" using 1 6 by (rule mp)
    qed
  qed
qed

theorem Example_1_11':
  shows "(Q \<Longrightarrow> R) \<Longrightarrow> ((\<not> Q \<Longrightarrow> \<not> P) \<Longrightarrow> (P \<Longrightarrow> R))"
proof-
  assume 1: "Q \<Longrightarrow> R"
  assume 2: "\<not> Q \<Longrightarrow> \<not> P"
  assume 3: "P"
  have 4: "\<not>\<not> P" using 3 by (rule notnotI)
  have 5: "\<not>\<not> Q" using 2 4 by (rule mt)
  have 6: "Q" using 5 by (rule notnotD)
  show 7: "R" using 1 6 by (rule mp)
qed

find_theorems "_ \<Longrightarrow> _ \<or> _"  (* disjI1 , disjI2 *)
theorem disjE: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R" by auto

theorem Example_1_16:
  assumes 1: "Q \<Longrightarrow> R"
  shows "P \<or> Q \<Longrightarrow> P \<or> R"
proof -
  assume 2: "P \<or> Q"
  show "P \<or> R"
  proof -
    have 34: "P \<Longrightarrow> P \<or> R"
    proof -
      assume 3: "P"
      show 4: "P \<or> R" using 3 by (rule disjI1)
    qed
    have 57: "Q \<Longrightarrow> P \<or> R"
    proof -
      assume 5: "Q"
      have 6: "R" using 1 5 by (rule mp)
      show 7: "P \<or> R" using 6 by (rule disjI2)
    qed
    show "P \<or> R" using 2 34 57 by (rule disjE)
  qed
qed

theorem Example_copy:
  shows "P \<Longrightarrow> (Q \<Longrightarrow> P)"
proof -
  assume 1: "P"
  show "Q \<Longrightarrow> P"
  proof -
    assume 2: "Q"
    show 3: "P" using 1 by assumption
  qed
qed

theorem Example_1_21:
  assumes 1: "P \<Longrightarrow> Q"
  assumes 2: "P \<Longrightarrow> \<not>Q"
  shows "\<not> P"
proof -
  have 36: "P \<Longrightarrow> False"
  proof -
    assume 3: "P"
    have 4: "Q" using 1 3 by (rule mp)
    have 5: "\<not> Q" using 2 3 by (rule mp)
    show 6: "False" using 5 4 by (rule notE)
  qed
  show "\<not> P" using 36 by (rule notI)
qed

end
