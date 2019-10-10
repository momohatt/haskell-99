theory Chapter4
  imports Main
begin

(* 4.1 Isar by Example *)

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

(* 4.1.1 this, then, hence and thus *)
lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  hence "\<exists>a. {x. x \<notin> f x} = f a" by blast
  thus "False" by blast
qed

(* 4.1.2 Structured Lemma Statements: fixes, assumes, shows *)
lemma
  fixes f :: " 'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists>a. {x. x \<notin> f x} = f a" using s by (auto simp:surj_def)
  thus "False" by blast
qed

(* 4.2 Proof Patterns *)
lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp:surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

(* 4.3 Streamlining Proofs *)

lemma
  fixes a b :: int
  assumes "b dvd (a + b)"
  shows "b dvd a"
proof -
  have "\<exists>k'. a = b * k'" if asm: "a + b = b * k" for k
  proof
    show "a = b * (k - 1)" using asm by (simp add:algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add:dvd_def)
qed

(* Exercise 4.1 *)
lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
      and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
      and TA: "\<forall>x y. T x y \<longrightarrow> A x y"
      and "A x y"
    shows "T x y"
proof -
  have "T x y \<or> T y x" by (simp add:T)
  then show "T x y"
  proof
    assume asm: "T x y"
    show ?thesis using asm by assumption
  next
    assume asm: "T y x"
    have "A y x" using TA asm by auto
    hence "x = y" using `A x y` A by auto
    thus ?thesis using asm by auto
  qed
qed

(* Exercise 4.2 *)
lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume asm:"even (length xs)"
  let ?ys = "take ((length xs) div 2) xs"
  let ?zs = "drop ((length xs) div 2) xs"
  show ?thesis
  proof
    show "\<exists>zs. xs = ?ys @ zs \<and> (length ?ys = length zs \<or> length ?ys = length zs + 1)"
    proof
      have "xs = ?ys @ ?zs" using append_eq_append_conv by auto
      have "length ?ys = length ?zs" using asm by (auto simp add:algebra_simps)
      hence "xs = ?ys @ ?zs \<and> length ?ys = length ?zs" by auto
      thus "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by auto
    qed
  qed
next
  assume asm:"odd (length xs)"
  let ?ys = "take (length xs div 2 + 1) xs"
  let ?zs = "drop (length xs div 2 + 1) xs"
  show ?thesis
  proof
    show "\<exists>zs. xs = ?ys @ zs \<and> (length ?ys = length zs \<or> length ?ys = length zs + 1)"
    proof
      have "xs = ?ys @ ?zs" using append_eq_append_conv by auto
      have "length ?ys = length ?zs + 1"
      proof -
        have "length xs = 2 * (length xs div 2) + 1" using asm by fastforce
        hence 0:"length ?zs = length xs div 2" by auto

        have "\<forall>n :: nat. odd n \<longrightarrow> n \<ge> 1" using Parity.odd_pos by fastforce
        hence "length xs \<ge> 1" using asm by auto
        hence 1:"length ?ys = length xs div 2 + 1" by auto
        thus ?thesis using 0 by auto
      qed
      hence "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by auto
      thus "xs = ?ys @ ?zs \<and> (length ?ys = length ?zs \<or> length ?ys = length ?zs + 1)" by auto
    qed
  qed
qed

end