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

(* 4.4 Case Analysis and Induction *)
(* 4.4.1 Datatype Case Analysis *)

lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  (* Note that by definition, "tl [] = []" *)
  case Nil (* assume "xs = []" *)
  thus ?thesis by simp
next
  case (Cons y ys) (* fix y ys assume xs = y # ys *)
  thus ?thesis by simp
qed

(* 4.4.2 Structural Induction *)
lemma "\<Sum>{0..n::nat} = n * (n + 1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P (Suc n)" by simp
qed

lemma "\<Sum>{0..n::nat} = n * (n + 1) div 2" (is "?P n")
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n) (* sets induction hypothesis to 'this' *)
  thus ?case by simp
qed

(* 4.4.3 Computation Induction *)
(* In computation induction (with induction rule defined by 'fun'),
   we can specify case names like 'case (i x y ...)' where 'i' is
   an index starting from 1 and x, y, ... are bound variables *)

(* 4.4.4 Rule Induction *)
inductive ev :: "nat \<Rightarrow> bool" where
  ev0 : "ev 0"
| evSS : "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc(Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule:ev.induct)
  case ev0
  show ?case by simp
next
  case (evSS n)
  have "evn (Suc (Suc n)) = evn n" by simp
  thus ?case using `evn n` by blast
qed

(* 4.4.6 Rule Inversion *)
lemma
  assumes "ev n"
  shows "ev (n - 2)"
  using assms
proof cases
  case ev0
  thus "ev(n - 2)" by (simp add: ev.ev0)
next
  case evSS
  thus "ev (n - 2)" by (simp add: ev.evSS)
qed

lemma "\<not> ev (Suc 0)"
proof
  assume "ev (Suc 0)"
  then show False by cases
qed

(* 4.4.7 Advanced Rule Induction *)
lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary:m rule:ev.induct)
  fix n assume IH: "\<And> m. n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev (Suc n)"
  proof
    assume "ev (Suc n)"
    thus False
    proof cases
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

(* Exercise 4.3 *)
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
  using a
proof cases
  case evSS
  show "ev n \<Longrightarrow> ev n" by (simp add: ev.ev0)
qed

(* Exercise 4.4 *)
lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  then have "ev (Suc 0)" by cases
  thus False by cases
qed

(* Exercise 4.5 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter_zero: "iter r 0 x x"
| iter_succ: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule:iter.induct)
  case iter_zero
  thus ?case by (auto simp add:refl)
next
  case iter_succ
  thus ?case by (auto simp add:step)
qed

(* Exercise 4.6 *)
fun elems :: "'a list \<Rightarrow> 'a set" where
  elems_Nil:  "elems [] = {}"
| elems_Cons: "elems (x#xs) = insert x (elems xs)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" (is "?P(x,xs) \<Longrightarrow> ?Q(x,xs)")
proof (induction xs)
  case Nil
  hence False by auto
  thus ?case by auto
next
  case (Cons x' xs)
  hence "x = x' \<or> (x \<noteq> x' \<and> x \<in> elems xs)" by auto
  then show ?case
  proof
    assume H:"x = x'"
    show ?case
    proof
      show "\<exists> zs. x' # xs = [] @ x # zs \<and> x \<notin> elems []"
      proof
        show "x' # xs = [] @ x # xs \<and> x \<notin> elems []" using H by auto
      qed
    qed
  next
    assume H:"(x \<noteq> x' \<and> x \<in> elems xs)"
    from this obtain ys where "\<exists>zs. xs = ys @ x # zs \<and> x \<notin> elems ys" using Cons.IH by auto
    from this obtain zs where H1: "xs = ys @ x # zs \<and> x \<notin> elems ys" by auto
    show ?case
    proof
      show "\<exists> zs. x' # xs = (x' # ys) @ x # zs \<and> x \<notin> elems (x' # ys)"
      proof
        show "x' # xs = (x' # ys) @ x # zs \<and> x \<notin> elems (x' # ys)" using H H1 by auto
      qed
    qed
  qed
qed

(* Exercise 4.7 *)

end