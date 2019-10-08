theory Chapter3
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}"
| "set (Node t1 a t2) = set t1 \<union> {a} \<union> set t2"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True"
| "ord (Node t1 a t2) = (ord t1 \<and> ord t2 \<and> (\<forall>x. x \<in> set t1 \<longrightarrow> x < a) \<and> (\<forall>x. x \<in> set t2 \<longrightarrow> a \<le> x))"
(* parentheses are necessary around (\<forall>x. ...)*)

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins x Tip = Node Tip x Tip"
| "ins x (Node t1 a t2) = (if x < a then Node (ins x t1) a t2 else Node t1 a (ins x t2))"

theorem ins_correct_1 : "set (ins x t) = {x} \<union> set t"
  apply (induction t)
   apply (auto)
  done

theorem ins_correct_2 : "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t)
   apply (auto simp add:ins_correct_1)
  done

(*** 3.3 Proof Automation ***)
lemma "\<forall>x. \<exists>y. x = y" by auto
lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C" by auto

(* fastforce can handle quantifiers *)
lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n + n" by fastforce

(* blast is strong in first-order logic, sets and relations, but weak in equality *)
lemma "\<lbrakk> \<forall> x y. T x y \<or> T y x;
         \<forall> x y. A x y \<and> A y x \<longrightarrow> x = y;
         \<forall> x y. T x y \<longrightarrow> A x y \<rbrakk> \<Longrightarrow> \<forall> x y. A x y \<longrightarrow> T x y" by blast

(* sledgehammer *)
lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  using append_eq_append_conv by blast

(* arith *)
lemma "\<lbrakk> (a :: nat) \<le> x + b; 2 * x < c \<rbrakk> \<Longrightarrow> 2 * a + 1 \<le> 2 * b + c"
  by arith

(* 3.4 Single Step Proofs *)
lemma "\<lbrakk> (a :: nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by (auto intro:le_trans)

thm conjI[OF refl[of "a"] refl[of "b"]] (* a = a \<and> b = b *)

lemma "Suc(Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b" by (auto dest:Suc_leD)

(* 3.5 Inductive Deifnitions *)
inductive ev :: "nat \<Rightarrow> bool" where
  ev0 : "ev 0"
| evSS : "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc(Suc n)) = evn n"

lemma "ev(Suc(Suc(Suc(Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma "ev m \<Longrightarrow> ev (m - 2)"
  apply (induction rule:ev.induct)
  by (simp_all add:ev0 evSS)

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule:ev.induct)
  by (simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule:evn.induct)
  by (simp_all add:ev0 evSS)

(* makes ev a simplification and introduction rule permanently *)
declare ev.intros[simp,intro]

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x"
| step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct) (* induction over star r x y (first matching assumption) *)
   apply (assumption)
  apply (metis step)
  done

(* Exercise 3.2 *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
  pEmpty: "palindrome []"
| pSingle: "palindrome [x]"
| pStep: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

theorem palindrome_spec : "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule:palindrome.induct)
    apply (auto)
  done

(* Exercise 3.3 *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x"
| step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

theorem star'_is_star : "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule:star'.induct)
   apply (auto simp add:refl step star_trans)
  done

lemma star'_trans' : "star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z"
  apply (induction rule:star'.induct)
   apply (assumption)
  apply (simp add:step')
  done

theorem star_is_star' : "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule:star.induct)
   apply (simp add:refl' step')
  apply (blast intro:refl' step' star'_trans')
  done

(* Exercise 3.4 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter_zero: "iter r 0 x x"
| iter_succ: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

theorem star_iter : "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply (induction rule:star.induct)
  apply (rule exI[of _ 0]) 
   apply (auto simp add:iter_zero iter_succ)
  apply (rule_tac x="Suc n" in exI)
  apply (auto simp add:iter_zero iter_succ)
  done

(* Exercise 3.5 *)
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  S_0: "S []"
| S_1: "S w \<Longrightarrow> S (a # w @ [b])"
| S_2: "S w \<Longrightarrow> S w' \<Longrightarrow> S (w @ w')"

inductive T :: "alpha list \<Rightarrow> bool" where
  T_0: "T []"
| T_1: "T w \<Longrightarrow> T w' \<Longrightarrow> T (w @ a # w' @ [b])"

lemma S_includes_T : "T w \<Longrightarrow> S w"
  apply (induction rule:T.induct)
   apply (auto simp add:S_0 S_1 S_2)
  done

lemma append_Nil_r : "l = [] @ l"
  apply (induction l)
   apply (auto)
  done

(* I'm not happy with having to prepare these lemmas... *)
lemma T_complies_S_1' : "T w \<Longrightarrow> T ([] @ a # w @ [b])"
  apply (rule T_1)
   apply (auto simp add:T_0)
  done

lemma T_complies_S_1'' : "T ([] @ a # w @ [b]) \<Longrightarrow> T(a # w @ [b])"
  apply (auto)
  done

lemma T_complies_S_1 : "T w \<Longrightarrow> T (a # w @ [b])"
  apply (rule T_complies_S_1'')
  apply (rule T_complies_S_1')
  apply (auto)
  done

lemma T_complies_S_2 : "S w' \<Longrightarrow> T w' \<Longrightarrow> T w \<Longrightarrow> T (w @ w')"
  apply (induction rule:S.induct)
    apply (auto)



lemma T_includes_S : "S w \<Longrightarrow> T w"
  apply (induction rule:S.induct)
    apply (rule T_0)
   apply (auto simp add:T_complies_S_1)

end