theory Chapter2_MyList
  imports Main
begin

(* Contains original definition of nat and list *)

datatype bool = True | False

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conj True True = True"
| "conj _ _ = False"

datatype nat = O | Suc nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add nat.O n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m nat.O = m"
  apply (induction m)
  apply (auto)
  done

(* List *)
datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  apply (auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply (auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply (auto)
  done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply (induction xs)
  apply (auto)
  done

(* Exercise 2.2 *)
theorem add_assoc [simp]: "add n (add m l) = add (add n m) l"
  apply (induction n)
  apply (auto)
  done

lemma add_comm' [simp]: "add n (Suc m) = Suc (add n m)"
  apply (induction n)
   apply (auto)
  done

theorem add_comm [simp]: "add n m = add m n"
  apply (induction m)
   apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
  "double nat.O = nat.O"
| "double (Suc n) = Suc (Suc (double n))"

theorem double_add_twice[simp]: "double n = add n n"
  apply (induction n)
   apply (auto)
  done


(* Exercise 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd nat.O m = m"
| "itadd (Suc n) m = itadd n (Suc m)"

theorem itadd_add : "itadd n m = add n m"
  apply (induction n arbitrary:m)
   apply (auto)
  done

end