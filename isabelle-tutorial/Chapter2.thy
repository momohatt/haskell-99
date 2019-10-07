theory Chapter2
  imports Complex_Main
begin

(* Exercise 2.1 *)
value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"

(* Exercise 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x Nil = 0"
| "count x (Cons y ys) = (if x = y then 1 + count x ys else count x ys)" 

theorem count_le_len [simp]: "count x xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

(* Exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = (Cons x Nil)"
| "snoc (Cons y ys) x = (Cons y (snoc ys x))"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil"
| "reverse (Cons x xs) = (snoc (reverse xs) x)"

lemma reverse_cons [simp]: "reverse (snoc xs a) = Cons a (reverse xs)"
  apply (induction xs)
   apply (auto)
  done

theorem reverse_reverse [simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto)
  done

(* Exercise 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto n = (if n = 0 then 0 else n + (sum_upto (n - 1)))"

theorem sum_upto_n [simp]: "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply (auto)
  done

(*********************************)

datatype 'a tree = Tip | Node "'a tree" 'a " 'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
  apply (induction t)
   apply (auto)
  done

datatype 'a option = None | Some 'a

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup [] x = None"
| "lookup ((a, b) # ps) x = (if a = x then Some b else lookup ps x)"

(* Exercise 2.6 *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = (contents l @ a # contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l a r) = (sum_tree l + a + sum_tree r)"

fun sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list [] = 0"
| "sum_list (x # xs) = x + sum_list xs"

lemma sum_list_app [simp]: "sum_list (xs @ ys) = sum_list xs + sum_list ys"
  apply (induction xs)
   apply (auto)
  done

theorem sum_tree_correct : "sum_tree t = sum_list (contents t)"
  apply (induction t)
   apply (auto)
  done

(* Exercise 2.7 *)
datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Tip x) = (Tip x)"
| "mirror2 (Node l a r) = Node (mirror2 r) a (mirror2 l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip x) = [x]"
| "pre_order (Node l x r) = x # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip x) = [x]"
| "post_order (Node l x r) = (post_order l) @ (post_order r) @ [x]"

theorem tree_traversal : "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t)
   apply (auto)
  done

(* Exercise 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []"
| "intersperse a (x # xs) = (x # a # intersperse a xs)"

theorem intersperse_map : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
   apply (auto)
  done

(****************************************)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary:ys)
   apply (auto)
  done

(* Exercise 2.10 *)
datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Leaf = 1"
| "nodes (Node t1 t2) = 1 + nodes t1 + nodes t2"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"
| "explode (Suc n) t = explode n (Node t t)"

theorem explode_node : "nodes (explode n t) = 2^n * (nodes t + 1) - 1"
  apply (induction n arbitrary:t)
   apply (auto)
  apply (simp add:algebra_simps)
  done

(* Exercise 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x"
| "eval (Const n) _ = n"
| "eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)"
| "eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] x = 0"
| "evalp (c#cs) x = c + x * (evalp cs x)"

fun list_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "list_add [] ys = ys"
| "list_add xs [] = xs"
| "list_add (x#xs) (y#ys) = (x + y) # (list_add xs ys)"

fun list_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "list_mult [] _ = []"
| "list_mult _ [] = []"
| "list_mult (x#xs) ys = list_add (map (\<lambda>n. n * x) ys) (list_mult xs (0 # ys))"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"
| "coeffs (Const n) = [n]"
| "coeffs (Add e1 e2) = list_add (coeffs e1) (coeffs e2)"
| "coeffs (Mult e1 e2) = list_mult (coeffs e1) (coeffs e2)"

lemma evalp_add_distr [simp]: "evalp (list_add l1 l2) x = evalp l1 x + evalp l2 x"
  apply (induction rule:list_add.induct)
   apply (auto simp add:algebra_simps)
  done

lemma evalp_map : "evalp (map (\<lambda>n. n * a) l) x = a * evalp l x"
  apply (induction l)
   apply (auto simp add:algebra_simps)
  done

lemma evalp_mult_distr : "evalp (list_mult l1 l2) x = evalp l1 x * evalp l2 x"
  apply (induction rule:list_mult.induct)
  apply (auto)
  apply (simp add:evalp_map)
  apply (simp add:algebra_simps)
  done

theorem coeffs_preserve : "evalp (coeffs e) x = eval e x"
  apply (induction e)
   apply (auto)
   apply (simp add:evalp_add_distr)
   apply (simp add:evalp_mult_distr)
  done

end