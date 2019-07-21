Require Import Defs.

(* It is not required, but it is a good idea to import ssreflect to benefit
   from the better rewrite tactic. (by uncommenting the two lines below)

   ssreflect's rewrite cheatsheet: a rewrite invocation is of the form [rewrite foo bar baz],
   where each of "foo", "bar", "baz" can be:
   - "foo" where foo is a lemma: rewrites with the lemma ("-foo" rewrites in the other direction)
   - "!foo" where foo is a lemma: rewrites repeatedly with foo
   - "/foo" where foo is a definition: unfolds the definition ("-/foo" folds the definition)
   - "//": try to prove the goal or side-condition if it is trivial
   - "//=": like "//" but also simplify the goal (using "simp")
   - "(_: foo = bar)": ask the user to prove "foo = bar" as a subgoal, and rewrite with it
*)

Require Import ssreflect ssrbool.
Ltac done ::= first [ solve [ trivial | auto | lia ] ].

(** Part 1 -- properties of XOR *)

(* a few useful lemmas: *)
Lemma xor_shuffle a b c : xor a b = c <-> xor a c = b.
Proof.
  split.
  - destruct a; destruct b; simpl; intros; subst; auto.
  - destruct a; destruct c; simpl; intros; subst; auto.
Qed.

Check bubble_foldr_xor.
(* forall (f : output) (xs : list nat) (y z : bool),
     xor (fold_right (fun (x : nat) (n : bool) => xor n (f x)) y xs) z =
     fold_right (fun (x : nat) (n : bool) => xor n (f x)) (xor y z) xs *)

Check seq_length_S.
(* forall start len : nat,
     seq start (S len) = seq start len ++ [start + len]
*)

Check interval_app.
(* forall x y z : nat,
     x <= y -> y <= z ->
     [x..<y] ++ [y..<z] = [x..<z]
*)

Lemma XOR_interval x y f:
  x <= y ->
  xor (XOR 0 x f) (XOR 0 y f) = XOR x y f.
Proof.
  intros.
  apply xor_shuffle.
  rewrite bubble_foldr_xor.
  simpl.
  unfold XOR.
  rewrite <- fold_right_app.
  replace (seq 0 (x - 0) ++ seq x (y - x)) with (seq 0 (y - 0)).
  done.

  rewrite interval_app; done.
Qed.

(** Part 2: number_of_true_between reduction to XOR *)

Lemma filter_app :
  forall A (f : A -> bool) l l',
  filter f (l ++ l') = filter f l ++ filter f l'.
Proof.
  intros.
  induction l.
  - simpl. done.
  - simpl. destruct (f a).
    + rewrite <- app_comm_cons.
      rewrite <- IHl. done.
    + done.
Qed.

Lemma XOR_odd_odd x y f: XOR x y f = Nat.odd (number_of_true_between x y f).
Proof.
  destruct (x <=? y) eqn:H.
  * set (n := y - x).
    unfold number_of_true_between.
    replace y with (x + n).
    replace (x + n - x) with n by lia.
    induction n.
    - replace (x + 0) with x by lia.
      rewrite XOR_same.
      auto.
    - replace (x + S n) with (S (x + n)) by lia.
      rewrite XOR_cons; try lia.
      rewrite IHn.
      rewrite seq_length_S.
      rewrite filter_app; simpl.
      rewrite app_length; simpl.
      destruct (f (x + n)).
      + rewrite xor_true_l.
        rewrite Nat.odd_add.
        rewrite Nat.odd_1.
        rewrite Bool.xorb_true_r.
        done.
      + simpl.
        rewrite xor_false_r.
        rewrite plus_0_r.
        done.
    - unfold n.
      symmetry.
      apply le_plus_minus.
      apply leb_complete in H.
      auto.
  * apply leb_complete_conv in H.
    unfold XOR, number_of_true_between.
    replace (y - x) with 0 by lia.
    auto.
Qed.

Lemma reduction (t: task) (i: input) (o: output):
  correct_solution_XOR t i o ->
  correct_solution t i o.
Proof.
  unfold correct_solution_XOR, correct_solution.
  intros.
  rewrite <- XOR_odd_odd.
  auto.
Qed.

(** Part 3 -- Implementation time! *)

Theorem goal :
  exists (prog: task -> list Com),
    (* functional correctness *)
    (forall (t: task) (s0: state) (i: input),
      correct_solution t i (out (execs i s0 (prog t))))
    /\
    (* complexity: linear in the size of the task *)
    (exists (n0 c: nat), forall t, n0 <= size t -> length (prog t) <= c * (size t)).
Proof.
  (* todo *)
Admitted.
