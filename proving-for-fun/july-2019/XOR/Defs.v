Require Export Arith Lia.
Require Import ssreflect ssrbool.
Require Export List.
Export ListNotations.

(*** xor *)

Definition xor (x y: bool): bool :=
  match x with
  | true => negb y
  | false => y
  end.

Lemma xor_com x y : xor x y = xor y x.
Proof. destruct x; destruct y; reflexivity. Qed.

Lemma xor_assoc x y z : xor x (xor y z) = xor (xor x y) z.
Proof. destruct x; destruct y; destruct z; reflexivity. Qed.

Lemma xor_same x : xor x x = false.
Proof. destruct x; reflexivity. Qed.

Lemma xor_false_r x : xor x false = x.
Proof. destruct x; reflexivity. Qed.
Lemma xor_false_l x : xor false x = x.
Proof. destruct x; reflexivity. Qed.
Lemma xor_true_l x : xor x true = negb x.
Proof. reflexivity. Qed.
Lemma xor_true_r x : xor true x = negb x.
Proof. reflexivity. Qed.

(* Can be used by ssreflect's rewrite to rewrite with any of the lemmas in the
   tuple: use "rewrite xorE" *)
Definition xorE := (xor_same, xor_false_r, xor_false_l, xor_true_l, xor_true_r).

(*** XOR: iterated xor *)

(* The list of natural numbers from i (included) to j (excluded) *)
Notation "'[' i '..<' j ']'" := (seq i (j-i)) (only parsing).

(* Useful lemma when reasoning by induction on [i..<j], ie on (j-i). *)
Lemma seq_length_S start len : seq start (S len) = seq start len ++ [start+len].
Proof.
  revert start. induction len; intros start.
  - rewrite //= Nat.add_0_r //.
  - rewrite //=. f_equal.
    rewrite -{1}seq_shift -map_cons. cbn [seq] in IHlen.
    rewrite IHlen map_app //= Nat.add_succ_r -seq_shift //.
Qed.

Lemma interval_app x y z:
  x <= y -> y <= z ->
  [x..<y] ++ [y..<z] = [x..<z].
Proof.
  intros Hxy Hyz.
  set n := z - y. rewrite (_:z = y+n) //.
  unfold n. rewrite le_plus_minus_r; lia.
  induction n.
  - rewrite //= app_nil_r Nat.add_0_r //.
  - rewrite (_:y + S n - x = S(y+n-x)) //. lia.
    rewrite !seq_length_S app_assoc IHn //=.
    rewrite (_: x + (y + n - x) = y + n) //=. lia.
Qed.

Definition XOR i j f :=
  fold_right (fun x n => xor n (f x)) false [i..<j].

Lemma bubble_foldr_xor (f: nat -> bool) xs y z :
  xor (fold_right (fun x n => xor n (f x)) y xs) z =
  fold_right (fun x n => xor n (f x)) (xor y z) xs.
Proof.
  revert y z. induction xs. reflexivity.
  intros y z. rewrite //= -IHxs -!xor_assoc (xor_com z) //.
Qed.

Lemma XOR_same x i : XOR x x i = false.
Proof. rewrite /XOR Nat.sub_diag /seq //. Qed.

Lemma XOR_cons x y f :
  x <= y ->
  XOR x (S y) f = xor (XOR x y f) (f y).
Proof.
  intro. rewrite /XOR. rewrite Nat.sub_succ_l //.
  rewrite seq_length_S fold_right_app //= -le_plus_minus //.
  rewrite bubble_foldr_xor xorE //=.
Qed.

(* Helpers to work on sequences represented as functions (nat -> A) *)

Definition update {A} (seq: nat -> A) (k: nat) (v: A): nat -> A :=
  fun n => if Nat.eq_dec k n then v else seq n.

Notation "f '{' k := v '}'" := (update f k v) (at level 0).

Lemma update_read_neq A (seq: nat -> A) k k' v :
  k <> k' ->
  seq {k:=v} k' = seq k'.
Proof.
  intros Hk. rewrite /update. destruct (Nat.eq_dec k k'); cbn.
  now exfalso; auto. auto.
Qed.

Lemma update_read_eq A (seq: nat -> A) k k' v :
  k = k' ->
  seq {k:=v} k' = v.
Proof.
  intros Hk. rewrite /update. destruct (Nat.eq_dec k k'); cbn.
  auto. now exfalso; auto.
Qed.

(*** Computational model *)

(* input sequence: nth number is odd iff (i n) is true *)
Notation input := (nat -> bool) (only parsing).

(* output sequence (is part of the state defined below) *)
Notation output := (nat -> bool) (only parsing).

Record state := State {
  (* Temporary memory that can be read/written by the program *)
  tmp : nat -> bool;

  (* Registers: can be xor'd together, or loaded with data from the input or
  temporary memory *)
  regA : bool;
  regB : bool;

  (* Output, is written by the program *)
  out : output;
}.

(* Program instructions *)
Variant Com :=
  | LoadIA of nat
  | LoadIB of nat
  | Xor
  | StoreTmp of nat
  | StoreFinal of nat
  | LoadTA of nat
  | LoadTB of nat.

(* Semantics of program instructions *)

Definition exec (i: input) (s: state) (c: Com): state :=
  match c with
  | LoadIA n =>
    (* LoadIA n : A <- i(n) *)
    {| tmp := tmp s; regA := i n; regB := regB s; out := out s |}
  | LoadIB n =>
    (* LoadIB n : B <- i(n) *)
    {| tmp := tmp s; regA := regA s; regB := i n; out := out s |}
  | LoadTA n =>
    (* LoadTA n : A <- tmp(n) *)
    {| tmp := tmp s; regA := tmp s n; regB := regB s; out := out s |}
  | LoadTB n =>
    (* LoadTB n : B <- tmp(n) *)
    {| tmp := tmp s; regA := regA s; regB := tmp s n; out := out s |}
  | Xor =>
    (* Xor : A <- xor A B *)
    {| tmp := tmp s; regA := xor (regA s) (regB s); regB := regB s; out := out s |}
  | StoreTmp n =>
    (* StoreTmp n : tmp(n) <- A *)
    {| tmp := (tmp s){n := regA s}; regA := regA s; regB := regB s; out := out s |}
  | StoreFinal n =>
    (* StoreFinal n : out(n) <- A *)
    {| tmp := tmp s; regA := regA s; regB := regB s; out := (out s){n := regA s} |}
  end.

Definition execs (i: input) (s: state) (cs: list Com): state :=
  fold_left (exec i) cs s.

Lemma execs_app i s cs cs' : execs i s (cs ++ cs') = execs i (execs i s cs) cs'.
Proof. rewrite /execs fold_left_app //=. Qed.


(** Definitions for the correctness statement *)

(* A given program solves a specific task *)

Record task := Task {
  (* the size of the relevant input prefix *)
  size : nat;
  (* start indices *)
  si : nat -> nat;
  (* end indices *)
  ei : nat -> nat;

  (* start and end indices are valid: they fall below the size *)
  si_lt_ei : forall n, n < size -> si n < ei n;
  ei_inbound : forall n, n < size -> ei n < size;
}.

Definition number_of_true_between x y i :=
  length (filter i [x..<y]).

Definition correct_solution (t: task) (i: input) (o: output) :=
  forall x, x < size t ->
  o x = Nat.odd (number_of_true_between (si t x) (ei t x) i).

Definition correct_solution_XOR (t: task) (i: input) (o: output) :=
  forall x, x < size t ->
  o x = XOR (si t x) (ei t x) i.
