Require Export Ascii List.
Require Export Arith ZArith Lia.
Require Import ssreflect.
Export ListNotations.
Open Scope char_scope.

(** In this challenge, we assume classical logic. *)
Require Export Classical.

(** A simple formalization of (possibly infinite) sets as predicates. *)
Notation set A := (A -> Prop) (only parsing).

Definition Incl {U} (A B: set U) : Prop := forall x, A x -> B x.
Definition Union {U} (A B: set U): set U := fun x => A x \/ B x.
Definition Single {U} a : set U := fun x => x = a.
Definition Pair {U} a b : set U := fun x => x = a \/ x = b.
Definition Empty {U} := fun (x: U) => False.

Notation "A  ⊆  B" := (Incl A B) (at level 70).
Notation "A  ∪  B" := (Union A B) (at level 50).
Notation "'{ x }" := (Single x) (at level 1).
Notation "∅" := Empty.

Axiom set_ext : forall U (A B: set U), (forall x, A x <-> B x) -> A = B.

(* Simple goals involving sets can be solved by the [firstorder] tactic.
   This should be enough for our needs here. *)
Goal forall U (A B: set U) a b,
  '{a} ∪ ∅ ∪ B ∪ (A ∪ '{b} ∪ B) ⊆ Pair a b ∪ A ∪ B.
Proof. firstorder. (* boom. *) Qed.

(** Definitions on words (as lists of characters). *)

Notation word := (list ascii).

(* [#{c} w] denotes the number of times the character [c] occurs in the word [w]. *)
Notation "'#' '{' c '}'" := (fun w => count_occ ascii_dec w c) (at level 1).

Eval compute in #{"a"} ["a"; "b"; "c"]. (* there is one "a" in "abc" *)

Definition a := "a".
Definition b := "b".

(* The strict prefix relation *)
Definition prefix {A} (xs ys: list A) :=
  exists zs, ys = xs ++ zs /\ zs <> [].

Notation "xs  ≺  ys" := (prefix xs ys) (at level 50).

(* The set of letters in a word *)
Definition letters (w: word): set ascii := fun c => List.In c w.

Lemma letters_nil : letters [] = ∅.
Proof. reflexivity. Qed.
Lemma letters_cons x xs : letters (x :: xs) = '{x} ∪ letters xs.
Proof. rewrite /letters /Union /Single //=. apply set_ext. firstorder. Qed.
Lemma letters_app xs ys : letters (xs ++ ys) = letters xs ∪ letters ys.
Proof. rewrite /letters. apply set_ext. intro. rewrite in_app_iff //=. Qed.

(* Can be used by ssreflect's rewrite to rewrite with any of the lemmas in the
   tuple: use "rewrite lettersE" *)
Definition lettersE := (letters_nil, letters_cons, letters_app).

(** Problem statement *)

(* Consider the following grammar, which inductively defines a set of words: *)
Inductive L : set word :=
  | L_nil : L []
  | L_app : forall x y, L x -> L y ->
      L (x ++ y)
  | L_aab : forall x y, L x -> L y ->
      L (a :: x ++ a :: y ++ [b])
  | L_aba : forall x y, L x -> L y ->
      L (a :: x ++ b :: y ++ [a])
  | L_baa : forall x y, L x -> L y ->
      L (b :: x ++ a :: y ++ [a]).

(* We want to prove that the grammar exactly produces the language of all words
   that contain twice as many a's than b's: *)

Definition M : set word :=
  fun w => letters w ⊆ Pair a b /\ #{a} w = 2 * #{b} w.

Goal L = M.
Abort.

(* The height function. w is in M iff h(w) = 0. *)
Definition h (w: word): Z :=
  2 * Z.of_nat (#{b} w) - Z.of_nat (#{a} w).
