Require Import Defs.
Require Import Coq.ZArith.Znat.

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
(*
Require Import ssreflect.
Local Ltac done ::= first [ solve [ trivial | eauto | lia ] ].
*)

(* Prevent simpl/cbn from unfolding the multiplication, which is never a good
   idea. *)
Arguments Nat.mul : simpl never.
Arguments Z.mul : simpl never.


(** First task *)

Lemma count_occ_app A dec l l' (x : A) :
  count_occ dec (l ++ l') x = count_occ dec l x + count_occ dec l' x.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    destruct (dec a x).
    + simpl. rewrite <- IHl. auto.
    + auto.
Qed.

Lemma Empty_Incl U (u : set U) :
  Incl Empty u.
Proof.
  unfold Incl, Empty. intros. inversion H.
Qed.

Lemma Union_Incl U (u1 u2 u3 : set U) :
  Incl u1 u3 -> Incl u2 u3 -> Incl (Union u1 u2) u3.
Proof.
  unfold Incl, Union.
  intros. destruct H1; auto.
Qed.

Lemma Pair_Incl_l U (a b : U) :
  Incl '{a} (Pair a b).
Proof. unfold Incl, Pair. auto. Qed.

Lemma Pair_Incl_r U (a b : U) :
  Incl '{b} (Pair a b).
Proof. unfold Incl, Pair. auto. Qed.

Hint Resolve Empty_Incl Union_Incl Pair_Incl_l Pair_Incl_r.

Ltac solve1 :=
  repeat (first [ rewrite letters_nil
                | rewrite letters_cons
                | rewrite letters_app]; auto);
  repeat (try apply Union_Incl; auto).

Ltac solve2 :=
  repeat (simpl; rewrite count_occ_app; rewrite count_occ_app);
  simpl; lia.

Theorem L_sub : L ⊆ M.
Proof.
  unfold Incl, M.
  intros.
  induction H;
    try (unfold Incl in IHL1, IHL2; destruct IHL1; destruct IHL2);
    split; try solve1; try solve2.
Qed.


(** Second task *)

Definition h' (a : ascii) : Z :=
  h (a :: nil).

(*
Lemma h_cons x xs :
  h (x :: xs) = (h' x + h xs)%Z.
Proof.
  destruct (ascii_dec x b); subst.
  - destruct (ascii_dec b a).
    + inversion e.
    + unfold h at q.
*)

Lemma h_app xs ys :
  (h (xs ++ ys)) = ((h xs) + (h ys))%Z.
Proof.
  unfold h at 1. rewrite count_occ_app. rewrite count_occ_app.
  repeat rewrite Nat2Z.inj_add.
  rewrite Z.mul_add_distr_l. rewrite Z.sub_add_distr.
  rewrite Z.add_sub_swap.
  rewrite <- Z.add_sub_assoc.
  reflexivity.
Qed.

Theorem h_first_zero xs ys :
  (h (xs ++ ys) < 0)%Z ->
  (0 <= h xs)%Z ->
  exists zs ws, ys = zs ++ ws /\ h (xs ++ zs) = 0%Z.
Proof.
  intros. rewrite h_app in H.
  induction ys.
  - assert ((h [] = 0)%Z) by auto. assert ((h xs < 0)%Z) by lia.
  (* todo *)
Admitted.


(** Third task *)

(* Hint: this is useful to reason by well-founded induction on words. *)
Definition word_len_lt := ltof _ (@length ascii).
Lemma word_len_wf : well_founded word_len_lt.
Proof. apply well_founded_ltof. Qed.

Definition smallest_word_st (P: word -> Prop) (w: word) :=
  P w /\ forall v, P v -> length w <= length v.

(* If [P] holds on some word [w], then we can consider "the" smallest word that
   satisfies [P]... *)
Lemma ex_smallest_word_st : forall (P: set word) (w: word),
  P w -> exists v, smallest_word_st P v.
Proof.
  (* todo *)
Admitted.

Theorem h_2_split w :
  h w = 2%Z ->
  (forall v, v ≺ w -> h v <> 1%Z) ->
  exists x y, h x = 0%Z /\ h y = 0%Z /\ w = x ++ [b] ++ y.
Proof.
  (* todo *)
Admitted.


(** Fourth task *)

Section L_sup.

Hypothesis h_first_zero : forall xs ys,
  (h (xs ++ ys) < 0)%Z ->
  (0 <= h xs)%Z ->
  exists zs ws, ys = zs ++ ws /\ h (xs ++ zs) = 0%Z.

Hypothesis h_2_split : forall w,
  h w = 2%Z ->
  (forall v, v ≺ w -> h v <> 1%Z) ->
  exists x y, h x = 0%Z /\ h y = 0%Z /\ w = x ++ [b] ++ y.

Theorem L_sup w :
  h w = 0%Z ->
  letters w ⊆ Pair a b ->
  L w.
Proof.
  (* todo *)
Admitted.

End L_sup.

(** The final theorem *)

Theorem final : L = M.
Proof.
  (* todo *)
Admitted.
