Section Confluency.
  Variable X : Set.
  Definition relation (X : Type) : Type :=
    X -> X -> Prop.
  Variable R : relation X.

  Inductive multi (R : relation X) : relation X :=
    | multi_refl :
        forall (x : X), multi R x x
    | multi_step :
        forall (x y z : X),
        R x y ->
        multi R y z ->
        multi R x z.

  Hint Constructors multi.

  Definition multiR := multi R.

  Notation "x '==>' y" := (R x y) (at level 80).
  Notation "x '==>*' y" := (multiR x y) (at level 80).

  Lemma multiR_refl :
    forall x, x ==>* x.
  Proof. intros. apply multi_refl. Qed.

  Lemma multiR_trans :
    forall x y z, x ==>* y -> y ==>* z -> x ==>* z.
  Proof.
    intros. generalize dependent z.
    induction H as [x | x w y]; auto.
    - intros. apply IHmulti in H1. apply multi_step with w; auto.
  Qed.

  Hint Rewrite multiR_refl multiR_trans.

  Definition weak_confluence_R :=
    forall x y y' : X, x ==> y -> x ==> y' ->
    exists z : X, y ==>* z /\ y' ==>* z.

  Definition confluence_R :=
    forall x y y' : X, x ==>* y -> x ==>* y' ->
    exists z : X, y ==>* z /\ y' ==>* z.

  Axiom well_founded_R : well_founded (fun x y => y ==> x).

  Theorem confluence :
    weak_confluence_R -> confluence_R.
  Proof.
    unfold weak_confluence_R, confluence_R.
    intros weak_confluence x.
    induction x using (well_founded_ind well_founded_R);
      intros; rename H into IH.

    destruct H0 as [x | x w y].
    - (* x = y *)
      exists y'; split; unfold multiR; eauto.
    - destruct H1 as [x | x w' y'].
      + (* x = y' *)
        exists y; split; unfold multiR; eauto.
      + assert (exists u, w ==>* u /\ w' ==>* u) by
          (apply weak_confluence with x; auto).
        destruct H3 as [u [? ?]].
        assert (exists v, y ==>* v /\ u ==>* v) by
          (apply IH with (y:=w); auto).
        destruct H5 as [v [? ?]].
        assert (multiR w' v) by (apply multiR_trans with u; auto).
        assert (exists d, v ==>* d /\ y' ==>* d) by
          (apply IH with w'; auto).
        destruct H8 as [d [? ?]].
        exists d; split; auto.
        apply multiR_trans with v; auto.
Qed.
