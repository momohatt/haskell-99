Section Confluency.
  Variable X : Set.
  Definition relation (X : Type) : Type :=
    X -> X -> Prop.
  Variable R : relation X.
  Notation "x '==>' y" := (R x y) (at level 80).

  Reserved Notation "x '==>*' y" (at level 80).
  Inductive multiR : relation X :=
  | multi_refl :
      forall (x : X), x ==>* x
  | multi_step :
      forall (x y z : X),
      x ==> y ->
      y ==>* z ->
      x ==>* z
  where "x '==>*' y" := (multiR x y).

  Hint Constructors multiR.

  Lemma multiR_trans :
    forall x y z, x ==>* y -> y ==>* z -> x ==>* z.
  Proof with auto.
    intros. generalize dependent z.
    induction H as [x | x w y]...
    - intros. apply multi_step with w...
  Qed.

  Definition weak_confluent_R :=
    forall x y y' : X, x ==> y -> x ==> y' ->
    exists z : X, y ==>* z /\ y' ==>* z.

  Definition confluent_R :=
    forall x y y' : X, x ==>* y -> x ==>* y' ->
    exists z : X, y ==>* z /\ y' ==>* z.

  Definition terminating_R :=
    well_founded (fun x y => y ==> x).

  Theorem newman :
    terminating_R -> weak_confluent_R -> confluent_R.
  Proof with eauto.
    unfold weak_confluent_R, confluent_R.
    intros termination weak_confluent x.
    induction x as [x IH] using (well_founded_ind termination);
      intros.

    destruct H as [x | x w y].
    - (* x = y *)
      exists y'; split...
    - destruct H0 as [x | x w' y'].
      + (* x = y' *)
        exists y; split...
      + assert (exists u, w ==>* u /\ w' ==>* u) by
          (apply weak_confluent with x; auto).
        destruct H3 as [u [? ?]].
        assert (exists v, y ==>* v /\ u ==>* v) by
          (apply IH with (y:=w); auto).
        destruct H5 as [v [? ?]].
        assert (multiR w' v) by (apply multiR_trans with u; auto).
        assert (exists d, v ==>* d /\ y' ==>* d) by
          (apply IH with w'; auto).
        destruct H8 as [d [? ?]].
        exists d; split...
        apply multiR_trans with v...
  Qed.

  (* reflexive symmetric transitive closure *)
  Reserved Notation "x '<==>*' y" (at level 80).
  Inductive rst_closure : relation X :=
  | rst_refl :
      forall x, x <==>* x
  | rst_step1 :
      forall x y z, x ==> y -> y <==>* z -> x <==>* z
  | rst_step2 :
      forall x y z, y ==> x -> y <==>* z -> x <==>* z
  where "x '<==>*' y" := (rst_closure x y).

  Hint Constructors rst_closure.

  Lemma multi_is_rst_closure :
    forall x y, x ==>* y -> x <==>* y.
  Proof.
    intros. induction H; eauto.
  Qed.

  Lemma rst_closure_symm :
    forall x y, x <==>* y -> y <==>* x.
  Proof.
  Admitted.

  Lemma rst_closure_trans :
    forall x y z, x <==>* y -> y <==>* z -> x <==>* z.
  Proof with auto.
    intros. generalize dependent z.
    induction H as [x | x w y | x w y ]; intros...
    - apply rst_step1 with w...
    - apply rst_step2 with w...
  Qed.

  Definition joinableR x y :=
    exists z, x ==>* z /\ y ==>* z.

  Definition church_rosser_R :=
    forall x y, x <==>* y -> joinableR x y.

  Theorem confluence_church_rosser_equiv :
    confluent_R <-> church_rosser_R.
  Proof.
    unfold confluent_R, church_rosser_R.
    split; intros.
    - (* confluent -> church rosser *)
      admit.
    - (* church rosser -> confluent *)
      apply H.
      apply multi_is_rst_closure in H0.
      apply multi_is_rst_closure in H1.
      apply rst_closure_symm in H0.
      apply rst_closure_trans with x; auto.
  Admitted.
End Confluency.
