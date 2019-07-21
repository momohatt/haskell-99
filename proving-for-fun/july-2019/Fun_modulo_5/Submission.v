Require Import Defs.

Lemma mod_power a b n :
  ((a mod b) ^ n) mod b = (a ^ n) mod b.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    destruct b. reflexivity.
    rewrite Nat.mul_mod; try lia.
    rewrite IHn.
    rewrite Nat.mod_mod; try lia.
    rewrite <- Nat.mul_mod; try lia.
Qed.

Lemma mod_succ a n :
  (S a) mod n = (S (a mod n)) mod n.
Proof.
  destruct n.
  - simpl. reflexivity.
  - rewrite <- Nat.add_1_r.
    replace (S (a mod S n)) with (a mod S n + 1).
    rewrite Nat.add_mod_idemp_l; lia.
    rewrite Nat.add_1_r.
    reflexivity.
Qed.

Lemma mod_10 n :
  n mod 10 = 0 \/ n mod 10 = 1 \/
  n mod 10 = 2 \/ n mod 10 = 3 \/
  n mod 10 = 4 \/ n mod 10 = 5 \/
  n mod 10 = 6 \/ n mod 10 = 7 \/
  n mod 10 = 8 \/ n mod 10 = 9.
Proof.
  induction n.
  - left. reflexivity.
  - destruct IHn as [H | IHn].
    right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; right; right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; right; right; right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; right; right; right; right; right; left.
    rewrite mod_succ; rewrite H; reflexivity.
    destruct IHn as [H | IHn].
    right; right; right; right; right; right; right; right; right.
    rewrite mod_succ; rewrite H; reflexivity.
    left.
    rewrite mod_succ; rewrite IHn; reflexivity.
Qed.

Theorem modpower5 : forall (n: nat),
  n mod 10 = (n ^ 5) mod 10.
Proof.
  intros.
  rewrite <- mod_power.
  destruct (mod_10 n).
  rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  destruct H. rewrite H; reflexivity.
  rewrite H; reflexivity.
Qed.
