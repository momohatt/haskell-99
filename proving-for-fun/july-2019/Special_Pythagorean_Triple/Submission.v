Require Import Defs.

Theorem goal : exists a b c, pythagorean_triple a b c /\ a + b + c = 1000.
Proof.
  exists 200. exists 375. exists 425.
  split.
  - split; lia.
  - simpl. reflexivity.
Qed.
