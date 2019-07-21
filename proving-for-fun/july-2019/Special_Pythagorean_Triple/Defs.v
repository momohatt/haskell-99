Require Export NArith Lia.
Open Scope N.

Definition pythagorean_triple (a b c: N) :=
  a < b /\ b < c /\ a*a + b*b = c*c.