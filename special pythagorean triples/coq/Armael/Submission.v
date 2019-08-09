Require Import Defs.

Theorem goal : exists a b c, pythagorean_triple a b c /\ a + b + c = 1000.
Proof.
  (* todo *)

  (* (dumb) solution *)
  now exists 200, 375, 425.
Qed.
