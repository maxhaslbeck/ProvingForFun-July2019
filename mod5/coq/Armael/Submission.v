Require Import Defs.

(* Proving this might be useful (but is not mandatory). *)
Lemma mod_power a b n :
  ((a mod b) ^ n) mod b = (a ^ n) mod b.
Admitted.

Theorem modpower5 : forall (n: nat),
  n mod 10 = (n ^ 5) mod 10.
Proof.
  (* todo *)
Admitted.
