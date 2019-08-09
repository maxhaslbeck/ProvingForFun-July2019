Require Import Defs.

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

Require Import ssreflect ssrbool.
Ltac done ::= first [ solve [ trivial | auto | lia ] ].

(** Part 1 -- properties of XOR *)

(* a few useful lemmas: *)
Lemma xor_shuffle a b c : xor a b = c <-> xor a c = b.
Proof.
  (* todo *)

  (* solution *)
  destruct a; destruct b; destruct c; cbn; split; auto.
Qed.

Check bubble_foldr_xor.
(* forall (f : output) (xs : list nat) (y z : bool),
     xor (fold_right (fun (x : nat) (n : bool) => xor n (f x)) y xs) z =
     fold_right (fun (x : nat) (n : bool) => xor n (f x)) (xor y z) xs *)

Check seq_length_S.
(* forall start len : nat,
     seq start (S len) = seq start len ++ [start + len]
*)

Check interval_app.
(* forall x y z : nat,
     x <= y -> y <= z ->
     [x..<y] ++ [y..<z] = [x..<z]
*)

Lemma XOR_interval x y f:
  x <= y ->
  xor (XOR 0 x f) (XOR 0 y f) = XOR x y f.
Proof.
  (* todo *)

  (* solution: *)
  intro H. rewrite xor_shuffle.
  rewrite /XOR.
  rewrite bubble_foldr_xor //=.
  rewrite -fold_right_app interval_app //.
Qed.

(** Part 2: number_of_true_between reduction to XOR *)

Lemma filter_app A f (l1 l2: list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof. induction l1; auto; rewrite //= IHl1. destruct (f a); auto. Qed.

Lemma XOR_odd_odd x y f: XOR x y f = Nat.odd (number_of_true_between x y f).
  (* todo *)

  (* solution *)
  destruct (le_dec y x) as [Hyx|Hyx].
  { rewrite /XOR /number_of_true_between (_:y-x=0) //. }
  set n := y - x. rewrite (_:y=x+n) //.
  clearbody n. induction n.
  - rewrite Nat.add_0_r XOR_same /number_of_true_between Nat.sub_diag //.
  - rewrite Nat.add_succ_r XOR_cons //.
    rewrite IHn /number_of_true_between (_:S (x+n)-x = S n) // (_:x+n-x=n) //.
    rewrite seq_length_S // filter_app //=.
    destruct (f (x+n)); rewrite xorE app_length //=.
    now rewrite Nat.add_1_r Nat.odd_succ Nat.negb_odd.
Qed.

Lemma reduction (t: task) (i: input) (o: output):
  correct_solution_XOR t i o ->
  correct_solution t i o.
Proof.
  (* todo *)

  (* solution *)
  intros C. unfold correct_solution_XOR, correct_solution in *.
  intros. rewrite -XOR_odd_odd. rewrite C //.
Qed.


(** Part 3 -- Implementation time! *)

(* puts false in register A *)
Definition regAFalse :=
  [LoadIA 0; LoadIB 0; Xor].

Lemma regAFalse_spec : forall i s,
  execs i s regAFalse =
  {| tmp := tmp s; regA := false; regB := i 0; out := out s |}.
Proof. intros. unfold regAFalse. rewrite //= xorE //. Qed.

(* tmp(n) <- XOR 0 n input *)
Fixpoint tabulate (upto: nat) :=
  match upto with
  | 0 =>
    regAFalse ++ [StoreTmp 0]
  | S upto =>
    tabulate upto ++
    [LoadTA upto;
     LoadIB upto;
     Xor;
     StoreTmp (S upto)]
  end.

Notation tmp_tabulated tmp i s upto :=
  (forall n, n <= upto -> tmp s n = XOR 0 n i) (only parsing).

Lemma tabulate_spec : forall i upto s' s,
  s' = execs i s (tabulate upto) ->
  tmp_tabulated tmp i s' upto /\
  (out s' = out s).
Proof.
  intros i upto. induction upto.
  { intros * Hs'.
    rewrite /tabulate execs_app regAFalse_spec //= in Hs'.
    subst s'. split; [| reflexivity]. intros.
    rewrite (_:n=0) //=. }
  { intros * Hs'.
    rewrite /tabulate execs_app -/tabulate in Hs'.
    set s1 := execs i s (tabulate upto). rewrite -/s1 in Hs'.
    specialize (IHupto s1 s eq_refl). destruct IHupto as [H1 H2].
    rewrite //= in Hs'. split.
    { intros. subst s'. cbn. destruct (le_dec n upto) as [Hn|Hn].
      - rewrite H1 // update_read_neq //.
      - rewrite (_:n = S upto) // update_read_eq // XOR_cons // H1 //. }
    { subst s'. now cbn. } }
Qed.

Lemma tabulate_time n : length (tabulate n) = 4 * n + 4.
Proof. induction n; rewrite //= app_length //=. Qed.

Definition calc (si ei : nat) :=
  [LoadTA si; LoadTB ei; Xor].

Lemma calc_spec : forall upto i si ei s,
  si <= ei -> ei <= upto ->
  tmp_tabulated tmp i s upto ->
  execs i s (calc si ei) =
  {| tmp := tmp s; regA := XOR si ei i; regB := tmp s ei; out := out s |}.
Proof.
  intros * Hsi Hei Htmp. rewrite /calc //=. f_equal.
  rewrite !Htmp // XOR_interval //.
Qed.

Fixpoint calc_all (si ei: nat -> nat) (upto: nat) :=
  match upto with
  | 0 =>
    []
  | S upto =>
    calc_all si ei upto ++
    calc (si upto) (ei upto) ++
    [StoreFinal upto]
  end.

Lemma calc_all_spec : forall size upto si ei i s s',
  s' = execs i s (calc_all si ei upto) ->
  upto <= size ->
  (forall n, n < size -> si n <= ei n <= size) ->
  tmp_tabulated tmp i s size ->
  tmp s' = tmp s /\
  (forall n, n < upto -> out s' n = XOR (si n) (ei n) i).
Proof.
  intros size. induction upto; intros * Hsize Hs' Hse Htmp; subst s'.
  { split; intros; rewrite /calc_all //=. }
  { rewrite /calc_all -/calc_all !execs_app.
    set s1 := execs i s (calc_all si ei upto).
    specialize (IHupto si ei i s s1 eq_refl).
    cbn. split; [by apply IHupto|]. intros n Hn.
    destruct (lt_dec n upto).
    - rewrite update_read_neq //. by apply IHupto.
    - rewrite update_read_eq // (_: tmp s1 = tmp s). by apply IHupto.
      rewrite (_: upto = n) // in Hs' |- *.
      assert (Hu: n < size) by lia. specialize (Hse n Hu) as [? ?].
      rewrite !Htmp // XOR_interval //. }
Qed.

Lemma calc_all_time si ei n : length (calc_all si ei n) = 4 * n.
Proof. induction n; rewrite //= app_length //=. Qed.

Definition program (t: task) :=
  tabulate (size t) ++ calc_all (si t) (ei t) (size t).

Lemma program_spec : forall i t s s',
  s' = execs i s (program t) ->
  forall n, n < size t -> out s' n = XOR (si t n) (ei t n) i.
Proof.
  intros * Hs' n Hn. subst s'. rewrite /program execs_app.
  set s1 := execs i s (tabulate (size t)).
  pose proof (tabulate_spec i (size t) s1 s eq_refl) as [H11 H12].
  set s2 := execs i s1 (calc_all (si t) (ei t) (size t)).
  pose proof (calc_all_spec (size t) (size t) (si t) (ei t) i s1 s2 eq_refl) as H2.
  apply H2; try done.
  intros k Hk. pose proof (si_lt_ei t k Hk). pose proof (ei_inbound t k Hk).
  done.
Qed.

Lemma program_time t : length (program t) = 8 * (size t) + 4.
Proof. rewrite /program app_length tabulate_time calc_all_time //=. Qed.

Theorem goal :
  exists (prog: task -> list Com),
    (* functional correctness *)
    (forall (t: task) (s0: state) (i: input),
      correct_solution t i (out (execs i s0 (prog t))))
    /\
    (* complexity: linear in the size of the task *)
    (exists (n0 c: nat), forall t, n0 <= size t -> length (prog t) <= c * (size t)).
Proof.
  (* todo *)

  (* solution *)
  exists program. split.
  { intros. apply reduction. unfold correct_solution_XOR. intros.
    rewrite (program_spec i t s0) //. }
  { exists 4, 9. intros. rewrite program_time //. }
Qed.
