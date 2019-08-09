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
Require Import ssreflect.
Local Ltac done ::= first [ solve [ trivial | eauto | lia ] ].

(* Prevent simpl/cbn from unfolding the multiplication, which is never a good
   idea. *)
Arguments Nat.mul : simpl never.
Arguments Z.mul : simpl never.

(** First task *)

Lemma L_alphabet : forall w, L w -> letters w ⊆ Pair a b.
Proof. intros w. induction 1. all: rewrite !lettersE; firstorder. Qed.

Lemma count_app c u v : #{c} (u ++ v) = #{c}u + #{c}v.
Proof. induction u; rewrite //= IHu. destruct (ascii_dec a c); auto. Qed.

Lemma L_count : forall w, L w -> #{a}w = 2 * #{b}w.
Proof.
  intros w. induction 1; rewrite //=.
  all: rewrite !count_app //= !count_app //=.
Qed.

Theorem L_sub : L ⊆ M.
Proof.
  (* todo *)

  (* solution *)
  intros w Lw. unfold M. auto using L_alphabet, L_count.
Qed.

(** Second task *)

Lemma h_app_a : forall xs, h (xs ++ ["a"]) = (h xs - 1)%Z.
Proof. intros. rewrite /h !count_app //=. Qed.

Lemma h_app_b : forall xs, h (xs ++ ["b"]) = (h xs + 2)%Z.
Proof. intros. rewrite /h !count_app //=. Qed.

Lemma h_app_other : forall xs c, c <> a -> c <> b -> h (xs ++ [c]) = h xs.
Proof.
  intros. rewrite /h !count_app //=. assert (a <> b) by (rewrite /a /b; congruence).
  destruct (ascii_dec c a); destruct (ascii_dec c b); cbn; subst; first [done|tauto].
Qed.

Lemma h_app : forall xs ys, h (xs ++ ys) = (h xs + h ys)%Z.
Proof. intros. rewrite /h !count_app //=. Qed.

Theorem h_first_zero xs ys :
  (h (xs ++ ys) < 0)%Z ->
  (0 <= h xs)%Z ->
  exists zs ws, ys = zs ++ ws /\ h (xs ++ zs) = 0%Z.
Proof.
  (* todo *)

  (* solution *)
  revert xs. induction ys using rev_ind; intro xs.
  { rewrite app_nil_r. lia. }
  { intros Hh H0.
    destruct (ascii_dec x "a").
    { subst x. rewrite app_assoc h_app_a in Hh.
      destruct (Z_lt_le_dec (h (xs ++ ys)) 0) as [HH|HH].
      - specialize (IHys xs HH H0) as (zs & ws & -> & Hxzs).
        rewrite -app_assoc //.
      - eauto with zarith. }
    destruct (ascii_dec x "b").
    { subst x. rewrite app_assoc h_app_b in Hh.
      assert (HH: (h (xs ++ ys) < 0)%Z) by lia. specialize (IHys xs HH H0) as (?&?&->&?).
      rewrite -app_assoc //. }
    rewrite app_assoc h_app_other // in Hh.
    specialize (IHys xs Hh H0) as (?&?&->&?). rewrite -app_assoc //. }
Qed.


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
  intros P w Pw.
  induction w using (well_founded_induction word_len_wf).
  destruct (classic (exists v, length v < length w /\ P v)) as [[v [? ?]]|HH].
  { eauto. }
  { pose proof (not_ex_all_not _ _ HH) as HH'. cbn in HH'.
    exists w. unfold smallest_word_st. split; eauto.
    intro v. specialize (HH' v). apply not_and_or in HH'.
    intro. destruct HH' as [|]. lia. now exfalso. }
Qed.

Theorem h_2_split w :
  h w = 2%Z ->
  (forall v, v ≺ w -> h v <> 1%Z) ->
  exists x y, h x = 0%Z /\ h y = 0%Z /\ w = x ++ [b] ++ y.
Proof.
  (* todo *)

  (* solution *)
  intros H2 Hn1.
  assert (exists v, smallest_word_st (fun v =>
    exists x, w = v ++ x /\ (h v > 0)%Z) v) as [v [Hv1 Hv2]].
  { apply ex_smallest_word_st with w. exists []. rewrite app_nil_r.
    split; auto with zarith. }
  destruct Hv1 as [u [Hwvu Hv]].
  assert (Hvnil: v <> []).
  { intros ->. cbv in Hv. congruence. }
  destruct (exists_last Hvnil) as [x [c Hveq]]. clear Hvnil.
  assert (h x <= 0)%Z.
  { enough (~ (h x > 0))%Z. lia. intro.
    assert (C: length v <= length x).
    { apply Hv2. exists (c :: u).
      subst w v. split; [| assumption]. rewrite -app_assoc //. }
    subst v; rewrite app_length //= in C. }
  destruct (ascii_dec c a) as [|Hca].
  { subst c. rewrite Hveq h_app_a // in Hv. }
  destruct (ascii_dec c b) as [Hcb|]; swap 1 2.
  { rewrite Hveq h_app_other // in Hv. }
  subst c. clear Hca.
  subst w. rewrite h_app in H2. rewrite Hveq h_app_b in Hv, H2.
  assert (h x + h u = 0)%Z by lia.
  assert (h x = 0)%Z.
  { enough (h x < 0 -> False)%Z. lia. intro.
    assert (h x = -1)%Z. lia.
    assert (u <> [])%Z.
    { intros ->. rewrite (_:h [] = 0)%Z // Z.add_0_r in H2. }
    assert (h v = 1%Z).
    { rewrite Hveq h_app_b //. }
    assert (v ≺ (v ++ u)). { unfold prefix. eauto. }
    specialize (Hn1 v). tauto. }
  exists x, u. repeat split; try done.
  rewrite Hveq app_assoc //.
Qed.

(** Fourth task *)

Hint Constructors L : L.

Lemma L_rev w : L w -> L (rev w).
Proof.
  induction 1; rewrite //= ?rev_app_distr //= ?rev_app_distr //=.
  all: rewrite -?app_assoc //=; eauto using L.
Qed.

Lemma h_rev w : h (rev w) = h w.
Admitted.

Lemma length_notnil A (l: list A) : l <> [] -> length l > 0.
Proof. destruct l. congruence. cbn. lia. Qed.

Lemma letters_union_l w v A :
  letters w ∪ letters v ⊆ A ->
  letters w ⊆ A.
Proof. firstorder. Qed.

Lemma letters_union_r w v A :
  letters w ∪ letters v ⊆ A ->
  letters v ⊆ A.
Proof. firstorder. Qed.

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

  (* solution *)
  induction w using (well_founded_induction word_len_wf).
  unfold word_len_lt, ltof in H.
  destruct (classic
    (exists x y, w = x ++ y /\ x <> [] /\ y <> [] /\ h x = 0%Z /\ h y = 0%Z))
  as [Split|NoSplit].
  { destruct Split as (w1 & w2 & ? & ? & ? & ? & ?). intros.
    subst w. rewrite app_length in H.
    assert (length w1 > 0) by auto using length_notnil.
    assert (length w2 > 0) by auto using length_notnil.
    rewrite -> letters_app in *.
    apply L_app.
    all: apply H; rewrite //= ?app_length //.
    all: eauto using letters_union_l, letters_union_r. }

Admitted.

End L_sup.

(** The final theorem *)

Theorem final : L = M.
Proof.
  (* todo *)
Admitted.
