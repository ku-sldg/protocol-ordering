Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Require Import AttestationProtocolOrdering.utilities.nat_le.

Section Reach.
  Context {T : Type}.
  Context (eqDec : forall x y : T, {x = y} + {x <> y}).
  Context (succ : T -> list T).
  Context (V : list T).
  Context (V_closed : forall t, In t V -> forall t', In t' (succ t) -> In t' V).

  Inductive reachStar : T -> T -> Prop :=
  | rs_refl : forall t, reachStar t t
  | rs_step : forall t1 t2, In t2 (succ t1) -> reachStar t1 t2
  | rs_trans : forall t1 t2 t3, reachStar t1 t2 -> reachStar t2 t3 -> reachStar t1 t3.

  Definition step (F : list T) : list T :=
    nodup eqDec (F ++ flat_map succ F).

  Lemma incl_step : forall F, 
    incl F (step F).
  Proof.
    intros F t H; apply nodup_In; apply in_or_app; auto.
  Qed.

  Lemma step_incl_V : forall F, 
    incl F V -> 
    incl (step F) V.
  Proof.
    intros F HF t H. 
    apply nodup_In in H; apply in_app_or in H; destruct H as [H|H].
    - apply HF; auto.
    - apply in_flat_map in H; destruct H as [s [Hs Ht]].
      eapply V_closed; eauto.
  Qed.

  Lemma step_incl : forall F F', 
    incl F F' -> 
    incl (step F) (step F').
  Proof.
    intros F F' HF t H. apply nodup_In in H; apply nodup_In.
    apply in_app_or in H; apply in_or_app.
    destruct H as [H|H].
    - left; apply HF; auto.
    - right; apply in_flat_map in H; destruct H as [s [Hs Ht]].
      apply in_flat_map; exists s; split; auto.
  Qed.

  Fixpoint stepN (n : nat) (F : list T) : list T :=
    match n with
    | 0 => F
    | S n' => stepN n' (step F)
    end.

  Lemma incl_stepN : forall n F, 
    incl F (stepN n F).
  Proof.
    induction n as [|n']; intros F t H; simpl; auto.
    apply IHn'; apply incl_step; auto.
  Qed.

  Lemma stepN_incl_V : forall n F, 
    incl F V -> 
    incl (stepN n F) V.
  Proof.
    induction n as [|n']; intros F HF; simpl; auto.
    apply IHn'; apply step_incl_V; auto.
  Qed.

  Lemma stepN_nodup : forall n F, 
    NoDup F -> 
    NoDup (stepN n F).
  Proof.
    induction n as [|n']; intros F HF; simpl; auto.
    apply IHn'; apply NoDup_nodup.
  Qed.

  Lemma stepN_add : forall n1 n2 F, 
    stepN (n1 + n2) F = stepN n2 (stepN n1 F).
  Proof.
    induction n1 as [|n1']; intros n2 F; simpl; auto.
  Qed.

  Lemma stepN_step : forall n F, 
    stepN (S n) F = step (stepN n F).
  Proof.
    intros n F; rewrite <- Nat.add_1_r;
    rewrite (stepN_add n 1 F); reflexivity.
  Qed.

  Definition sameset (F F' : list T) : Prop := 
    incl F F' /\ incl F' F.

  Lemma sameset_reflexive : forall F, 
    sameset F F.
  Proof. 
    intros F; split; apply incl_refl. 
  Qed.

  Lemma sameset_symmetric : forall F F', 
    sameset F F' -> 
    sameset F' F.
  Proof. 
    intros F F' [H1 H2]; split; auto. 
  Qed.

  Lemma sameset_transitive : forall F F' F'', 
    sameset F F' -> 
    sameset F' F'' -> 
    sameset F F''.
  Proof.
    intros F F' F'' [H1 H2] [H3 H4]; split; eapply incl_tran; eauto.
  Qed.

  Lemma step_sameset : forall F F', 
    sameset F F' -> 
    sameset (step F) (step F').
  Proof. 
    intros F F' [H1 H2]; split; apply step_incl; auto.
  Qed.

  Definition stableAt (F : list T) (n : nat) : Prop := 
    sameset (stepN n F) (stepN (S n) F).

  Lemma stepN_stable_or_grows : forall F n, 
    incl F V -> 
    NoDup F -> 
    length (stepN n F) < length (stepN (S n) F) \/ stableAt F n.
  Proof.
    intros F n HIncl HNd.
    assert (incl (stepN n F) (stepN (S n) F)) as HIncl'
    by (rewrite stepN_step; apply incl_step).
    pose proof (stepN_nodup n F HNd) as HNd'.
    pose proof (stepN_nodup (S n) F HNd) as HNd''.
    pose proof (NoDup_incl_length HNd' HIncl') as HLen'.
    destruct (Nat.eq_dec (length (stepN n F)) (length (stepN (S n) F))) as [HEq|HNeq].
    - right; split; auto.
      apply NoDup_length_incl; auto; lia.
    - left; lia.
  Qed.

  Lemma step_stable : forall F n, 
    sameset F (step F) -> 
    sameset F (stepN n F).
  Proof.
    intros F n H. induction n as [|n'].
    - apply sameset_reflexive.
    - rewrite stepN_step; eapply sameset_transitive; [apply H | apply step_sameset]; auto.
  Qed.

  Lemma stable_add : forall F n k, 
    stableAt F n -> 
    sameset (stepN n F) (stepN (n + k) F).
  Proof.
    intros F n k H.
    rewrite stepN_add; apply step_stable; rewrite <- stepN_step; auto.
  Qed.

  Lemma stableAt_add : forall F n k, 
    stableAt F n -> 
    stableAt F (n + k).
  Proof.
    intros F n k H.
    eapply sameset_transitive.
    - apply sameset_symmetric; apply stable_add; auto.
    - rewrite <- Nat.add_succ_r; apply stable_add; auto.
  Qed.

  Lemma exists_stable_within : forall F k n, 
    incl F V -> 
    NoDup F -> 
    length V - length (stepN n F) <= k ->
    exists m, n <= m /\ m <= n + k /\ stableAt F m.
  Proof.
    intros F k n HIncl HNd HLen. generalize dependent n; induction k as [|k']; intros.
    - assert (incl (stepN n F) (stepN (S n) F)) as HIncl'
      by (rewrite stepN_step; apply incl_step).
      exists n. repeat split; try lia; auto.
      apply NoDup_length_incl.
    -- apply stepN_nodup; auto.
    -- assert ((length (stepN n F) = (length V))) as HEq
       by (apply le_antisymmetric; [|lia]; 
           apply NoDup_incl_length;
           [apply stepN_nodup | apply stepN_incl_V]; auto).
      assert ((length (stepN (S n) F)) <= length V) as HLen'
      by (apply NoDup_incl_length; [apply stepN_nodup | apply stepN_incl_V]; auto).
      rewrite <- HEq in HLen'; auto.
    -- apply HIncl'.
    - destruct (stepN_stable_or_grows F n HIncl HNd) as [HGrow|HStable].
    -- assert (length (stepN n F) <= length V)
       by (apply NoDup_incl_length; [apply stepN_nodup | apply stepN_incl_V]; auto).
       assert (length (stepN (S n) F) <= length V)
       by (apply NoDup_incl_length; [apply stepN_nodup | apply stepN_incl_V]; auto).
       assert (length V - length (stepN (S n) F) <= k') as HLen' by lia.
       pose proof (IHk' (S n) HLen') as [m [HLe1 [HLe2 HSt]]].
       exists m. split; [|split]; try lia; auto.
    -- exists n; split; [|split]; try lia; auto.
  Qed.

  Lemma stableAt_succ_closed : forall F n, 
    stableAt F n ->
    forall t, In t (stepN n F) -> 
    forall t', In t' (succ t) -> In t' (stepN n F).
  Proof.
    intros F n H t Ht t' Ht'.
    assert (In t' (stepN (S n) F)) as HIn
    by (rewrite stepN_step; apply nodup_In; apply in_or_app; right;
        apply in_flat_map; exists t; split; assumption).
    destruct H as [_ H]; apply H; apply HIn.
  Qed.

  Lemma reachStar_succ_closed : forall F,
      (forall t, In t F -> forall t', In t' (succ t) -> In t' F) ->
      forall t1 t2, reachStar t1 t2 -> In t1 F -> In t2 F.
  Proof.
    intros F HF t1 t2 H; induction H; intros HIn; auto.
    eapply HF; eauto.
  Qed.

  Lemma stepN_sound : forall n F t1, 
    (forall t, In t F -> reachStar t1 t) ->
    forall t, In t (stepN n F) -> reachStar t1 t.
  Proof.
    induction n as [|n']; intros F t1 H t HIn; simpl in HIn; auto.
    apply (IHn' (step F) t1); auto.
    intros t' HIn'; apply nodup_In in HIn'; 
    apply in_app_or in HIn'; destruct HIn' as [|HIn']; auto.
    apply in_flat_map in HIn'; destruct HIn' as [t'' []].
    eapply rs_trans; eauto. apply rs_step; auto.
  Qed.

  Definition N : nat := length V.

  Definition reach (t1 t2 : T) : bool :=
    if (in_dec eqDec t2 (stepN N [t1]))
    then true 
    else false.

  Theorem stableAt_singleton : forall t1, 
    In t1 V -> 
    stableAt [t1] N.
  Proof.
    intros t1 HIn.
    assert (incl [t1] V) as HIncl by (intros t H; inversion H; subst; auto; contradiction).
    assert (NoDup [t1]) as HNd by (constructor; [intros contra; contradiction | constructor]).
    assert (length V - length (stepN 0 [t1]) <= N) as HLen by (simpl; unfold N; lia).
    destruct (exists_stable_within [t1] N 0 HIncl HNd HLen) as [m [_ []]].
    replace N with (m + (N - m)) by lia.
    apply stableAt_add; auto.
  Qed.

  Theorem reach_sound : forall t1 t2, 
    reach t1 t2 = true -> 
    reachStar t1 t2.
  Proof.
    intros t1 t2 H; unfold reach in H.
    destruct (in_dec eqDec t2 (stepN N [t1])) as [HIn|]; [|inversion H].
    eapply stepN_sound; eauto.
    intros t Ht; inversion Ht; subst; try contradiction. constructor.
  Qed.

  Theorem reach_complete : forall t1 t2, 
    In t1 V -> 
    reachStar t1 t2 -> 
    reach t1 t2 = true.
  Proof.
    intros t1 t2 HIn H; unfold reach.
    destruct (in_dec eqDec t2 (stepN N [t1])) as [|HNIn2]; [reflexivity|].
    exfalso; apply HNIn2.
    eapply reachStar_succ_closed; eauto.
    - eapply stableAt_succ_closed; apply stableAt_singleton; auto.
    - apply incl_stepN; simpl; auto.
  Qed.

  Definition reachDec (t1 t2 : T) (HIn1 : In t1 V) : 
      {reachStar t1 t2} + {~ reachStar t1 t2} :=
    match Bool.bool_dec (reach t1 t2) true with
    | left Heq => left (reach_sound t1 t2 Heq)
    | right Hneq => right (fun H => Hneq (reach_complete t1 t2 HIn1 H))
    end.

End Reach.
