(** ==========================================================================
 ** Generic decidable reachability in a directed graph whose vertex type T
 ** need only have decidable equality -- T itself need NOT be finite.
 **
 ** The caller supplies a finite vertex list V that is closed under the
 ** successor function succ and contains the query's start vertex; V can be
 ** as small as the set of labels actually mentioned by the concrete edge
 ** relation being decided (see adversary_order.v's `candidates`), so this
 ** works even when the ambient type T (e.g. tauTaggedLabel components) is
 ** infinite. This replaces an earlier MathComp/fingraph.dfs-based decision
 ** procedure that required components to be a finite type (via an
 ** allComponents/allComponents_complete enumeration) -- finiteness of the
 ** *ambient type* was never actually necessary, only finiteness of the
 ** *edge relation itself* (which a `list` of pairs already guarantees).
 **
 ** Algorithm: stepNate the monotone "add one more hop" operator step,
 ** starting from [t1], for N := length V rounds. Soundness is immediate
 ** (every vertex added is reached via genuine successor hops). Completeness
 ** rests on a standard fixpoint argument: the set can only grow (as a set,
 ** tracked via NoDup lengths) a bounded number of times before it must
 ** stabilize (a version of the pigeonhole principle, via the stdlib lemmas
 ** NoDup_incl_length / NoDup_length_incl), and once stabilized it is closed
 ** under succ, hence (by a plain structural induction on the reachability
 ** relation itself) contains everything reachable from t1.
 **
 ** Reading guide: the lemmas below build up in four stages --
 **   1. step/stepN and their basic monotonicity/bookkeeping facts;
 **   2. sameset and the "stableAt" fixpoint notion, plus the pigeonhole
 **      argument (exists_stable_within) that a fixpoint is always reached
 **      within `length V` rounds;
 **   3. the two halves of correctness (stepN_sound / closed_reachable_subset
 **      + stable_implies_closed) connecting "what stepN computes" back to
 **      the actual reachStar relation;
 **   4. reach/reach_sound/reach_complete/reachDec, which package all of the
 **      above into the actual computable decision procedure. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Require Import AttestationProtocolOrdering.utilities.nat_le.

Section Reach.
  (* T: the vertex type -- arbitrary, need not be finite.
     eqDec: the only structural assumption on T; needed for `nodup`/`In`
       membership tests inside step and reach.
     succ: the edge relation, as a function to a list of direct successors.
     V: a finite vertex list, supplied per-query by the caller (e.g.
       adversary_order.v's `candidates t1`), closed under succ (V_closed).
       V is what bounds the search: everything below shows N := length V
       rounds of BFS from a start vertex in V already finds everything
       reachable from it, without ever needing V = "all of T". *)
  Context {T : Type}.
  Context (eqDec : forall x y : T, {x = y} + {x <> y}).
  Context (succ : T -> list T).
  Context (V : list T).
  Context (V_closed : forall t, In t V -> forall t', In t' (succ t) -> In t' V).

  (* The relation we actually want to decide: t1 can reach t2 by zero or
     more succ-edges. This is the semantic target -- adversary_order.v
     proves this is equivalent to trianglelefteq once succ is instantiated
     to the tau-rule-plus-advOrder successor function. Everything else in
     this file exists to build a Boolean/sumbool decision procedure for
     this Prop. *)
  Inductive reachStar : T -> T -> Prop :=
  | rs_refl : forall t, reachStar t t
  | rs_step : forall t1 t2, In t2 (succ t1) -> reachStar t1 t2
  | rs_trans : forall t1 t2 t3, reachStar t1 t2 -> reachStar t2 t3 -> reachStar t1 t3.

  (* One round of breadth-first expansion: F together with every direct
     successor of an element of F, deduplicated. This is the monotone
     operator whose n-fold stepNation (below, `stepN`) approximates "the set
     reachable from F within n hops"; repeatedly applying it is the whole
     algorithm. *)
  Definition step (F : list T) : list T :=
    nodup eqDec (F ++ flat_map succ F).

  (* step never loses elements (it's "extensive"). Needed to show
     stepN is monotonically non-decreasing in its round count, which is
     what makes the "grows or stabilizes" dichotomy (stepN_stable_or_grows)
     well-founded/eventually-forced. *)
  Lemma incl_step : forall F, 
    incl F (step F).
  Proof.
    intros F t H; apply nodup_In; apply in_or_app; auto.
  Qed.

  (* If F stays inside V, so does step F. Combined with stepN_nodup
     below, this is what bounds `length (stepN n F0)` by `length V` at
     every round -- the ceiling the pigeonhole argument (exists_stable_
     within) needs in order to force stabilization. *)
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

  (* step is monotone w.r.t. subset inclusion. Needed only to build
     the two-directional versions below (step_mono/sameset_step)
     used when propagating a fixpoint fact from one round to later rounds. *)
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

  (* n-fold application of step to F: "the set reachable from F within
     (at most) n hops", computed by BFS. `reach` below is exactly `stepN`
     run for N := length V rounds starting from the singleton [t1]; this
     Fixpoint is the actual algorithm everything else exists to justify. *)
  Fixpoint stepN (n : nat) (F : list T) : list T :=
    match n with
    | 0 => F
    | S n' => stepN n' (step F)
    end.

  (* F ⊆ stepN n F for every n (the n-fold analogue of incl_step).
     Needed by reach_complete to know the start vertex t1 is still present
     in its own N-round stepNate (so `In t1 (stepN N [t1])` is available
     as the base case closed_reachable_subset needs). *)
  Lemma incl_stepN : forall n F, 
    incl F (stepN n F).
  Proof.
    induction n as [|n']; intros F t H; simpl; auto.
    apply IHn'; apply incl_step; auto.
  Qed.

  (* stepNating from inside V never escapes V. Together with NoDup-ness
     (stepN_nodup), this gives `length (stepN n F0) <= length V` for every
     n -- the fixed ceiling the pigeonhole argument needs. *)
  Lemma stepN_incl_V : forall n F, 
    incl F V -> 
    incl (stepN n F) V.
  Proof.
    induction n as [|n']; intros F HF; simpl; auto.
    apply IHn'; apply step_incl_V; auto.
  Qed.

  (* stepNating a duplicate-free list stays duplicate-free (each round
     re-nodups). Needed so that "length" is actually meaningful as a
     measure of set size at every round -- the stdlib pigeonhole lemmas
     NoDup_incl_length/NoDup_length_incl both require NoDup hypotheses. *)
  Lemma stepN_nodup : forall n F, 
    NoDup F -> 
    NoDup (stepN n F).
  Proof.
    induction n as [|n']; intros F HF; simpl; auto.
    apply IHn'; apply NoDup_nodup.
  Qed.


  (* stepN is additive in its round count: doing a+b rounds is the same as
     doing a rounds then b more. This is the key algebraic fact used to
     derive stepN_S_comm (put step on the *outside*, i.e. after n
     rounds instead of before), which in turn is what lets `stableAt`
     (defined via stepN (S n)) be related to "one more step application
     of stepN n F0". *)
  Lemma stepN_add : forall n1 n2 F, 
    stepN (n1 + n2) F = stepN n2 (stepN n1 F).
  Proof.
    induction n1 as [|n1']; intros n2 F; simpl; auto.
  Qed.

  (* stepN (S n) F = step (stepN n F): applying step after n rounds
     gives the same result whether you fold it in at the start (the
     Fixpoint's own definition) or apply it once more at the end. Used
     pervasively below (stableAt's unfolding, stable_implies_closed,
     stepN_stable_or_grows) to reason about "the next round" as a single
     step application on top of the current accumulated set. *)
  Lemma stepN_step : forall n F, 
    stepN (S n) F = step (stepN n F).
  Proof.
    intros n F; rewrite <- Nat.add_1_r;
    rewrite (stepN_add n 1 F); reflexivity.
  Qed.

  (* stepN is monotone (one direction) w.r.t. subset inclusion -- the n-fold
     lift of step_mono1. Used only to build sameset_stepN, which is
     what lets us replace F by any set with the same elements inside an
     stepN and get the same elements back out. *)
  (*Lemma stepN_incl : forall n F F', 
    incl F F' -> 
    incl (stepN n F) (stepN n F').
  Proof.
    induction n as [|n']; intros F F' H; simpl; auto.
    apply IHn'; apply step_incl; auto.
  Qed. *)

  (* "F and F' have the same elements" (mutual inclusion). This is our
     stand-in for set equality, since we work with plain (possibly
     differently-ordered, differently-deduplicated) lists rather than an
     actual finite-set type. Used throughout the stabilization argument:
     once a round's output has the *same elements* as the previous round,
     it's a fixpoint, regardless of lstepNal list structure. *)
  Definition sameset (F F' : list T) : Prop := 
    incl F F' /\ incl F' F.

  (* sameset is an equivalence relation. Needed to chain the stabilization
     reasoning below (e.g. "stable at round m" plus "m relates to N" gives
     "stable at round N") via ordinary rewriting-style transitivity. *)
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

  (* step/stepN send sameset inputs to sameset outputs (they only
     "see" F through its membership, so equal-as-sets inputs can't be
     told apart). This is exactly what's needed to prove that once a set
     is a fixpoint of step, ALL further stepNations of it keep the
     same elements (fixpoint_stable), not just the very next one. *)
  Lemma step_sameset : forall F F', 
    sameset F F' -> 
    sameset (step F) (step F').
  Proof. 
    intros F F' [H1 H2]; split; apply step_incl; auto.
  Qed.

  (*
  Lemma stepN_sameset : forall n F F', 
    sameset F F' -> 
    sameset (stepN n F) (stepN n F').
  Proof. 
    intros n F F' [H1 H2]; split; apply stepN_incl; assumption. 
  Qed. *)

  (* "Round n has already stabilized": one more round of BFS from F0 adds
     nothing new (as a set). This is the formal notion of "the search has
     saturated" -- reach_complete_closed shows this holds (for F0 := [t1])
     at exactly the round count N := length V that `reach` actually uses,
     and stable_implies_closed then shows a stabilized round is closed
     under succ, which is the property closed_reachable_subset needs to
     conclude completeness. *)
  Definition stableAt (F : list T) (n : nat) : Prop := 
    sameset (stepN n F) (stepN (S n) F).

  (* At every round, either the set strictly grew (in length) or it has
     already stabilized. This is the trichotomy driving the pigeonhole
     argument below: since length is bounded above by length V
     (stepN_incl_V + NoDup_incl_length) and can't be negative, it cannot
     strictly grow forever -- so stabilization must eventually happen. *)
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

  (* Once a set G is a fixpoint of step (sameset G (step G)),
     it has the same elements as ITSELF stepNated any number k of further
     times, not just once more. Needed to propagate a stabilization
     witnessed at some round m (found by the pigeonhole search) forward to
     later rounds, in particular to the specific round N that `reach`
     uses (see stable_forward / reach_complete_closed). *)
  Lemma step_stable : forall F n, 
    sameset F (step F) -> 
    sameset F (stepN n F).
  Proof.
    intros F n H. induction n as [|n'].
    - apply sameset_reflexive.
    - rewrite stepN_step; eapply sameset_transitive; [apply H | apply step_sameset]; auto.
  Qed.

  (* Corollary of fixpoint_stable phrased directly in terms of stepN n F0:
     if round n has stabilized, then round n and round n+k have the same
     elements, for every k. This is the "stability persists forever after
     it first happens" fact. *)
  Lemma stable_add : forall F n k, 
    stableAt F n -> 
    sameset (stepN n F) (stepN (n + k) F).
  Proof.
    intros F n k H.
    rewrite stepN_add; apply step_stable; rewrite <- stepN_step; auto.
  Qed.

  (* If round n is stable, so is every later round n+k -- i.e. stability,
     once reached, is itself a stable property of the round index. This is
     what lets reach_complete_closed convert "stable at SOME round m ≤ N"
     (found by exists_stable_within) into "stable at exactly N". *)
  Lemma stableAt_add : forall F n k, 
    stableAt F n -> 
    stableAt F (n + k).
  Proof.
    intros F n k H.
    eapply sameset_transitive.
    - apply sameset_symmetric; apply stable_add; auto.
    - rewrite <- Nat.add_succ_r; apply stable_add; auto.
  Qed.

  (* The heart of the pigeonhole argument: starting from round n, a stable
     round is reached within k more rounds whenever k is at least the
     remaining "room to grow" (length V - length (stepN n F0)). Proved by
     induction on k: either the current round is already stable (done), or
     it strictly grew (stepN_stable_or_grows), which eats into the room-to-
     grow budget by at least 1, so the recursive call has strictly less
     room left to search through. Instantiated below (in
     reach_complete_closed) at n := 0, k := length V, which is always a
     valid budget since a single-vertex start set has length 1 <= length V. *)
  
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

  (* A stabilized round is closed under succ: every successor of every
     element already-present stays present. This turns the purely numeric
     "stableAt" fact into the graph-theoretic "closed" property that
     closed_reachable_subset (below) actually consumes to get completeness. *)
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

  (* The master completeness lemma: ANY list F that is closed under succ
     and contains a start vertex t1 must contain every vertex t2 with
     reachStar t1 t2 -- proved by a plain structural induction on the
     reachStar derivation itself (no fuel/rounds involved here at all).
     Combined with stable_implies_closed, this shows the specific set
     `stepN N [t1]` that `reach` computes already contains everything
     reachable from t1, once we know it has stabilized. *)
  Lemma reachStar_succ_closed : forall F,
      (forall t, In t F -> forall t', In t' (succ t) -> In t' F) ->
      forall t1 t2, reachStar t1 t2 -> In t1 F -> In t2 F.
  Proof.
    intros F HF t1 t2 H; induction H; intros HIn; auto.
    eapply HF; eauto.
  Qed.

  (* The soundness half of the algorithm: everything that shows up in
     stepN n F0 is genuinely reachStar-reachable from t1, PROVIDED every
     element of the starting set F0 already was (the hypothesis here is
     what lets the induction go through one step round at a time,
     chaining a fresh succ-edge onto an already-reachable vertex via
     rs_trans/rs_step). Instantiated below (reach_sound) with F0 := [t1]
     and the trivial fact that t1 reaches itself (rs_refl). *)
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

  (* The fuel/round-count actually used by the algorithm: the length of
     the caller-supplied vertex list. This is exactly the ceiling the
     pigeonhole argument (exists_stable_within) needs to guarantee
     stabilization has already happened by round N, for ANY start vertex
     in V -- no larger bound is ever required, regardless of how V arose. *)
  Definition N : nat := length V.

  (* The actual computable decision procedure: does t2 appear after N
     rounds of BFS from t1? This is what runs (e.g. under vm_compute) when
     a client calls trianglelefteqDec; everything else in this file exists
     solely to prove this Boolean test correct (reach_sound/reach_complete
     below). *)
  Definition reach (t1 t2 : T) : bool :=
    if (in_dec eqDec t2 (stepN N [t1]))
    then true 
    else false.

  (* The linchpin connecting the abstract pigeonhole machinery to the
     concrete round count N: for any start vertex t1 in V, round N (the
     one `reach` actually computes) has already stabilized. Proved by
     finding SOME stable round m <= N via exists_stable_within (starting
     from the singleton [t1], budget N, which suffices since a singleton
     has length 1 <= length V = N... plus one, handled by the lia call),
     then pushing that stability forward from m to N via stableAt_forward. *)
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

  (* reach never produces a false positive: if it says true, reachStar
     genuinely holds. This is (half of) what trianglelefteqDec in
     adversary_order.v needs to build the `left` case of its sumbool. *)
  Theorem reach_sound : forall t1 t2, 
    reach t1 t2 = true -> 
    reachStar t1 t2.
  Proof.
    intros t1 t2 H; unfold reach in H.
    destruct (in_dec eqDec t2 (stepN N [t1])) as [HIn|]; [|inversion H].
    eapply stepN_sound; eauto.
    intros t Ht; inversion Ht; subst; try contradiction. constructor.
  Qed.

  (* reach never produces a false negative (given t1 ∈ V): if reachStar
     genuinely holds, reach says true. Combines reach_complete_closed
     (round N has stabilized) with stable_implies_closed (so it's closed
     under succ) and closed_reachable_subset (so it contains every
     reachStar-successor of t1, in particular t2) to derive a
     contradiction from the assumption that t2 is absent. This is (the
     other half of) what trianglelefteqDec needs, for its `right` case. *)
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

  (* The public entry point: packages the Boolean `reach` together with
     its soundness/completeness proofs into an actual sumbool decision
     procedure for reachStar. This is what adversary_order.v's
     trianglelefteqDec is built directly on top of, instantiating T,
     eqDec, succ, V and V_closed with tauTaggedLabel components,
     eqDec_tauTaggedLabel, successors, and candidates/candidates_closed
     respectively. The caller must additionally supply a proof that the
     query's start vertex t1 lies in V (Ht1); adversary_order.v's
     t1_in_candidates discharges this automatically for candidates t1. *)
  Definition reachDec (t1 t2 : T) (HIn1 : In t1 V) : 
      {reachStar t1 t2} + {~ reachStar t1 t2} :=
    match Bool.bool_dec (reach t1 t2) true with
    | left Heq => left (reach_sound t1 t2 Heq)
    | right Hneq => right (fun H => Hneq (reach_complete t1 t2 HIn1 H))
    end.

End Reach.
