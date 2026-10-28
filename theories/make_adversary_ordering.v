Require Import Coq.Lists.List.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.reach.
Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.

Section MakeAdversaryOrdering.
    Context {components : Type}.
    Context (eqDec_components : forall (x y : components), {x = y} + {x <> y}).

    Context (advOrder : list (tauTaggedLabel components * tauTaggedLabel components)).

    Inductive makeTrianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop :=
    | makeTrianglelefteq_refl_intro : forall t, 
        makeTrianglelefteq t t
    | makeTrianglelefteq_tau_intro  : forall l, 
        makeTrianglelefteq (blankTag _ l) (tauTag _ l)
    | makeTrianglelefteq_base_intro : forall t1 t2,
        In (t1, t2) advOrder ->
        makeTrianglelefteq t1 t2
    | makeTrianglelefteq_trans_intro : forall t1 t2 t3,
        makeTrianglelefteq t1 t2 ->
        makeTrianglelefteq t2 t3 ->
        makeTrianglelefteq t1 t3.

    Lemma makeTrianglelefteq_reflexive : forall t, 
        makeTrianglelefteq t t.
    Proof.
        intros; apply makeTrianglelefteq_refl_intro.
    Qed.

    Lemma makeTrianglelefteq_tau : forall l,
        makeTrianglelefteq (blankTag _ l) (tauTag _ l).
    Proof.
        intros; apply makeTrianglelefteq_tau_intro.
    Qed.

    Lemma makeTrianglelefteq_transitive : forall t1 t2 t3,
        makeTrianglelefteq t1 t2 ->
        makeTrianglelefteq t2 t3 ->
        makeTrianglelefteq t1 t3.
    Proof.
        intros; eapply makeTrianglelefteq_trans_intro; eauto.
    Qed.



    Lemma eqDec_advLabel : forall (l1 l2 : advLabel components),
        {l1 = l2} + {l1 <> l2}.
    Proof.
        repeat decide equality.
    Defined.

    Lemma eqDec_ttl : forall (t1 t2 : tauTaggedLabel components),
        {t1 = t2} + {t1 <> t2}.
    Proof.
        repeat decide equality.
    Defined.



    Definition successors (t : tauTaggedLabel components) : list (tauTaggedLabel components) :=
        map snd (filter (fun p => if eqDec_ttl (fst p) t then true else false) advOrder) ++
        match t with
        | blankTag _ a => tauTag _ a :: nil
        | tauTag _ _ => nil
        end.

    Lemma successors_sound : forall t1 t2,
        In t2 (successors t1) -> 
        makeTrianglelefteq t1 t2.
    Proof.
        intros t1 t2 H; apply in_app_or in H; destruct H as [H|H].
        - apply in_map_iff in H; destruct H as [[t1' t2'] [HEq HIn]]; simpl in HEq; subst.
          apply filter_In in HIn; destruct HIn as [HIn HIf]; simpl in HIf.
          destruct (eqDec_ttl t1' t1); [|inversion HIf]; subst.
          apply makeTrianglelefteq_base_intro; auto.
        - destruct t1 as [a1|a1]; [inversion H|].
          destruct H; subst; [|inversion H]. 
          apply makeTrianglelefteq_tau_intro.
    Qed.

    Lemma makeTrianglelefteq_reachStar : forall t1 t2,
        makeTrianglelefteq t1 t2 -> 
        reachStar successors t1 t2.
    Proof.
        intros t1 t2 H; induction H.
        - constructor.
        - apply rs_step; apply in_or_app; right; simpl; auto.
        - apply rs_step; apply in_or_app; left; apply in_map_iff.
          exists (t1, t2); split; auto.
          apply filter_In; split; auto.
          simpl; destruct (eqDec_ttl t1 t1); auto.
        - eapply rs_trans; eauto.
    Qed.

    Lemma reachStar_makeTrianglelefteq : forall t1 t2,
        reachStar successors t1 t2 -> 
        makeTrianglelefteq t1 t2.
    Proof.
        intros t1 t2 H; induction H.
        - constructor.
        - apply successors_sound; auto.
        - eapply makeTrianglelefteq_trans_intro; eauto.
    Qed.

    Definition baseLabels : list (tauTaggedLabel components) :=
        flat_map (fun p => fst p :: snd p :: nil) advOrder.

    Definition getTauTag (t : tauTaggedLabel components) : tauTaggedLabel components :=
        match t with
        | blankTag _ a => tauTag _ a
        | tauTag _ a => tauTag _ a
        end.

    Definition candidates (t1 : tauTaggedLabel components) : list (tauTaggedLabel components) :=
        t1 :: getTauTag t1 :: baseLabels ++ map getTauTag baseLabels.

    Lemma candidates_closed : forall t1 t t',
        In t (candidates t1) -> 
        In t' (successors t) -> 
        In t' (candidates t1).
    Proof.
        intros t1 t t' Ht Ht'; apply in_app_or in Ht'; destruct Ht' as [Ht'|Ht'].
        - apply in_map_iff in Ht'; destruct Ht' as [[t1' t2'] [HEq HIn]]; simpl in HEq; subst.
          apply filter_In in HIn; destruct HIn as [HIn _].
          right; right; apply in_or_app; left.
          apply in_flat_map; exists (t1', t'); split; simpl; auto.
        - destruct t as [a|a]; simpl in Ht'; [destruct Ht'|]; destruct Ht'; subst; try contradiction.
          simpl in Ht; destruct Ht as [Ht|[Ht|Ht]]; subst; simpl; auto.
        -- destruct t1 as [a1|a1]; simpl in Ht; inversion Ht.
        -- apply in_app_or in Ht; destruct Ht as [Ht|Ht].
        --- right; right; apply in_or_app; right.
            apply (in_map getTauTag baseLabels (blankTag components a) Ht).
        --- apply in_map_iff in Ht; destruct Ht as [t [Ht _]].
            destruct t; simpl in Ht; inversion Ht.
    Qed.

    Lemma candidates_nodup_closed : forall t1 t,
        In t (nodup eqDec_ttl (candidates t1)) ->
        forall t', In t' (successors t) ->
        In t' (nodup eqDec_ttl (candidates t1)).
    Proof.
        intros t1 t Ht t' Ht'.
        apply nodup_In; apply nodup_In in Ht.
        eapply candidates_closed; eauto.
    Qed.

    Lemma t1_in_candidates : forall t1, 
        In t1 (nodup eqDec_ttl (candidates t1)).
    Proof.
        intros t1; apply nodup_In; left; auto.
    Qed.

    Definition makeTrianglelefteqDec (t1 t2 : tauTaggedLabel components) :
        {makeTrianglelefteq t1 t2} + {~ makeTrianglelefteq t1 t2}.
    Proof.
        destruct (reachDec eqDec_ttl 
                           successors
                           (nodup eqDec_ttl (candidates t1))
                           (candidates_nodup_closed t1)
                           t1 
                           t2 
                           (t1_in_candidates t1)) 
                    as [H|H].
        - left; apply reachStar_makeTrianglelefteq; auto.
        - right; intro HTri; apply H; apply makeTrianglelefteq_reachStar; auto.
    Defined.



    Lemma makeTrianglelefteq_cases : forall t1 t2,
        makeTrianglelefteq t1 t2 ->
        t1 = t2 \/
        (exists l, t1 = blankTag _ l /\ t2 = tauTag _ l) \/
        (exists t1' t2', In (t1', t2') advOrder /\
                         t1' <> t2' /\
                         makeTrianglelefteq t1 t1' /\
                         makeTrianglelefteq t2' t2).
    Proof.
        intros t1 t2 H; induction H; auto.
        - right; left; eexists; eauto.
        - destruct (eqDec_ttl t1 t2) as [HEq|HNeq]; [left; auto|].
          right; right; eexists; eexists; repeat split; eauto; constructor.
        - destruct IHmakeTrianglelefteq1 as [HEq | [[l1 [HEq1 HEq2]] | [t1' [t2' [HIn [HNeq [H1' H2']]]]]]]; subst; auto.
        -- destruct IHmakeTrianglelefteq2 as [HEq | [[l2 [HEq1 HEq2]] | [t1' [t2' [HIn [HNeq [H1' H2']]]]]]]; subst.
        --- right; left; eexists; eauto.
        --- inversion HEq1.
        --- right; right; eexists; eexists; repeat split; eauto.
            eapply makeTrianglelefteq_transitive; eauto.
        -- right; right; eexists; eexists; repeat split; eauto.
           eapply makeTrianglelefteq_transitive; eauto.
    Qed.

    Definition makeTrianglelefteq_antisymmetric_pair
        (tp : tauTaggedLabel components * tauTaggedLabel components) : Prop :=
    fst tp <> snd tp -> 
    ~ makeTrianglelefteq (snd tp) (fst tp).

    Definition makeTrianglelefteqAntisymmetricPairDec
            (tp : tauTaggedLabel components * tauTaggedLabel components) :
        {makeTrianglelefteq_antisymmetric_pair tp} + {~ makeTrianglelefteq_antisymmetric_pair tp}.
    Proof.
        unfold makeTrianglelefteq_antisymmetric_pair.
        destruct tp as [t1 t2]; simpl.
        destruct (eqDec_ttl t1 t2) as [|].
        - left; intros HNeq; contradiction.
        - destruct (makeTrianglelefteqDec t2 t1) as [|]; auto.
    Defined.

    Definition makeTrianglelefteq_antisymmetric_fix : Prop :=
        forallP_fix makeTrianglelefteqAntisymmetricPairDec advOrder.

    Lemma makeTrianglelefteq_antisymmetric_same :
        makeTrianglelefteq_antisymmetric_fix <->
        (forall t1 t2,
         makeTrianglelefteq t1 t2 ->
         makeTrianglelefteq t2 t1 ->
         t1 = t2).
    Proof.
        unfold makeTrianglelefteq_antisymmetric_fix; rewrite forallP_same'; split.
        - intros HAll t1 t2 H12 H21.
          destruct (eqDec_ttl t1 t2) as [|HNeq]; auto; exfalso.
          destruct (makeTrianglelefteq_cases _ _ H12) as [HEq | [[l1 [HEq1 HEq2]]|[t1' [t2' [HIn [HNeq' [H1' H2']]]]]]]; subst.
        -- contradiction.
        -- destruct (makeTrianglelefteq_cases _ _ H21) as [HEq | [[l2 [HEq1 HEq2]]|[t1' [t2' [HIn [HNeq' [H2' H1']]]]]]]; subst.
        --- inversion HEq.
        --- inversion HEq1.
        --- apply (HAll (t1', t2') HIn HNeq'); simpl;
            eapply makeTrianglelefteq_transitive; [apply H1'|];
            eapply makeTrianglelefteq_transitive; [apply makeTrianglelefteq_tau | apply H2'].
        -- apply (HAll (t1', t2') HIn HNeq'); simpl;
           eapply makeTrianglelefteq_transitive; [apply H2'|];
           eapply makeTrianglelefteq_transitive; [apply H21 | apply H1'].
        - intros H [t1' t2'] HIn HNeq H21; simpl in *.
          apply HNeq, H; auto;
          apply makeTrianglelefteq_base_intro; auto.
    Qed.

    Lemma makeTrianglelefteqAntisymmetricDec :
        {makeTrianglelefteq_antisymmetric_fix} + {~ makeTrianglelefteq_antisymmetric_fix}.
    Proof.
        unfold makeTrianglelefteq_antisymmetric_fix.
        destruct (forallPDec _ _ makeTrianglelefteqAntisymmetricPairDec advOrder) as [HAll|HAll].
        - left; apply forallP_same'; auto.
        - right; intros H; apply HAll; apply forallP_same' in H; auto.
    Defined.

End MakeAdversaryOrdering.