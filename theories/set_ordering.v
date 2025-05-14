Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.utilities.supports.
Require Import AttestationProtocolOrdering.utilities.min.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.attackgraph_adversary.
Require Import AttestationProtocolOrdering.attackgraph_ordering.
(*Require Import AttestationProtocolOrdering.set_minimization.*)




Section SetOrdering. 
    Context {components : Type}.

(** equal
 **
 ** Sets of attack graphs P and Q are equal (i.e., P = Q)
 ** if and only if they are the same set under the simeq relation. *)

    Definition equal (P Q : list (attackgraph components)) : Prop :=
        supports simeq P Q /\ supports simeq Q P.

    Definition equal_fix (P Q : list (attackgraph components)) : Prop :=
        if (supportsDec simeq_fix simeqDec P Q)
        then if (supportsDec simeq_fix simeqDec Q P)
             then True
             else False
        else False.

    Hint Unfold equal : core.

    Lemma equal_same : forall P Q,
        equal_fix P Q <->
        equal P Q.
    Proof.
        unfold equal_fix; intros P Q; split; intros HEq.
        - destruct (supportsDec simeq_fix simeqDec P Q) as [HST|HST], 
                   (supportsDec simeq_fix simeqDec Q P) as [HTS|HTS];
          try (inversion HEq; fail);
          split; intros B HIn; apply supports_same in HST; apply supports_same in HTS;
          [ apply HST in HIn | apply HTS in HIn ]; 
          destruct HIn as [A]; exists A; rewrite <- simeq_same; auto.
        - destruct (supportsDec simeq_fix simeqDec P Q) as [HST|HST], 
                   (supportsDec simeq_fix simeqDec Q P) as [HTS|HTS];
          auto; destruct HEq as [HST' HTS'];
          try apply HST; try apply HTS; apply supports_same; 
          intros B HIn; try apply HST' in HIn; try apply HTS' in HIn;
          destruct HIn as [A]; exists A; rewrite simeq_same; auto.
    Qed.

    Lemma equalDec : forall P Q,
        {equal_fix P Q} + {~ equal_fix P Q}.
    Proof.
        unfold equal_fix; intros P Q; 
        destruct (supportsDec simeq_fix simeqDec P Q), (supportsDec simeq_fix simeqDec Q P);
        auto.
    Defined.

    Theorem equal_reflexive : forall P,
        equal P P.
    Proof.
        intros; split; apply supports_reflexive; apply simeq_reflexive.
    Qed. 

    Theorem equal_symmetric : forall P Q,
        equal P Q ->
        equal Q P.
    Proof.
        intros P Q HEq; destruct HEq; split; auto.
    Qed.

    Theorem equal_transitive : forall P Q R,
        equal P Q ->
        equal Q R ->
        equal P R.
    Proof.
        intros P Q R HST HTU; destruct HST, HTU; split; 
        eapply supports_transitive; eauto; apply simeq_transitive.
    Qed.


(** equiv (Equivalence)
 **
 ** Sets of attack graphs P and Q are equivalent (i.e., P \equiv Q)
 ** if and only if min(P) = min(Q). *)

    Definition equiv (P Q : list (attackgraph components)) : Prop := forall P' Q',
        min_ind prec P P P' ->
        min_ind prec Q Q Q' ->
        equal P' Q'.

    Definition equiv_fix (P Q : list (attackgraph components)) : Prop :=
        equal_fix (min_fix prec_fix precDec P P) (min_fix prec_fix precDec Q Q).

    Hint Unfold equiv : core.

    Lemma equiv_same : forall P Q,
        equiv_fix P Q <->
        equiv P Q.
    Proof.
        intros P Q; split; intros H.
        - intros P' Q' HMinP HMinQ;
          apply equal_same; unfold equiv_fix in H;
          eapply min_spo_same in HMinP, HMinQ; try apply prec_same;
          rewrite <- HMinP, <- HMinQ; eauto.
        - apply equal_same; apply H;
          eapply min_spo_same; try apply prec_same; eauto.
    Qed.

    Lemma equivDec : forall P Q,
        {equiv_fix P Q} + {~ equiv_fix P Q}.
    Proof.
        intros; apply equalDec.
    Defined.

    Theorem equiv_reflexive : forall P,
        equiv P P.
    Proof.
        intros; apply equiv_same; apply equal_same; apply equal_reflexive.
    Qed. 

    Theorem equiv_symmetric : forall P Q,
        equiv P Q ->
        equiv Q P.
    Proof.
        intros P Q H; apply equiv_same; apply equal_same; 
        apply equiv_same in H; apply equal_same in H;
        apply equal_symmetric; auto.
    Qed.

    Theorem equiv_transitive : forall P Q R,
        equiv P Q ->
        equiv Q R ->
        equiv P R.
    Proof.
        intros P Q R HPQ HQR; apply equiv_same; apply equal_same;
        apply equiv_same in HPQ, HQR; apply equal_same in HPQ, HQR;
        eapply equal_transitive; eauto.
    Qed.



(** leq (Partial order)
 **
 ** Set of attack graphs P is less than or equal to Q (i.e., P \leq Q)
 ** if and only if P supports Q under the preceq relation. *)

    Definition leq (P Q : list (attackgraph components)) : Prop :=
        supports preceq P Q.

    Hint Unfold leq : core.

    Definition leq_fix (P Q : list (attackgraph components)) : Prop :=
        supports_fix preceq_fix preceqDec P Q.


    Lemma leq_same : forall P Q,
        leq_fix P Q <->
        leq P Q.
    Proof.
        intros P Q; split; intros HLeq; 
        [ apply supports_same in HLeq | apply supports_same ]; 
        intros B HIn; apply HLeq in HIn; destruct HIn as [A];
        exists A; [ rewrite <- preceq_same | rewrite preceq_same ]; auto.
    Qed.

    Lemma leqDec : forall P Q,
        {leq_fix P Q} + {~ leq_fix P Q}.
    Proof.
        intros; apply supportsDec.
    Defined.


    Theorem leq_reflexive : forall P Q,
        equiv P Q ->
        leq P Q.
    Proof.
        intros P Q HEq B HIn;
        apply equiv_same in HEq; apply equal_same in HEq; destruct HEq as [HPQ HQP];
        remember (min_fix prec_fix precDec P P) as P'; remember (min_fix prec_fix precDec Q Q) as Q';
        symmetry in HeqP', HeqQ'; apply min_same in HeqP', HeqQ';
        assert (forall (A B C : attackgraph components), prec_fix A B -> prec_fix B C -> prec_fix A C) as HTrans
          by (intros; rewrite prec_same; eapply prec_transitive; rewrite <- prec_same; eauto);
        pose proof (min_spoeq prec_fix HTrans Q Q Q' HeqQ' B HIn) as H;
        destruct H as [A' H]; destruct H as [HIn' H];
        apply HPQ in HIn'; destruct HIn' as [A HIn']; destruct HIn';
        exists A; split;
        [ eapply min_in; eauto | ];
        apply preceq_correct; destruct H; 
        [ left; rewrite prec_same in H; eapply prec_simeq1 
        | right; subst ]; eauto.
    Qed.

    Theorem leq_transitive : forall P Q R,
        leq P Q ->
        leq Q R ->
        leq P R.
    Proof.
        intros P Q R HST HTU; eapply supports_transitive; eauto; apply preceq_transitive.
    Qed.


    Lemma min_leq1 : forall P P',
        min_ind prec P P P' ->
        leq P' P.
    Proof.
        intros P P' HMin B HIn;
        pose proof (min_spoeq prec prec_transitive P P P' HMin B HIn) as HPreceq;
        destruct HPreceq as [G HPreceq]; destruct HPreceq;
        exists G; split; auto; apply preceq_preceq; auto.
    Qed.

    Lemma min_leq2 : forall P P',
        min_ind prec P P P' ->
        leq P P'.
    Proof.
        intros P P' HMin B HIn; exists B; split;
        [ eapply min_in; eauto | apply preceq_reflexive; apply simeq_reflexive ].
    Qed.

    Lemma leq_min1 : forall P Q P',
        leq P Q ->
        min_ind prec P P P' ->
        leq P' Q.
    Proof.
        intros P Q P' HLeq HMin;
        apply min_leq1 in HMin;
        eapply leq_transitive; eauto.
    Qed.

    Lemma leq_min2 : forall P Q Q',
        leq P Q ->
        min_ind prec Q Q Q' ->
        leq P Q'.
    Proof.
        intros P Q Q' HLeq HMin B HIn; apply HLeq; eapply min_in; eauto.
    Qed.

    Theorem leq_antisymmetric : forall P Q,
        leq P Q ->
        leq Q P ->
        equiv P Q.
    Proof.
        intros P Q HLeqPQ HLeqQP. unfold equiv. intros P' Q' HMinP HMinQ.
        assert (leq P' Q') as HPQ by
        ( pose proof (min_leq1 P P' HMinP); pose proof (min_leq2 Q Q' HMinQ);
          eapply leq_transitive; eauto; eapply leq_transitive; eauto );
        assert (leq Q' P') as HQP by 
        ( pose proof (min_leq1 Q Q' HMinQ); pose proof (min_leq2 P P' HMinP);
          eapply leq_transitive; eauto; eapply leq_transitive; eauto );
        clear HLeqPQ HLeqQP; split;
        intros A' HIn; pose proof HIn as HIn';
        [ apply HPQ in HIn' | apply HQP in HIn' ];
        destruct HIn' as [B' HIn']; destruct HIn' as [HIn' HOrd];
        apply preceq_correct in HOrd; destruct HOrd.
        - exfalso; 
          apply HQP in HIn'; destruct HIn' as [A HIn']; destruct HIn' as [HIn' HOrd];
          apply preceq_correct in HOrd; destruct HOrd;
          [ assert (prec A A') as contra by (eapply prec_transitive; eauto)
          | assert (prec A A') as contra by (eapply prec_simeq1; eauto) ];
          assert (forall (A : attackgraph components), ~ prec A A) as prec_irreflexive
            by (intros; apply prec_irreflexive; apply simeq_reflexive);
          pose proof (min_minimal prec prec_irreflexive prec_asymmetric prec_transitive Q Q' HMinQ A' HIn) as HMin;
          eapply minimal_same in HMin; apply minimal_same' in HMin;
          unfold minimal, not in HMin;  
          eapply HMin; eauto; eapply min_in; eauto.
        - exists B'; auto.
        - exfalso; 
          apply HPQ in HIn'; destruct HIn' as [A HIn']; destruct HIn' as [HIn' HOrd];
          apply preceq_correct in HOrd; destruct HOrd;
          [ assert (prec A A') as contra by (eapply prec_transitive; eauto)
          | assert (prec A A') as contra by (eapply prec_simeq1; eauto) ];
          assert (forall (A : attackgraph components), ~ prec A A) as prec_irreflexive
            by (intros; apply prec_irreflexive; apply simeq_reflexive);
          pose proof (min_minimal prec prec_irreflexive prec_asymmetric prec_transitive P P' HMinP A' HIn) as HMin;
          eapply minimal_same in HMin; apply minimal_same' in HMin;
          unfold minimal, not in HMin;  
          eapply HMin; eauto; eapply min_in; eauto.
        - exists B'; auto.
        Unshelve.
        intros x y; pose proof (precDec x y) as HPrecDec; destruct HPrecDec; [left|right]; rewrite <- prec_same; auto.
        intros x y; pose proof (precDec x y) as HPrecDec; destruct HPrecDec; [left|right]; rewrite <- prec_same; auto.
        intros x y; pose proof (precDec x y) as HPrecDec; destruct HPrecDec; [left|right]; rewrite <- prec_same; auto.
        intros x y; pose proof (precDec x y) as HPrecDec; destruct HPrecDec; [left|right]; rewrite <- prec_same; auto.
    Qed.


End SetOrdering. 