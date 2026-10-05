Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.supports.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.attackgraph_ordering.
Require Import AttestationProtocolOrdering.set_ordering.


Section TraceOrdering. 
    Context {components : Type}.

(** Partial order over time-contraint tagged adversary event labels *)
    Context {trianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop}.
    Context {trianglelefteqDec : forall l1 l2, {trianglelefteq l1 l2} + {~ trianglelefteq l1 l2}}.
    Context {trianglelefteq_tau : forall l, trianglelefteq (blankTag _ l) (tauTag _ l)}.
    Context {trianglelefteq_reflexive : forall l, trianglelefteq l l}.
    Context {trianglelefteq_antisymmetric : forall l1 l2, trianglelefteq l1 l2 -> trianglelefteq l2 l1 -> l1 = l2}.
    Context {trianglelefteq_transitive : forall l1 l2 l3, trianglelefteq l1 l2 -> trianglelefteq l2 l3 -> trianglelefteq l1 l3}.

    Local Notation equiv := (@equiv components trianglelefteq).
    Local Notation leq := (@leq components trianglelefteq).
    Local Notation leq_fix := (@leq_fix components trianglelefteq trianglelefteqDec).

    Local Notation equiv_reflexive := (@equiv_reflexive components trianglelefteq trianglelefteqDec).
    Local Notation equiv_symmetric := (@equiv_symmetric components trianglelefteq trianglelefteqDec).
    Local Notation leqDec := (@leqDec components trianglelefteq trianglelefteqDec).
    Local Notation leq_same := (@leq_same components trianglelefteq trianglelefteqDec).
    Local Notation leq_reflexive := (@leq_reflexive components trianglelefteq trianglelefteqDec
        trianglelefteq_reflexive trianglelefteq_antisymmetric trianglelefteq_transitive).
    Local Notation leq_transitive := (@leq_transitive components trianglelefteq trianglelefteq_transitive).
    Local Notation leq_antisymmetric := (@leq_antisymmetric components trianglelefteq trianglelefteqDec
        trianglelefteq_reflexive trianglelefteq_antisymmetric trianglelefteq_transitive).

    Local Notation geq := (fun P Q => leq Q P).
    Local Notation geq_fix := (fun P Q => leq_fix Q P).
    Local Notation geqDec := (fun P Q => leqDec Q P).

(** tleq (Preorder / Partial Order)
 **
 ** Set of traces M is less than or equal to N (i.e., M \leq_T N) 
 ** if and only if M supports N under leq
 ** and N supports M under geq. *)
    Definition tleq (M N : list (list (attackgraph components))) : Prop :=
        supports leq M N /\ supports geq N M.

    Definition tleq_fix (M N : list (list (attackgraph components))) : Prop :=
        if (supportsDec leq_fix leqDec M N)
            then if (supportsDec geq_fix geqDec N M)
                 then True
                 else False
            else False.

    Lemma tleq_same : forall M N,
        tleq_fix M N <->
        tleq M N.
    Proof.
        unfold tleq_fix.
        intros M N; split; intros H.
        - destruct (supportsDec leq_fix leqDec M N) as [HMN|], (supportsDec geq_fix geqDec N M) as [HNM|];
          try (inversion H; fail).
          apply supports_same in HMN, HNM; split.
        -- intros Q HIn; apply HMN in HIn; destruct HIn as [P [HIn HLeq]]. 
           exists P; split; auto. apply leq_same; auto.
        -- intros P HIn; apply HNM in HIn; destruct HIn as [Q [HIn HLeq]].
           exists Q; split; auto. apply leq_same; auto.
        - destruct H as [HMN' HNM'];
          destruct (supportsDec leq_fix leqDec M N) as [HMN|HMN], (supportsDec geq_fix geqDec N M) as [HNM|HNM]; auto.
        -- apply HNM; apply supports_same; intros P HIn.
           apply HNM' in HIn; destruct HIn as [Q [HIn HLeq]].
           exists Q; split; auto. apply leq_same; auto.
        -- apply HMN; apply supports_same; intros Q HIn.
           apply HMN' in HIn; destruct HIn as [P [HIn HLeq]].
           exists P; split; auto. apply leq_same; auto.
        -- apply HMN; apply supports_same; intros Q HIn.
           apply HMN' in HIn; destruct HIn as [P [HIn HLeq]].
           exists P; split; auto. apply leq_same; auto.
    Qed.

    Lemma tleqDec : forall M N,
        {tleq_fix M N} + {~ tleq_fix M N}.
    Proof.
        unfold tleq_fix; intros M N.
        destruct (supportsDec leq_fix leqDec M N), (supportsDec geq_fix geqDec N M); auto.
    Defined.

    Lemma tleq_transitive : forall M N R,
        tleq M N ->
        tleq N R ->
        tleq M R.
    Proof.
        intros M N R [] []. 
        split; eapply supports_transitive; eauto;
        intros; eapply leq_transitive; eauto.
    Qed.

(** tequiv (Equivalence)
 **
 ** Set of traces M and N are equivalent (i.e., M \equiv_T N) 
 ** if and only if M \leq_T N and N leq_T M.
 ** This identifies traces with the same range. *)
    Definition tequiv (M N : list (list (attackgraph components))) : Prop :=
        tleq M N /\ tleq N M.
    
    Definition tequiv_fix (M N : list (list (attackgraph components))) : Prop :=
        if (tleqDec M N)
        then if (tleqDec N M)
             then True
             else False
        else False.

    Lemma tequiv_same : forall M N,
        tequiv_fix M N <->
        tequiv M N.
    Proof.
        unfold tequiv_fix; intros M N; split; intros H.
        - destruct (tleqDec M N) as [HPQ|HPQ], (tleqDec N M) as [HQP|HQP];
          try (inversion H; fail);
          rewrite tleq_same in HPQ, HQP; split; auto.
        - destruct (tleqDec M N) as [HPQ|HPQ], (tleqDec N M) as [HQP|HQP];
          auto; destruct H as [HPQ' HQP'];
          try apply HPQ; try apply HQP; apply tleq_same; auto.
    Qed.

    Lemma tequivDec : forall M N,
        {tequiv_fix M N} + {~ tequiv_fix M N}.
    Proof.
        unfold tequiv_fix; intros M N.
        destruct (tleqDec M N), (tleqDec N M); auto.
    Defined.

    Theorem tequiv_reflexive : forall M,
        tequiv M M.
    Proof.
        intros; repeat split; apply supports_reflexive;
        intros; apply leq_reflexive; apply equiv_reflexive.
    Qed.

    Theorem tequiv_symmetric : forall M N,
        tequiv M N ->
        tequiv N M.
    Proof.
        intros M N []; split; auto.
    Qed.

    Theorem tequiv_transitive : forall M N R,
        tequiv M N ->
        tequiv N R ->
        tequiv M R.
    Proof.
        intros M N R [] []; split;
        eapply tleq_transitive; eauto.
    Qed.



    Theorem tleq_reflexive : forall M N,
        tequiv M N ->
        tleq M N.
    Proof.
        intros M N []; auto.
    Qed.

    Theorem tleq_antisymmetric : forall M N,
        tleq M N ->
        tleq N M ->
        tequiv M N.
    Proof.
        intros; split; auto.
    Qed.

(** tstar (Likelihood independence)
 **
 ** Set of traces M is less than or equal to N independent of trace likelihood (i.e., M \equiv^\star_T N) 
 ** if and only if every trace in M is less than or equal to every trace of N. *)
    Definition tstar (M N : list (list (attackgraph components))) : Prop :=
        (M = nil <-> N = nil) /\
        forall P Q, In P M -> In Q N -> leq P Q.

    Definition tstar_fix (M N : list (list (attackgraph components))) : Prop :=
        match M, N with
        | nil, _::_ => False
        | _::_, nil => False
        | _, _ => forallP_fix (fun Q => forallPDec _ (fun P => leq_fix P Q) (fun P => leqDec P Q) M) N
        end.

    Lemma tstar_same : forall M N,
        tstar_fix M N <->
        tstar M N.
    Proof.
        unfold tstar_fix, tstar; intros M N; split; intros HStar.
        - destruct M, N; try contradiction;
          apply forallP_same' in HStar;
          split; try (split; intros; congruence);
          intros P Q HInP HInQ; apply leq_same; apply HStar; auto.
        - destruct HStar as [[HMN HNM] HStar]; destruct M, N;
          try (specialize (HMN eq_refl); inversion HMN; fail);
          try (specialize (HNM eq_refl); inversion HNM; fail);
          apply forallP_same'; intros Q HInQ P HInP; apply leq_same; apply HStar; auto.
    Qed.

    Lemma tstarDec : forall M N,
        {tstar_fix M N} + {~ tstar_fix M N}.
    Proof.
        unfold tstar_fix; intros M N.
        destruct (forallPDec _ _ (fun Q => forallPDec _ _ (fun P => leqDec P Q) M) N) as [HAll|HAll].
        - destruct M, N; auto;
          left; rewrite forallP_same'; auto.
        - destruct M, N; auto;
          right; rewrite forallP_same'; auto.
    Defined.

    Lemma tstar_tleq : forall M N,
        tstar M N ->
        tleq M N.
    Proof.
        intros M N [[HMN HNM] HStar]. 
        split; destruct M as [|P' M'], N as [|Q' N'];
        try (specialize (HMN eq_refl); inversion HMN; fail);
        try (specialize (HNM eq_refl); inversion HNM; fail);
        intros X HIn; try (inversion HIn; fail);
        eexists; split; simpl; eauto; apply HStar; simpl; auto.
    Qed.

    Theorem tleq_tstar1 : forall P N,
        tleq (P::nil) N ->
        tstar (P::nil) N.
    Proof.
        intros P N [HPQ HQP]; repeat split.
        - intros contra; inversion contra.
        - intros HEq; subst. destruct (HQP P) as [Q [HIn _]]; simpl; auto; inversion HIn.
        - intros P' Q HInP HInQ.
          apply HPQ in HInQ; destruct HInQ as [P'' [HIn HLeq]].
          destruct HInP as [HInP|HInP], HIn as [HIn|HIn]; subst; auto;
          try (inversion HInP; fail); try (inversion HIn; fail).
    Qed.

    Theorem tleq_tstar2 : forall Q M,
        tleq M (Q::nil) ->
        tstar M (Q::nil).
    Proof.
        intros Q M [HPQ HQP]; repeat split.
        - intros HEq; subst. destruct (HPQ Q) as [P [HIn _]]; simpl; auto; inversion HIn.
        - intros contra; inversion contra.
        - intros P Q' HInP HInQ.
          apply HQP in HInP; destruct HInP as [Q'' [HIn HLeq]].
          destruct HInQ as [HInQ|HInQ], HIn as [HIn|HIn]; subst; auto;
          try (inversion HInQ; fail); try (inversion HIn; fail).
    Qed.
        
    Theorem tleq_single : forall P Q,
        tleq (P::nil) (Q::nil) <->
        leq P Q.
    Proof.
        intros P Q; split; intros H.
        - apply (tleq_tstar1 P (Q::nil)); simpl; auto.
        - split; intros X HIn; destruct HIn as [|HIn]; try (inversion HIn; fail); subst;
          eexists; split; simpl; eauto.
    Qed.

    Theorem tequiv_single : forall P Q,
        tequiv (P::nil) (Q::nil) <->
        equiv P Q.
    Proof.
        intros  P Q; split; intros H.
        - destruct H as [HPQ HQP]; rewrite tleq_single in HPQ, HQP;
          apply leq_antisymmetric; auto.
        - split; apply tleq_single; apply leq_reflexive;
          [|apply equiv_symmetric]; auto.
    Qed.


    (* The clairvoyant ordering refines the schedule-controlling one.
     * If M \leq_T N, then M \leq N when the traces are pooled. 
     * Only the first half of tleq is needed. *)
    Theorem tleq_concat : forall M N,
        tleq M N ->
        leq (concat M) (concat N).
    Proof.
        intros M N [HPQ _] B HIn.
        apply in_concat in HIn; destruct HIn as [Q [HInQ HInB]].
        apply HPQ in HInQ; destruct HInQ as [P [HInP HLeq]].
        apply HLeq in HInB; destruct HInB as [A [HInA HPreceq]].
        exists A; split; auto; apply in_concat; exists P; auto. 
    Qed.

End TraceOrdering. 
