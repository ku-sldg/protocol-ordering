Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.attackgraph_ordering.
Require Import AttestationProtocolOrdering.set_ordering.


Section ProtocolOrdering.
    Context {components : Type}.

    Context (trianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop).
    Context (trianglelefteqDec : forall l1 l2, {trianglelefteq l1 l2} + {~ trianglelefteq l1 l2}).
    Context (trianglelefteq_tau : forall l, trianglelefteq (blankTag _ l) (tauTag _ l)).
    Context (trianglelefteq_reflexive : forall l, trianglelefteq l l).
    Context (trianglelefteq_antisymmetric : forall l1 l2, trianglelefteq l1 l2 -> trianglelefteq l2 l1 -> l1 = l2).
    Context (trianglelefteq_transitive : forall l1 l2 l3, trianglelefteq l1 l2 -> trianglelefteq l2 l3 -> trianglelefteq l1 l3).

    Local Notation equivDec := (@equivDec components trianglelefteq trianglelefteqDec).
    Local Notation leqDec := (@leqDec components trianglelefteq trianglelefteqDec).

    Inductive orderT : Type :=
    | equiv : orderT
    | leq : orderT
    | geq : orderT
    | incomparable : orderT.


    Definition order_fix (P Q : list (attackgraph components)) : orderT :=
    if (equivDec P Q) then equiv else
    if (leqDec P Q)   then leq else
    if (leqDec Q P)   then geq else
                           incomparable.

(** Introduce orderT from leq *)

    Local Notation set_leq := (@set_ordering.leq components trianglelefteq).
    Local Notation set_equiv := (@set_ordering.equiv components trianglelefteq).
    Local Notation equiv_same := (@equiv_same components trianglelefteq trianglelefteqDec).
    Local Notation leq_same := (@leq_same components trianglelefteq trianglelefteqDec).
    Local Notation equiv_symmetric := (@equiv_symmetric components trianglelefteq trianglelefteqDec).
    Local Notation leq_reflexive := (@leq_reflexive components trianglelefteq trianglelefteqDec
        trianglelefteq_reflexive trianglelefteq_antisymmetric trianglelefteq_transitive).
    Local Notation leq_antisymmetric := (@leq_antisymmetric components trianglelefteq trianglelefteqDec
        trianglelefteq_reflexive trianglelefteq_antisymmetric trianglelefteq_transitive).
    Local Notation equiv_leq := (@equiv_leq components trianglelefteq trianglelefteqDec
        trianglelefteq_reflexive trianglelefteq_antisymmetric trianglelefteq_transitive).

    Lemma order_equiv_intro : forall P Q,
        set_leq P Q -> 
        set_leq Q P -> 
        order_fix P Q = equiv.
    Proof.
        intros P Q HPQ HQP; unfold order_fix.
        destruct (equivDec P Q) as [|HN]; auto.
        exfalso; apply HN; apply equiv_same; apply leq_antisymmetric; auto.
    Qed.

    Lemma order_leq_intro : forall P Q,
        set_leq P Q -> 
        ~ set_leq Q P -> 
        order_fix P Q = leq.
    Proof.
        intros P Q HPQ HQP; unfold order_fix.
        destruct (equivDec P Q) as [HE|].
        - exfalso; apply HQP; apply equiv_same in HE; apply equiv_leq in HE; destruct HE; auto.
        - destruct (leqDec P Q) as [|HN]; auto.
          exfalso; apply HN; apply leq_same; auto.
    Qed.

    Lemma order_geq_intro : forall P Q,
        ~ set_leq P Q -> 
        set_leq Q P -> 
        order_fix P Q = geq.
    Proof.
        intros P Q HPQ HQP; unfold order_fix.
        destruct (equivDec P Q) as [HE|].
        - exfalso; apply HPQ; apply equiv_same in HE; apply equiv_leq in HE; destruct HE; auto.
        - destruct (leqDec P Q) as [HL|]; [exfalso; apply HPQ; apply leq_same; auto|].
          destruct (leqDec Q P) as [|HN]; auto.
          exfalso; apply HN; apply leq_same; auto.
    Qed.

    Lemma order_incomparable_intro : forall P Q,
        ~ set_leq P Q -> 
        ~ set_leq Q P -> 
        order_fix P Q = incomparable.
    Proof.
        intros P Q HPQ HQP; unfold order_fix.
        destruct (equivDec P Q) as [HE|].
        - exfalso; apply HPQ; apply equiv_same in HE; apply equiv_leq in HE; destruct HE; auto.
        - destruct (leqDec P Q) as [HL|]; [exfalso; apply HPQ; apply leq_same; auto|].
          destruct (leqDec Q P) as [HL|]; [exfalso; apply HQP; apply leq_same; auto|].
          reflexivity.
    Qed.

End ProtocolOrdering.
