Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.attackgraph_ordering.
Require Import AttestationProtocolOrdering.set_ordering.


Section ProtocolOrdering.
    Context {components : Type}.

    Context {trianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop}.
    Context {trianglelefteqDec : forall l1 l2, {trianglelefteq l1 l2} + {~ trianglelefteq l1 l2}}.
    Context {trianglelefteq_tau : forall l, trianglelefteq (blankTag _ l) (tauTag _ l)}.
    Context {trianglelefteq_reflexive : forall l, trianglelefteq l l}.
    Context {trianglelefteq_antisymmetric : forall l1 l2, trianglelefteq l1 l2 -> trianglelefteq l2 l1 -> l1 = l2}.
    Context {trianglelefteq_transitive : forall l1 l2 l3, trianglelefteq l1 l2 -> trianglelefteq l2 l3 -> trianglelefteq l1 l3}.

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

End ProtocolOrdering.
