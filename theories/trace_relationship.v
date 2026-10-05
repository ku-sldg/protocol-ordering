Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.attackgraph_ordering.
Require Import AttestationProtocolOrdering.set_ordering.
Require Import AttestationProtocolOrdering.set_relationship.
Require Import AttestationProtocolOrdering.trace_ordering.


Section TraceRelationship.
    Context {components : Type}.

    Context {trianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop}.
    Context {trianglelefteqDec : forall l1 l2, {trianglelefteq l1 l2} + {~ trianglelefteq l1 l2}}.
    Context {trianglelefteq_tau : forall l, trianglelefteq (blankTag _ l) (tauTag _ l)}.
    Context {trianglelefteq_reflexive : forall l, trianglelefteq l l}.
    Context {trianglelefteq_antisymmetric : forall l1 l2, trianglelefteq l1 l2 -> trianglelefteq l2 l1 -> l1 = l2}.
    Context {trianglelefteq_transitive : forall l1 l2 l3, trianglelefteq l1 l2 -> trianglelefteq l2 l3 -> trianglelefteq l1 l3}.

    Local Notation equivDec := (@equivDec components trianglelefteq trianglelefteqDec).
    Local Notation leqDec := (@leqDec components trianglelefteq trianglelefteqDec).
    Local Notation order_fix := (@order_fix components trianglelefteq trianglelefteqDec).

    Local Notation equiv_same := (@equiv_same components trianglelefteq trianglelefteqDec).
    Local Notation leq_same := (@leq_same components trianglelefteq trianglelefteqDec).

    Local Notation tequivDec := (@tequivDec components trianglelefteq trianglelefteqDec).
    Local Notation tleqDec := (@tleqDec components trianglelefteq trianglelefteqDec).
    Local Notation tstarDec := (@tstarDec components trianglelefteq trianglelefteqDec).

    Local Notation tequiv_same := (@tequiv_same components trianglelefteq trianglelefteqDec).
    Local Notation tleq_same := (@tleq_same components trianglelefteq trianglelefteqDec).
    Local Notation tequiv_single := (@tequiv_single components trianglelefteq trianglelefteqDec
        trianglelefteq_reflexive trianglelefteq_antisymmetric trianglelefteq_transitive).
    Local Notation tleq_single := (@tleq_single components trianglelefteq).


(** torder_fix
 **
 ** order_fix for the clairvoyant adversary, over lists of traces. The
 ** boolean is tstar: true when the verdict holds no matter how likely
 ** each trace is. For equiv it needs tstar in both directions, which
 ** holds only when every trace of P and Q is equivalent to the same
 ** set of attack graphs. incomparable is never starred. *)

    Definition torder_fix (P Q : list (list (attackgraph components))) : orderT * bool :=
    if (tequivDec P Q) then (equiv, if (tstarDec P Q)
                                    then if (tstarDec Q P) then true else false
                                    else false) else
    if (tleqDec P Q)   then (leq, if (tstarDec P Q) then true else false) else
    if (tleqDec Q P)   then (geq, if (tstarDec Q P) then true else false) else
                            (incomparable, false).

    (* On protocols with one trace each, torder_fix agrees with order_fix. *)
    Theorem torder_fix_single : forall P Q,
        fst (torder_fix (P::nil) (Q::nil)) = order_fix P Q.
    Proof.
        intros P Q; unfold torder_fix, order_fix.
        destruct (tequivDec (P::nil) (Q::nil)) as [HTEq|HTEq], (equivDec P Q) as [HEq|HEq];
        rewrite tequiv_same, tequiv_single in HTEq; rewrite equiv_same in HEq;
        try contradiction; auto.
        destruct (tleqDec (P::nil) (Q::nil)) as [HTPQ|HTPQ], (leqDec P Q) as [HPQ|HPQ];
        rewrite tleq_same, tleq_single in HTPQ; rewrite leq_same in HPQ;
        try contradiction; auto.
        destruct (tleqDec (Q::nil) (P::nil)) as [HTQP|HTQP], (leqDec Q P) as [HQP|HQP];
        rewrite tleq_same, tleq_single in HTQP; rewrite leq_same in HQP;
        try contradiction; auto.
    Qed.

End TraceRelationship.