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
 ** holds only when every trace of M and N is equivalent to the same
 ** set of attack graphs. incomparable is never starred. *)

    Definition torder_fix (M N : list (list (attackgraph components))) : orderT * bool :=
    if (tequivDec M N) then (equiv, if (tstarDec M N)
                                    then if (tstarDec N M) then true else false
                                    else false) else
    if (tleqDec M N)   then (leq, if (tstarDec M N) then true else false) else
    if (tleqDec N M)   then (geq, if (tstarDec N M) then true else false) else
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

(** Introduce orderT * bool from tleq and tstar *)
    
    Local Notation tleq := (@tleq components trianglelefteq).
    Local Notation tstar := (@tstar components trianglelefteq).
    Local Notation tstar_same := (@tstar_same components trianglelefteq trianglelefteqDec).

    Lemma torder_equiv_intro : forall M N b1 b2,
        tleq M N -> 
        tleq N M ->
        (b1 = true -> tstar M N) -> (b1 = false -> ~ tstar M N) ->
        (b2 = true -> tstar N M) -> (b2 = false -> ~ tstar N M) ->
        torder_fix M N = (equiv, andb b1 b2).
    Proof.
        intros M N b1 b2 HMN HNM H1T H1F H2T H2F; unfold torder_fix.
        destruct (tequivDec M N) as [|HN]; [|exfalso; apply HN; apply tequiv_same; split; auto].
        destruct (tstarDec M N) as [H1|H1], (tstarDec N M) as [H2|H2];
        rewrite tstar_same in H1, H2; destruct b1, b2; simpl; auto; exfalso;
        try apply (H1F eq_refl H1); 
        try apply (H2F eq_refl H2);
        try (apply H1; apply H1T; reflexivity);
        try (apply H2; apply H2T; reflexivity).
    Qed.

    Lemma torder_leq_intro : forall M N b,
        tleq M N -> 
        ~ tleq N M ->
        (b = true -> tstar M N) -> (b = false -> ~ tstar M N) ->
        torder_fix M N = (leq, b).
    Proof.
        intros M N b HMN HNM HT HF; unfold torder_fix.
        destruct (tequivDec M N) as [HE|]; [rewrite tequiv_same in HE; destruct HE; contradiction|].
        destruct (tleqDec M N) as [|HN]; [|exfalso; apply HN; apply tleq_same; auto].
        rewrite (tstar_bool M N b HT HF); reflexivity.
    Qed.

    Lemma torder_geq_intro : forall M N b,
        ~ tleq M N -> 
        tleq N M ->
        (b = true -> tstar N M) -> (b = false -> ~ tstar N M) ->
        torder_fix M N = (geq, b).
    Proof.
        intros M N b HMN HNM HT HF; unfold torder_fix.
        destruct (tequivDec M N) as [HE|]; [rewrite tequiv_same in HE; destruct HE; contradiction|].
        destruct (tleqDec M N) as [HL|]; [rewrite tleq_same in HL; contradiction|].
        destruct (tleqDec N M) as [|HN]; [|exfalso; apply HN; apply tleq_same; auto].
        rewrite (tstar_bool N M b HT HF); reflexivity.
    Qed.

    Lemma torder_incomparable_intro : forall M N,
        ~ tleq M N -> 
        ~ tleq N M ->
        torder_fix M N = (incomparable, false).
    Proof.
        intros M N HMN HNM; unfold torder_fix.
        destruct (tequivDec M N) as [HE|]; [rewrite tequiv_same in HE; destruct HE; contradiction|].
        destruct (tleqDec M N) as [HL|]; [rewrite tleq_same in HL; contradiction|].
        destruct (tleqDec N M) as [HL|]; [rewrite tleq_same in HL; contradiction|].
        reflexivity.
    Qed.

End TraceRelationship.