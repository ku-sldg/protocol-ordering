Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.

Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.
Require Import AttestationProtocolOrdering.utilities.mset.
Require Import AttestationProtocolOrdering.utilities.permute.


Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.attackgraph_adversary.


Section AdversaryOrdering. 
    Context {components : Type}.
    
(** Time-contraint tagged adversary event label *)
    Inductive tauTaggedLabel (component : Type) : Type :=
    | tauTag : advLabel component -> tauTaggedLabel component
    | blankTag : advLabel component -> tauTaggedLabel component.


    (* \ell^\tau *)
    Definition myLabelTagged {A : attackgraph components} (ev : myEvent A) : option (tauTaggedLabel components) := 
        match (myLabel A ev) with
        | inr adv => if In_dec (myEqDec_event A) ev (tau A)
                     then Some (tauTag _ adv)
                     else if In_dec (myEqDec_event A) ev (pi A)
                          then Some (blankTag _ adv)
                          else None
        | inl _ => None
        end.

    Lemma myLabelTagged_some : forall A ev,
        In ev (pi A) <->
        exists l', myLabelTagged ev = Some l'.
    Proof.
        unfold myLabelTagged; intros A ev; split; intros H.
        - remember (myLabel A ev) as l; destruct l as [meas|adv].
        -- apply pi_fact in H; destruct H as [HIn Hl]; destruct Hl as [adv Hl];
           rewrite Hl in Heql; inversion Heql.
        -- destruct (in_dec (myEqDec_event A) ev (tau A)); eauto; 
           destruct (in_dec (myEqDec_event A) ev (pi A)); eauto; 
           contradiction.
        - destruct (myLabel A ev); destruct H as [l' H];
          [inversion H; fail|];
          destruct (in_dec (myEqDec_event A) ev (tau A));
          [apply tau_pi; auto|];
          destruct (in_dec (myEqDec_event A) ev (pi A)); 
          auto; inversion H.
    Qed.

    Lemma myLabelTagged_none : forall A ev,
        ~ In ev (pi A) <->
        myLabelTagged ev = None.
    Proof.
        unfold myLabelTagged; intros A ev; split; intros H.
        - remember (myLabel A ev) as l; destruct l as [meas|adv]; auto.
          destruct (in_dec (myEqDec_event A) ev (tau A)) as [Ht|Ht].
        -- apply tau_pi in Ht; contradiction.
        -- destruct (in_dec (myEqDec_event A) ev (pi A)); auto; contradiction.
        - remember (myLabel A ev) as l; destruct l as [meas|adv].
        -- intros contra. apply pi_fact in contra. destruct contra as [HEdge [adv Hl]].
           rewrite <- Heql in Hl. inversion Hl.
        -- destruct (in_dec (myEqDec_event A) ev (tau A)).
        --- inversion H.
        --- destruct (in_dec (myEqDec_event A) ev (pi A)); auto. inversion H.
    Qed.

    (** Multiset of tau-tagged adversary event labels *)
    Definition ttlPi (A : attackgraph components) :=
        map myLabelTagged (pi A).


    Lemma myEqDec_ttl : forall (A : attackgraph components),
        forall (x y : tauTaggedLabel components),
        {x = y} + {x <> y}.
    Proof.
        intros A x y. destruct x as [adv|adv], y as [adv'|adv'];
        destruct (myEqDec_advLabel A adv adv'); subst;
        auto; right; intros contra; inversion contra; contradiction.
    Defined.

    Lemma eqDec_option : forall {X : Type},
        (forall (x y : X), {x = y} + {x <> y}) ->
        forall (o p : option X), {o = p} + {o <> p}.
    Proof.
        intros X eqDec_X o p; destruct o as [x|], p as [y|];
        try (destruct (eqDec_X x y); subst);
        auto; right; intros contra; inversion contra; contradiction.
    Defined.

    Lemma eqLift_Some : forall {X : Type} (x1 x2 : X),
        Some x1 = Some x2 <-> x1 = x2.
    Proof.
        intros X x1 x2; split; intros H;
        [inversion H|]; subst; auto.
    Qed.

    Definition myLabelTagged_option {A : attackgraph components} (ev : option (myEvent A)) : option (tauTaggedLabel components) := 
    match ev with
    | Some ev' => myLabelTagged ev'
    | None => None
    end.

(** Partial order over time-contraint tagged adversary event labels *)
    Context {trianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop}.
    Context {trianglelefteqDec : forall l1 l2, {trianglelefteq l1 l2} + {~ trianglelefteq l1 l2}}.
    Context {trianglelefteq_tau : forall l, trianglelefteq (blankTag _ l) (tauTag _ l)}.
    Context {trianglelefteq_reflexive : forall l, trianglelefteq l l}.
    Context {trianglelefteq_antisymmetric : forall l1 l2, trianglelefteq l1 l2 -> trianglelefteq l2 l1 -> l1 = l2}.
    Context {trianglelefteq_transitive : forall l1 l2 l3, trianglelefteq l1 l2 -> trianglelefteq l2 l3 -> trianglelefteq l1 l3}.
    
    Definition trianglelefteq_option (l1 l2 : option (tauTaggedLabel components)) : Prop :=
    match l1, l2 with
    | Some l1', Some l2' => trianglelefteq l1' l2'
    | None, _ => True
    | _, _ => False
    end.

    Lemma trianglelefteqOptionDec : forall l1 l2, 
        {trianglelefteq_option l1 l2} + {~ trianglelefteq_option l1 l2}.
    Proof.
        destruct l1, l2; simpl; auto.
    Defined.


    Lemma trianglelefteqOption_reflexive : forall l, 
        trianglelefteq_option l l.
    Proof.
        destruct l; simpl; auto.
    Qed.

    Lemma trianglelefteqOption_antisymmetric : forall l1 l2,
        trianglelefteq_option l1 l2 ->
        trianglelefteq_option l2 l1 ->
        l1 = l2.
    Proof.
        intros l1 l2 H12 H21; destruct l1, l2;
        simpl in *; auto; try contradiction.
        apply eqLift_Some; auto.
    Qed.

    Lemma trianglelefteqOption_transitive : forall l1 l2 l3, 
        trianglelefteq_option l1 l2 -> 
        trianglelefteq_option l2 l3 -> 
        trianglelefteq_option l1 l3.
    Proof.
        destruct l1, l2, l3; simpl; eauto;
        intros; try contradiction.
    Qed.

    Lemma trianglelefteq_Forall : forall (A B : attackgraph components) (f : list (eventT A * eventT B)),
        (forall ev, trianglelefteq_option (myLabelTagged ev) (myLabelTagged_option (find (myEqDec_event A) f ev))) <->
        Forall (fun ev => trianglelefteq_option (myLabelTagged ev) (myLabelTagged_option (find (myEqDec_event A) f ev))) (pi A).
    Proof.
        intros A B f; rewrite Forall_forall; split; intros H.
        - intros; apply H.
        - intros ev; destruct (in_dec (myEqDec_event A) ev (pi A)) as [HIn|HNIn].
        -- apply H; auto.
        -- unfold trianglelefteq_option; apply myLabelTagged_none in HNIn;
           rewrite HNIn; auto.
    Qed.

End AdversaryOrdering.
