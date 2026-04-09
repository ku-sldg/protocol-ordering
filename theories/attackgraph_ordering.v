
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.

Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.
Require Import AttestationProtocolOrdering.utilities.mset.
Require Import AttestationProtocolOrdering.utilities.partialfun.
Require Import AttestationProtocolOrdering.utilities.map_po.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.attackgraph_adversary.


Section AttackGraphOrdering. 
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


(** simeq (Equivalence) *)

    Definition simeq (A B : attackgraph components) : Prop :=
        mSameset (eqDec_option (myEqDec_ttl A)) (ttlPi A) (ttlPi B).

    Definition simeq_fix (A B : attackgraph components) : Prop :=
        mSameset_fix (eqDec_option (myEqDec_ttl A)) (ttlPi A) (ttlPi B).

    Lemma simeq_same : forall A B,
        simeq_fix A B <-> simeq A B.
    Proof.
        intros A B. apply mSameset_same'.
    Qed.

    Lemma simeqDec : forall A B,
        {simeq_fix A B} + {~ simeq_fix A B}.
    Proof.
        intros A B; apply mSamesetDec.
    Defined.

    Lemma simeq_reflexive : forall A,
        simeq A A.
    Proof.
        intros A; apply mSameset_reflexive.
    Qed.

    Lemma simeq_symmetric : forall A B,
        simeq A B ->
        simeq B A.
    Proof.
        intros A B H; apply mSameset_symmetric; eapply mSameset_eqDec; eauto.
    Qed.

    Lemma simeq_transitive : forall A B C,
        simeq A B ->
        simeq B C ->
        simeq A C.
    Proof.
        intros A B C H H'; eapply mSameset_transitive; eapply mSameset_eqDec; eauto.
    Qed.







(** preceq (Partial Order) *)

    (** Mathematical Definition *)
    Definition preceq (A B : attackgraph components) (f : eventT A -> eventT B) : Prop :=
        (* Injective map f from pi(A) to pi(B) *)
        partialFunction f (pi A) (pi B) /\ partialInjective f (pi A) /\
        (* For every n in \pi(a), the tagged label of n is less than the tagged label of f(n) *)
        (forall ev, trianglelefteq_option (myLabelTagged ev) (myLabelTagged (f ev))).

    (** Inductive Definition *)
    Inductive preceqHelper_ind {A B : attackgraph components} :
        list (eventT A) -> list (eventT B) -> Prop :=
    | preceqCons : forall ev ev' pi pi', 
        In ev' pi' ->
        trianglelefteq_option (myLabelTagged ev) (myLabelTagged ev') ->
        preceqHelper_ind (pi) (remove (myEqDec_event B) ev' pi') ->
        preceqHelper_ind (ev :: pi) (pi')
    | preceqNil : forall pi',
        preceqHelper_ind nil pi'.

    Definition preceq_ind (A B : attackgraph components) :=
    preceqHelper_ind (pi A) (pi B).

    Lemma preceq_strong : forall A B,
        (exists f, preceq A B f) <->
        (exists f, partialFunction f (pi A) (pi B) /\ partialInjective f (pi A) /\  (forall ev, In ev (pi A) -> trianglelefteq_option (myLabelTagged ev) (myLabelTagged (f ev)))).
    Proof.
        intros A B; split; intros H; destruct H as [f [HfIn [HfInj HfTri]]];
        exists f; repeat split; auto.
        intros ev. destruct (in_dec (myEqDec_event A) ev (pi A)); auto.
        apply myLabelTagged_none in n. unfold trianglelefteq_option. rewrite n; auto.
    Qed.


    Lemma preceq_same : forall A B,
        inhabited (eventT B) ->
        (exists f, preceq A B f) <->
        preceq_ind A B.
    Proof.
        intros A B nmt_eventTB. split; intros H.
        - unfold preceq, preceq_ind in *.
          remember (pi A) as piA.
          assert (NoDup piA) as HNd by (rewrite HeqpiA; apply NoDup_nodup).
          clear HeqpiA.
          generalize dependent (pi B). induction piA as [|ev piA]; intros.
        -- apply preceqNil.
        -- destruct H as [f [HfIn [HfInj HfTri]]].
           apply preceqCons with (ev' := f ev).
        --- apply HfIn; simpl; auto.
        --- apply HfTri.
        --- inversion HNd; subst. apply IHpiA; auto.
            exists f. repeat split; auto.
        ---- intros e HeIn. apply in_in_remove.
        ----- intros contra. apply HfInj in contra; simpl; auto; subst. contradiction.
        ----- apply HfIn; simpl; auto.
        ---- apply partialInjective_incl with (xs:=ev::piA); auto.
             intros e HeIn; simpl; auto.
        - apply preceq_strong. unfold preceq_ind in *.
          remember (pi A) as piA.
          assert (NoDup piA) as HNd by (rewrite HeqpiA; apply NoDup_nodup).
          clear HeqpiA. induction H.
          -- inversion HNd; subst. apply IHpreceqHelper_ind in H5.
             clear IHpreceqHelper_ind.
             destruct H5 as [f [HfIn [HfInj HfTri]]].
             exists ( fun e => if (myEqDec_event A) ev e
                               then ev'
                               else f e).
           repeat split.
        --- intros e HeIn. destruct HeIn; subst.
        ---- destruct (myEqDec_event A e e); try contradiction. auto.
        ---- destruct (myEqDec_event A ev e); subst; try contradiction.
             apply HfIn in H2. apply in_remove in H2; destruct H2; auto.
        --- intros e1 e2 [HIn1 HIn2] HEq.
            destruct (myEqDec_event A ev e1), (myEqDec_event A ev e2); subst; auto.
        ---- exfalso. destruct HIn2 as [|HIn2]; subst; try contradiction.
             apply HfIn in HIn2. apply in_remove in HIn2; destruct HIn2; contradiction.
        ---- exfalso. destruct HIn1 as [|HIn1]; subst; try contradiction.
             apply HfIn in HIn1. apply in_remove in HIn1; destruct HIn1; contradiction.
        ---- destruct HIn1, HIn2; subst; try contradiction. apply HfInj; auto.
        --- intros e HeIn. destruct (myEqDec_event A ev e); subst;
            destruct HeIn; try contradiction; auto.
        -- destruct nmt_eventTB as [e']. exists (fun _ => e'). repeat split.
        --- intros e HeIn. inversion HeIn.
        --- intros e1 e2 [HIn1 HIn2]. inversion HIn1.
        --- intros ee HeIn. inversion HeIn.
    Qed.


    Lemma preceqDec' : forall A B,
        {preceq_ind A B} + {~ preceq_ind A B}.
    Proof.
        intros A B. unfold preceq_ind. 
        remember (pi B) as pi'. clear Heqpi'. generalize dependent pi'.
        induction (pi A) as [|ev pi]; intros.
        - left. apply preceqNil.
        - destruct (existsPDec (fun ev' => trianglelefteqOptionDec (myLabelTagged ev) (myLabelTagged ev')) pi') as [HE|HE].
        -- unfold existsP in HE.
      
           left. destruct HE as [ev' [HIn' HTri]].

           apply preceqCons with (ev':=ev'); auto.
           specialize IHpi with (remove (myEqDec_event B) ev' pi').
    
           
    Abort.


(** Preceq partial order *)

    Theorem preceq_transitive : forall A B C,
        (exists f, preceq A B f) ->
        (exists g, preceq B C g) ->
        (exists h, preceq A C h).
    Proof.
        intros A B C [f [HfIn [HfInj HfTri]]] [g [HgIn [HgInj HgTri]]].
        exists (fun e => g (f e)); repeat split.
        - intros e HeIn; auto.
        - intros e1 e2 [HIn1 HIn2]; auto.
        - intros e. eapply trianglelefteqOption_transitive; eauto.
    Qed.


    Theorem preceq_reflexive : forall A B,
        simeq A B ->
        (exists f, preceq A B f).
    Proof.
        unfold simeq.
        intros A B HS. apply preceq_same. rewrite mSameset_universe in HS.
        unfold preceq_ind, ttlPi in *.
        (*remember (pi A) as piA; clear HeqpiA.*)
        assert (NoDup (pi B)) as HNodupB 
        by (unfold pi; apply NoDup_nodup).
        assert (forall ev', In ev' (pi B) -> exists t, (myLabelTagged ev') = Some t) as HSome 
        by (intros; apply myLabelTagged_some; auto). 
        generalize dependent (pi B). induction (pi A) as [|ev piA]; intros piB; intros.
        - apply preceqNil.
        - pose proof (HS (myLabelTagged ev)) as HEq.
          remember (multiplicity_fix (eqDec_option (myEqDec_ttl A)) (myLabelTagged ev) (map myLabelTagged (ev :: piA))) as mEv.
          destruct mEv.
        -- exfalso. symmetry in HeqmEv; apply multiplicity_zero in HeqmEv.
           apply HeqmEv; simpl; auto.
        -- assert (le_fix 1 (S mEv)) as HIn by (simpl; auto).
           rewrite HEq in HIn; apply multiplicity_succ in HIn; apply in_map_iff in HIn; 
           destruct HIn as [ev' HIn]; destruct HIn as [Hl HIn];
           apply preceqCons with (ev':=ev'); auto.
        --- apply HSome in HIn; destruct HIn as [t HOption]; 
            rewrite <- Hl; rewrite HOption; simpl; auto.
        --- apply IHpiA.
        ---- apply mSameset_universe. split.
        ----- intros a' H; rewrite HeqmEv in HEq; simpl in HEq. 
             destruct (eqDec_option (myEqDec_ttl A) (myLabelTagged ev) (myLabelTagged ev)); subst;
             try contradiction;
             destruct (eqDec_option (myEqDec_ttl B) (myLabelTagged ev') a'); subst.
        ------ assert (multiplicity_fix (eqDec_option (myEqDec_ttl A)) (myLabelTagged ev') (map myLabelTagged piB) = S (multiplicity_fix (eqDec_option (myEqDec_ttl A)) (myLabelTagged ev') (map myLabelTagged (remove (myEqDec_event B) ev' piB))))
               as Hmult by (eapply multiplicity_map_eq; auto).
               rewrite <- Hl in HEq; rewrite <- HEq in Hmult;
               inversion Hmult; auto.
        ------ assert (multiplicity_fix (eqDec_option (myEqDec_ttl A)) a' (map myLabelTagged piB) = multiplicity_fix (eqDec_option (myEqDec_ttl A)) a' (map myLabelTagged (remove (myEqDec_event B) ev' piB)))
               as Hmult by (eapply multiplicity_map_neq; auto).
               rewrite <- Hmult; rewrite <- HS; simpl; auto.
               destruct (eqDec_option(myEqDec_ttl A) a' (myLabelTagged ev)); subst; 
               try contradiction; auto.
        ----- intros a' H. rewrite HeqmEv in HEq; simpl in HEq. 
              destruct (eqDec_option (myEqDec_ttl A) (myLabelTagged ev) (myLabelTagged ev)); subst;
              try contradiction.
              destruct (eqDec_option (myEqDec_ttl B) (myLabelTagged ev') a'); subst.
        ------ assert (multiplicity_fix (eqDec_option (myEqDec_ttl A)) (myLabelTagged ev') (map myLabelTagged piB) = S (multiplicity_fix (eqDec_option (myEqDec_ttl A)) (myLabelTagged ev') (map myLabelTagged (remove (myEqDec_event B) ev' piB))))
               as Hmult by (eapply multiplicity_map_eq; auto).
               rewrite <- Hl in HEq; rewrite <- HEq in Hmult;
               inversion Hmult; auto.
        ------ assert (multiplicity_fix (eqDec_option (myEqDec_ttl A)) a' (map myLabelTagged piB) = multiplicity_fix (eqDec_option  (myEqDec_ttl A)) a' (map myLabelTagged (remove (myEqDec_event B) ev' piB)))
               as Hmult by (eapply multiplicity_map_neq; auto).
               rewrite <- Hmult; rewrite <- HS; simpl; auto.
               destruct (eqDec_option (myEqDec_ttl A) a' (myLabelTagged ev)); subst; 
               try contradiction; auto.
        ---- intros. apply remove_nodup. auto.
        ---- intros ev'' H; apply HSome.
             apply in_remove in H; destruct H; auto.
    Qed.

    
    Theorem preceq_antisymmetric : forall A B,
        (exists f, preceq A B f) ->
        (exists g, preceq B A g) ->
        simeq A B.
    Proof.
        intros A B [f [HfIn [HfInj HfTri]]] [g [HgIn [HgInj HgTri]]].
        pose proof trianglelefteqOptionDec as trianglelefteqOptionDec.
        pose proof trianglelefteqOption_reflexive as trianglelefteqOption_reflexive.
        pose proof trianglelefteqOption_antisymmetric as trianglelefteqOption_antisymmetric.
        pose proof trianglelefteqOption_transitive as trianglelefteqOption_transitive.
        pose proof eqDec_event as eqDec_event.
        assert (NoDup (pi A)) as HaNd by apply NoDup_nodup.
        assert (NoDup (pi B)) as HbNd by apply NoDup_nodup.
        
        apply partialBijective_mSameset with (f:=f); auto.
        - repeat split; auto.
          apply cantorSchroderBernstein_finite with (g:=g); auto.
        - apply function_fixed with (po:=trianglelefteq_option) (g:=g) (ys:=pi B); auto.
    Qed.
     


    (** prec (Strict Partial Order) *)

    Definition prec (A B : attackgraph components) : Prop :=
        (exists f, preceq A B f) /\ ~ simeq A B.

    Lemma prec_irreflexive : forall A B,
        simeq A B ->
        ~ prec A B.
    Proof.
        intros A B HS [HP HNS]. contradiction.
    Qed.

    Lemma prec_asymmetric : forall A B,
        prec A B ->
        ~ prec B A.
    Proof.
        intros A B [HaP HaNS] [HbP HbNS].
        apply HaNS; apply preceq_antisymmetric; auto.
    Qed.

    Lemma prec_transitive : forall A B C,
        prec A B ->
        prec B C ->
        prec A C.
    Proof.
        intros A B C [HaP HaNS] [HbP HbNS]. split.
        - eapply preceq_transitive; eauto.
        - intros HS; apply HaNS.
          apply preceq_antisymmetric; auto.
          eapply preceq_transitive; eauto.
          apply preceq_reflexive; apply simeq_symmetric; auto.
    Qed.


End AttackGraphOrdering.

    
