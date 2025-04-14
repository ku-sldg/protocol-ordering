
(*************************
 ** ATTACK GRAPH NORMALIZATION
 **
 ** Transforms an attack graph to contain only the
 ** events relevant to determining the difficulty
 ** of the adversary's attack.
 **
 ** An attack graph is in its normal form when
 ** all sequences of consecutive measurement
 ** events are reduced to a single measurement
 ** event and all remaining measurement events
 ** are renamed to a constant label. *)

Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.

Require Import AttestationProtocolOrdering.utilities.list_removeFirst.
Require Import AttestationProtocolOrdering.attackgraph.




Section Normalization.
    Context {components : Type}.


(** Edges have decidable equality. *)
    Lemma myEqDec_edge : forall (A : attackgraph components) (x y : eventT A * eventT A), {x = y} + {x <> y}.
    Proof.
        intros A e1 e2;
        destruct e1 as [ev1 ev1']; destruct e2 as [ev2 ev2'].
        destruct (myEqDec_event A ev1 ev2); destruct (myEqDec_event A ev1' ev2'); subst;
        try (left; auto; fail);
        right; intros contra; inversion contra; subst; auto.
    Defined.
    Lemma myEqDec_edges : forall (A : attackgraph components) (x y : edgesT A), {x = y} + {x <> y}.
    Proof.
        intros; apply list_eq_dec; apply myEqDec_edge.
    Defined.


(** replaceMeasEvent 
 ** 
 ** Replace all occurences of measurement event ev by ev' in edges. *)

    (** Fixpoint definition. *)
    Fixpoint replaceMeasEvent_fix {A : attackgraph components} ev ev' edges : 
        edgesT A :=
    match edges with
    | (ev1, ev2) :: edges' => 
        if (myEqDec_event A ev1 ev)
        then if (myEqDec_event A ev2 ev)
            then (ev', ev') :: replaceMeasEvent_fix ev ev' edges'
            else (ev', ev2) :: replaceMeasEvent_fix ev ev' edges'
        else if (myEqDec_event A ev2 ev)
            then (ev1, ev') :: replaceMeasEvent_fix ev ev' edges'
            else (ev1, ev2) :: replaceMeasEvent_fix ev ev' edges'
    | nil => edges
    end.

    (** Inductive definition. *)
    Inductive replaceMeasEvent_ind {A : attackgraph components} ev ev' : 
        edgesT A -> edgesT A -> Prop :=
    | replaceBoth : forall ev1 ev2 edges' reducedEdges',
        ev1 = ev ->
        ev2 = ev ->
        replaceMeasEvent_ind ev ev' edges' reducedEdges' ->
        replaceMeasEvent_ind ev ev' ((ev1, ev2) :: edges') ((ev', ev') :: reducedEdges')
    | replaceEv1 : forall ev1 ev2 edges' reducedEdges',
        ev1 = ev ->
        ev2 <> ev ->
        replaceMeasEvent_ind ev ev' edges' reducedEdges' ->
        replaceMeasEvent_ind ev ev' ((ev1, ev2) :: edges') ((ev', ev2) :: reducedEdges')
    | replaceEv2 : forall ev1 ev2 edges' reducedEdges',
        ev1 <> ev ->
        ev2 = ev ->
        replaceMeasEvent_ind ev ev' edges' reducedEdges' ->
        replaceMeasEvent_ind ev ev' ((ev1, ev2) :: edges') ((ev1, ev') :: reducedEdges')
    | replaceNone : forall ev1 ev2 edges' reducedEdges',
        ev1 <> ev ->
        ev2 <> ev ->
        replaceMeasEvent_ind ev ev' edges' reducedEdges' ->
        replaceMeasEvent_ind ev ev' ((ev1, ev2)::edges') ((ev1, ev2) :: reducedEdges')
    | replaceNil : 
        replaceMeasEvent_ind ev ev' nil nil.

    (** The fixpoint and inductive definitions are equivalent. *)
    Lemma replaceMeasEvent_same : forall A ev ev' edges reducedEdges,
        @replaceMeasEvent_fix A ev ev' edges = reducedEdges <->
        @replaceMeasEvent_ind A ev ev' edges reducedEdges.
    Proof.
        intros A ev ev' edges reducedEdges; split; intros H.
        - subst; induction edges; [apply replaceNil|];
          simpl; destruct a as [e1 e2].
          destruct (myEqDec_event A e1 ev);
          destruct (myEqDec_event A e2 ev);
          subst;
          [ apply replaceBoth 
          | apply replaceEv1
          | apply replaceEv2
          | apply replaceNone ];
          auto.
        - induction H; subst; simpl;
          try destruct (myEqDec_event A ev ev);
          try destruct (myEqDec_event A ev1 ev);
          try destruct (myEqDec_event A ev2 ev);
          subst; auto; contradiction.
    Qed.

    (** The length of edges is the same after replacing
     ** ev with ev'. *)
    Lemma replaceMeasEvent_length : forall A ev ev' edges reducedEdges,
        @replaceMeasEvent_ind A ev ev' edges reducedEdges ->
        length reducedEdges = length edges.
    Proof.
        intros A ev ev' edges reducedEdges H;
        induction H; auto; simpl; rewrite IHreplaceMeasEvent_ind; auto.
    Qed.

    (** If ev $\neq ev'$, then there are no occurences of 
     ** ev in edges after replacing ev with ev'. *)
     Lemma replaceMeasEvent_all : forall A ev ev' edges, ev <> ev' ->
        forall ev1 ev2, In (ev1, ev2) (@replaceMeasEvent_fix A ev ev' edges) ->
        ev <> ev1 /\ ev <> ev2.
    Proof.
        intros A ev ev' edges Neq ev1 ev2 HIn;
        induction edges; auto;
        destruct a as [e1 e2]; simpl in HIn;
        destruct (myEqDec_event A e1 ev);
        destruct (myEqDec_event A e2 ev);
        destruct HIn; subst;
        try (inversion H; subst); auto.
    Qed.




(** findConsecutiveMeasEvent 
 ** 
 ** Find consecutive measurement events. Then replace all
 ** occurences of the former measurement event by the latter. *)

    (** Fixpoint definition. *)
    Fixpoint findConsecutiveMeasEvent_fix {A : attackgraph components} allEdges edges :  
        edgesT A := 
    match edges with 
    | (ev1, ev2) :: edges' => match (myLabel A ev1) with 
                              | inl m1 => match (myLabel A ev2) with 
                                         (* if both m1 and m2 are measurement events then replace m1 with m2 *)
                                         | inl m2 => replaceMeasEvent_fix ev1 ev2 (removeFirst (myEqDec_edge A) (ev1, ev2) allEdges)
                                         | _ => findConsecutiveMeasEvent_fix allEdges edges'
                                         end
                              | _ => findConsecutiveMeasEvent_fix allEdges edges' 
                             end
    | nil => allEdges
    end.

    (** Inductive definition. *)
    Inductive findConsecutiveMeasEvent_ind {A : attackgraph components} allEdges :
        edgesT A -> edgesT A -> Prop :=
    | findMeas : forall ev1 ev2 m1 m2 edges' reducedEdges,
        myLabel A ev1 = inl m1 ->
        myLabel A ev2 = inl m2 ->
        replaceMeasEvent_ind ev1 ev2 (removeFirst (myEqDec_edge A) (ev1, ev2) allEdges) reducedEdges ->
        findConsecutiveMeasEvent_ind allEdges ((ev1, ev2) :: edges') reducedEdges
    | findAdv1 : forall ev1 ev2 adv edges' reducedEdges,
        myLabel A ev1 = inr adv ->
        findConsecutiveMeasEvent_ind allEdges edges' reducedEdges ->
        findConsecutiveMeasEvent_ind allEdges ((ev1, ev2) :: edges') reducedEdges
    | findAdv2 : forall ev1 ev2 adv edges' reducedEdges,
        myLabel A ev2 = inr adv ->
        findConsecutiveMeasEvent_ind allEdges edges' reducedEdges ->
        findConsecutiveMeasEvent_ind allEdges ((ev1, ev2) :: edges') reducedEdges
    | findNil :
        findConsecutiveMeasEvent_ind allEdges nil allEdges.


    (** The fixpoint and inductive definitions are equivalent. *)
    Lemma findConsecutiveMeasEvent_same : forall A allEdges edges reducedEdges,
        @findConsecutiveMeasEvent_fix A allEdges edges = reducedEdges <->
        @findConsecutiveMeasEvent_ind A allEdges edges reducedEdges.
    Proof.
        intros A allEdges edges reducedEdges; split; intros H.
        - subst; induction edges; simpl; [apply findNil|].
          destruct a as [e1 e2].
          remember (myLabel A e1) as l1; remember (myLabel A e2) as l2;
          destruct l1 as [m1 | adv1]; destruct l2 as [m2 | adv2].
        -- apply findMeas with (ev1:=e1) (ev2:=e2) (m1:=m1) (m2:=m2); auto.
           apply replaceMeasEvent_same; auto.
        -- eapply findAdv2; eauto.
        -- eapply findAdv1; eauto.
        -- eapply findAdv1; eauto.
        - induction H; simpl;
          try (destruct (myLabel A ev1); destruct (myLabel A ev2));
          auto; try (inversion H; inversion H0; fail).
          apply replaceMeasEvent_same; auto.
    Qed.


    (** If finding and replacing consecutive measurement events
     ** results in distinct edges, then the length of edges is
     ** one less after finding and replacing consecutive 
     ** measurement events. *)
    Lemma findConsecutiveMeasEvent_length : forall A allEdges edges reducedEdges,
        @findConsecutiveMeasEvent_ind A allEdges edges reducedEdges ->
        allEdges <> reducedEdges ->
        (exists l, l ++ edges = allEdges) ->
        length reducedEdges + 1 = length allEdges.
    Proof.
        intros A allEdges edges reducedEdges H Heq HApp;
        induction H.
        - apply replaceMeasEvent_length in H1; rewrite H1.
        apply removeFirst_lengthAdd. 
        destruct HApp as [l HApp]; rewrite <- HApp.
        apply in_or_app; right;
        left; auto.
        - apply IHfindConsecutiveMeasEvent_ind; auto. 
        destruct HApp as [l HApp]; rewrite <- HApp. 
        exists (l ++ ((ev1, ev2) :: nil)); rewrite <- app_assoc; auto.
        - apply IHfindConsecutiveMeasEvent_ind; auto. 
        destruct HApp as [l HApp]; rewrite <- HApp. 
        exists (l ++ ((ev1, ev2) :: nil)); rewrite <- app_assoc; auto.
        - exfalso; apply Heq; auto.
    Qed.


    (** If there are consecutive measurement events in edges,
     ** then finding and replacing consecutive measurement
     ** events results in distinct edges. *)
     Lemma findConsecutiveMeasEvent_more : forall A allEdges edges reducedEdges,
        edges <> nil ->
        ( forall ev1 ev2, In (ev1, ev2) edges ->
        exists m1 m2, myLabel A ev1 = inl m1 /\ myLabel A ev2 = inl m2) ->
        @findConsecutiveMeasEvent_ind A allEdges edges reducedEdges ->
        (exists l, l ++ edges = allEdges) ->
        allEdges <> reducedEdges.
    Proof.
        intros A allEdges edges reducedEdges HNil Hl H HApp; induction H.
        - destruct HApp as [l HApp]; subst.
        apply replaceMeasEvent_length in H1;
        rewrite removeFirst_lengthSub in H1.
        -- intros contra; apply listEq_length in contra;
            rewrite <- contra in H1; clear contra.
            rewrite length_app in H1; simpl in H1;
            rewrite <- plus_n_Sm in H1; simpl in H1;
            rewrite PeanoNat.Nat.sub_0_r in H1.
            pose proof (PeanoNat.Nat.neq_succ_diag_l (length l + length edges'));
            contradiction.
        -- apply in_or_app; right;
            left; auto.
        - specialize Hl with ev1 ev2.
        assert (In (ev1, ev2) ((ev1, ev2) :: edges')) as HIn.
        { simpl; auto. }
        apply Hl in HIn; clear Hl.
        destruct HIn as [m1 HIn]; destruct HIn as [m2 Hl];
        destruct Hl as [Hl1 Hl2]; rewrite Hl1 in H; inversion H.
        - specialize Hl with ev1 ev2.
        assert (In (ev1, ev2) ((ev1, ev2) :: edges')) as HIn.
        { simpl; auto. }
        apply Hl in HIn; clear Hl.
        destruct HIn as [m1 HIn]; destruct HIn as [m2 Hl];
        destruct Hl as [Hl1 Hl2]; rewrite Hl2 in H; inversion H.
        - exfalso; apply HNil; auto.
    Qed. 

    (** If there are no consecutive measurement events in edges,
     ** then finding and replacing consecutive measurement events
     ** results in no change. *)
    Lemma findConsecutiveMeasEvent_done : forall A allEdges edges reducedEdges,
        ( forall ev1 ev2, In (ev1, ev2) edges ->
          exists c, myLabel A ev1 = inr c \/ myLabel A ev2 = inr c ) ->
        @findConsecutiveMeasEvent_ind A allEdges edges reducedEdges ->
        allEdges = reducedEdges.
    Proof.
        intros A allEdges edges reducedEdges Hl H; induction H; auto;
        try (apply IHfindConsecutiveMeasEvent_ind;
            intros; apply Hl; simpl; auto; fail).
        pose proof (Hl ev1 ev2) as Hl'; clear Hl.
        assert (In (ev1, ev2) ((ev1, ev2) :: edges')) as HIn.
        { simpl; auto. }
        apply Hl' in HIn; clear Hl';
        destruct HIn as [c HIn];
        destruct HIn as [Hl|Hl].
        - rewrite H in Hl; inversion Hl.
        - rewrite H0 in Hl; inversion Hl.
    Qed.

    

    


(** reduce1 
 ** 
 ** A single iteration of the reduction process. *)

    (* Fixpoint definition. *)
    Definition reduce1_fix {A : attackgraph components} edges : 
        edgesT A :=
    findConsecutiveMeasEvent_fix edges edges.

    (** Inductive definiton. *)
    Definition reduce1_ind {A : attackgraph components} edges reducedEdges:
        Prop :=
    @findConsecutiveMeasEvent_ind A edges edges reducedEdges.

    Hint Unfold reduce1_fix : core.
    Hint Unfold reduce1_ind : core.

    (** The fixpoint and inductive definitions are equivalent. *)
    Lemma reduce1_same : forall A edges reducedEdges,
        reduce1_fix edges = reducedEdges <->
        @reduce1_ind A edges reducedEdges.
    Proof.
        intros; apply findConsecutiveMeasEvent_same.
    Qed.

    (** If reducing edges results in distinct edges, then the 
     ** length of edges is one less after reducing. *)
    Lemma reduce1_length : forall A edges reducedEdges,
        @reduce1_ind A edges reducedEdges ->
        edges <> reducedEdges ->
        length reducedEdges + 1 = length edges.
    Proof.
        intros A edges reducedEdges H HDiff; 
        inversion H; subst.
        - apply replaceMeasEvent_length in H2; rewrite H2.
         unfold removeFirst. 
          
         destruct (myEqDec_edge A (ev1, ev2) (ev1, ev2)) as [Heq|Heq].
        -- rewrite PeanoNat.Nat.add_1_r; auto.
        -- exfalso; apply Heq; auto.
        - eapply findConsecutiveMeasEvent_length; eauto.
        exists ((ev1,ev2)::nil); auto.
        - eapply findConsecutiveMeasEvent_length; eauto.
        exists ((ev1,ev2)::nil); auto.
        - exfalso; apply HDiff; auto.
    Qed.

    (** If there are consecutive measurement events in edges,
     ** then reducing results in distinct edges. *)
    Lemma reduce1_more : forall A edges reducedEdges,
        edges <> nil ->
        ( forall ev1 ev2, In (ev1, ev2) edges ->
          exists m1 m2, myLabel A ev1 = inl m1 /\ myLabel A ev2 = inl m2) ->
        @reduce1_ind A edges reducedEdges ->
        edges <> reducedEdges.
    Proof.
        intros; eapply findConsecutiveMeasEvent_more; eauto.
        exists nil; auto.
    Qed.

    (** If there are no consecutive measurement events in edges,
     ** then reducing results in no change. *)
    Lemma reduce1_done : forall A edges reducedEdges,
        ( forall ev1 ev2, In (ev1, ev2) edges ->
            exists c, myLabel A ev1 = inr c \/ myLabel A ev2 = inr c ) ->
        @reduce1_ind A edges reducedEdges ->
        edges = reducedEdges.
    Proof.
        intros; eapply findConsecutiveMeasEvent_done; eauto.
    Qed.

    

    

    



(** reduce 
 ** 
 ** The complete attack graph reduction procedure.
 ** Reduce all sequences of consecutive measurement
 ** events to only the final measurement event in
 ** the sequence. *)

    (** Fixpoint definition using fuel. *)
    Fixpoint reduce_option_fuel {A : attackgraph components} fuel edges : option (edgesT A) := 
    match fuel with
    | S fuel' => if (myEqDec_edges A (reduce1_fix edges) edges)
                then Some edges
                else reduce_option_fuel fuel' (reduce1_fix edges)
    | _ => None
    end.

    (** Initial fuel should be the length of edges plus one. *)
    Definition reduce_option {A : attackgraph components} edges : option (edgesT A) :=
        reduce_option_fuel (length edges + 1) edges.

    Hint Unfold reduce_option : core.

    (** Inductive definition using fixpoint definitions. *)
    Inductive reduce_fix {A : attackgraph components} : 
        edgesT A -> edgesT A -> Prop :=
    | reduceDone_fix : forall edges, 
        reduce1_fix edges = edges -> 
        reduce_fix edges edges
    | reduceMore_fix : forall edges normEdges, 
        reduce1_fix edges <> edges -> 
        reduce_fix (reduce1_fix edges) normEdges-> 
        reduce_fix edges normEdges. 

    (** Inductive definition using inductive definitions. *)
    Inductive reduce_ind {A : attackgraph components} : 
        edgesT A -> edgesT A -> Prop :=
    | reduceDone_ind : forall edges, 
        reduce1_ind edges edges -> 
        reduce_ind edges edges
    | reduceMore_ind : forall edges reducedEdges normEdges, 
        reduce1_ind edges reducedEdges ->  
        edges <> reducedEdges ->
        reduce_ind reducedEdges normEdges -> 
        reduce_ind edges normEdges. 


    (** The inductive using the fixpoint definitions and
     ** the inductive definition using the inductive 
     ** definitions are equivalent. *)
    Lemma reduce_same : forall A edges normEdges,
        reduce_fix edges normEdges <->
        @reduce_ind A edges normEdges.
    Proof.
        intros edges normEdges; split; intros H; induction H;
        econstructor; eauto; try (apply reduce1_same; auto; fail);
        apply reduce1_same in H; subst; auto.
    Qed.

    (** The fixpoint definition using fuel and the inductive
     ** definition are equivalent. *)
    Lemma reduce_same' : forall A edges normEdges,
        reduce_fix edges normEdges <->
        @reduce_option A edges = Some normEdges.
    Proof.
        autounfold. intros A edges normEdges; split; intros H.
        - induction H; destruct edges; simpl.
        -- auto.
           
        -- rewrite H; destruct (myEqDec_edges A (p::edges) (p::edges)) as [Heq|Heq]; auto.
           exfalso; apply Heq; auto.
        -- simpl in H; exfalso; apply H; auto.
        -- destruct (myEqDec_edges A (reduce1_fix (p::edges)) (p::edges)) as [Heq|Heq].
        --- exfalso; apply H; auto.
        --- pose proof (reduce1_length A (p::edges) (reduce1_fix (p::edges))) as Hl.
            assert (reduce1_ind (p::edges) (reduce1_fix (p::edges))) as HInd.
            { apply reduce1_same; auto. }
            apply Hl in HInd; auto; clear Hl Heq. 
            rewrite HInd in IHreduce_fix; rewrite <- IHreduce_fix.
            assert (length (p::edges) = length edges + 1) as Hl.
            { simpl; rewrite  PeanoNat.Nat.add_1_r; auto. }
            rewrite Hl; auto.        
        - remember (length edges) as l; generalize dependent edges; 
          induction l; intros.
        -- destruct edges.
        --- rewrite PeanoNat.Nat.add_1_r in H; simpl in H;
            autounfold in *; simpl in H;
            destruct (myEqDec_edges A nil nil) as [Heq|Heq].
        ---- inversion H; subst; apply reduceDone_fix; auto.
        ---- exfalso; apply Heq; auto.
        --- simpl in Heql; inversion Heql.
        -- simpl in H; destruct (myEqDec_edges A (reduce1_fix edges) edges) as [Heq|Heq].
        --- inversion H; subst; apply reduceDone_fix; auto.
        --- apply reduceMore_fix; auto.
            apply IHl; auto.
            remember (reduce1_fix edges) as reducedEdges.
            apply eq_sym in HeqreducedEdges; apply reduce1_same in HeqreducedEdges;
            apply reduce1_length in HeqreducedEdges; auto.
            rewrite <- Heql in HeqreducedEdges; apply eq_sym in HeqreducedEdges;
            rewrite PeanoNat.Nat.add_1_r in HeqreducedEdges;
            inversion HeqreducedEdges; auto.
    Qed.


    (** The reduction procedure terminates and therefore is an algorithm *)

    (** The fixpoint definition using fuel terminates. *)
    Lemma reduce_terminates' : forall A edges,
        exists normEdges, @reduce_option A edges = Some normEdges.
    Proof.
        autounfold; intros A edges; remember (length edges) as l;
        generalize dependent edges; induction l; intros; simpl.
        - destruct edges.
        -- exists nil; destruct (myEqDec_edges A (reduce1_fix nil) nil) as [Heq|Heq]; auto.
           exfalso; apply Heq; auto.
        -- simpl in Heql; inversion Heql.
        - destruct (myEqDec_edges A (reduce1_fix edges) edges) as [Heq|Heq]; eauto.
          apply IHl; remember (reduce1_fix edges) as reducedEdges;
          apply eq_sym in HeqreducedEdges; apply reduce1_same in HeqreducedEdges;
          apply reduce1_length in HeqreducedEdges; auto.
          rewrite <- Heql in HeqreducedEdges; apply eq_sym in HeqreducedEdges;
          rewrite PeanoNat.Nat.add_1_r in HeqreducedEdges;
          inversion HeqreducedEdges; auto.
    Qed.

    (** The inductive definition terminates. *)
    Theorem reduce_terminates : forall A edges,
        exists normEdges, @reduce_ind A edges normEdges.
    Proof.
        intros A edges;
        pose proof (reduce_terminates' A edges) as H;
        destruct H as [normEdges H];
        exists normEdges; apply reduce_same;
        apply reduce_same'; auto.
    Qed.

    (** The reduction procedure is deterministic *)
    Lemma reduce_deterministic : forall A x y z, 
        @reduce_fix A x y -> 
        @reduce_fix A x z -> 
        y = z.
    Proof.
        intros A x y z H;
        generalize dependent z;
        induction H; intros.
        + destruct H0; try contradiction; auto.
        + destruct H1; try contradiction; auto.
    Qed.
    
    (** The reduction procedure is transitive. *)
    Lemma reduce_transitive : forall A x y, 
        @reduce_fix A x y -> 
        forall z, reduce_fix y z -> 
        @reduce_fix A x z.
    Proof.
        intros A x y H; induction H; intros; auto;
        apply reduceMore_fix; auto.
    Qed.


(** constantMeasLabel
 ** 
 ** Rename all measurement events to a constant label. *)

    Definition constantMeasLabel {A : attackgraph components} ev : (measLabel components) + (advLabel components) := 
    match (myLabel A ev) with
    | inl m => inl (ms _)
    | inr a => inr a
    end.

    Hint Unfold constantMeasLabel : core.


(** normalizeAttackGraph
 ** 
 ** The complete attack graph normalization procedure. *)

    (** All sequences of consecutive measurement events
     ** are reduced to a single measurement event and
     ** all remaining measurement events are renamed to
     ** a constant label. *)
    Definition normalizeAttackGraph (A : attackgraph components): option (attackgraph components) := 
    match reduce_option (myEdges A) with
    | Some normEdges => Some {| event := myEvent A ;
                                edges := normEdges ;
                                label := constantMeasLabel ;
                                eqDec_event := myEqDec_event A ;
                                eqDec_component := myEqDec_component A |}
    | None => None
    end.

    Hint Unfold normalizeAttackGraph : core.

    (** Every attack graph has a normal form. *)
    Lemma normalizeAttackGraph_success : forall A,
        exists normAttack, normalizeAttackGraph A = Some normAttack.
    Proof.
        intros A;
        unfold normalizeAttackGraph;
        remember (reduce_option (myEdges A)) as normEdges;
        destruct normEdges; eauto.
        pose proof (reduce_terminates' A (myEdges A)) as H;
        destruct H as [normEdges H].
        assert (None = Some normEdges) as contra.
        { rewrite HeqnormEdges; rewrite <- H; auto. } 
        inversion contra.
    Qed.


End Normalization.