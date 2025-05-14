Require Import Coq.Lists.List.


Section Supports.

    Context {X : Type}.
    Context (rel : X -> X -> Prop).
    Context (relDec : forall (x y : X), {rel x y} + {~ rel x y}).
    Context (rel_transitive : forall (x y z : X),
                                rel x y ->
                                rel y z ->
                                rel x z).

    Definition supports (S T : list X) : Prop :=
        forall H, In H T ->
        exists G, In G S /\ rel G H.

    Hint Unfold supports : core.

    Lemma supports_reflexive : forall S, 
        (forall (x : X), rel x x) ->
        supports S S.
    Proof.
        intros S HRefl H HIn;
        exists H; split; auto.
    Qed.

    Lemma supports_transitive : forall S T U, 
        supports S T ->
        supports T U ->
        supports S U.
    Proof.
        intros S T U HST HTU u HIn;
        apply HTU in HIn; destruct HIn as [t HIn]; destruct HIn as [HIn];
        apply HST in HIn; destruct HIn as [s HIn]; destruct HIn;
        exists s; split; auto; eapply rel_transitive; eauto.
    Qed.

    Fixpoint getRelatedElement_fix (H : X) (S : list X) : Prop :=
    match S with 
    | G::S' => if relDec G H
               then True 
               else getRelatedElement_fix H S'
    | nil => False
    end.

    Lemma getRelatedElementDec : forall H S,
        {getRelatedElement_fix H S} + {~ getRelatedElement_fix H S}.
    Proof.
        intros H S; 
        induction S as [|G S']; simpl; auto;
        destruct (relDec G H); auto.
    Defined.

    Fixpoint supports_fix (S T : list X) : Prop :=
    match T with
    | H::T' => if (getRelatedElementDec H S)
               then supports_fix S T'
               else False
    | nil => True
    end.

    Lemma getRelatedElement_exists : forall H S,
        getRelatedElement_fix H S <->
        exists G, In G S /\ rel G H.
    Proof.
        intros H S; split; intros HRel.
        - induction S as [|G S']; simpl in HRel; try (inversion HRel; fail);
          destruct (relDec G H).
        -- exists G; split; simpl; auto.
        -- apply IHS' in HRel; destruct HRel as [G' HRel]; destruct HRel;
           exists G'; split; simpl; auto.
        - induction S as [|G S']; simpl; destruct HRel as [G' HRel]; destruct HRel as [HIn HOrd];
          try (inversion HIn; fail);
          destruct (relDec G H); auto;
          destruct HIn; subst; try contradiction;
          apply IHS'; exists G'; split; auto.
    Qed.


    Lemma supports_same : forall S T,
        supports_fix S T <->
        supports S T.
    Proof.
        intros S T; split; intros HSup.
        - intros G HIn; induction T as [|H T']; try (inversion HIn; fail);
          simpl in HSup; destruct (getRelatedElementDec H S);
          try (inversion HSup; fail);
          destruct HIn; subst;
          [ eapply getRelatedElement_exists | apply IHT' ]; eauto.
        - induction T as [|H T']; simpl; auto;
          destruct (getRelatedElementDec H S);
          [ apply IHT'; intros G HIn | apply n; apply getRelatedElement_exists ];
          apply HSup; simpl; auto.
    Qed.

    Lemma supportsDec : forall S T,
        {supports_fix S T} + {~ supports_fix S T}.
    Proof.
        intros S T; 
        induction T as [|H T']; simpl; auto;
        destruct (getRelatedElementDec H S); auto.
    Defined.

End Supports.
