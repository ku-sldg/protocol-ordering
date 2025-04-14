Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.attackgraph_adversary.
Require Import AttestationProtocolOrdering.attackgraph_ordering.


(** Given a set of attack graphs P and an attack graph A,
 ** find an attack graph in P that is less than A and
 ** minimal with respect to P.
 **
 ** Follow a chain of attack graphs in P such that
 ** A > A' > A'' > ... > some minimal element. *)

Section Minimization. 
  Context {components : Type}.


(** minimal
 ** 
 ** An element A is minimal with respect to a set P
 ** if and only if B is not strictly less than A for
 ** every B in P. *)

    Definition minimal (A : attackgraph components) P : Prop :=
        forall A', In A' P -> ~ prec A' A.

    Fixpoint minimal_fix (A : attackgraph components) P : Prop :=
    match P with
    | A' :: P' => if precDec A' A 
                  then False
                  else minimal_fix A P'
    | nil => True 
    end.

    Inductive minimal_ind A :
        list (attackgraph components) -> Prop :=
    | minimalCons : forall A' P',
        ~ prec A' A ->
        minimal_ind A P' ->
        minimal_ind A (A'::P')
    | minimalNil :
        minimal_ind A nil.

    Hint Unfold minimal : core.

    Lemma minimal_same : forall A P,
        minimal_fix A P <->  minimal_ind A P.
    Proof.
        intros A P; split; intros H.
        - induction P; constructor; simpl in H; destruct (precDec a A);
          try inversion H; 
          [ rewrite <- prec_same | ]; auto.
        - induction H; simpl; auto; destruct (precDec A' A);
          [ apply H; apply prec_same | ]; auto.
    Qed.

    Lemma minimal_same' : forall A P,
        minimal_fix A P <-> minimal A P.
    Proof.
        intros A P; split; intros H.
        - intros A' HIn; induction P;
          try (inversion HIn; fail);
          simpl in H; destruct (precDec a A);
          try inversion H; destruct HIn; subst;
          [ rewrite <- prec_same | apply IHP ]; auto.
        - induction P; simpl; auto; destruct (precDec a A).
        -- unfold minimal in H; unfold not in *; apply H with (A' := a); 
           simpl; auto; eapply prec_same; eauto.
        -- apply IHP; intros A' HIn; apply H; simpl; auto.
    Qed.
        



(** getMinimal
 ** 
 ** Gets an element A' such that A' is less than A 
 ** and A' is minimal with respect to P. *)

    Fixpoint getMinimal_fix A P : attackgraph components :=
    match P with
    | A' :: P' => if (precDec A' A)
                  then getMinimal_fix A' P'
                  else getMinimal_fix A P'
    | nil => A 
    end.

    Inductive getMinimal_ind : 
        attackgraph components -> list (attackgraph components) -> attackgraph components -> Prop :=
    | getMinimalPrec : forall A P' A' A'',
        prec A' A ->
        getMinimal_ind A' P' A'' ->
        getMinimal_ind A (A' :: P') A''
    | getMinimalNotPrec : forall A P' A' A'',
        ~ prec A' A ->
        getMinimal_ind A P' A'' ->
        getMinimal_ind A (A' :: P') A''
    | getMinimalNil : forall A,
        getMinimal_ind A nil A.


    Lemma getMinimal_same : forall A P A',
        getMinimal_fix A P = A' <->
        getMinimal_ind A P A'.
    Proof.
        intros A P A'; split; intros H.
        - generalize dependent A'; generalize dependent A; 
          induction P; intros; simpl in *;
          try (subst; apply getMinimalNil);
          destruct (precDec a A); apply IHP in H;
          [ apply getMinimalPrec | apply getMinimalNotPrec ]; auto;
          rewrite <- prec_same; auto.
        - induction H; simpl; subst; auto;
          destruct (precDec A' A) as [Hp|Hp]; auto;
          [ apply prec_same in H | apply prec_same in Hp ]; contradiction.
    Qed.


    Lemma getMinimal_preceq : forall A P A',
        getMinimal_ind A P A' ->
        preceq A' A.
    Proof.
        intros A P A' H; apply preceq_correct; 
        induction H; auto.
        - left; destruct IHgetMinimal_ind;
          [ eapply prec_transitive | eapply prec_simeq1 ]; eauto.
        - right; apply simeq_reflexive.
    Qed.


    Lemma getMinimal_minimal : forall A P A',
        getMinimal_ind A P A' ->
        minimal_ind A' P.
    Proof.
        intros A P A' H; induction H; constructor; auto;
        apply getMinimal_preceq in H0; apply preceq_correct in H0.
        - destruct H0; 
          [ apply prec_asymmetric 
          | apply prec_irreflexive; apply simeq_symmetric ]; 
          auto.
        - intros contra; apply H; destruct H0;
          [ eapply prec_transitive
          | eapply prec_simeq2 ]; 
          eauto.
    Qed.


    Lemma getMinimal_in : forall A P A',
        getMinimal_ind A P A' ->
        In A' P \/ A' = A.
    Proof.
        intros A P A' HMin; induction HMin; auto;
        destruct IHHMin; subst; simpl; auto.
    Qed.


(** min
 **
 ** Produces a set containing minimal attack graphs.
 **
 ** Furthermore, the nth element of min(P) is less
 ** than the nth element of P and is minimal with
 ** respect to P. *)

    Fixpoint min_fix Q P : list (attackgraph components) :=
    match P with
    | A'::P' => (getMinimal_fix A' Q) :: (min_fix Q P')
    | nil => nil
    end.

    Inductive min_ind Q :
        list (attackgraph components) -> list (attackgraph components) -> Prop :=
    | minCons : forall A' A'' P' P'',
        getMinimal_ind A' Q A'' ->
        min_ind Q P' P'' ->
        min_ind Q (A'::P') (A''::P'')
    | minNil : 
        min_ind Q nil nil.


    Lemma min_same : forall Q P P',
        min_fix Q P = P' <->
        min_ind Q P P'.
    Proof.
        intros Q P P'; split; intros H.
        - generalize dependent P'; induction P; intros;
          simpl in H; subst; constructor;
          [ apply getMinimal_same | apply IHP ]; auto.
        - induction H; simpl; auto;
          apply getMinimal_same in H; subst; auto.
    Qed.


    Lemma min_getMinimal' : forall Q P P',
        min_ind Q P P' ->
        forall A, In A P ->
        exists A', In A' P' /\ getMinimal_ind A Q A'.
    Proof.
        intros Q P P' HMin A HIn;
        induction HMin; inversion HIn; subst.
        -- exists A''; split; simpl; auto.
        -- apply IHHMin in H0; destruct H0 as [A''' H0]; destruct H0;
           exists A'''; split; simpl; auto.
    Qed.

    Lemma min_preceq : forall P P',
        min_ind P P P'->
        forall A, In A P ->
        exists A', In A' P' /\ preceq A' A.
    Proof.
        intros P P' HMin A HIn;
        pose proof (min_getMinimal' P P P' HMin A HIn) as H;
        destruct H as [A' H]; destruct H as [H H'];
        apply getMinimal_preceq in H';
        exists A'; split; auto.
    Qed.


    Lemma min_getMinimal : forall Q P P',
        min_ind Q P P' ->
        forall A', In A' P' ->
        exists A, In A P /\ getMinimal_ind A Q A'.
    Proof.
        intros Q P P' HMin A' HIn; induction HMin;
        try (inversion HIn; fail);
        destruct HIn as [|HIn]; subst;
        [ eexists; split; simpl; eauto 
        | apply IHHMin in HIn; destruct HIn as [A HIn]; destruct HIn;
          exists A; split; simpl; auto ].
    Qed.


    Lemma min_in : forall P P',
        min_ind P P P' ->
        forall A', In A' P' ->
        In A' P.
    Proof.
        intros P P' HMin A' HIn; eapply min_getMinimal in HMin; eauto;
        destruct HMin as [A HMin]; destruct HMin as [HMin HGet];
        apply getMinimal_in in HGet; destruct HGet; subst; auto.
    Qed.


    Lemma min_minimal : forall P P',
        min_ind P P P' ->
        forall A', In A' P' ->
        minimal_ind A' P.
    Proof.
        intros P P' HMin A' HIn';
        pose proof (min_getMinimal P P P' HMin A' HIn') as HGet;
        destruct HGet as [A HGet]; destruct HGet;
        eapply getMinimal_minimal; eauto.
    Qed.


End Minimization. 
