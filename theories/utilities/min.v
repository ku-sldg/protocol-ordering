Require Import Coq.Lists.List.

(** Given a set of attack graphs P and an attack graph A,
 ** find an attack graph in P that is less than A and
 ** minimal with respect to P.
 **
 ** Follow a chain of attack graphs in P such that
 ** A > A' > A'' > ... > some minimal element. *)

Section Min. 

    Context {X : Type}.
    Context (spo : X -> X -> Prop).
    Context (spoDec : forall (x y : X), 
                                {spo x y} + {~ spo x y}).
    Context (spo_irreflexive : forall (x : X), 
                                ~ spo x x).
    Context (spo_asymmetric : forall (x y : X),
                                spo x y ->
                                ~ spo y x).
    Context (spo_transitive : forall (x y z : X),
                                spo x y ->
                                spo y z ->
                                spo x z).


(** minimal
 ** 
 ** An element x is minimal with respect to a set S
 ** if and only if y is not strictly less than x for
 ** every y in S. *)

    Definition minimal (x : X) (S : list X) : Prop :=
        forall y, In y S -> ~ spo y x.

    Fixpoint minimal_fix (x : X) (S : list X) : Prop :=
    match S with
    | x' :: S' => if spoDec x' x 
                  then False
                  else minimal_fix x S'
    | nil => True 
    end.

    Inductive minimal_ind (x : X) : list X -> Prop :=
    | minimalCons : forall x' S',
        ~ spo x' x ->
        minimal_ind x S' ->
        minimal_ind x (x'::S')
    | minimalNil :
        minimal_ind x nil.

    Lemma minimal_same : forall x S,
        minimal_fix x S <->  minimal_ind x S.
    Proof.
        intros x S; split; intros H.
        - induction S as [|x' S']; constructor; simpl in H; destruct (spoDec x' x);
          try inversion H; auto.
        - induction H; simpl; auto; destruct (spoDec x' x);
          [apply H|]; auto.
    Qed.

    Lemma minimal_same' : forall x S,
        minimal_fix x S <-> minimal x S.
    Proof.
        intros x S; split; intros H.
        - intros y HIn; induction S as [|x' S'];
          try (inversion HIn; fail);
          simpl in H; destruct (spoDec x' x);
          try inversion H; destruct HIn; subst;
          [|apply IHS']; auto.
        - induction S as [|x' S']; simpl; auto; destruct (spoDec x' x).
        -- unfold minimal in H; unfold not in *; apply H with (y := x'); 
           simpl; auto.
        -- apply IHS'; intros y HIn; apply H; simpl; auto.
    Qed.
        



(** getMinimal
 ** 
 ** Gets an element x'' such that x'' is less than x
 ** and x'' is minimal with respect to S. *)

    Fixpoint getMinimal_fix (x : X) (S : list X) : X :=
    match S with
    | x' :: S' => if (spoDec x' x)
                  then getMinimal_fix x' S'
                  else getMinimal_fix x S'
    | nil => x
    end.

    Inductive getMinimal_ind : X -> list X -> X -> Prop :=
    | getMinimalOrd : forall x S' x' x'',
        spo x' x ->
        getMinimal_ind x' S' x'' ->
        getMinimal_ind x (x' :: S') x''
    | getMinimalNotOrd : forall x S' x' x'',
        ~ spo x' x ->
        getMinimal_ind x S' x'' ->
        getMinimal_ind x (x' :: S') x''
    | getMinimalNil : forall x,
        getMinimal_ind x nil x.


    Lemma getMinimal_same : forall x S x'',
        getMinimal_fix x S = x'' <->
        getMinimal_ind x S x''.
    Proof.
        intros x S x''; split; intros H.
        - generalize dependent x''; generalize dependent x; 
          induction S as [|x' S']; intros; simpl in *;
          try (subst; apply getMinimalNil);
          destruct (spoDec x' x); apply IHS' in H;
          [ apply getMinimalOrd | apply getMinimalNotOrd ]; auto.
        - induction H; simpl; subst; auto;
          destruct (spoDec x' x) as [Hp|Hp]; auto; contradiction.
    Qed.

    Lemma getMinimal_spoeq : forall x S x'',
        getMinimal_ind x S x'' ->
        spo x'' x \/ x'' = x.
    Proof.
        intros x S x'' H;
        induction H; auto;
        left; destruct IHgetMinimal_ind;
        [eapply spo_transitive|]; subst; eauto.
    Qed.


    Lemma getMinimal_minimal : forall x S x'',
        getMinimal_ind x S x'' ->
        minimal_ind x'' S.
    Proof.
        intros x S x'' H; 
        induction H; constructor; auto; apply getMinimal_spoeq in H0; auto.
        - destruct H0; subst;
          [ apply spo_asymmetric; auto
          | apply spo_irreflexive ].
        - intros contra; apply H; destruct H0; subst;
          [eapply spo_transitive|]; eauto.
    Qed.


    Lemma getMinimal_in : forall x S x'',
        getMinimal_ind x S x'' ->
        In x'' S \/ x'' = x.
    Proof.
        intros x S x'' H; induction H; auto;
        destruct IHgetMinimal_ind; subst; simpl; auto.
    Qed.


(** min
 **
 ** Produces a set containing minimal elements.
 **
 ** Furthermore, the nth element of min(P) is less
 ** than the nth element of P and is minimal with
 ** respect to P. *)

    Fixpoint min_fix (SS S : list X) : list X :=
    match S with
    | x' :: S' => (getMinimal_fix x' SS) :: (min_fix SS S')
    | nil => nil
    end.

    Inductive min_ind (SS : list X) : list X -> list X -> Prop :=
    | minCons : forall x' x'' S' S'',
        getMinimal_ind x' SS x'' ->
        min_ind SS S' S'' ->
        min_ind SS (x'::S') (x''::S'')
    | minNil : 
        min_ind SS nil nil.


    Lemma min_same : forall SS S S'',
        min_fix SS S = S'' <->
        min_ind SS S S''.
    Proof.
        intros SS S S''; split; intros H.
        - generalize dependent S''; induction S; intros;
          simpl in H; subst; constructor;
          [ apply getMinimal_same | apply IHS ]; auto.
        - induction H; simpl; auto;
          apply getMinimal_same in H; subst; auto.
    Qed.

    Lemma min_spoeq : forall SS S S'',
        min_ind SS S S''->
        forall x, In x S ->
        exists x'', In x'' S'' /\ (spo x'' x \/ x'' = x).
    Proof.
        intros SS S S'' HMin x HIn;
        induction HMin; inversion HIn; subst.
        - exists x''; split; simpl; auto; eapply getMinimal_spoeq; eauto.
        - apply IHHMin in H0; destruct H0 as [x''' H0]; destruct H0;
          exists x'''; split; simpl; auto.
    Qed.

    Lemma min_getMinimal : forall SS S S'',
        min_ind SS S S'' ->
        forall x'', In x'' S'' ->
        exists x, In x S /\ getMinimal_ind x SS x''.
    Proof.
        intros SS S S'' HMin x'' HIn; induction HMin;
        try (inversion HIn; fail);
        destruct HIn as [|HIn]; subst;
        [ eexists; split; simpl; eauto 
        | apply IHHMin in HIn; destruct HIn as [x HIn]; destruct HIn;
          exists x; split; simpl; auto ].
    Qed.

    Lemma min_in : forall S S'',
        min_ind S S S'' ->
        forall x'', In x'' S'' ->
        In x'' S.
    Proof.
        intros S S'' HMin x'' HIn; eapply min_getMinimal in HMin; eauto;
        destruct HMin as [A HMin]; destruct HMin as [HMin HGet];
        apply getMinimal_in in HGet; destruct HGet; subst; auto.
    Qed.


    Lemma min_minimal : forall S S'',
        min_ind S S S'' ->
        forall x'', In x'' S'' ->
        minimal_ind x'' S.
    Proof.
        intros S S'' HMin x'' HIn';
        pose proof (min_getMinimal S S S'' HMin x'' HIn') as HGet;
        destruct HGet as [x HGet]; destruct HGet;
        eapply getMinimal_minimal; eauto.
    Qed.


End Min. 




Lemma getMinimal_spo_same : forall {X} (spo : X -> X -> Prop) spo_fix spoDec x S x'',
    (forall x y, spo_fix x y <-> spo x y) ->
    getMinimal_fix spo_fix spoDec x S = x'' <->
    getMinimal_ind spo x S x''.
Proof.
    intros X spo spo_fix spoDec x S x'' spo_same; split; intros H.
    - rewrite getMinimal_same in H; induction H;
      [ apply getMinimalOrd | apply getMinimalNotOrd | apply getMinimalNil ]; auto;
      rewrite <- spo_same; auto.
    - rewrite getMinimal_same; induction H;
      [ apply getMinimalOrd | apply getMinimalNotOrd | apply getMinimalNil ]; auto;
      rewrite spo_same; auto.
Qed.


Lemma min_spo_same : forall {X} (spo : X -> X -> Prop) spo_fix spoDec SS S S'',
    (forall x y, spo_fix x y <-> spo x y) ->
    min_fix spo_fix spoDec SS S = S'' <->
    min_ind spo SS S S''.
Proof.
    intros X spo spo_fix spoDec SS S S'' spo_same; split; intros H;
    [ rewrite min_same in H | rewrite min_same ]; 
    induction H; constructor; auto.
    - eapply getMinimal_spo_same; eauto; eapply getMinimal_same; eauto. 
    - eapply getMinimal_spo_same in H; eauto; eapply getMinimal_same in H; auto.
    Unshelve. auto. auto.
Qed.
