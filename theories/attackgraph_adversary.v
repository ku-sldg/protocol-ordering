Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.

Section AdversarySets. 
    Context {components : Type}.
    
(** pi 
 ** 
 ** The set of adversary events in an attack graph. *)

    Fixpoint piHelper {A : attackgraph components} (edges : edgesT A) : 
        list (eventT A) :=
    match edges with
    | (ev1, ev2) :: edges' => match (myLabel A ev1), (myLabel A ev2) with
                              | inr _, inr _ => ev1 :: ev2 :: (piHelper edges')
                              | inr _, inl _ => ev1 :: (piHelper edges')
                              | inl _, inr _ => ev2 :: (piHelper edges')
                              | inl _, inl _ => piHelper edges'
                              end
    | nil => nil
    end.

    Definition pi (A : attackgraph components) : 
        list (eventT A) :=
    nodup (myEqDec_event A) (piHelper (myEdges A)).

    Hint Unfold pi : core.

    Lemma pi_fact : forall A ev,
        In ev (pi A)
        <->
        (exists ev', In (ev, ev') (myEdges A) \/ In (ev', ev) (myEdges A)) 
         /\ 
        (exists adv, myLabel A ev = inr adv).
    Proof.
        intros A ev; autounfold; rewrite nodup_In; split; intros H.
        - split; induction (myEdges A); try (inversion H; fail);
          destruct a as [ev1 ev2]; simpl in H;
          remember (myLabel A ev1) as Hl1; remember (myLabel A ev2) as Hl2;
          destruct Hl1, Hl2;
          try (repeat destruct H; subst);
          try (apply IHl in H; destruct H as [ans H]; exists ans; simpl; destruct H; auto);
          try (exists ev1; simpl; auto; fail);
          try (exists ev2; simpl; auto; fail);
          try (exists a; auto; fail);
          try (exists a0; auto; fail).
        - destruct H as [HIn HAdv]; destruct HIn as [ev' HIn]; destruct HAdv as [adv HAdv];
          induction (myEdges A); try (destruct HIn as [HIn|HIn]; inversion HIn; fail);
          destruct a as [ev1 ev2]; destruct HIn; simpl; destruct H;
          try (inversion H; destruct (myLabel A ev); destruct (myLabel A ev'); try (inversion HAdv; fail); simpl; auto);
          try (destruct (myLabel A ev1); destruct (myLabel A ev2); repeat right; apply IHl; auto).
    Qed.


(** tau
 ** 
 ** The set of time-constrained adversary events in an attack graph. *)

    Fixpoint tau_helper {A : attackgraph components} (edges : edgesT A) :
        list (eventT A) :=
    match edges with
    | (ev1, ev2) :: edges' => match (myLabel A ev1), (myLabel A ev2) with
                    | inl _, inr _ => ev2 :: (tau_helper edges')
                    | _, _ => tau_helper edges'
                    end
    | nil => nil
    end.

    Definition tau (A : attackgraph components) : 
        list (eventT A) :=
    nodup (myEqDec_event A) (tau_helper (myEdges A)).

    Hint Unfold tau : core.

    Lemma tau_fact : forall A ev,
        In ev (tau A)
        <->
        (exists ev' meas, In (ev', ev) (myEdges A) /\ myLabel A ev' = inl meas) 
        /\ 
        (exists adv, myLabel A ev = inr adv).
    Proof.
        intros A ev; autounfold; rewrite nodup_In; split; intros H.
        - split; induction (myEdges A); try (inversion H; fail);
          destruct a as [ev1 ev2]; simpl in H;
          remember (myLabel A ev1) as Hl1; remember (myLabel A ev2) as Hl2;
          destruct Hl1, Hl2;
          try (destruct H; subst);
          try (apply IHl in H; destruct H as [ans H]; exists ans; auto);
          try (destruct H as [ans' H]; destruct H; exists ans'; simpl; auto).
        -- exists ev1, m; simpl; auto.
        -- exists a; auto.
        - destruct H as [HIn HAdv]; destruct HIn as [ev' HIn]; destruct HIn as [meas HIn];
          destruct HIn as [HIn HMeas]; destruct HAdv as [adv HAdv];
          induction (myEdges A); try (inversion HIn; fail).
          destruct a as [ev1 ev2]; destruct HIn; simpl.
        -- inversion H; destruct (myLabel A ev'); destruct (myLabel A ev); inversion HAdv; inversion HMeas; simpl; auto.
        -- destruct (myLabel A ev1); destruct (myLabel A ev2); repeat right; apply IHl; auto.
    Qed.


    Lemma tau_pi : forall A ev,
        In ev (tau A) ->
        In ev (pi A).
    Proof.
        intros A ev H; apply pi_fact; apply tau_fact in H; destruct H as [HPair HLab]; split.
        - destruct HPair as [ev' HPair]; destruct HPair as [meas HPair]; destruct HPair as [HIn HLab'];
          exists ev'; auto.
        - destruct HLab as [adv HLab];
          exists adv; auto.
    Qed.


End AdversarySets.