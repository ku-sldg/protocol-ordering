Require Import Coq.Lists.List.

(** forallP *)

Definition forallP {X : Type}
        (P : X -> Prop)
        (l : list X) :=
forall x, In x l -> P x.

Fixpoint forallP_fix {X : Type}
        {P : X -> Prop}
        (PDec : forall x, {P x} + {~ P x})
        (l : list X) :=
match l with
| x :: l' => if PDec x 
             then forallP_fix PDec l'
             else False
| nil => True
end.

Inductive forallP_ind {X : Type} (P : X -> Prop) : list X -> Prop :=
| forallPCons : forall x l,
    P x ->
    forallP_ind P l ->
    forallP_ind P (x::l)
| forallPNil :
    forallP_ind P nil.

Lemma forallP_same : forall X (P : X -> Prop) (PDec : forall x, {P x} + {~ P x}) l,
    forallP_fix PDec l <->
    forallP_ind P l.
Proof.
    intros X P PDec l; split; intros H.
    - induction l as [|x l']; [apply forallPNil|];
      simpl in H; destruct (PDec x); try contradiction;
      apply forallPCons; auto.
    - induction H; simpl; auto;
      destruct (PDec x); try contradiction; auto.
Qed.

Lemma forallP_same' : forall X (P : X -> Prop) (PDec : forall x, {P x} + {~ P x}) l,
    forallP_fix PDec l <->
    forallP P l.
Proof.
    intros X P PDec l; split; intros H.
    - intros x HIn; induction l as [|x' l']; [inversion HIn|];
      simpl in H; destruct (PDec x'); destruct HIn; subst; auto;
      contradiction.
    - induction l as [|x' l']; simpl; auto;
      unfold forallP in H; destruct (PDec x').
    -- apply IHl'; intros x HIn; apply H; simpl; auto.
    -- apply n; apply H; simpl; auto.
Qed.

Lemma forallPDec : forall X (P : X -> Prop) (PDec : forall x, {P x} + {~ P x}) l,
    {forallP P l} + {~ forallP P l}.
Proof.
    intros X P PDec l.
    induction l as [|x' l'].
    - left; intros x HIn; inversion HIn.
    - destruct (PDec x'); [destruct IHl'|].
    -- left; intros x HIn; destruct HIn; subst; auto.
    -- right; intros contra; apply n; intros x HIn; apply contra; simpl; auto.
    -- right; intros contra; apply n; apply contra; simpl; auto.
Defined.


(* existsP *)

Definition existsP {X : Type}
        (P : X -> Prop)
        (l : list X) :=
exists x, In x l /\ P x.

Fixpoint existsP_fix {X : Type}
    {P : X -> Prop}
    (PDec : forall x, {P x} + {~ P x})
    (l : list X) :=
match l with
| x :: l' => if PDec x
             then True
             else existsP_fix PDec l'
| nil => False
end.

Inductive existsP_ind {X : Type} (P : X -> Prop) : list X -> Prop :=
| existsPHead : forall x l,
    P x ->
    existsP_ind P (x::l)
| existsPTail : forall x l,
    existsP_ind P l ->
    existsP_ind P (x::l).

Lemma existsP_same : forall X (P : X -> Prop) (PDec : forall x, {P x} + {~ P x}) l,
    existsP_fix PDec l <->
    existsP_ind P l.
Proof.
    intros X P PDec l; split; intros H.
    - induction l as [|x l]; simpl in H; try contradiction.
      destruct (PDec x); [apply existsPHead | apply existsPTail]; auto.
    - induction H; simpl; destruct (PDec x); try contradiction; auto.
Qed.

Lemma existsP_same' : forall X (P : X -> Prop) (PDec : forall x, {P x} + {~ P x}) l,
    existsP_fix PDec l <->
    existsP P l.
Proof.
    intros X P PDec l; split; intros H.
    - induction l as [|x l]; simpl in H; try contradiction.
      destruct (PDec x).
    -- exists x; split; simpl; auto.
    -- apply IHl in H. destruct H as [x' [HIn HP]].
       exists x'; split; simpl; auto.
    - induction l as [|x l]; destruct H as [x' [HIn HP]];
      [inversion HIn|]; simpl.
      destruct (PDec x); auto.
      apply IHl. exists x'; split; auto.
      destruct HIn; subst; try contradiction; auto.
Qed.

Lemma existsPDec : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l,
    {existsP P l} + {~ existsP P l}.
Proof.
    intros X P PDec l. induction l as [|x l].
    - right. intros contra. destruct contra as [x' [HIn HP]]. inversion HIn.
    - destruct (PDec x).
    -- left. exists x; split; simpl; auto.
    -- destruct IHl as [IH|IH].
    --- left. destruct IH as [x' [HIn HP]]. 
        exists x'; split; simpl; auto.
    --- right. intros contra. destruct contra as [x' [HIn HP]].
        apply IH. exists x'; split; simpl; auto.
        destruct HIn; subst; try contradiction; auto.
Qed.
      



(** filter *)
    
Fixpoint filter_fix {X : Type}
        {P : X -> Prop}
        (PDec : forall x, {P x} + {~ P x})
        (l : list X) :=
match l with
| x :: l' => if (PDec x) then x::(filter_fix PDec l') else (filter_fix PDec l')
| nil => nil
end.

Inductive filter_ind {X : Type} (P : X -> Prop) : list X -> list X -> Prop :=
| filterKeep : forall x l fl,
    P x ->
    filter_ind P l fl ->
    filter_ind P (x::l) (x::fl)
| filterDiscard : forall x l fl,
    ~ P x ->
    filter_ind P l fl ->
    filter_ind P (x::l) fl
| filterNil : filter_ind P nil nil.

Lemma filter_same : forall X (P : X -> Prop) (PDec : forall x, {P x} + {~ P x}) l fl,
    filter_fix PDec l = fl <->
    filter_ind P l fl.
Proof.
    intros X P PDec l fl; split; intros H.
    - rewrite <- H; clear H; induction l as [|x l']; simpl; [apply filterNil|];
      destruct (PDec x); [apply filterKeep | apply filterDiscard]; auto.
    - induction H; simpl; auto; destruct (PDec x); try contradiction;
      rewrite IHfilter_ind; auto.
Qed.


(** removeFirst *)

Fixpoint removeFirst_fix {X : Type} 
        (eq_dec : forall x y : X, {x = y}+{x <> y}) 
        (a : X) 
        (l : list X) {struct l} : 
    list X :=
match l with
| x::l' => if (eq_dec x a) then l' else x::(removeFirst_fix eq_dec a l')
| nil => nil
end.

Inductive removeFirst_ind {X : Type} (a : X) : list X -> list X -> Prop :=
| removeFirstRemove : forall l,
    removeFirst_ind a (a::l) l
| removeFirstKeep : forall x l rl,
    x <> a ->
    removeFirst_ind a l rl ->
    removeFirst_ind a (x::l) (x::rl)
| removeFirstNil : removeFirst_ind a nil nil.

Lemma removeFirst_same : forall X eq_dec (a : X) l rl,
    removeFirst_fix eq_dec a l = rl <->
    removeFirst_ind a l rl.
Proof.
    intros X eq_dec a l rl; split; intros H.
    - rewrite <- H; clear H; induction l as [|x l']; simpl; [apply removeFirstNil|].
      destruct (eq_dec x a); subst; [apply removeFirstRemove | apply removeFirstKeep ]; auto.
    - induction H; simpl; auto; [destruct (eq_dec a a) | destruct (eq_dec x a)]; subst;
      try contradiction; auto.
Qed.
