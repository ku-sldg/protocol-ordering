Require Import Coq.Init.Peano.


(** eqDec_nat
 **
 ** The natural numbers have decidable equality. *)
Lemma eqDec_nat : forall (x y : nat),
    {x = y} + {x <> y}.
Proof.
    decide equality.
Defined.


(** le
 **
 ** Less than or equal to.
 **
 ** Inductive definition le found in Coq.Init.Peano.
 ** Fixpoint definition defined below. *)

Fixpoint le_fix (x y : nat) : Prop :=
  match x, y with
    | 0, _ => True
    | _, 0 => False
    | S x', S y' => le_fix x' y'
  end.

Lemma le_same : forall x y,
    le_fix x y <->
    le x y.
Proof.
    intros x y; split; intros H.
    - generalize dependent y; induction x; intros.
    -- induction y; constructor; auto.
    -- destruct y; simpl in *;
       [ inversion H | apply le_n_S; auto ].
    - generalize dependent x; induction y; intros;
      destruct x; simpl; auto;
      [ inversion H | apply IHy; apply le_S_n; auto ].
Qed.

Lemma leDec : forall (x y : nat), 
    {le_fix x y} + {~ le_fix x y}.
Proof.
    intros x; induction x; simpl; auto;
    intros y; destruct y; simpl; auto.
Defined.

Lemma le_reflexive : forall (x : nat),
    le x x.
Proof.
    intros; auto.
Qed.

Lemma le_antisymmetric : forall (x y : nat),
    le x y ->
    le y x ->
    x = y.
Proof.
    intros x y Hxy Hyx; generalize dependent y;
    induction x; intros; destruct y;
    auto; try (inversion Hxy; fail); try (inversion Hyx; fail);
    assert (forall (x y : nat), x = y -> S x = S y) as eq_succ by auto;
    apply eq_succ; apply IHx; apply le_same; apply le_same in Hxy, Hyx;
    simpl in *; auto.
Qed.

Lemma le_transitive : forall (x y z : nat),
    le x y ->
    le y z ->
    le x z.
Proof.
    intros x y z Hxy Hyz; generalize dependent x; generalize dependent y;
    induction z; intros; inversion Hyz; subst;
    [ inversion Hxy; subst; constructor
    | auto
    | constructor; eapply IHz; eauto ].
Qed.


Lemma le_0_0 : forall x,
    le x 0 ->
    x = 0.
Proof.
    intros x H; destruct x; [ auto | inversion H ].
Qed.
