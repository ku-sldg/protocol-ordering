Require Import Coq.Lists.List.
Require Import Coq.Init.Peano.
Require Import AttestationProtocolOrdering.utilities.nat_le.

(********************************)


(** multiplicity 
 **
 ** The number of instances of an element in a list. *)

Inductive multiplicity_ind {A : Type} (a : A) :
    list A -> nat -> Prop :=
| multEq : forall a' M' x,
    a = a' ->
    multiplicity_ind a M' x ->
    multiplicity_ind a (a'::M') (S x)
| multNeq : forall a' M' x,
    a <> a' ->
    multiplicity_ind a M' x ->
    multiplicity_ind a (a'::M') x
| multNil : 
    multiplicity_ind a nil 0.

Fixpoint multiplicity_fix {A : Type} 
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (a : A) (M : list A)  :
    nat :=
match M with
| a' :: M' => if eqDec_A a a'
              then 1 + multiplicity_fix eqDec_A a M'
              else multiplicity_fix eqDec_A a M'
| nil => 0
end.


Lemma multiplicity_same : forall {A} eqDec_A a (M : list A) x,
    multiplicity_fix eqDec_A a M = x <->
    multiplicity_ind a M x.
Proof.
    intros A eqDec_A a M x; split; intros H.
    - generalize dependent x; induction M as [|a' M']; 
      intros; simpl in H.
    -- subst; constructor.
    -- destruct (eqDec_A a a'); subst;
       [ apply multEq | apply multNeq ]; auto.
    - induction H; simpl; auto;
      destruct (eqDec_A a a'); subst; try contradiction; auto.
Qed.

Lemma multiplicity_eqDec : forall {A} eqDec_A eqDec_A' a (M : list A),
    multiplicity_fix eqDec_A a M = multiplicity_fix eqDec_A' a M.
Proof.
    intros A eqDec_A eqDec_A' a M; induction M as [|a' M']; auto;
    simpl; destruct (eqDec_A a a'), (eqDec_A' a a'); subst;
    try contradiction; auto.
Qed.

Lemma multiplicity_zero : forall {A} eqDec_A a (M : list A),
    ~ In a M <->
    multiplicity_fix eqDec_A a M = 0.
Proof.
    intros A eqDec_A a M; split; intros H.
    - induction M as [|a' M']; simpl; auto;
      destruct (eqDec_A a a'); subst;
      [ exfalso | apply IHM'; intros contra ]; 
      apply H; simpl; auto.
    - intros HIn; induction M as [|a' M'].
    -- inversion HIn.
    -- destruct HIn; subst; simpl in H;
       [ destruct (eqDec_A a a) | destruct (eqDec_A a a') ]; subst;
       try (inversion H; fail); try contradiction; 
       apply IHM'; auto.
Qed.

Lemma multiplicity_succ : forall {A} eqDec_A a (M : list A),
    In a M <->
    le_fix 1 (multiplicity_fix eqDec_A a M).
Proof.
    intros A eqDec_A a M; split; intros H;
    induction M as [|a' M']; simpl in *;
    try (inversion H; fail);
    destruct (eqDec_A a a') as [|contra]; subst; auto;
    destruct H; [ symmetry in H; contradiction | apply IHM'; auto ].
Qed.







(** mSamesetHelper
 **
 ** Multiset mSameset helper function. *)

Definition mSamesetHelper {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) 
        (m : list A) :
    Prop :=
forall a', In a' m -> (multiplicity_fix eqDec_A a' M) = (multiplicity_fix eqDec_A a' N).

Inductive mSamesetHelper_ind {A : Type} (M N: list A) :
    list A -> Prop :=
| mSameEq : forall a' m' x y,
    multiplicity_ind a' M x ->
    multiplicity_ind a' N y ->
    x = y ->
    mSamesetHelper_ind M N m' ->
    mSamesetHelper_ind M N (a' :: m')
| mSameNil : 
    mSamesetHelper_ind M N nil.

Fixpoint mSamesetHelper_fix {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) 
        (m : list A) :
    Prop :=
match m with
| a' :: m' => if eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)
              then mSamesetHelper_fix eqDec_A M N m'
              else False
| nil => True
end.


Lemma mSamesetHelper_same : forall {A} eqDec_A (M N m : list A),
    mSamesetHelper_fix eqDec_A M N m <->
    mSamesetHelper_ind M N m.
Proof.
    intros A eqDec_A M N m; split; intros H.
    - induction m as [|a' m']; [ apply mSameNil | ]; simpl in *; 
      destruct (eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N));
      try contradiction;
      eapply mSameEq;
      [ eapply multiplicity_same | eapply multiplicity_same | | ]; eauto.
    - induction H; simpl; auto;
      destruct (eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)) as [|contra];
      auto; apply contra; eapply multiplicity_same in H, H0; rewrite H, H0; auto.
Qed.

Lemma mSamesetHelper_same' : forall {A} eqDec_A (M N m : list A),
    mSamesetHelper_fix eqDec_A M N m <->
    mSamesetHelper eqDec_A M N m.
Proof.
    intros A eqDec_A M N m; split; intros H.
    - intros a HIn; induction m as [|a' m']; [destruct HIn | inversion HIn ]; 
      subst; simpl in H.
    -- destruct (eqDec_nat (multiplicity_fix eqDec_A a M) (multiplicity_fix eqDec_A a N));
       [ auto | inversion H ].
    -- apply IHm'; auto; destruct (eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)); 
       [ auto | inversion H ].
    - induction m as [|a' m']; simpl; auto;
      destruct (eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)) as [|contra].
    -- apply IHm'; intros a HIn; apply H; simpl; auto.
    -- apply contra; apply H; simpl; auto.
Qed.


Lemma mSamesetHelperDec : forall {A} eqDec_A (M N m : list A),
    {mSamesetHelper_fix eqDec_A M N m} + {~ mSamesetHelper_fix eqDec_A M N m}.
Proof.
    intros A eqDec_A M N m; induction m as [|a' m']; simpl; auto;
    destruct (eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)); auto.
Defined.

Lemma mSamesetHelper_eqDec : forall {A} eqDec_A eqDec_A' (M N m: list A),
    mSamesetHelper eqDec_A M N m <-> mSamesetHelper eqDec_A' M N m.
Proof.
    intros A eqDec_A eqDec_A' M N m; unfold mSamesetHelper;
    split; intros H a' HIn; apply H in HIn;
    [ rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A) (M:=M); rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A) (M:=N)
    | rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A') (M:=M); rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A') (M:=N) ]; 
    auto.
Qed.


Lemma mSamesetHelper_reflexive : forall {A} eqDec_A (M m : list A),
    mSamesetHelper eqDec_A M M m.
Proof.
    intros A eqDec_A M m; apply mSamesetHelper_same'; induction m as [|a' m']; simpl; auto;
    destruct (eqDec_nat (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' M)) as [|contra];
    auto; apply contra; auto.
Qed.



(** mSameset
 **
 ** Multiset equality. 
 **
 ** $M = N$ iff
 ** $\forall a \in M \cup N, mult_M(a) = mult_N(a). *)

 Definition mSameset  {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) :
    Prop :=
mSamesetHelper eqDec_A M N M /\ mSamesetHelper eqDec_A N M N.

Definition mSameset_ind {A : Type}
        (M N: list A) : 
    Prop :=
mSamesetHelper_ind M N M /\ mSamesetHelper_ind N M N.

Definition mSameset_fix {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) :
    Prop :=
if (mSamesetHelperDec eqDec_A M N M)
then if (mSamesetHelperDec eqDec_A N M N)
     then True
     else False
else False.

Lemma mSameset_same : forall {A} eqDec_A (M N : list A),
    mSameset_fix eqDec_A M N <->
    mSameset_ind M N.
Proof.
    intros A eqDec_A M N; unfold mSameset_fix; split; intros H.
    - destruct (mSamesetHelperDec eqDec_A M N M), (mSamesetHelperDec eqDec_A N M N);
      try (inversion H; fail);
      split; eapply mSamesetHelper_same; eauto.
    - destruct (mSamesetHelperDec eqDec_A M N M), (mSamesetHelperDec eqDec_A N M N); 
      auto; destruct H; apply n; apply mSamesetHelper_same; auto.
Qed.

Lemma mSameset_same' : forall {A} eqDec_A (M N : list A),
    mSameset_fix eqDec_A M N <->
    mSameset eqDec_A M N.
Proof.
    intros; rewrite mSameset_same; split; intros H; destruct H; split; 
    try (apply mSamesetHelper_same'; apply mSamesetHelper_same; auto; fail);
    try (eapply mSamesetHelper_same; apply mSamesetHelper_same'; eauto; fail). 
Qed.

Lemma mSamesetDec : forall {A} eqDec_A (M N : list A),
    {mSameset_fix eqDec_A M N} + {~ mSameset_fix eqDec_A M N}.
Proof.
    intros; unfold mSameset_fix;
    destruct (mSamesetHelperDec eqDec_A M N M), (mSamesetHelperDec eqDec_A N M N); auto.
Defined.

Lemma mSameset_eqDec : forall {A} eqDec_A eqDec_A' (M N: list A),
    mSameset eqDec_A M N <-> mSameset eqDec_A' M N.
Proof.
    intros A eqDec_A eqDec_A' M N; split; intros H;
    destruct H; split; eapply mSamesetHelper_eqDec; eauto.
Qed.


Theorem mSameset_reflexive : forall {A} eqDec_A (M : list A),
    mSameset eqDec_A M M.
Proof.
    intros; split; apply mSamesetHelper_reflexive.
Qed.

Theorem mSameset_symmetric : forall {A} eqDec_A (M N : list A),
    mSameset eqDec_A M N ->
    mSameset eqDec_A N M.
Proof.
    intros A eqDec_A M N H;
    destruct H; split; auto.
Qed.


Theorem mSameset_transitive : forall {A} eqDec_A (M1 M2 M3 : list A),
    mSameset eqDec_A M1 M2 ->
    mSameset eqDec_A M2 M3 ->
    mSameset eqDec_A M1 M3.
Proof.
    intros A eqDec_A M1 M2 M3 H12 H23; destruct H12 as [H12 H21], H23 as [H23 H32]; split.
    - intros a HIn1; apply H12 in HIn1; rewrite HIn1; destruct (In_dec eqDec_A a M2) as [HIn2|HIn2].
    -- apply H23 in HIn2; auto.
    -- pose proof (multiplicity_zero eqDec_A a M2) as HZero2; 
       apply HZero2 in HIn2; rewrite HIn2; 
       destruct (In_dec eqDec_A a M3) as [HIn3|HIn3].
    --- apply H32 in HIn3; rewrite HIn3; symmetry; auto.
    --- pose proof (multiplicity_zero eqDec_A a M3) as HZero3; apply HZero3 in HIn3; rewrite HIn3; auto.
    - intros a HIn3; apply H32 in HIn3; rewrite HIn3; destruct (In_dec eqDec_A a M2) as [HIn2|HIn2].
    -- apply H21 in HIn2; auto.
    -- pose proof (multiplicity_zero eqDec_A a M2) as HZero2; 
       apply HZero2 in HIn2; rewrite HIn2;
       destruct (In_dec eqDec_A a M1) as [HIn1|HIn1].
    --- apply H12 in HIn1; rewrite HIn1; symmetry; auto.
    --- pose proof (multiplicity_zero eqDec_A a M1) as HZero1;
        apply HZero1 in HIn1; rewrite HIn1; auto.
Qed.


(** mIncludedHelper
 **
 ** Multiset inclusion helper function. *)

 Definition mIncludedHelper {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) 
        (m : list A) :
    Prop :=
forall a', In a' m -> le_fix (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N).

Inductive mIncludedHelper_ind {A : Type} (M N: list A) :
    list A -> Prop :=
| mInclLe : forall a' m' x y,
    multiplicity_ind a' M x ->
    multiplicity_ind a' N y ->
    le x y ->
    mIncludedHelper_ind M N m' ->
    mIncludedHelper_ind M N (a' :: m')
| mInclNil : 
    mIncludedHelper_ind M N nil.


Fixpoint mIncludedHelper_fix {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) 
        (m : list A) :
    Prop :=
match m with
| a' :: m' => if leDec (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)
       then mIncludedHelper_fix eqDec_A M N m'
       else False
| nil => True
end.


Lemma mIncludedHelper_same : forall {A} eqDec_A (M N m : list A),
    mIncludedHelper_fix eqDec_A M N m <->
    mIncludedHelper_ind M N m.
Proof.
    intros A eqDec_A M N m; split; intros H.
    - induction m as [|a' m']; [ apply mInclNil | ]; simpl in *; 
      destruct (leDec (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N));
      try contradiction;
      eapply mInclLe;
      [ eapply multiplicity_same | eapply multiplicity_same | apply le_same | ]; eauto.
    - induction H; simpl; auto;
      destruct (leDec (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)) as [|contra];
      auto; apply contra; eapply multiplicity_same in H, H0; rewrite H, H0; apply le_same; auto.
Qed.

Lemma mIncludedHelper_same' : forall {A} eqDec_A (M N m : list A),
    mIncludedHelper_fix eqDec_A M N m <->
    mIncludedHelper eqDec_A M N m.
Proof.
    intros A eqDec_A M N m; split; intros H.
    - intros a HIn; induction m as [|a' m']; [destruct HIn | inversion HIn ]; 
      subst; simpl in H.
    -- destruct (leDec (multiplicity_fix eqDec_A a M) (multiplicity_fix eqDec_A a N));
       [ auto | inversion H ].
    -- apply IHm'; auto; destruct (leDec (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)); 
       [ auto | inversion H ].
    - induction m as [|a' m']; simpl; auto;
      destruct (leDec (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)) as [|contra].
    -- apply IHm'; intros a HIn; apply H; simpl; auto.
    -- apply contra; apply H; simpl; auto.
Qed.


Lemma mIncludedHelperDec : forall {A} eqDec_A (M N m : list A),
    {mIncludedHelper_fix eqDec_A M N m} + {~ mIncludedHelper_fix eqDec_A M N m}.
Proof.
    intros A eqDec_A M N m; induction m as [|a' m']; simpl; auto;
    destruct (leDec (multiplicity_fix eqDec_A a' M) (multiplicity_fix eqDec_A a' N)); auto.
Defined.

Lemma mIncludedHelper_eqDec : forall {A} eqDec_A eqDec_A' (M N m: list A),
    mIncludedHelper eqDec_A M N m <-> mIncludedHelper eqDec_A' M N m.
Proof.
    intros A eqDec_A eqDec_A' M N m; unfold mIncludedHelper.
    split; intros H a' HIn; apply H in HIn;
    [ rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A) (M:=M); rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A) (M:=N)
    | rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A') (M:=M); rewrite multiplicity_eqDec with (eqDec_A':=eqDec_A') (M:=N) ];
    auto.
Qed.


(** mIncluded 
 **
 ** Multiset inclusion. 
 **
 ** $M \subseteq N$ iff
 ** $\forall a \in M, mult_M(a) \leq mult_N(a). *)

Definition mIncluded  {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) :
    Prop :=
mIncludedHelper eqDec_A M N M.

Definition mIncluded_ind {A : Type}
        (M N: list A) : 
    Prop :=
mIncludedHelper_ind M N M.

Definition mIncluded_fix {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) :
    Prop :=
mIncludedHelper_fix eqDec_A M N M.

Lemma mIncluded_same : forall {A} eqDec_A (M N : list A),
    mIncluded_fix eqDec_A M N <->
    mIncluded_ind M N.
Proof.
    intros; apply mIncludedHelper_same.
Qed.

Lemma mIncluded_same' : forall {A} eqDec_A (M N : list A),
    mIncluded_fix eqDec_A M N <->
    mIncluded eqDec_A M N.
Proof.
    intros; apply mIncludedHelper_same'.
Qed.

Lemma mIncludedDec : forall {A} eqDec_A (M N : list A),
    {mIncluded_fix eqDec_A M N} + {~ mIncluded_fix eqDec_A M N}.
Proof.
    intros; apply mIncludedHelperDec.
Defined.

Lemma mIncluded_eqDec : forall {A} eqDec_A eqDec_A' (M N: list A),
    mIncluded eqDec_A M N <-> mIncluded eqDec_A' M N.
Proof.
    intros A eqDec_A eqDec_A' M N; split; intros H;
    eapply mIncludedHelper_eqDec; eauto.
Qed.

Theorem mIncluded_reflexive : forall {A} eqDec_A (M N : list A),
    mSameset eqDec_A M N ->
    mIncluded eqDec_A M N.
Proof.
    intros A eqDec_A M N H; destruct H; 
    intros a' HIn; apply H in HIn; rewrite HIn; apply le_same; auto.
Qed.

Theorem mIncluded_antisymmetric : forall {A} eqDec_A (M N : list A),
    mIncluded eqDec_A M N ->
    mIncluded eqDec_A N M ->
    mSameset eqDec_A M N.
Proof.
    intros A eqDec_A M N HMN HNM;
    split; intros a HIn.
    - apply HMN in HIn; destruct (In_dec eqDec_A a N) as [HIn'|HIn'].
    -- apply HNM in HIn'; apply le_antisymmetric; apply le_same; auto.
    -- pose proof (multiplicity_zero eqDec_A a N) as HZero; apply HZero in HIn';
       rewrite HIn'; rewrite HIn' in HIn; apply le_same in HIn; apply le_0_0 in HIn; auto.
    - apply HNM in HIn; destruct (In_dec eqDec_A a M) as [HIn'|HIn'].
    -- apply HMN in HIn'; apply le_antisymmetric; apply le_same; auto.
    -- pose proof (multiplicity_zero eqDec_A a M) as HZero; apply HZero in HIn';
       rewrite HIn'; rewrite HIn' in HIn; apply le_same in HIn; apply le_0_0 in HIn; auto.
Qed.


Theorem mIncluded_transitive : forall {A} eqDec_A (M1 M2 M3 : list A),
    mIncluded eqDec_A M1 M2 ->
    mIncluded eqDec_A M2 M3 ->
    mIncluded eqDec_A M1 M3.
Proof.
    intros A eqDec_A M1 M2 M3 H12 H23 a HIn1;
    apply H12 in HIn1; destruct (In_dec eqDec_A a M2) as [HIn2|HIn2].
    - apply H23 in HIn2; apply le_same; apply le_same in HIn1, HIn2; eapply le_transitive; eauto.
    - pose proof (multiplicity_zero eqDec_A a M2) as [HZero]; apply HZero in HIn2; 
      rewrite HIn2 in HIn1; apply le_same; apply le_same in HIn1; apply le_0_0 in HIn1;
      rewrite HIn1; apply le_0_n.
Qed.


Lemma mSameset_correct : forall {A} eqDec_A (M N : list A),
    mSameset eqDec_A M N ->
    mIncluded eqDec_A M N /\ mIncluded eqDec_A N M.
Proof.
    intros A eqDec_A  M N H; 
    split; intros a HIn; apply H in HIn; rewrite HIn; apply le_same; auto.
Qed.



(** mStrictIncluded 
 **
 ** Multiset strict inclusion. 
 **
 ** $M \subset N$ iff
 ** $M \subseteq N$ and $M \not \subseteq N$. *)

Definition mStrictIncluded  {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) :
    Prop :=
mIncluded eqDec_A M N /\ ~ mIncluded eqDec_A N M.

Definition mStrictIncluded_ind {A : Type}
        (M N: list A) : 
    Prop :=
mIncluded_ind M N /\ ~ mIncluded_ind N M.

Definition mStrictIncluded_fix {A : Type}
        (eqDec_A : forall (x y : A), {x = y} + {x <> y})
        (M N: list A) :
    Prop :=
if (mIncludedDec eqDec_A M N)
then if (mIncludedDec eqDec_A N M)
     then False
     else True
else False.

Lemma mStrictIncluded_same : forall {A} eqDec_A (M N : list A),
    mStrictIncluded_fix eqDec_A M N <->
    mStrictIncluded_ind M N.
Proof.
    unfold mStrictIncluded_fix; intros A eqDec_A M N; split; intros H.
    - split; destruct (mIncludedDec eqDec_A M N), (mIncludedDec eqDec_A N M);
      try (inversion H; fail); rewrite <- mIncluded_same; eauto.
    - destruct H as [H H']; destruct (mIncludedDec eqDec_A M N), (mIncludedDec eqDec_A N M);
      rewrite <- mIncluded_same in H, H'; eauto.
    Unshelve. auto. auto. auto. auto. auto.
Qed.

Lemma mStrictIncluded_same' : forall {A} eqDec_A (M N : list A),
    mStrictIncluded_fix eqDec_A M N <->
    mStrictIncluded eqDec_A M N.
Proof.
    intros A eqDec_A M N; rewrite mStrictIncluded_same; split; intros H.
    - destruct H as [H H']; split; 
      rewrite <- mIncluded_same'; rewrite <- mIncluded_same in H, H'; eauto.
    - destruct H as [H H']; split;
      rewrite <- mIncluded_same; rewrite <- mIncluded_same' in H, H'; eauto.
    Unshelve. auto. auto.
Qed.

Lemma mStrictIncludedDec : forall {A} eqDec_A (M N : list A),
    {mStrictIncluded_fix eqDec_A M N} + {~ mStrictIncluded_fix eqDec_A M N}.
Proof.
    unfold mStrictIncluded_fix; intros A eqDec_A M N;
    destruct (mIncludedDec eqDec_A M N), (mIncludedDec eqDec_A N M); auto.
Defined.

Lemma mStrictIncluded_eqDec : forall {A} eqDec_A eqDec_A' (M N: list A),
    mStrictIncluded eqDec_A M N <-> mStrictIncluded eqDec_A' M N.
Proof.
    intros A eqDec_A eqDec_A' M N; split; intros H;
    destruct H as [H contra]; split;
    try (intros contra'; apply contra);
    eapply mIncluded_eqDec; eauto.
Qed.


Theorem mStrictIncluded_irreflexive : forall {A} eqDec_A (M N : list A),
    mSameset eqDec_A M N ->
    ~ mStrictIncluded eqDec_A M N.
Proof.
    intros A eqDec_A M N HEq contra;
    destruct contra as [HIn contra]; apply contra;
    apply mSameset_correct in HEq; destruct HEq; auto.
Qed.


Theorem mStrictIncluded_asymmetric : forall {A} eqDec_A (M N : list A),
    mStrictIncluded eqDec_A M N ->
    ~ mStrictIncluded eqDec_A N M.
Proof.
    intros A eqDec_A M N H H'; destruct H, H'; contradiction.
Qed.


Theorem mStrictIncluded_transitive : forall {A} eqDec_A (M1 M2 M3 : list A),
    mStrictIncluded eqDec_A M1 M2 ->
    mStrictIncluded eqDec_A M2 M3 ->
    mStrictIncluded eqDec_A M1 M3.
Proof.
    intros A eqDec_A M1 M2 M3.
    intros H12 H23; destruct H12 as [H12 H12'], H23 as [H23 H23']; split;
    [|intros H31; apply H23'];
    eapply mIncluded_transitive; eauto.
Qed.


Lemma mStrictIncluded_correct : forall {A} eqDec_A (M N : list A),
    mStrictIncluded eqDec_A M N ->
    ~ mSameset eqDec_A M N.
Proof.
    intros A eqDec_A M N HStr HEq; apply mSameset_correct in HEq;
    destruct HEq, HStr; contradiction.
Qed.

Lemma mStrictIncluded_mIncluded1 : forall {A} eqDec_A (M1 M2 M3 : list A),
    mStrictIncluded eqDec_A M1 M2 ->
    mIncluded eqDec_A M2 M3 ->
    mStrictIncluded eqDec_A M1 M3.
Proof.
    intros A eqDec_A M1 M2 M3 H1 H2;
    destruct H1 as [H contra]; split;
    [|intros contra'; apply contra];
    eapply mIncluded_transitive; eauto.
Qed.

Lemma mStrictIncluded_mIncluded2 : forall {A} eqDec_A (M1 M2 M3 : list A),
    mIncluded eqDec_A M1 M2 ->
    mStrictIncluded eqDec_A M2 M3 ->
    mStrictIncluded eqDec_A M1 M3.
Proof.
    intros A eqDec_A M1 M2 M3 H1 H2;
    destruct H2 as [H contra]; split;
    [|intros contra'; apply contra];
    eapply mIncluded_transitive; eauto.
Qed.
