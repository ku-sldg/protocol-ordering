Require Import Coq.Lists.List.
Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.mset.
Require Import AttestationProtocolOrdering.utilities.list_functions.

Lemma in_nil_absurd : forall {X : Type} (x : X), In x nil -> False.
Proof.
    intros X x H. inversion H.
Qed.


Lemma app_cons : forall {X} (x : X) l',
    x :: l' = (x::nil) ++ l'.
Proof.
    intros; simpl; auto.
Qed.

Lemma app_exists : forall {X} (l : list X),
    exists l1 l2, l = l1 ++ l2.
Proof.
    intros X l. induction l as [|x l'].
    - exists nil, nil. simpl. auto.
    - destruct IHl' as [l1 [l2 IH]].
      exists (x :: l1), l2; simpl; rewrite IH; auto.
Qed.

(** mset facts *)

Lemma multiplicity_countOcc : forall {A} eqDec_A a (M : list A),
    multiplicity_fix eqDec_A a M = count_occ eqDec_A M a.
Proof.
    intros A eqDec_A a M. induction M as [|a' M']; simpl; auto.
    destruct (eqDec_A a a'), (eqDec_A a' a); subst; try contradiction; auto.
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

Lemma multiplicity_NoDup_one : forall {A} eqDec_A a (M : list A),
    NoDup M ->
    In a M ->
    (multiplicity_fix eqDec_A a M) = 1.
Proof.
    intros A eqDec_A a M HNd HIn.
    induction M as [|a' M']; simpl;
    try (inversion HIn; fail).
    inversion HNd; subst;
    destruct (eqDec_A a a'); subst;
    destruct HIn; subst; try contradiction.
    -- apply multiplicity_zero with (eqDec_A:=eqDec_A) in H1;
       rewrite H1; auto.
    -- apply IHM'; auto.
Qed.  

Lemma multiplicity_app : forall {A} eqDec_A a (M1 M2 : list A),
    multiplicity_fix eqDec_A a (M1 ++ M2) =  multiplicity_fix eqDec_A a M1 + multiplicity_fix eqDec_A a M2.
Proof.
    intros A eqDec_A a M1 M2; generalize dependent M2;
    induction M1 as [|a' M']; intros; simpl; auto.
    destruct (eqDec_A a a'); subst; auto.
    rewrite plus_Sn_m; apply eq_S; auto.
Qed.

Lemma multiplicity_app_comm : forall {A} eqDec_A a (M1 M2 : list A),
    multiplicity_fix eqDec_A a (M1 ++ M2) = multiplicity_fix eqDec_A a (M2 ++ M1).
Proof.
    intros A eqDec_A a M1 M2; repeat rewrite multiplicity_app;
    rewrite PeanoNat.Nat.add_comm; auto.
Qed.

Lemma multiplicity_app_cons : forall {A} eqDec_A a a' (M N1 N2 : list A),
    multiplicity_fix eqDec_A a (a' :: M) = multiplicity_fix eqDec_A a (N1 ++ a' :: N2) ->
    multiplicity_fix eqDec_A a M = multiplicity_fix eqDec_A a (N1 ++ N2).
Proof.
    intros A eqDec_A a a' M' N1 N2 H;
    rewrite multiplicity_app_comm in H; rewrite <- app_comm_cons in H; simpl in H; 
    destruct (eqDec_A a a'); subst;
    rewrite multiplicity_app_comm; auto.
Qed.

Lemma multiplicity_removeFirst : forall {A} eqDec_A a (M : list A),
    In a M ->
    multiplicity_fix eqDec_A a M = S (multiplicity_fix eqDec_A a (removeFirst_fix eqDec_A a M)).
Proof.
    intros A eqDec_A a M HIn. induction M as [|a' M'].
    - inversion HIn.
    - simpl; destruct (eqDec_A a a'), (eqDec_A a' a); subst; try contradiction; auto.
      simpl; destruct (eqDec_A a a'); subst; try contradiction.
      destruct HIn; subst; try contradiction.
      rewrite IHM'; auto.
Qed.

Lemma multiplicity_removeFirst_neq : forall {A} eqDec_A a (M : list A),
    forall b, a <> b ->
    multiplicity_fix eqDec_A a M = multiplicity_fix eqDec_A a (removeFirst_fix eqDec_A b M).
Proof.
    intros A eqDec_A a M; induction M as [|a' M']; intros; simpl; auto.
    destruct (eqDec_A a' b); simpl; destruct (eqDec_A a a'); subst; auto.
    contradiction.
Qed.

Lemma multiplicity_zero_all : forall {A} eqDec_A (M : list A),
    (forall a, multiplicity_fix eqDec_A a M = 0) ->
    M = nil.
Proof.
    intros A eqDec_A M H; induction M as [|a' M']; auto.
    specialize H with a'; simpl in H; destruct (eqDec_A a' a'); try contradiction; inversion H.
Qed.


Lemma multiplicity_remove_neq : forall {A} eqDec_A a (M : list A),
    forall b, a <> b ->
    multiplicity_fix eqDec_A a M = multiplicity_fix eqDec_A a (remove eqDec_A b M).
Proof.
    intros A eqDec_A a M. induction M as [|a' M']; intros; simpl; auto.
    destruct (eqDec_A b a'); simpl; destruct (eqDec_A a a'); simpl;
    subst; auto. contradiction.
Qed.

Lemma multiplicity_map_neq : forall {X Y : Type} eqDec_X eqDec_Y (l : list X) (f : X -> Y),
    NoDup l ->
    forall x y, f x <> y ->
    multiplicity_fix eqDec_Y y (map f l) = multiplicity_fix eqDec_Y y (map f (remove eqDec_X x l)).
Proof.
    intros X Y eqDec_X eqDec_Y l f HNodup; induction l as [|a l]; 
    intros x y Hneq; simpl; auto.
    inversion HNodup; subst.
    destruct (eqDec_X x a); subst; simpl.
    - destruct (eqDec_Y y (f a)); subst; try contradiction;
      apply IHl; auto.
    - destruct (eqDec_Y y (f a)); subst.
    -- rewrite <- IHl; auto.
    -- apply IHl; auto.
Qed.

Lemma multiplicity_map_eq : forall {X Y : Type} eqDec_X eqDec_Y (l : list X) (f : X -> Y),
    NoDup l ->
    forall x y, In x l -> f x = y -> 
    multiplicity_fix eqDec_Y y (map f l) = S (multiplicity_fix eqDec_Y y (map f (remove eqDec_X x l))).
Proof.
    intros X Y eqDec_X eqDec_Y l f HNodup; induction l as [|a l];
    intros x y HIn Heq; simpl.
    - inversion HIn.
    - inversion HNodup; subst.
      destruct (eqDec_X x a); subst; simpl.
    -- destruct (eqDec_Y (f a) (f a)); subst; try contradiction.
       eapply notin_remove in H1; rewrite H1; auto.
    -- destruct (eqDec_Y (f x) (f a)); subst.
    --- rewrite <- IHl; auto. inversion HIn; subst; try contradiction; auto.
    --- apply IHl; auto. inversion HIn; subst; try contradiction; auto.
Qed.

Lemma mIncluded_incl :  forall {A} eqDec_A (M N : list A),
    mIncluded eqDec_A M N ->
    incl M N.
Proof.
    intros A eqDec_A M N H a HIn; pose proof HIn as HIn';
    apply H in HIn; eapply multiplicity_succ in HIn'; eapply multiplicity_succ.
    apply le_same; eapply le_transitive; eapply le_same; eauto.
Qed.


Lemma mIncluded_length : forall {A} eqDec_A (M N : list A),
    mIncluded eqDec_A M N ->
    le (length M) (length N).
Proof.
    intros A eqDec_A M N H; rewrite mIncluded_universe in H;
    generalize dependent N; induction M as [|a M']; intros.
    - destruct N; apply le_same; simpl; auto.
    - assert (In a N) as HIn
      by (specialize H with a; simpl in H; destruct (eqDec_A a a); try contradiction;
          apply le_same in H; apply le_S_S in H; destruct H as [m H];
          eapply multiplicity_succ; rewrite H; simpl; auto).
      apply in_split in HIn; destruct HIn as [N1 [N2 HEq]];
      rewrite HEq; rewrite HEq in H.
      rewrite length_app; simpl;
      rewrite <- PeanoNat.Nat.add_succ_comm; 
      rewrite plus_Sn_m; rewrite <- length_app.
      apply le_same; simpl; apply le_same.
      apply IHM'; intros a'. 
      specialize H with a'; rewrite multiplicity_app_comm in H; simpl in H;
      destruct (eqDec_A a' a); subst;
      rewrite multiplicity_app_comm; auto.
Qed.

Lemma mIncluded_NoDup : forall {A} eqDec_A (M N : list A),
    NoDup N ->
    mIncluded eqDec_A M N ->
    NoDup M.
Proof.
    intros A eqDec_A M N HNd H. rewrite mIncluded_universe in H.
    induction M as [|a M'].
    - constructor.
    - constructor.
    -- intros contra.
       specialize H with a. simpl in H. destruct (eqDec_A a a); try contradiction.
       apply multiplicity_succ with (eqDec_A:=eqDec_A) in contra.
       assert (le_fix 1 (multiplicity_fix eqDec_A a N)) as HIn
       by (rewrite le_same in *; eapply le_transitive; eauto; eapply le_transitive with (y:=S (multiplicity_fix eqDec_A a M')); auto).
       apply multiplicity_succ in HIn.
       pose proof (multiplicity_NoDup_one eqDec_A a N HNd HIn) as HEq. rewrite HEq in H.
       rewrite le_same in contra. apply le_S_S in contra. destruct contra as [m contra]. rewrite contra in H.
       simpl in H. inversion H.
    -- apply IHM'. intros a'. specialize H with a'. simpl in H.
       destruct (eqDec_A a' a); subst; auto.
       rewrite le_same in *; apply le_transitive with (y := S (multiplicity_fix eqDec_A a M')); auto.
Qed.

Lemma incl_NoDup_mIncluded : forall {A} eqDec_A (M N : list A),
    NoDup M ->
    incl M N ->
    mIncluded eqDec_A M N.
Proof.
    intros A eqDec_A M N HNd HIncl.
    unfold mIncluded. unfold mIncludedHelper. unfold incl in HIncl.
    destruct M as [|a M']; intros a' HIn; simpl;
    try (inversion HIn; fail).
    inversion HNd; subst;
    destruct (eqDec_A a' a); subst;
    destruct HIn; subst; try contradiction.
    - apply multiplicity_zero with (eqDec_A:=eqDec_A) in H1; rewrite H1.
      apply multiplicity_succ; apply HIncl; simpl; auto.
    - rewrite multiplicity_NoDup_one; auto.
      apply multiplicity_succ; apply HIncl; simpl; auto.
Qed.

Lemma incl_NoDup_mSameset : forall {A} eqDec_A (M N : list A),
    NoDup M -> NoDup N ->
    incl M N -> incl N M ->
    mSameset eqDec_A M N.
Proof.
    intros A eqDec_A M N HNd_M HNd_N HIncl_MN HIncl_NM.
    apply mIncluded_antisymmetric; apply incl_NoDup_mIncluded; auto.
Qed.


Lemma mSameset_length : forall {A} eqDec_A (M N : list A),
    mSameset eqDec_A M N ->
    length M = length N.
Proof.
    intros A eqDec_A M N H; apply mSameset_correct in H;
    destruct H as [HM HN]; apply mIncluded_length in HM, HN;
    apply le_antisymmetric; auto.
Qed.

Lemma mStrictIncluded_length : forall {A} eqDec_A (M N : list A),
    mStrictIncluded eqDec_A M N ->
    le (length M + 1) (length N).
Proof.
    intros A eqDec_A M N H;
    generalize dependent N; induction M as [|a M']; 
    intros; destruct H as [HIncl HN].
    - destruct N.
    -- exfalso; apply HN; auto.
    -- simpl; apply le_same; simpl; auto.
    - rewrite mIncluded_universe in HIncl, HN.
      assert (In a N) as HIn
      by (specialize HIncl with a; simpl in HIncl; destruct (eqDec_A a a); try contradiction;
          apply le_same in HIncl; apply le_S_S in HIncl; destruct HIncl as [m HIncl];
          eapply multiplicity_succ; rewrite HIncl; simpl; auto).
      apply in_split in HIn; destruct HIn as [N1 [N2 HEq]];
      rewrite HEq; rewrite HEq in HIncl, HN; clear HEq.
      simpl; rewrite length_app; simpl;
      repeat rewrite <- PeanoNat.Nat.add_succ_comm; simpl;
      rewrite PeanoNat.Nat.add_0_r; rewrite <- length_app;
      rewrite <- PeanoNat.Nat.add_1_r;
      apply le_same; simpl; apply le_same.
      apply IHM'; split.
    -- intros a'; specialize HIncl with a';
       rewrite multiplicity_app_comm in HIncl; simpl in HIncl;
       destruct (eqDec_A a' a); subst;
       rewrite multiplicity_app_comm; auto.
    -- rewrite mIncluded_universe; intros contra; apply HN.
       intros a'; specialize contra with a'.
       rewrite multiplicity_app_comm; simpl;
       destruct (eqDec_A a' a); subst;
       rewrite multiplicity_app_comm; auto.
Qed.

Lemma mIncluded_cons_removeFirst : forall {A} eqDec_A (M N : list A) a,
    mIncluded eqDec_A (a :: M) N ->
    mIncluded eqDec_A M (removeFirst_fix eqDec_A a N).
Proof.
    intros A eqDec_A M N a H.
    rewrite mIncluded_universe; rewrite mIncluded_universe in H.
    intros a'; specialize H with a'.
    simpl in *; destruct (eqDec_A a' a); subst.
    - assert (In a N) as HIn
      by (eapply multiplicity_succ; rewrite le_same; 
          apply le_transitive with (y := S (multiplicity_fix eqDec_A a M)); 
          rewrite <- le_same; [simpl; auto|eauto]).
      rewrite multiplicity_removeFirst with (M:=N) in H; auto.
    - rewrite <- multiplicity_removeFirst_neq; auto.
Qed.

Lemma mSameset_cons_removeFirst : forall {A} eqDec_A (M N : list A) a,
    mSameset eqDec_A (a :: M) N ->
    mSameset eqDec_A M (removeFirst_fix eqDec_A a N).
Proof.
    intros A eqDec_A M N a H.
    rewrite mSameset_universe; rewrite mSameset_universe in H.
    intros a'; specialize H with a'.
    simpl in *; destruct (eqDec_A a' a); subst.
    - assert (In a N) as HIn by (eapply multiplicity_succ; rewrite <- H; simpl; auto).
      rewrite multiplicity_removeFirst with (M:=N) in H; auto.
    - rewrite <- multiplicity_removeFirst_neq; auto.
Qed.





Lemma mStrictIncluded_in : forall {A} eqDec_A (M N : list A) a,
    mIncluded eqDec_A M N ->
    In a N ->
    ~ In a M -> 
    mStrictIncluded eqDec_A M N.
Proof.
    intros A eqDec_A M N a HIncl HIn HNIn; split; auto;
    intros contra.
    assert (mSameset eqDec_A M N) as H by (apply mIncluded_antisymmetric; auto).
    rewrite mSameset_universe in H; specialize H with a;
    eapply multiplicity_succ in HIn; eapply multiplicity_zero in HNIn;
    rewrite <- H in HIn; rewrite HNIn in HIn; simpl in HIn; contradiction.
Qed.


Lemma filter_morigin : forall {X} (eq_dec : forall x1 x2, {x1=x2} + {x1<>x2}) {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l,
    mIncluded eq_dec (filter_fix PDec l) l.
Proof.
    intros X eq_dec P PDec l; apply mIncluded_universe; intros x;
    induction l as [|x' l']; simpl; auto;
    destruct (PDec x'); simpl; 
    destruct (eq_dec x x'); subst; simpl; auto.
    apply le_same; constructor; apply le_same; auto.
Qed.


(**
 ** filter 
 *)

Lemma filter_origin : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l,
    incl (filter_fix PDec l) l.
Proof.
    intros X P PDec l x HIn; induction l as [|x' l'];
    simpl in HIn; try contradiction.
    destruct (PDec x'); [destruct HIn|]; subst; simpl; auto.
Qed.


Lemma filter_P : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l x,
    In x (filter_fix PDec l) ->
    P x.
Proof. 
    intros X P PDec l x HIn; induction l as [|x' l'];
    simpl in HIn; try contradiction;
    destruct (PDec x'); auto;
    destruct HIn; subst; auto.
Qed.

Lemma P_filter : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l x,
    In x l ->
    P x ->
    In x (filter_fix PDec l).
Proof.
    intros X P PDec l x HIn HP; induction l as [|x' l'];
    simpl in HIn; try contradiction.
    simpl; destruct (PDec x'); destruct HIn; subst;
    simpl; auto; contradiction.
Qed.

Lemma negPDec : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) x,
    {~P x} + {~~P x}.
Proof.
    intros X P PDec x; specialize PDec with x; destruct PDec; auto.
Qed.

Lemma filter_neg_all : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l x,
    In x l ->
    In x (filter_fix PDec l) \/ In x (filter_fix (negPDec PDec) l).
Proof.
    intros X P PDec l x HIn; induction l as [|x' l']; simpl;
    try (inversion HIn; fail);
    destruct (PDec x'), (negPDec PDec x'); try contradiction;
    destruct HIn; subst; simpl; auto.
    - rewrite or_assoc; right; auto.
    - rewrite or_comm; rewrite or_assoc; right; rewrite or_comm; auto.
Qed. 

Lemma filter_NoDup : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l,
    NoDup l ->
    NoDup (filter_fix PDec l).
Proof.
    intros X P PDec l H; induction H as [|x l']; simpl; [constructor|].
    destruct (PDec x); [constructor|]; auto.
    intros contra; apply H; eapply filter_origin; eauto.
Qed.

(**
 ** filter
 ** forallP
 *)
Lemma forallP_filter : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l,
    forallP P (filter_fix PDec l).
Proof.
    intros X P PDec l x; apply filter_P.
Qed.


(** 
 ** forallP
 ** incl
 *)

Lemma forallP_incl : forall {X} (P : X -> Prop) l m,
    incl l m ->
    forallP P m ->
    forallP P l.
Proof.
    intros X P l m HIncl HFp x HIn;
    apply HFp; apply HIncl; auto.
Qed.



Lemma filter_length : forall {X} (eq_dec : forall x y : X, {x=y}+{x<>y}) {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l x,
    In x l ->
    P x ->
    le (length (filter_fix (negPDec PDec) l) + 1) (length l).
Proof.
    intros X eq_dec P PDec l x HIn HP.
    apply mStrictIncluded_length with (eqDec_A:=eq_dec).
    apply mStrictIncluded_in with (a:=x); auto.
    - apply filter_morigin.
    - intros contra; apply forallP_filter in contra; contradiction.
Qed.

(**
 ** filter
 ** incl
 *)

Lemma filter_incl : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) l m,
    incl l m ->
    incl (filter_fix PDec l) (filter_fix PDec m).
Proof.
    intros X P PDec l m HIncl x HIn.
    apply P_filter;
    [ apply filter_origin in HIn 
    | apply filter_P in HIn ];
    auto.
Qed.

Lemma P_filter_incl : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) {Q : X -> Prop} (QDec : forall x, {Q x} + {~ Q x}) l,
    (forall x, P x -> Q x) ->
    incl (filter_fix PDec l) (filter_fix QDec l).
Proof.
    intros X P PDec Q QDec l HImpl x HIn;
    apply P_filter;
    [ eapply filter_origin; eauto
    | apply HImpl; eapply filter_P; eauto ].
Qed.

Lemma P_filter_same : forall {X} {P : X -> Prop} (PDec : forall x, {P x} + {~ P x}) {Q : X -> Prop} (QDec : forall x, {Q x} + {~ Q x}) l,
    (forall x, P x <-> Q x) ->
    (filter_fix PDec l) = (filter_fix QDec l).
Proof.
    intros X P PDec Q QDec l HIff; induction l as [|x' l']; simpl; auto.
    destruct (PDec x') as [p|np], (QDec x') as [q|nq].
    -- rewrite IHl'; auto.
    -- apply HIff in p. contradiction.
    -- apply HIff in q. contradiction.
    -- auto.
Qed.


(** 
 ** length 
 *)

Lemma listEq_length : forall {X : Type} (l m : list X),
    l = m ->
    length l = length m.
Proof.
    intros X l m H; 
    destruct l; subst; auto.
Qed.

Lemma length_app_comm : forall {X : Type} (l m : list X),
    length (l ++ m) = length (m ++ l).
  Proof.
    intros; repeat rewrite length_app;
    rewrite PeanoNat.Nat.add_comm; auto.
  Qed.





(** 
 ** length
 ** removeFirst 
 *)

Lemma removeFirst_lengthAdd : forall {X} eq_dec a (l : list X),
    In a l ->
    length (removeFirst_fix eq_dec a l) + 1 = length l.
Proof.
    intros X eq_dec a l HIn.
    induction l as [|x l']; [inversion HIn|]; simpl;
    destruct (eq_dec x a) as [Heqx|Heqx]; subst.
    - rewrite PeanoNat.Nat.add_1_r; auto.
    - destruct HIn as [HIn|HIn]; subst; simpl;
      try contradiction;
      apply IHl' in HIn; rewrite <- HIn; auto.
Qed.

Lemma removeFirst_lengthSub : forall {X} eq_dec a (l : list X),
    In a l ->
    length (removeFirst_fix eq_dec a l) = length l - 1.
Proof.
    intros X eq_dec a l HIn; 
    induction l as [|x l']; [inversion HIn|]; simpl;
    destruct (eq_dec x a) as [Heqx|Heqx]; subst.
    - rewrite PeanoNat.Nat.sub_0_r; auto.
    - destruct HIn as [HIn|HIn]; subst; simpl;
      try contradiction.
      assert (exists n, length l' = S n) as Hl' 
        by (destruct l'; [inversion HIn | simpl; exists (length l'); auto]).
      apply IHl' in HIn; rewrite HIn;
      destruct Hl' as [n Hl']; rewrite Hl';
      simpl; rewrite PeanoNat.Nat.sub_0_r; auto.
Qed.



(** 
 ** length
 ** nodup 
 *)

Lemma NoDup_incl_length : forall {X} (l m : list X),
    NoDup l ->
    incl l m->
    length l <= length m.
Proof.
    intros X l m HNd HIncl;
    generalize dependent m; induction HNd; intros.
    - apply le_same; simpl; auto.
    - assert (In x m) as HIn by (apply HIncl; simpl; auto);
      apply in_split in HIn; destruct HIn as [m1 [m2 HEq]];
      rewrite HEq.
      assert (forall x, In x l -> In x (m1 ++ m2)).
      { intros x0 HIn;
        assert (In x0 m) as HIn' by (apply HIncl; simpl; auto); rewrite HEq in HIn';
        assert (x <> x0) as HNeq by (intros contra; subst; contradiction);
        apply in_app_iff; apply in_app_or in HIn'; destruct HIn' as [HIn'|HIn']; auto;
        destruct HIn'; [contradiction|auto]. }
      rewrite length_app; simpl; rewrite <- plus_n_Sm; rewrite <- length_app;
      apply le_same; simpl; apply le_same;
      apply IHHNd; auto.
Qed.



(**
 ** nodup
 ** snd
 *)

Lemma NoDup_map_snd : forall {X Y : Type} (l : list (X * Y)) (x1 x2 : X) (y : Y),
    NoDup (map snd l) ->
    In (x1, y) l ->
    In (x2, y) l ->
    x1 = x2.
Proof.
    intros X Y l. induction l as [|[x' y'] l']; intros x1 x2 y HNd HIn1 HIn2;
    simpl in *; [inversion HIn1|].
    inversion HNd; subst.
    destruct HIn1 as [HIn1|HIn1], HIn2 as [HIn2|HIn2]; subst.
    - inversion HIn1; inversion HIn2; subst; auto.
    - exfalso; inversion HIn1; subst;
      apply H1; apply in_map_iff; exists (x2,y); auto.
    - exfalso; inversion HIn2; subst;
      apply H1; apply in_map_iff; exists (x1,y); auto.
    - eapply IHl'; eauto.
Qed.


(**
 ** cons
 ** app
 *)

Lemma cons_eq_app : forall {X} (xs1 xs2 : list X),
    xs1 <> nil ->
    exists x' xs', xs1 ++ xs2 = x' :: xs'.
Proof.
    intros X xs1 xs2 HNeq; destruct xs1 as [|x1 xs1'];
    try contradiction.
     exists x1; exists (xs1' ++ xs2); apply app_comm_cons.
Qed.



Lemma map_remove_in : forall {X Y : Type} eqDec_X eqDec_Y (l : list X) (f : X -> Y) x y,
    In y (map f (remove eqDec_X x l)) ->
    f x <> y ->
    In y (remove eqDec_Y (f x) (map f l)).
Proof.
    intros X Y eqDec_X eqDec_Y l f x y HIn HNeq.
    induction l as [|x' l']; simpl in *; auto.
    destruct (eqDec_X x x'); subst.
    - destruct (eqDec_Y (f x') (f x')) as [|contra]; [|exfalso; apply contra; auto].
        apply IHl'; auto.
    - destruct HIn; destruct (eqDec_Y (f x) (f x')).
    -- rewrite H in e; contradiction.
    -- left; auto.
    -- apply IHl'; auto.
    -- right; apply IHl'; auto.
Qed.


Lemma remove_NoDup : forall {X : Type} eqDec_X (x : X) l,
    NoDup l ->
    NoDup (remove eqDec_X x l).
Proof.
    intros X eqDec_X x l H; induction l as [|a l];
    simpl; auto; inversion H; subst;
    destruct (eqDec_X x a); subst.
    -- apply IHl; auto.
    -- apply NoDup_cons.
    --- intros contra; apply H2. 
        apply in_remove in contra; destruct contra; auto.
    --- apply IHl; auto.
Qed.

Lemma removeFirst_in : forall {X} eq_dec a b (l : list X),
    a <> b ->
    In b l <->
    In b (removeFirst_fix eq_dec a l).
Proof.
    intros X eq_dec a b l HNeq; split; intros H.
    - induction l as [|x' l']; simpl; [inversion H|].
      destruct (eq_dec x' a), H; subst; simpl; auto.
      contradiction.
    - induction l as [|x' l']; simpl in H; [inversion H|].
      destruct (eq_dec x' a); subst; simpl; auto.
      destruct H; subst; simpl; auto.
Qed.



Lemma removeFirst_NoDup : forall {X} eq_dec a (l : list X),
    NoDup l ->
    NoDup (removeFirst_fix eq_dec a l).
Proof.
    intros X eq_dec a l H; induction H; simpl;
    [apply NoDup_nil|].
    destruct (eq_dec x a); auto.
    apply NoDup_cons; auto.
    intros contra; apply H; eapply removeFirst_in; eauto.
Qed.


