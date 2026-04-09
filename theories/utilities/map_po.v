Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.

Require Import AttestationProtocolOrdering.utilities.mset.
Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.
Require Import AttestationProtocolOrdering.utilities.partialfun.
Require Import AttestationProtocolOrdering.utilities.tsort.

Section MapPo. 

(* Partial order of labels *)
    Context {L : Type}.
    Context (eqDec_L : forall l1 l2 : L, {l1 = l2} + {l1 <> l2}).

    Context (po : L -> L -> Prop).
    Context (poDec : forall l1 l2, {po l1 l2} + {~ po l1 l2}).
    Context (po_reflexive : forall l, po l l).
    Context (po_antisymmetric : forall l1 l2, po l1 l2 -> po l2 l1 -> l1 = l2).
    Context (po_transitive : forall l1 l2 l3, po l1 l2 -> po l2 l3 -> po l1 l3).


(* Lift partial order over labels to preorder over events *)

    Definition pre {T : Type} (lt : T -> L) (t1 t2 : T) : Prop :=
        po (lt t1) (lt t2).

    Lemma preDec : forall {T} (lt : T -> L) t1 t2,
        {pre lt t1 t2} + {~ pre lt t1 t2}.
    Proof. intros; apply poDec. Defined.

    Lemma pre_reflexive : forall {T} (lt : T -> L) t,
        pre lt t t.
    Proof. intros; apply po_reflexive. Qed.

    Lemma pre_transitive : forall {T} (lt : T -> L) t1 t2 t3,
        pre lt t1 t2 -> pre lt t2 t3 -> pre lt t1 t3.
    Proof. intros; eapply po_transitive; eauto. Qed.


(* The various definition of maximal are equivalent *)

    Lemma maximal_same : forall {T} (lt : T -> L) ts m,
        maximal (pre lt) ts m <->
        maximal po (map lt ts) (lt m).
    Proof.
        intros T lt ts m; split; intros H.
        - intros l HIn HPo.
          apply in_map_iff in HIn. destruct HIn as [t [HEq HIn]]; subst.
          apply H; auto.
        - intros t HIn HPre.
          apply H; auto.
          apply in_map; auto.
    Qed.

    Lemma maximal_same' : forall {T} (lt : T -> L) ts m,
        forallP (fun l => po (lt m) l -> l = (lt m)) (map lt ts) <->
        maximal po (map lt ts) (lt m).
    Proof.
        intros T lt ts m; split; intros H l HIn HPo.
        - apply H in HIn; apply HIn in HPo; subst; auto.
        - pose proof HIn as HInMp.
          apply in_map_iff in HIn; destruct HIn as [t [HEq HIn]]; subst.
          apply po_antisymmetric; auto.
    Qed.



(* Maximal elements are mapped to equivalent labels *)
    Theorem max_fixed : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (g : Y -> X) (xs : list X) (ys : list Y),
    (* Maps f:X->Y and g:Y->X between lists xs and ys *)
        partialFunction f xs ys ->
        partialFunction g ys xs ->
    (* Maps according to label partial order *)
        (forall x, In x xs -> po (lx x) (ly (f x))) ->
        (forall y, In y ys -> po (ly y) (lx (g y))) ->
    (* Maximal elements are mapped to equivalent labels *)    
        forall m, In m xs ->
        maximal po (map lx xs) (lx m) ->
        (ly (f m)) = (lx m).
    Proof.
        intros X Y lx ly f g xs ys HfIn HgIn HfPo HgPo m HmIn Hm.
        apply maximal_same' in Hm.
        pose proof (HfIn m HmIn) as HfmIn.
        pose proof (HfPo m HmIn).
        pose proof (HgPo (f m) HfmIn).
        assert ((lx (g (f m))) = (lx m)) as HEq
        by (apply Hm; [apply in_map; apply HgIn; auto | eapply po_transitive; eauto]).
        apply po_antisymmetric; auto.
        rewrite <- HEq; auto.
    Qed.  


(* Maximal elements are mapped to maximal elements *)
    Lemma max_to_max : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (g : Y -> X) (xs : list X) (ys : list Y),
    (* Maps f:X->Y and g:Y->X between lists xs and ys *)
        partialFunction f xs ys ->
        partialFunction g ys xs ->
    (* Maps according to label partial order *)
        (forall x, In x xs -> po (lx x) (ly (f x))) ->
        (forall y, In y ys -> po (ly y) (lx (g y))) ->
    (* Maximal elements are mapped to maximal elements *)
        forall m, In m xs ->
        maximal po (map lx xs) (lx m) ->
        maximal po (map ly ys) (ly (f m)).
    Proof.
        intros X Y lx ly f g xs ys HfIn HgIn HfPo HgPo m HmIn Hm.
        apply maximal_same with (lt:=ly); apply maximal_same with (lt:=lx) in Hm.
        intros y HyIn HfmyPo.
        pose proof (HfIn m HmIn) as HfmIn.
        pose proof (HfPo m HmIn) as HmfmPo.
        pose proof (HgPo y HyIn) as HygyPo.
        assert (po (lx (g y)) (lx m))  as HgymPo
        by (apply Hm; [apply HgIn; auto | eapply po_transitive; eauto]).
        eapply po_transitive; eauto.
    Qed.





(* Maps are surjective over maximal elements *)
    Lemma max_partialSurjective : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (g : Y -> X) (xs : list X) (ys : list Y),
    (* Decidable equality on Y *)
        (forall y1 y2 : Y, {y1=y2}+{y1<>y2}) ->
    (* No duplicates in lists xs and ys *)
        NoDup xs ->    
        NoDup ys ->
    (* Bijections f:X->Y and g:Y->X between lists xs and ys *)
        partialBijective f xs ys ->
        partialBijective g ys xs ->
    (* Maps according to label partial order *)
        (forall x, In x xs -> po (lx x) (ly (f x))) ->
        (forall y, In y ys -> po (ly y) (lx (g y))) ->
    (* Map is surjective over maximal elements *)
        partialSurjective f (getMaximals_fix (pre lx) (preDec lx) xs xs) (getMaximals_fix (pre ly) (preDec ly) ys ys).
    Proof.
        intros X Y lx ly f g xs ys eqDec_Y HxNd HyNd HfBij HgBij HfPo HgPo.
        destruct HfBij as [HfInj [HfSur Hf]].
        destruct HgBij as [HgInj [HgSur Hg]].
        apply cantorSchroderBernstein_finite with (g:=g); auto.
        - apply filter_NoDup; auto.
        - apply filter_NoDup; auto.
        - intros x HIn; pose proof HIn as HMax.
          apply filter_origin in HIn; apply filter_P in HMax.
          apply P_filter.
        -- apply Hf; auto.
        -- apply maximal_same; apply maximal_same in HMax.
           eapply max_to_max; eauto.
        - intros y HIn; pose proof HIn as HMax.
          apply filter_origin in HIn; apply filter_P in HMax.
          apply P_filter.
        -- apply Hg; auto.
        -- apply maximal_same; apply maximal_same in HMax.
           eapply max_to_max; eauto.
        - eapply partialInjective_incl; eauto.
          apply filter_origin.
        - eapply partialInjective_incl; eauto.
          apply filter_origin.
    Qed.



(* Maps are bijective over maximal elements *)
    Lemma max_partialBijective : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (g : Y -> X) (xs : list X) (ys : list Y),
    (* Decidable equality on Y *)
        (forall y1 y2 : Y, {y1=y2}+{y1<>y2}) ->
    (* No duplicates in lists xs and ys *)
        NoDup xs ->    
        NoDup ys ->
    (* Bijections f:X->Y and g:Y->X between lists xs and ys *)
        partialBijective f xs ys ->
        partialBijective g ys xs ->
    (* Maps according to label partial order *)
        (forall x, In x xs -> po (lx x) (ly (f x))) ->
        (forall y, In y ys -> po (ly y) (lx (g y))) ->
    (* Map is surjective over maximal elements *)
        partialBijective f (getMaximals_fix (pre lx) (preDec lx) xs xs) (getMaximals_fix (pre ly) (preDec ly) ys ys).
    Proof.
        intros X Y lx ly f g xs ys eqDec_Y HxNd HyNd HfBij HgBij HfPo HgPo.
        destruct HfBij as [HfInj [HfSur Hf]].
        destruct HgBij as [HgInj [HgSur Hg]].
        repeat split.
        - eapply partialInjective_incl; eauto.
          apply filter_origin.
        - eapply max_partialSurjective; eauto;
          repeat split; auto.
        - intros x HIn; pose proof HIn as HMax.
          apply filter_origin in HIn; apply filter_P in HMax.
          apply P_filter.
        -- apply Hf; auto.
        -- apply maximal_same; apply maximal_same in HMax.
           eapply max_to_max; eauto.
    Qed.



(* Maximal elements are mapped from maximal elements *)
    Lemma max_from_max : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (g : Y -> X) (xs : list X) (ys : list Y),
    (* Decidable equality on X and Y *)
        (forall x1 x2 : X, {x1=x2} + {x1<>x2}) ->
        (forall y1 y2 : Y, {y1=y2} + {y1<>y2}) ->
    (* No duplicates in lists xs and ys *)
        NoDup xs ->    
        NoDup ys ->
    (* Maps f:X->Y and g:Y->X between lists xs and ys *)
        partialFunction f xs ys ->
        partialFunction g ys xs ->
    (* Injective maps f and g *)
        partialInjective f xs ->
        partialInjective g ys ->
    (* Maps according to label partial order *)
        (forall x, In x xs -> po (lx x) (ly (f x))) ->
        (forall y, In y ys -> po (ly y) (lx (g y))) ->
    (* Maximal elements are mapped from maximal elements *)
        forall mx, In mx xs ->
        maximal po (map ly ys) (ly (f mx)) ->
        maximal po (map lx xs) (lx mx).
    Proof.
        intros X Y lx ly f g xs ys eqDec_X eqDec_Y HxNd HyNd HfIn HgIn HfInj HgInj HfPo HgPo m HmIn Hm.
        assert (partialSurjective f xs ys) as HfSur by (eapply cantorSchroderBernstein_finite; eauto).
        assert (partialBijective f xs ys) as HfBij by (repeat split; auto).
        assert (partialSurjective g ys xs) as HgSur by (eapply cantorSchroderBernstein_finite; eauto).
        assert (partialBijective g ys xs) as HgBij by (repeat split; auto).
        assert (partialBijective f (getMaximals_fix (pre lx) (preDec lx) xs xs) (getMaximals_fix (pre ly) (preDec ly) ys ys)) as HfmBij
        by (eapply max_partialBijective; eauto).
        pose proof (HfIn m HmIn) as HfmIn.
        assert (In (f m) (getMaximals_fix (pre ly) (preDec ly) ys ys)) as HfmInM
        by (apply P_filter; [apply HfIn; auto | apply maximal_same; auto]).
        pose proof (partialBijective_origin_unique f (getMaximals_fix (pre lx) (preDec lx) xs xs) (getMaximals_fix (pre ly) (preDec ly) ys ys) HfmBij (f m) HfmInM) as HUniqM.
        destruct HUniqM as [m' [[Hm'InM Hm'Eq] HUniqM]].
        pose proof (partialBijective_origin_unique f xs ys HfBij (f m) HfmIn) as HUniq.
        destruct HUniq as [x' [[Hx'In Hx'Eq] HUniq]].
        assert (x' = m') as HEq' by (apply HUniq; split; [eapply filter_origin; eauto | auto]).
        assert (x' = m) as HEq by (apply HUniq; split; auto). subst.
        rewrite <- maximal_same. eapply filter_P; eauto.
    Qed.





(* All elements are mapped to equivalent labels *)
    Theorem function_fixed : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (g : Y -> X) (xs : list X) (ys : list Y),
    (* Decidable equality on X and Y *)
        (forall x1 x2 : X, {x1=x2} + {x1<>x2}) ->
        (forall y1 y2 : Y, {y1=y2} + {y1<>y2}) ->
    (* No duplicates in lists xs and ys *)
        NoDup xs ->
        NoDup ys ->
    (* Maps f:X->Y and g:Y->X between lists xs and ys *)
        partialFunction f xs ys ->
        partialFunction g ys xs ->
    (* Injective maps f and g *)
        partialInjective f xs ->
        partialInjective g ys ->
    (* Maps according to label partial order *)
        (forall x, In x xs -> po (lx x) (ly (f x))) ->
        (forall y, In y ys -> po (ly y) (lx (g y))) ->
    (* All elements are mapped to equivalent labels *)
        forall x, In x xs ->
        (ly (f x)) = (lx x).
    Proof.
        intros X Y lx ly f g xs ys eqDec_X eqDec_Y HxNd HyNd HfIn HgIn HfInj HgInj HfPo HgPo x HIn.
        pose proof (preDec lx); pose proof (pre_reflexive lx); pose proof (pre_transitive lx).
        pose proof (tsort_terminates eqDec_X (pre lx) (preDec lx) (pre_transitive lx) xs) as HTs.
        destruct HTs as [sxs HTs]. pose proof HTs as HAll.
        apply tsort_same in HTs, HAll; auto. apply tsort_all in HAll; auto.
        apply HAll in HIn. clear HAll.
        generalize dependent ys. induction HTs as [xs mxs nmxs snmxs HCons HM HN HS|]; intros.
        - apply getMaximals_same with (preDec := preDec lx) in HM.
          apply getNonMaximals_same with (preDec := preDec lx) in HN.
          apply in_app_or in HIn. destruct HIn as [HIn|HIn].
        -- eapply max_fixed; eauto.
        --- eapply filter_origin. rewrite <- HM in HIn; eauto.
        --- rewrite <- maximal_same.
            eapply filter_P; rewrite <- HM in HIn; eauto.
        -- apply IHHS with (getNonMaximals_fix (pre ly) (preDec ly) ys ys).
        --- rewrite <- HN. apply filter_NoDup; auto.
        --- intros x1 x2 [HIn1 HIn2]. apply HfInj.
            split; eapply filter_origin; rewrite <- HN in HIn1, HIn2; eauto.
        --- intros a HaIn. apply HfPo.
            eapply filter_origin; rewrite <- HN in HaIn; eauto.
        --- auto.
        --- apply filter_NoDup. auto.
        --- intros a HaInN. 
            assert (In a xs) as HaInX by (eapply filter_origin; rewrite <- HN in HaInN; eauto).
            apply P_filter; auto.
            rewrite <- HN in HaInN; apply filter_P in HaInN.
            intros contra; apply HaInN.
            apply maximal_same; apply maximal_same in contra.
            eapply max_from_max; eauto.
        --- intros y HyInN.
            assert (In y ys) as HyInY by (eapply filter_origin; eauto).
            pose proof (HgIn y HyInY) as HgyIn.
            rewrite <- HN. apply P_filter; auto.
            apply filter_P in HyInN.
            intros contra; apply HyInN.
            apply maximal_same; apply maximal_same in contra.
            apply max_from_max with (ly:=lx) (f:=g) (g:=f) (ys:=xs); auto.
        --- intros y1 y2 [HIn1 HIn2]. apply HgInj.
            split; eapply filter_origin; eauto.
        --- intros y HInNmys. apply HgPo.
            eapply filter_origin; eauto.
        - inversion HIn.
    Qed.


    Theorem partialBijective_mSameset : forall {X Y} (lx : X -> L) (ly : Y -> L)
        (f : X -> Y) (xs : list X) (ys : list Y),
    (* Decidable equality on X and Y *)
        (forall x1 x2 : X, {x1=x2} + {x1<>x2}) ->
        (forall y1 y2 : Y, {y1=y2} + {y1<>y2}) ->
    (* No duplicates in lists xs and ys *)
        NoDup xs ->
        NoDup ys ->
    (* Bijections f:X->Y and g:Y->X between lists xs and ys *)
        partialBijective f xs ys ->
    (* All elements are mapped to equivalent labels *)
        (forall x, In x xs -> (ly (f x)) = (lx x)) ->
    (* Label msets are equivalent *)
        mSameset eqDec_L (map lx xs) (map ly ys).
    Proof.
        intros X Y lx ly f xs ys eqDec_X eqDec_Y HxNd HyNd [HfInj [HfSur HfIn]] HfEq.
        apply mSameset_universe.
        generalize dependent ys. induction xs as [|x' xs'];
        intros ys HyNd HfSur HfIn a.
        - destruct ys as [|y' ys']; simpl; auto.
          assert (In y' (y'::ys')) as HIn by (simpl; auto).
          apply HfSur in HIn. destruct HIn as [x [HxIn HEq]]. inversion HxIn.
        - simpl. destruct (eqDec_L a (lx x')); subst. 
        -- pose proof (multiplicity_map_eq eqDec_Y eqDec_L ys ly HyNd (f x') (lx x')) as HM.
           rewrite HM; [| apply HfIn | apply HfEq]; simpl; auto.
           apply eq_S. 
           apply IHxs'.
        --- inversion HxNd; subst; auto.
        --- apply partialInjective_incl with (xs:=x'::xs'); simpl; auto.
             intros x HIn; simpl; auto.
        --- intros. apply HfEq; simpl; auto.
        --- apply remove_nodup; auto.
        --- unfold partialSurjective in *.
             intros y HyIn. apply in_remove in HyIn. destruct HyIn as [HyIn HyNeq].
             apply HfSur in HyIn. destruct HyIn as [x [HxIn HxEq]].
             destruct HxIn; subst; try contradiction.
             exists x; split; auto.
        --- unfold partialFunction in *.
             intros x HxIn. inversion HxNd; subst.
             assert (x <> x') as HxNeq by (intros contra; subst; contradiction).
             pose proof (in_cons x' x xs' HxIn) as HxIn'. apply HfIn in HxIn'.
             apply in_in_remove; auto.
             intros contra. apply HxNeq. apply HfInj; [split|]; simpl; auto.
        -- pose proof (multiplicity_map_neq eqDec_Y eqDec_L ys ly HyNd (f x') a) as HM.
           rewrite HM; [| intros contra; apply n; rewrite <- contra; apply HfEq; simpl; auto].
           apply IHxs'.
        --- inversion HxNd; subst; auto.
        --- apply partialInjective_incl with (xs:=x'::xs'); simpl; auto.
             intros x HIn; simpl; auto.
        --- intros. apply HfEq; simpl; auto.
        --- apply remove_nodup; auto.
        --- unfold partialSurjective in *.
             intros y HyIn. apply in_remove in HyIn. destruct HyIn as [HyIn HyNeq].
             apply HfSur in HyIn. destruct HyIn as [x [HxIn HxEq]].
             destruct HxIn; subst; try contradiction.
             exists x; split; auto.
        --- unfold partialFunction in *.
             intros x HxIn. inversion HxNd; subst.
             assert (x <> x') as HxNeq by (intros contra; subst; contradiction).
             pose proof (in_cons x' x xs' HxIn) as HxIn'. apply HfIn in HxIn'.
             apply in_in_remove; auto.
             intros contra. apply HxNeq. apply HfInj; [split|]; simpl; auto.
    Qed. 



End MapPo.