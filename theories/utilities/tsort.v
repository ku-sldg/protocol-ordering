Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.

Require Import AttestationProtocolOrdering.utilities.mset.
Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.

Section TSort. 

    Context {X : Type}.
    Context (eq_dec : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}).
    Context (pre : X -> X -> Prop).
    Context (preDec : forall x1 x2, {pre x1 x2} + {~ pre x1 x2}).
    Context (pre_reflexive : forall x, pre x x).
    Context (pre_transitive : forall x1 x2 x3, pre x1 x2 -> pre x2 x3 -> pre x1 x3).


(** maximal *)

    Definition maximal (xs : list X) (mx : X) : Prop :=
        forallP (fun x => pre mx x -> pre x mx) xs.
  
    Lemma maximalDec : forall xs mx,
        {maximal xs mx} + {~ maximal xs mx}.
    Proof.
        intros xs mx; apply forallPDec; intros x;
        destruct (preDec mx x); destruct (preDec x mx); auto.
        left; intros; contradiction.
    Defined.

    Lemma maximal_incl : forall xs xs' mx,
        incl xs' xs ->
        maximal xs mx ->
        maximal xs' mx.
    Proof.
        intros xs xs' mx HIncl HMx x HIn HOrd; apply HMx; auto.
    Qed.

    Theorem maximal_exists : forall (xs : list X),
        xs <> nil ->
        exists mx, In mx xs /\ maximal xs mx.
    Proof.
        unfold maximal; intros xs HNil; induction xs as [|x' xs'].
        - exfalso; apply HNil; auto.
        - destruct xs' as [|x'' xs''].
        -- exists x'; split; simpl; auto;
           intros x HIn HOrd; destruct HIn as [|HIn]; subst; auto; inversion HIn.
        -- assert (x''::xs'' <> nil) as HN by (intros contra; inversion contra);
           pose proof (IHxs' HN) as IH; destruct IH as [mx'' IH]; destruct IH as [HIn'' IH].
           destruct (preDec mx'' x') as [p|np].
        --- exists x'; split; simpl; auto;
            intros x HIn HOrd; destruct HIn as [|HIn]; subst; auto.
            pose proof (IH x HIn) as HMx;
            pose proof (pre_transitive mx'' x' x p HOrd) as HOrd'.
            apply HMx in HOrd'.
            eapply pre_transitive; eauto.
        --- exists mx''; split; simpl; auto;
            intros x HIn HOrd; destruct HIn as [|HIn]; subst; try contradiction;
            apply IH; auto.
    Qed.



(** getMaximals *)

    Definition getMaximals_fix (XS xs : list X) : list X :=
        filter_fix (maximalDec XS) xs.

    Definition getMaximals_ind (XS : list X) : list X -> list X -> Prop :=
        filter_ind (maximal XS).

    Lemma getMaximals_same : forall XS xs mxs,
        getMaximals_fix XS xs = mxs <->
        getMaximals_ind XS xs mxs.
    Proof.
        intros; apply filter_same.
    Qed.

    (* Lemma getMaximals_incl : forall XS XS' xs,
        incl XS' XS ->
        incl (getMaximals_fix XS xs) (getMaximals_fix XS' xs).
    Proof.
        intros XS XS' xs HIncl mx HIn.
        induction xs as [|x' xs'].
        - inversion HIn.
        - unfold getMaximals_fix in *. simpl in *.
          destruct (maximalDec XS x').
        -- eapply forallP_incl in m; eauto.
           destruct (maximalDec XS' x'); try contradiction.
           destruct HIn; subst; simpl; auto.
        -- destruct (maximalDec XS' x'); simpl; auto.
    Qed. *)

    Lemma getMaximals_maximal : forall xs mx,
        In mx (getMaximals_fix xs xs) ->
        maximal (getMaximals_fix xs xs) mx.
    Proof.
        intros xs mx HIn; eapply forallP_incl;
        [ apply filter_origin
        | apply filter_P with (PDec:=maximalDec xs) (l:=xs); auto ].
    Qed.

    Lemma getMaximals_nonempty : forall xs,
        xs <> nil ->
        (getMaximals_fix xs xs) <> nil.
    Proof.
        intros xs H; apply maximal_exists in H; destruct H as [mx [HIn HMx]];
        pose proof (P_filter (maximalDec xs) xs mx HIn HMx) as H;
        unfold getMaximals_fix; intros contra; rewrite contra in H; inversion H.
    Qed.




(** getNonMaximals *)

    Definition getNonMaximals_fix (XS xs : list X) : list X :=
        filter_fix (negPDec (maximalDec XS)) xs.

    Definition getNonMaximals_ind (XS : list X) : list X -> list X -> Prop :=
        filter_ind (fun x => ~ maximal XS x).

    Lemma getNonMaximals_same : forall XS xs nmxs,
        getNonMaximals_fix XS xs = nmxs <->
        getNonMaximals_ind XS xs nmxs.
    Proof.
        intros XS xs nmxs; apply filter_same.
    Qed.

    Lemma getNonMaximals_length : forall xs,
        xs <> nil ->
        le (length (getNonMaximals_fix xs xs) + 1) (length xs).
    Proof.
        intros xs HNil.
        pose proof (filter_morigin eq_dec (negPDec (maximalDec xs)) xs) as HIncl.
        pose proof (maximal_exists xs HNil) as HMx. destruct HMx as [mx [HIn HMax]].
        assert (~ In mx (getNonMaximals_fix xs xs)) as HNIn 
        by (intros contra; apply filter_P in contra; contradiction).
        eapply mStrictIncluded_length; eapply mStrictIncluded_in; eauto.
    Qed.




(** tsort *)

    Inductive tsort_ind : list X -> list X -> Prop :=
    | tsortCons : forall xs mxs nmxs snmxs,
        xs <> nil ->
        getMaximals_ind xs xs mxs ->
        getNonMaximals_ind xs xs nmxs ->
        tsort_ind nmxs snmxs ->
        tsort_ind xs (mxs ++ snmxs)
    | tsortNil :
        tsort_ind nil nil.

    Fixpoint tsort_option_fuel (fuel : nat) (xs : list X) : option (list X) :=
    match fuel with
    | S fuel' => match xs with
                 | cons _ _ => match tsort_option_fuel fuel' (getNonMaximals_fix xs xs) with
                        | Some snmxs => Some ((getMaximals_fix xs xs) ++ snmxs)
                        | None => None
                        end
                 | _ => Some nil
                 end
    | _ => None
    end.

    Definition tsort_option (xs : list X) : option (list X) :=
        tsort_option_fuel (length xs + 1) xs.
        

    Lemma tsort_fuel_terminates : forall fuel xs,
        le (length xs + 1) fuel ->
        exists sxs, tsort_option_fuel fuel xs = Some sxs.
    Proof.
        intros fuel xs HLen.
        generalize dependent xs; induction fuel as [|fuel']; intros.
        - rewrite PeanoNat.Nat.add_1_r in HLen; simpl in HLen; inversion HLen.
        - simpl; destruct xs.
        -- exists nil; auto.
        -- remember (tsort_option_fuel fuel' (getNonMaximals_fix (x :: xs) (x :: xs))) as snmxs;
           destruct snmxs as [snmxs|].
        --- eauto.
        --- exfalso; assert (x :: xs <> nil) as HNil by (intros contra; inversion contra);
            remember (x::xs) as l.
            pose proof (getNonMaximals_length l HNil).
            rewrite PeanoNat.Nat.add_1_r in HLen; apply le_same in HLen; simpl in HLen; apply le_same in HLen.
            assert (le (length (getNonMaximals_fix l l) + 1) fuel') as HLen' by (eapply le_transitive; eauto).
            apply IHfuel' in HLen'; destruct HLen' as [snmxs contra].
            rewrite <- Heqsnmxs in contra; inversion contra.
    Qed.

    Lemma tsort_terminates : forall xs,
        exists sxs, tsort_option xs = Some sxs.
    Proof.
        intros; apply tsort_fuel_terminates; auto.
    Qed.


    Lemma tsort_fuel_same : forall fuel xs sxs,
        le (length xs + 1) fuel ->
        tsort_option_fuel fuel xs = Some sxs <->
        tsort_ind xs sxs.
    Proof.
        intros fuel xs sxs HLen; split; intros H.
        - generalize dependent xs; generalize dependent sxs. 
          induction fuel as [|fuel']; intros; 
          destruct xs as [|x' xs']; try (simpl in HLen; inversion HLen; fail); simpl in H.
        -- inversion H; subst; apply tsortNil.
        -- remember (tsort_option_fuel fuel' (getNonMaximals_fix (x' :: xs') (x' :: xs'))) as snmxs.
           destruct snmxs as [snmxs|]; inversion H; subst.
           eapply tsortCons.
        --- intros contra; inversion contra.
        --- apply getMaximals_same; auto.
        --- apply getNonMaximals_same; auto.
        --- apply IHfuel'; auto.
             apply le_transitive with (y := length (x'::xs')).
        ---- apply getNonMaximals_length; intros contra; inversion contra.
        ---- remember (x'::xs') as l.
             rewrite PeanoNat.Nat.add_1_r in HLen; apply le_same in HLen; simpl in HLen; apply le_same in HLen.
             auto.
        - generalize dependent fuel; induction H; intros.
        -- destruct fuel as [|fuel']; 
           destruct xs as [|x' xs']; try (simpl in HLen; inversion HLen; fail); 
           simpl; try contradiction.
           remember (x'::xs') as l.
           remember (tsort_option_fuel fuel' (getNonMaximals_fix l l)) as snmxs'.
           destruct snmxs' as [snmxs'|].
        --- apply getMaximals_same in H0; rewrite H0.
            pose proof (getNonMaximals_length l H) as HLen'.
            assert (le (length (getNonMaximals_fix l l) + 1) fuel') as HFuel 
            by (rewrite PeanoNat.Nat.add_1_r in HLen; apply le_same in HLen; simpl in HLen; apply le_same in HLen;
                eapply le_transitive; eauto).
            apply getNonMaximals_same in H1; rewrite H1 in Heqsnmxs'; rewrite H1 in HFuel.
            apply IHtsort_ind in HFuel; rewrite <- Heqsnmxs' in HFuel; inversion HFuel; auto.
        --- pose proof (getNonMaximals_length l H) as HLen'.
            assert (le (length (getNonMaximals_fix l l) + 1) fuel') as HFuel 
            by (rewrite PeanoNat.Nat.add_1_r in HLen; apply le_same in HLen; simpl in HLen; apply le_same in HLen;
                eapply le_transitive; eauto).
            apply tsort_fuel_terminates in HFuel; destruct HFuel as [snmxs' HSome];
            rewrite <- Heqsnmxs' in HSome; inversion HSome.
        -- destruct fuel as [|fuel']; simpl; auto.
           simpl in HLen; inversion HLen.
    Qed.
      

    Lemma tsort_same : forall xs sxs,
        tsort_option xs = Some sxs <->
        tsort_ind xs sxs.
    Proof.
        intros; apply tsort_fuel_same; auto.
    Qed.

    Lemma tsort_origin : forall xs sxs,
        tsort_ind xs sxs ->
        incl sxs xs.
    Proof.
        intros xs sxs H x HIn; induction H; auto.
        apply in_app_or in HIn; destruct HIn as [HIn|HIn]; eapply filter_origin.
        - apply getMaximals_same in H0; rewrite <- H0 in HIn; eauto.
        - apply getNonMaximals_same in H1; rewrite <- H1 in IHtsort_ind; eauto.
    Qed.

    Lemma tsort_all : forall xs sxs,
        tsort_ind xs sxs ->
        incl xs sxs.
    Proof.
        intros xs sxs H x HIn; induction H; auto.
        apply in_or_app; destruct (maximalDec xs x); [left|right].
        - apply getMaximals_same in H0; rewrite <- H0. 
          apply P_filter; auto.
        - apply IHtsort_ind; apply getNonMaximals_same in H1; rewrite <- H1.
          apply P_filter; auto.
    Qed.




(** tsorted *)

    Fixpoint tsorted_fix (xs : list X) : Prop :=
        match xs with
        | x' :: xs' => if (maximalDec xs' x')
                   then tsorted_fix xs'
                   else False
        | nil => True
        end.

    Inductive tsorted_ind : list X -> Prop :=
    | tsortedCons : forall x' xs',
        maximal xs' x' ->
        tsorted_ind xs' ->
        tsorted_ind (x'::xs')
    | tsortedNil :  
        tsorted_ind nil.

    Lemma tsorted_same : forall xs,
        tsorted_fix xs <-> 
        tsorted_ind xs.
    Proof.
        intros xs; split; intros H.
        - induction xs as [|x' xs']; [apply tsortedNil|];
          simpl in H; destruct (maximalDec xs' x'); try contradiction;
          apply tsortedCons; auto.
        - induction H; simpl; auto;
          destruct (maximalDec xs' x'); auto.
    Qed.


    Lemma tsort_tsorted : forall xs sxs,
        tsort_ind xs sxs ->
        tsorted_ind sxs.
    Proof.
        intros xs sxs H; induction H as [xs mxs nmxs snmxs HCons HM HN HS|].
        - pose proof (getMaximals_maximal xs) as H;
          apply getMaximals_same in HM; rewrite HM in H; apply getMaximals_same in HM.
          induction HM as [mx xs' mxs HMxs | x xs' mxs | ]. 
        -- rewrite <- app_comm_cons; constructor.
        --- clear IHHS; clear IHHM.
            intros x HIn HOrd; apply in_app_or in HIn; destruct HIn as [HIn|HIn].
        ---- generalize dependent HOrd; generalize dependent HIn; generalize dependent x;
             assert ((forall x, In x mxs -> pre mx x -> pre x mx) <-> maximal mxs mx) as HDef by (split; intros; auto);
             apply HDef; clear HDef.
             assert (In mx (mx::mxs)) as HMmxs by (simpl; auto); apply H in HMmxs; clear H;
             apply maximal_incl with (xs:=mx::mxs); auto.
             intros mx' HIn; simpl; auto.
        ---- apply getNonMaximals_same in HN; unfold getNonMaximals_fix in HN.
             pose proof (tsort_origin nmxs snmxs HS) as HSIncl; apply HSIncl in HIn; clear HSIncl.
             pose proof (filter_P (negPDec (maximalDec xs)) xs) as HNm;
             rewrite HN in HNm; pose proof (HNm x HIn) as HNm;
             exfalso; apply HNm; clear HNm.
             intros x' HIn' HOrd'.
             assert (pre x' mx) as HOrd'' by (apply HMxs; auto; eapply pre_transitive; eauto).
             eapply pre_transitive; eauto.
        --- apply IHHM; intros mx' HIn; apply maximal_incl with (xs := mx :: mxs).
        ---- intros mx'' HIn'; simpl; auto.
        ---- apply H; simpl; auto.
        -- apply IHHM; auto.
        -- simpl; apply IHHS.
        - constructor.
    Qed. 


End TSort.