Require Import Coq.Lists.List.
Import ListNotations.
(* Require Import Coq.Logic.Description.
Require Import Coq.Logic.IndefiniteDescription. *)
Require Import Coq.Logic.FinFun.
Require Import Coq.Init.Peano.

Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.
Require Import AttestationProtocolOrdering.utilities.permute.
Require Import AttestationProtocolOrdering.utilities.mset.



(* Total function f : X -> Y *)
    (* Definition injective {X Y : Type} (f : X -> Y) := forall x1 x2, f x1 = f x2 -> x1 = x2.
    Definition surjective {X Y : Type} (f : X -> Y) := forall y, exists x, f x = y.
    Definition bijective {X Y : Type} (f : X -> Y) := injective f /\ surjective f.

    Definition leftInverse {X Y : Type} (f : X -> Y) g := forall x, g (f x) = x.
    Definition rightInverse {X Y : Type} (f : X -> Y) g := forall y, f (g y) = y.
    Definition inverse {X Y : Type} (f : X -> Y) g := leftInverse f g /\ rightInverse f g.

    Lemma inverse_symmetric : forall {X Y} (f : X -> Y) g,
        inverse f g -> inverse g f.
    Proof.
        intros X Y f g HInv; destruct HInv as [HL HR]; split; auto.
    Qed.

    Lemma bijective_iff_inverse : forall {X Y} (f : X -> Y),
        bijective f <->
        exists g, inverse f g.
    Proof.
        intros X Y f. split.
        - intros HBij. destruct HBij as [HInj HSur].
          assert (HUniq : forall y, exists! x, f x = y).
          { intros y. destruct (HSur y). 
            exists x. split; auto.
            intros x' H'.
            apply HInj. rewrite H, H'. auto. }
          assert (HSig : forall y, { x | f x  = y}).
          { intros y. apply constructive_definite_description. apply HUniq. }
          exists (fun y => proj1_sig ((HSig y))).
          split.
        -- intros x. destruct (HSig (f x)); auto.
        -- intros y. destruct (HSig y); auto.
        - intros HInv. destruct HInv as [g HInv].
          destruct HInv as [HL HR].
          split.
        -- intros x1 x2 H. eapply f_equal with (f:=g) in H.
           repeat rewrite HL in H; auto.
        -- intros y. exists (g y). apply HR.
    Qed. *)









(* Partial function f : xs -> ys *)

    Definition partialFunction {X Y : Type} (f : X -> Y) xs ys :=
        forall x, In x xs -> In (f x) ys.

    Definition partialInjective {X Y : Type} (f : X -> Y) (xs : list X) := 
        forall x1 x2, In x1 xs /\ In x2 xs -> f x1 = f x2 -> x1 = x2.
    Definition partialSurjective {X Y : Type} (f : X -> Y) (xs : list X) (ys : list Y) := 
        forall y, In y ys -> exists x, In x xs /\ f x = y.
    Definition partialBijective {X Y : Type} (f : X -> Y) (xs : list X) (ys : list Y) := 
        partialInjective f xs /\ partialSurjective f xs ys /\ partialFunction f xs ys.

    Definition partialLeftInverse {X Y : Type} (f : X -> Y) g (xs : list X) := 
        forall x, In x xs -> g (f x) = x.
    Definition partialRightInverse {X Y : Type} (f : X -> Y) g (ys : list Y) := 
        forall y, In y ys -> f (g y) = y.
    Definition partialInverse {X Y : Type} (f : X -> Y) g (xs : list X) (ys : list Y) := 
        partialLeftInverse f g xs /\ partialRightInverse f g ys /\ partialFunction f xs ys /\ partialFunction g ys xs.


    Lemma partialFunction_range : forall {X Y} (f : X -> Y) xs ys,
        partialFunction f xs ys ->
        incl (map f xs) ys.
    Proof.
        unfold partialFunction; intros X Y f xs ys Hf y HIn.
        apply in_map_iff in HIn; destruct HIn as [x [HEq HIn]]; subst; auto.
    Qed. 

    Lemma partialInjective_same : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2}) (f : X -> Y) xs,
        partialInjective f xs <->
        forall x1 x2, In x1 xs /\ In x2 xs -> x1 <> x2 -> f x1 <> f x2.
    Proof.
        unfold partialInjective.
        intros X Y eqDec_X f xs; split; intros HInj x1 x2 [HIn1 HIn2] H; auto.
        destruct (eqDec_X x1 x2) as [|HNeq]; subst; auto.
        exfalso; apply HInj in HNeq; auto.
    Qed.


    Lemma partialInjective_carac : forall {X Y} (f : X -> Y) xs,
        NoDup xs ->
        partialInjective f xs <-> NoDup (map f xs).
    Proof.
        unfold partialInjective.
        intros X Y f xs HNd; split; intros H.
        - induction xs as [|x' xs']; simpl; constructor;
        inversion HNd; subst.
        -- intros HIn; apply in_map_iff in HIn; destruct HIn as [x [HEq HIn]].
        apply H in HEq; simpl; auto. subst; contradiction.
        -- apply IHxs'; auto.
        intros x1 x2 [HIn1 HIn2] HEq.
        apply H; simpl; auto.
        - induction xs as [|x' xs']; intros x1 x2 [HIn1 HIn2] HEq.
        -- inversion HIn1.
        -- inversion HNd; subst; inversion H; subst.
        destruct HIn1 as [|HIn1], HIn2 as [|HIn2]; subst; auto.
        --- exfalso; apply H4; rewrite HEq; apply in_map; auto.
        --- exfalso; apply H4; rewrite <-HEq; apply in_map; auto.
    Qed.
    
    (* Try proving other direction too, hopefully without inhabited *)
    Lemma partialFunction_alist : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2}) (xs : list X) (ys : list Y),
        NoDup xs -> NoDup ys ->
        (exists f' : list (X * Y), mSameset eqDec_X (map fst f') xs /\ mIncluded eqDec_Y (map snd f') ys) ->
        inhabited Y ->
        (exists f : X -> Y, partialFunction f xs ys /\ partialInjective f xs).
    Proof.
       intros X Y eqDec_X eqDec_Y xs ys HNd_X HNd_Y Hf' nmt_Y.
       destruct Hf' as [f' [HS HI]].
       pose proof (mIncluded_NoDup eqDec_Y _ _ HNd_Y HI) as HNd_snd. 
       apply mIncluded_incl in HI.
       pose proof (mSameset_symmetric eqDec_X _ _ HS) as HSS.
       apply mIncluded_reflexive in HS, HSS.
       pose proof (mIncluded_NoDup eqDec_X _ _ HNd_X HS) as HNd_fst.
       apply mIncluded_incl in HS, HSS. 
       generalize dependent xs. generalize dependent ys.
       induction f' as [|[x' y'] f'']; intros.
       - destruct nmt_Y as [yd]. exists (fun _ => yd). split.
       -- intros x HIn. apply HSS in HIn. inversion HIn.
       -- intros x1 x2 [HIn1 HIn2]. apply HSS in HIn1. inversion HIn1.
       - simpl in HNd_fst; inversion HNd_fst; subst.
         simpl in HNd_snd; inversion HNd_snd; subst.
         pose proof (remove_NoDup eqDec_Y y' ys HNd_Y) as HNd_Y'.
         assert (incl (map snd f'') (remove eqDec_Y y' ys)) as HI'
         by (intros y HIn; apply in_in_remove; 
            [intros contra; subst; contradiction 
            |apply HI; simpl; auto]).
         pose proof (remove_NoDup eqDec_X x' xs HNd_X) as HNd_X'.
         assert (incl (map fst f'') (remove eqDec_X x' xs)) as HS'
         by (intros x HIn; apply in_in_remove; 
            [intros contra; subst; contradiction 
            |apply HS; simpl; auto]).
         assert (incl (remove eqDec_X x' xs) (map fst f'')) as HSS' 
         by (intros x HIn; apply in_remove in HIn; destruct HIn as [HIn HNeq];
             apply HSS in HIn; simpl in HIn; destruct HIn; subst; [contradiction | auto]).
         pose proof (IHf'' H4 H2 _ HNd_Y' HI' _ HNd_X' HS' HSS') as IH.
         destruct IH as [f [Hf HInj]].
         exists (fun x => if eqDec_X x x'
                          then y'
                          else f x); split.
        -- intros x HIn; destruct (eqDec_X x x') as [|HNeq]; subst.
        --- apply HI; simpl; auto.
        --- pose proof (in_in_remove eqDec_X xs HNeq HIn) as H;
            apply Hf in H; apply in_remove in H; destruct H; auto.
        -- intros x1 x2 [HIn1 HIn2] HEq.
           destruct (eqDec_X x1 x') as [|HNeq1], (eqDec_X x2 x') as [|HNeq2]; subst; auto.
        --- exfalso. 
            pose proof (in_in_remove eqDec_X xs HNeq2 HIn2) as H; apply Hf in H. 
            pose proof (remove_In eqDec_Y ys (f x2)); contradiction.
        --- exfalso.
            pose proof (in_in_remove eqDec_X xs HNeq1 HIn1) as H; apply Hf in H.
            pose proof (remove_In eqDec_Y ys (f x1)); contradiction.
        --- apply HInj; auto. split; apply in_in_remove; auto.
    Qed.

    Lemma alist_partialFunction : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2}) (xs : list X) (ys : list Y),
        NoDup xs -> NoDup ys ->
        (exists f : X -> Y, partialFunction f xs ys /\ partialInjective f xs) ->
        (exists f' : list (X * Y), mSameset eqDec_X (map fst f') xs /\ mIncluded eqDec_Y (map snd f') ys).
    Proof.
        intros X Y eqDec_X eqDec_Y xs ys HNd_X HNd_Y [f [Hf HInj]]. 
        exists (combine xs (map f xs)); split.
        - apply incl_NoDup_mSameset; auto.
        -- clear Hf HInj. induction xs as [|x' xs']; simpl; auto.
           inversion HNd_X; subst. constructor.
        --- intros HIn; apply H1.
            apply in_map_iff in HIn; destruct HIn as [[xa' y'] [HEq HIn]].
            simpl in HEq; subst; eapply in_combine_l; eauto.
        --- apply IHxs'; auto.
        -- intros x HIn. apply in_map_iff in HIn; destruct HIn as [[xa y] [HEq HIn]].
           simpl in HEq; subst; eapply in_combine_l; eauto.
        -- intros x HIn; apply in_map_iff.
           exists (x, f x); split; simpl; auto.
           pose proof (length_map f xs) as HLen. clear HNd_X Hf HInj.
           induction xs as [|x' xs']; [inversion HIn|].
           destruct HIn; subst; simpl in *; auto.
        - apply incl_NoDup_mIncluded.
        -- apply partialInjective_carac in HInj; auto.
           clear HNd_X Hf. induction xs as [|x' xs']; simpl; auto.
           inversion HInj; subst. constructor.
        --- intros HIn; apply H1.
            apply in_map_iff in HIn; destruct HIn as [[xa' y'] [HEq HIn]].
            simpl in HEq; subst. eapply in_combine_r; eauto.
        --- apply IHxs'; auto.
        -- intros y HIn; apply in_map_iff in HIn; destruct HIn as [[x ya] [HEq HIn]].
           simpl in HEq; subst; apply partialFunction_range in Hf.
           apply in_combine_r in HIn; apply Hf in HIn; auto.
    Qed.

    

    Lemma NoDup_injective_incl_length : forall {X Y} (f : X -> Y) xs ys,
        NoDup xs ->
        partialFunction f xs ys ->
        partialInjective f xs ->
        le (length xs) (length ys).
    Proof.
        intros X Y f xs ys HNd HIncl HInj. 
        assert (NoDup (map f xs)) as HNdMap by (apply partialInjective_carac; auto).
        assert (forall y, In y (map f xs) -> In y ys) as HInMap.
        { intros y HIn; apply in_map_iff in HIn; 
        destruct HIn as [x [HEq HIn]]; subst; 
        apply HIncl; auto. }
        pose proof (length_map f xs) as HLen; rewrite <- HLen;
        eapply NoDup_incl_length; auto.
    Qed.





    Lemma partialFunction_sigma : forall {X Y} (f : X -> Y) xs ys,
        partialFunction f xs ys <->
        exists (f' : {x | In x xs} -> {y | In y ys}), forall sigx, proj1_sig (f' sigx) = f (proj1_sig sigx).
    Proof.
        intros X Y f xs ys; split; intros H. 
        - exists (fun (sigx : {x | In x xs}) => (exist (fun y => In y ys) (f (proj1_sig sigx))) (H (proj1_sig sigx) (proj2_sig sigx))).
          simpl; reflexivity.
        - destruct H as [f' H]; intros x HIn.
          specialize H with (exist (fun x => In x xs) x HIn); simpl in H; rewrite <- H.
          pose proof (proj2_sig (f' (exist (fun x => In x xs) x HIn))) as H'; simpl in H';
          assumption.
    Qed.

    Lemma sigma_partialFunction : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2}) (nmt_Y : inhabited Y)
            (xs : list X) (ys : list Y) (f' : {x | In x xs} -> {y | In y ys}),
        (forall sigx1 sigx2, proj1_sig sigx1 = proj1_sig sigx2 -> proj1_sig (f' sigx1) = proj1_sig (f' sigx2)) ->
        exists f, partialFunction f xs ys /\ forall sigx, proj1_sig (f' sigx) = f (proj1_sig sigx).
    Proof.
        intros X Y eqDec_X nmt_Y xs ys f' HPIr.
        destruct nmt_Y as [yd].
        exists (fun x => match (in_dec eqDec_X x xs) with
                         | left Hx => proj1_sig (f' (exist _ x Hx))
                         | right _ => yd
                         end).
        split.
        - intros x HIn. 
          destruct (in_dec eqDec_X x xs) as [Hx|]; try contradiction.
          destruct (f' (exist (fun x0 : X => In x0 xs) x Hx)) as [y Hy].
          simpl; auto.
        - intros [x Hx]; simpl.
          destruct (in_dec eqDec_X x xs) as [Hx'|]; try contradiction.
          pose proof HPIr (exist _ x Hx) (exist _ x Hx') as HEq.
          rewrite HEq; simpl; auto.
    Qed.


    Fixpoint enumList {X : Type} (l : list X) : list {x : X | In x l} := 
    match l with
    | x :: l' => (exist _ x (or_introl eq_refl)) :: (map (fun sigx => exist _ (proj1_sig sigx) (or_intror (proj2_sig sigx))) (enumList l'))
    | nil => nil
    end.
  
    Lemma enumList_Finite : forall {X} (xs : list X),
        Finite {x | In x xs}.
    Proof.
        intros X xs. exists (enumList xs). intros sigx. induction xs as [|x xs']; intros.
        - destruct sigx as [a HIn]. inversion HIn.
        - destruct sigx as [a HIn]. destruct HIn as [|HIn]; subst.
        -- left. reflexivity.
        -- right. apply in_map_iff. exists (exist _ a HIn). split.
        --- reflexivity.
        --- apply IHxs'.
    Qed.


  Fixpoint combineFunSigma
            {X Y : Type}
            (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2})
            (xs : list X) (ys : list Y)
            (HLen : le (length xs) (length ys)) : 
        {x | In x xs} -> {y | In y ys} :=
  match xs, ys, HLen with
  | nil, _, _ =>
      fun sigx =>
        False_rect _ (in_nil_absurd _ (proj2_sig sigx))
  | x' :: xs', nil, HLen' =>
      False_rect _ (nle_S_0 _ HLen')
  | x' :: xs', y' :: ys', HLen' =>
      fun sigx => 
        match sigx with
        | exist _ x Hx => 
            match eqDec_X x x' with
            | left _ => 
                exist (fun y => In y (y' :: ys')) y' (or_introl eq_refl)
            | right HNeq => 
                let Hx_tail : In x xs' :=
                    match Hx with
                    | or_introl HEq => False_rect _ (HNeq (eq_sym HEq))
                    | or_intror H   => H
                    end in
                let HLen_tail : le (length xs') (length ys') :=
                    le_S_n _ _ HLen' in
                let (y, Hy) :=
                    combineFunSigma eqDec_X xs' ys' HLen_tail (exist _ x Hx_tail) in
                exist (fun y => In y (y' :: ys')) y (or_intror Hy)
            end
        end
    end.

    Lemma combineFunSigma_origin :  forall {X Y} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2})
            (xs : list X) (ys : list Y) (HLen : le (length xs) (length ys)) sigx,
        In (proj1_sig (combineFunSigma eqDec_X xs ys HLen sigx)) ys.
    Proof.
        intros X Y eqDec_X xs ys HLen [x Hx]. destruct xs as [|x' xs'].
        - inversion Hx.
        - destruct ys as [|y' ys'].
        -- simpl in HLen. inversion HLen.
        -- simpl. destruct (eqDec_X x x'); subst; simpl; auto.
           destruct Hx as [|Hx]; subst; try contradiction.
           destruct (combineFunSigma eqDec_X xs' ys' (le_S_n _ _ HLen) (exist _ x Hx)) as [r Hr].
           right; simpl; auto.
    Qed.


    
    (* Lemma dkljv : forall {X Y} (xs : list X) (ys : list Y) (nmt_Y : inhabited Y),
        NoDup ys ->
        le (length xs) (length ys) ->
        exists (f : X -> Y), partialFunction f xs ys /\ partialInjective f xs.
    Proof.
        intros X Y xs ys nmt_Y HNd_Y HLen.
    Abort.


    Lemma combineFunSigma_NoDup : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2})
            (xs : list X) (ys : list Y) (HLen : le (length xs) (length ys)),
        NoDup ys ->
        NoDup (map (fun x => proj1_sig (combineFunSigma eqDec_X xs ys HLen x)) (enumList xs)).
    Proof.
        intros X Y eqDec_X xs ys HLen.
    Abort. *)


    Lemma combineFunSigma_injective : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2})
            (xs : list X) (ys : list Y) (HLen : le (length xs) (length ys)),
        NoDup ys ->
        forall sigx1 sigx2,
        proj1_sig (combineFunSigma eqDec_X xs ys HLen sigx1) = proj1_sig (combineFunSigma eqDec_X xs ys HLen sigx2) ->
        proj1_sig sigx1 = proj1_sig sigx2.
    Proof.
        intros X Y eqDec_X xs. intros ys HLen HNd [x1 Hx1] [x2 Hx2] HEq.
        simpl. generalize dependent ys.
        induction xs as [|x' xs']; intros ys HLen HNd HEq.
        - inversion Hx1.
        - destruct ys as [|y' ys'].
        -- simpl in HLen. inversion HLen.
        -- inversion HNd; subst.
           simpl in HEq.
           destruct (eqDec_X x1 x'), (eqDec_X x2 x'); subst; auto.
        --- exfalso. simpl in HEq.
            destruct Hx2 as [|Hx2]; subst; try contradiction.            
            remember (le_S_n _ _ HLen) as HLen'.
            remember (exist (fun x : X => In x xs') x2 Hx2) as sigx.
            pose proof (combineFunSigma_origin eqDec_X xs' ys' HLen' sigx).
            destruct (combineFunSigma eqDec_X xs' ys' HLen' sigx) as [y Hy].
            simpl in *; subst; contradiction.
        --- exfalso. simpl in HEq.
            destruct Hx1 as [|Hx1]; subst; try contradiction.
            remember (le_S_n _ _ HLen) as HLen'.
            remember (exist (fun x : X => In x xs') x1 Hx1) as sigx.
            pose proof (combineFunSigma_origin eqDec_X xs' ys' HLen' sigx).
            destruct (combineFunSigma eqDec_X xs' ys' HLen' sigx) as [y Hy].
            simpl in *; subst; contradiction.
        --- destruct Hx1 as [|Hx1], Hx2 as [|Hx2]; subst; try contradiction.
            remember (le_S_n _ _ HLen) as HLen'.
            specialize IHxs' with Hx1 Hx2 ys' HLen'.
            apply IHxs'; auto.
            destruct (combineFunSigma eqDec_X xs' ys' HLen' (exist (fun x => In x xs') x1 Hx1)) as [y1 Hy1].
            destruct (combineFunSigma eqDec_X xs' ys' HLen' (exist (fun x => In x xs') x2 Hx2)) as [y2 Hy2].
            simpl in *; auto.
    Qed.
            

    
    (* Note: If xs has duplicates then I think combineFunSigma uses shadowing *)

    Lemma combineFunSigma_ProofIrrelevance : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2})
            (xs : list X) (ys : list Y) (HLen : le (length xs) (length ys)) sigx1 sigx2,
        proj1_sig sigx1 = proj1_sig sigx2 ->
        proj1_sig (combineFunSigma eqDec_X xs ys HLen sigx1) = proj1_sig (combineFunSigma eqDec_X xs ys HLen sigx2).
    Proof.
        intros X Y eqDec_X.
        induction xs as [|x' xs']; intros ys HLen [x1 Hx1] [x2 Hx2] HEq.
        - inversion Hx1.
        - destruct ys as [|y' ys'].
        -- simpl in HLen; inversion HLen.
        -- simpl in HEq; subst.
           simpl; destruct (eqDec_X x2 x') as [|HNeq]; subst.
        --- simpl; auto.
        --- set (Hx1_tail :=
              match Hx1 with
              | or_introl HEq => False_rect (In x2 xs') (HNeq (eq_sym HEq))
              | or_intror H => H
              end).
            set (Hx2_tail :=
              match Hx2 with
              | or_introl HEq => False_rect (In x2 xs') (HNeq (eq_sym HEq))
              | or_intror H => H
              end).
            set (HLen_tail := le_S_n _ _ HLen).
            assert (proj1_sig (exist (fun x : X => In x xs') x2 Hx1_tail) = proj1_sig (exist (fun x : X => In x xs') x2 Hx2_tail))
            as HEq' by (simpl; auto).
            pose proof
            (IHxs' ys' HLen_tail
                     (exist _ x2 Hx1_tail)
                     (exist _ x2 Hx2_tail)
                     HEq') as IH.
            destruct (combineFunSigma eqDec_X xs' ys' HLen_tail (exist (fun x : X => In x xs') x2 Hx1_tail)) as [x1' Hx1'].
            destruct (combineFunSigma eqDec_X xs' ys' HLen_tail (exist (fun x : X => In x xs') x2 Hx2_tail)) as [x2' Hx2'].
            simpl in IH; subst.
            simpl; auto.
    Qed.

    Lemma combineFunSigma_partialInjective : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2}) (nmt_Y : inhabited Y)
            (xs : list X) (ys : list Y) (HNd_Y : NoDup ys) (HLen : le (length xs) (length ys)),
        exists f, partialFunction f xs ys /\ partialInjective f xs /\ forall sigx, proj1_sig (combineFunSigma eqDec_X xs ys HLen sigx) = f (proj1_sig sigx).
    Proof.
        intros X Y eqDec_X nmt_Y xs ys HNd_Y HLen.
        destruct nmt_Y as [yd].
        pose proof (combineFunSigma_ProofIrrelevance eqDec_X xs ys HLen) as HPIr.
        exists (fun x => match (in_dec eqDec_X x xs) with
                         | left Hx => proj1_sig (combineFunSigma eqDec_X xs ys HLen (exist _ x Hx))
                         | right _ => yd
                         end).
        repeat split.
        - intros x HIn. 
          destruct (in_dec eqDec_X x xs) as [Hx|]; try contradiction.
          destruct (combineFunSigma eqDec_X xs ys HLen (exist (fun x0 : X => In x0 xs) x Hx)) as [y Hy].
          simpl; auto.
        - intros x1 x2 [HIn1 HIn2] HEq.
          destruct (in_dec eqDec_X x1 xs) as [Hx1|], (in_dec eqDec_X x2 xs) as [Hx2|]; try contradiction.
          pose proof (combineFunSigma_injective eqDec_X xs ys HLen HNd_Y (exist _ x1 Hx1) (exist _ x2 Hx2)) as H.
          simpl in *; auto.
        - intros [x Hx]; simpl.
          destruct (in_dec eqDec_X x xs) as [Hx'|]; try contradiction.
          pose proof HPIr (exist _ x Hx) (exist _ x Hx') as HEq.
          rewrite HEq; simpl; auto.
    Qed.
   

    Lemma le_reflexive' : forall (x y : nat),
        x = y ->
        le x y.
    Proof.
        intros; subst; auto.
    Qed.

    Lemma vkcndDec : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2}) (nmt_Y : inhabited Y)
            (xs : list X) (ys : list Y) (HNd_Y : NoDup ys) (HLen : le (length xs) (length ys)) (P : (X -> Y) -> Prop),
        (forall f, {P f} + {~ P f}) ->
        (forall f g, (forall x, In x xs -> f x = g x) -> P f -> P g) ->
        {exists f, partialFunction f xs ys /\ partialInjective f xs /\ P f} + 
        {forall p (HLenP : le (length xs) (length p)), 
         In p (permutations ys) -> 
         forall f, (forall sigx, proj1_sig (combineFunSigma eqDec_X xs p HLenP sigx) = f (proj1_sig sigx)) -> ~ P f}.
    Proof.
        intros X Y eqDec_X nmt_Y xs ys HNd_Y HLen P PDec PExt.
        assert (forall p, In p (permutations ys) -> NoDup p) as HNd_P.
        { intros; eapply permutations_NoDup; eauto. }
        pose proof (permutations_length ys) as HLen_P.
        induction (permutations ys) as [|p pys].
        - right. intros p HLenP HIn. inversion HIn.
        - destruct IHpys as [IHl|IHr]; intros; [ apply HNd_P | apply HLen_P | | ]; simpl; auto.
        -- assert (NoDup p) as HNdP.
           { apply HNd_P; simpl; auto. }
           assert (le (length xs) (length p)) as HLenP.
           { rewrite <- HLen_P; simpl; auto. }
           pose proof (combineFunSigma_partialInjective eqDec_X nmt_Y xs p HNdP HLenP) as H.
           (* destruct H as [f [Hf [HInj HEq]]]. *)
    Admitted.



    Lemma ckjvDec : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2}) (nmt_Y : inhabited Y)
            (xs : list X) (ys : list Y) (HNd_Y : NoDup ys) (HLen : le (length xs) (length ys)) (P : (X -> Y) -> Prop),
        (forall f, {P f} + {~ P f}) ->
        (forall f g, (forall x, In x xs -> f x = g x) -> P f -> P g) ->
        {exists f, partialFunction f xs ys /\ partialInjective f xs /\ P f} + {forall f, partialFunction f xs ys -> partialInjective f xs -> ~ P f}.
    Proof.
        intros X Y eqDec_X nmt_Y xs ys HNd_Y HLen P PDec PExt.
        pose proof (vkcndDec eqDec_X nmt_Y xs ys HNd_Y HLen P PDec PExt) as H. destruct H as [H|H].
        - left; auto.
        - right.
    Admitted.

    Lemma existsInjFunDec : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2}) (nmt_Y : inhabited Y)
            (xs : list X) (ys : list Y) (HNd_Y : NoDup ys) (HLen : le (length xs) (length ys)) (P : (X -> Y) -> Prop),
        (forall f, {P f} + {~ P f}) ->
        (forall f g, (forall x, In x xs -> f x = g x) -> P f -> P g) ->
        {exists f, partialFunction f xs ys /\ partialInjective f xs /\ P f} + {~ exists f, partialFunction f xs ys /\ partialInjective f xs /\ P f}.
    Proof.
        intros X Y eqDec_X nmt_Y xs ys HNd_Y HLen P PDec PExt.
        pose proof (ckjvDec eqDec_X nmt_Y xs ys HNd_Y HLen P PDec PExt) as H. destruct H as [H|H].
        - left; auto.
        - right. intros contra. destruct contra as [f [Hf [HInj HP]]]. unfold not in H; apply H with f; auto.
    Abort.
    

(*     Lemma alistDec : forall {X Y} (eqDec_X : forall x1 x2 : X, {x1=x2} + {x1<>x2})
            (xs : list X) (ys : list Y) (P : (X -> Y) -> Prop),
        (forall f, {P f} + {~ P f}) ->
        (forall f g, (forall x, In x xs -> f x = g x) -> P f -> P g) -> *)




    Lemma partialInverse_symmetric : forall {X Y} (f : X -> Y) g xs ys,
        partialInverse f g xs ys -> partialInverse g f ys xs.
    Proof.
        intros X Y f g xs ys HInv. destruct HInv as [HL [HR [Hf Hg]]].
        repeat split; auto.
    Qed.


    Lemma partialBijective_origin_unique : forall {X Y} (f : X -> Y) xs ys,
        partialBijective f xs ys ->
        forall y, In y ys ->
        exists! x, In x xs /\ f x = y.
    Proof.
        intros X Y f xs ys HBij y HIn.
        destruct HBij as [HInj [HSur Hf]].
        destruct (HSur y); auto.
        exists x; split; auto.
        intros x' H'; destruct H as [H HEq]; destruct H' as [H' HEq'].
        apply HInj; auto.
        rewrite HEq, HEq'; auto.
    Qed.


    Lemma partialInjective_partialSurjective : forall {X Y} (f : X -> Y) xs ys,
        (forall y1 y2 : Y, {y1 = y2} + {y1 <> y2}) ->
        NoDup xs ->
        NoDup ys ->
        partialFunction f xs ys ->
        partialInjective f xs ->
        length xs = length ys ->
        partialSurjective f xs ys.
    Proof.
        intros X Y f xs ys eqDec_Y HNdX HNdY Hf HInj HLen y HIn.
        generalize dependent ys. induction xs as [|x' xs']; intros.
        - assert (ys = nil) by (apply length_zero_iff_nil; auto); subst.
          inversion HIn.
        - destruct (eqDec_Y (f x') y).
        -- exists x'; simpl; auto.
        -- assert ((exists x, In x xs' /\ f x = y) -> (exists x, In x (x'::xs') /\ f x = y)).
           { intros H. destruct H as [x [HIn' HEq]]. exists x. simpl; auto. }
           apply H. clear H.
           inversion HNdX; subst.
           assert (In (f x') ys) as HInFx' by (apply Hf; simpl; auto).
           apply IHxs' with (ys := removeFirst_fix eqDec_Y (f x') ys).
        --- auto.
        --- intros x1 x2 [HIn1 HIn2]. apply HInj; simpl; auto.
        --- apply removeFirst_NoDup; auto.
        --- intros x HIn'. apply removeFirst_in.
        ---- intros HEq. assert (In x' (x'::xs') /\ In x (x'::xs')) as HIn'' by (simpl; auto). 
             pose proof (HInj x' x HIn'' HEq); subst. contradiction.
        ---- apply Hf; simpl; auto.
        --- pose proof (removeFirst_lengthAdd eqDec_Y (f x') ys HInFx') as HLen'.
            rewrite <- HLen' in HLen; simpl in HLen.
            rewrite PeanoNat.Nat.add_1_r in HLen. auto.
        --- apply removeFirst_in; auto.
    Qed.


    Theorem cantorSchroderBernstein_finite : forall {X Y} (f : X -> Y) (g : Y -> X) xs ys,
        (forall y1 y2 : Y, {y1 = y2} + {y1 <> y2}) ->
        NoDup xs ->
        NoDup ys ->
        partialFunction f xs ys ->
        partialFunction g ys xs ->
        partialInjective f xs ->
        partialInjective g ys ->
        partialSurjective f xs ys.
    Proof.
        intros X Y f g xs ys eqDec_Y HNdX HNdY Hf Hg HInjF HInjG.
        apply partialInjective_partialSurjective; auto.
        apply le_antisymmetric; eapply NoDup_injective_incl_length; eauto.
    Qed.


    Lemma partialInjective_incl : forall {X Y} (f : X -> Y) xs' xs,
        incl xs' xs ->
        partialInjective f xs ->
        partialInjective f xs'.
    Proof.
        intros X Y f xs' xs HIncl HInj x1' x2' [HIn1' HIn2'];
        apply HInj; split; apply HIncl; auto.
    Qed.




