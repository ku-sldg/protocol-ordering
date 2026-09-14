Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.
Require Import AttestationProtocolOrdering.utilities.mset.


Fixpoint insert {X : Type} (a : X) (l : list X) : list (list X) :=
match l with
| x :: l' => (a :: l) :: map (fun xs => x :: xs) (insert a l')
| nil => [[a]]
end.

Eval compute in (insert 1 [2;3;4]). (* [[1; 2; 3; 4]; [2; 1; 3; 4]; [2; 3; 1; 4]; [2; 3; 4; 1]] *)
Eval compute in (insert 1 [2;4;3]). (* [[1; 2; 4; 3]; [2; 1; 4; 3]; [2; 4; 1; 3]; [2; 4; 3; 1]] *)

Fixpoint permutations {X : Type} (l : list X) : list (list X) :=
match l with
| x :: l' => flat_map (insert x) (permutations l')
| nil => [[]]
end.

Eval compute in (permutations (1::2::3::nil)).
Eval compute in (permutations (1::2::3::5::nil)).

Definition getAllInjections {X Y : Type} (xs : list X) (ys : list Y) :=
    map (combine xs) (permutations ys).

Eval compute in (getAllInjections (0::1::2::nil) (6::7::8::9::nil)).






Fixpoint find {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2}) 
        (m : list (X * Y)) (k : X) : option Y :=
match m with
| (x,y)::m' => if eqDec_X x k
               then Some y
               else find eqDec_X m' k
| nil => None
end.

Lemma find_combine_map : forall {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2})
        (f : X -> Y) (xs : list X) (x : X),
    In x xs ->
    find eqDec_X (combine xs (map f xs)) x = Some (f x).
Proof.
    intros X Y eqDec_X f xs. induction xs as [|x' xs']; intros x HIn; [inversion HIn|].
    destruct HIn as [HEq|HIn]; subst; simpl.
    - destruct (eqDec_X x x); auto. contradiction.
    - destruct (eqDec_X x' x); subst; auto.
Qed.

Lemma find_In : forall {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2}) 
        (m : list (X * Y)) (x : X) (y : Y),
    find eqDec_X m x = Some y ->
    In (x, y) m.
Proof.
    intros X Y eqDec_X m. induction m as [|[x' y'] m']; 
    intros x y H; simpl in *; [inversion H|].
    destruct (eqDec_X x' x); subst.
    - inversion H; subst; auto.
    - right; apply IHm'; auto.
Qed.


Lemma find_Some : forall {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2}) 
        (m : list (X * Y)) (k : X) (xs : list X),
    mSameset eqDec_X (map fst m) xs ->
    forall x, In x xs ->
    exists y, find eqDec_X m x = Some y.
Proof.
    intros X Y eqDec_X m k xs H x HIn.
    generalize dependent xs; induction m as [|[x' y'] m']; intros; simpl in H.
    - rewrite mSameset_universe in H; simpl in H; symmetry in H.
        apply multiplicity_zero_all in H; subst; inversion HIn.
    - simpl; destruct (eqDec_X x' x).
    -- exists y'; auto.
    -- apply IHm' with (removeFirst_fix eqDec_X x' xs).
    --- apply mSameset_cons_removeFirst; auto.
    --- apply removeFirst_in; auto.
Qed.

Lemma find_snd : forall {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2}) 
        (m : list (X * Y)) (k : X) (xs : list X),
    mSameset eqDec_X (map fst m) xs ->
    forall x, In x xs ->
    exists y, find eqDec_X m x = Some y /\ In y (map snd m).
Proof.
    intros X Y eqDec_X m k xs H x HIn.
    generalize dependent xs; induction m as [|[x' y'] m']; intros; simpl in H.
    - rewrite mSameset_universe in H; simpl in H; symmetry in H.
        apply multiplicity_zero_all in H; subst; inversion HIn.
    - simpl; destruct (eqDec_X x' x) as [|HNeq].
    -- exists y'; auto.
    -- apply mSameset_cons_removeFirst in H.
        apply removeFirst_in with eqDec_X x' x xs in HIn; auto.
        pose proof (IHm' _ H HIn) as IH; destruct IH as [y []].
        exists y; split; auto.
Qed.

Lemma find_ys : forall {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2, {y1 = y2} + {y1 <> y2}) 
        (m : list (X * Y)) (k : X) (xs : list X) (ys : list Y),
    mSameset eqDec_X (map fst m) xs ->
    mIncluded eqDec_Y (map snd m) ys ->
    forall x, In x xs ->
    exists y, find eqDec_X m x = Some y /\ In y ys.
Proof.
    intros X Y eqDec_X eqDec_Y m k xs ys HM HI x HIn.
    pose proof (find_snd eqDec_X m k xs HM x HIn) as H.
    destruct H as [y []]. exists y; split; auto.
    apply mIncluded_incl in HI; apply HI; auto.
Qed. 

Lemma match_find_P : forall {X Y : Type} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2})
        (m : list (X * Y)) (yd : Y) (x : X) (P : Y -> Prop),
    (exists y, find eqDec_X m x = Some y /\ P y) ->
    P (match find eqDec_X m x with Some y => y | None => yd end).
Proof.
    intros X Y eqDec_X m yd x P [y [Heq HP]]; rewrite Heq; auto.
Qed.


Lemma combine_find : forall {X Y : Type} (eqDec_X : forall x1 x2, {x1 = x2} + {x1 <> x2}) (xs : list X) (ys : list Y),
    le (length xs) (length ys) ->
    forall x, In x xs ->
    exists y, find eqDec_X (combine xs ys) x = Some y /\ In y ys.
Proof.
    intros X Y eqDec_X xs ys HLen x HIn. 
    generalize dependent ys; induction xs as [|x' xs']; 
    intros; simpl in *.
    - inversion HIn.
    - destruct ys as [|y' ys']; simpl in *.
    -- inversion HLen.
    -- destruct HIn as [|HIn]; destruct (eqDec_X x' x); subst; try contradiction.
    --- exists y'; auto.
    --- exists y'; auto.
    --- apply le_same in HLen; simpl in HLen; apply le_same in HLen.
        pose proof (IHxs' HIn ys' HLen) as IH; destruct IH as [y [HEq HIn']].
        exists y; auto.
Qed.

Lemma Permutation_insert : forall {X} (a : X) l xs,
    In xs (insert a l) ->
    Permutation (a :: l) xs.
Proof.
    intros X a l xs HIn. generalize dependent xs. induction l as [|x l']; intros.
    - simpl in HIn; destruct HIn as [|HIn]; subst.
    -- apply Permutation_refl.
    -- inversion HIn.
    - simpl in HIn; destruct HIn as [|HIn]; subst.
    -- apply Permutation_refl.
    -- apply in_map_iff in HIn; destruct HIn as [xs' [HEq HIn]]; subst.
       pose proof (IHl' xs' HIn) as IH; clear IHl' HIn.
       rewrite app_cons; rewrite app_cons in IH.
       apply Permutation_sym; apply Permutation_cons_app; apply Permutation_sym; auto.
Qed.


Lemma insert_everywhere : forall {X} (a : X) l1 l2,
    In (l1 ++ a :: l2) (insert a (l1 ++ l2)).
Proof.
    intros X a l1 l2; generalize dependent l2;
    induction l1 as [|x l1']; intros.
    - simpl; destruct l2; simpl; auto.
    - simpl; right; apply in_map; auto.
Qed.


Lemma Permutation_cons_app_exists : forall {X} (a : X) l xs,
    Permutation (a :: l) xs ->
    exists l1 l2, xs = l1 ++ a :: l2 /\ Permutation l (l1 ++ l2).
Proof.
    intros X a l xs HPerm.
    assert (In a xs) as HIn
    by (eapply Permutation_in; eauto; simpl; auto).
    apply in_split in HIn; destruct HIn as [l1 [l2 HEq]]; subst.
    exists l1, l2; split; auto.
    eapply Permutation_cons_app_inv; eauto.
Qed.
    

Lemma Permutation_permutations : forall {X} (l p : list X),
    In p (permutations l) ->
    Permutation l p.
Proof.
    intros X l p HIn. generalize dependent p.
    induction l as [|x l']; intros; simpl in HIn.
    - destruct HIn as [|HIn]; subst.
    -- apply perm_nil.
    -- inversion HIn.
    - apply in_flat_map in HIn; destruct HIn as [xs [HInPerm HInIns]].
      apply IHl' in HInPerm. apply Permutation_insert in HInIns.
      apply Permutation_cons_app_exists in HInIns. destruct HInIns as [l1 [l2 [HEq HPerm]]]; subst.
      apply Permutation_cons_app. eapply perm_trans; eauto.
Qed.

Lemma permutations_Permutation : forall {X} (l p : list X),
    Permutation l p ->
    In p (permutations l).
Proof.
    intros X l p HPerm. generalize dependent p. induction l as [|x l']; intros.
    - apply Permutation_nil in HPerm; subst; simpl; auto.
    - apply Permutation_cons_app_exists in HPerm; destruct HPerm as [l1 [l2 [HEq HPerm]]]; subst.
      apply IHl' in HPerm. 
      simpl; apply in_flat_map.
      exists (l1 ++ l2); split; auto.
      apply insert_everywhere.
Qed.
      

Lemma insert_length : forall {X} (a : X) l xs,
    In xs (insert a l) ->
    length xs = S (length l).
Proof.
    intros X a l xs HIn.
    generalize dependent xs; induction l as [|x' l']; intros;
    simpl in *; destruct HIn as [|HIn]; subst; simpl; auto.
    - inversion HIn.
    - apply in_map_iff in HIn; destruct HIn as [xs' [HEq HI]]; subst.
      simpl; auto.
Qed.

Lemma permutations_length : forall {X} (l p : list X),
    In p (permutations l) ->
    length l = length p.
Proof.
    intros X l p HIn.
    generalize dependent p; induction l as [|x l']; intros; simpl in *.
    - destruct HIn as [|HIn]; subst; auto. inversion HIn.
    - apply in_flat_map in HIn; destruct HIn as [xs [HP HI]].
      apply IHl' in HP; rewrite HP.
      apply insert_length in HI; rewrite HI.
      reflexivity.
Qed.




Lemma insert_origin : forall {X} (a : X) l xs,
    In xs (insert a l) ->
    incl xs (a::l).
Proof.
    intros X a l xs HI x HIn; simpl.
    generalize dependent xs; induction l as [|x' l']; 
    intros; simpl in *; destruct HI as [|HI]; subst; auto.
    apply in_map_iff in HI; destruct HI as [xs' [HEq HI]]; subst.
    destruct HIn as [|HIn]; subst; simpl; auto.
    pose proof (IHl' xs' HI HIn) as IH; destruct IH; auto.
Qed.

Lemma permutations_origin : forall {X} (l p : list X),
    In p (permutations l) ->
    incl p l.
Proof.
    intros X l p HP x HIn.
    generalize dependent p; induction l as [|x' l'];
    intros; simpl in *.
    - destruct HP; subst; auto.
    - apply in_flat_map in HP. destruct HP as [p' [HP HI]].
      apply insert_origin in HI. apply HI in HIn. destruct HIn as [|HIn]; subst; auto.
      right; apply IHl' with (p:=p'); auto.
Qed.


Lemma insert_NoDup : forall {X} (a : X) l xs,
    ~ In a l ->
    In xs (insert a l) ->
    NoDup l -> 
    NoDup xs.
Proof.
    intros X a l xs HNIn HIn HNd.
    generalize dependent xs; induction l as [|x l']; intros;
    simpl in HIn.
    - destruct HIn; subst; [constructor; auto | contradiction].
    - inversion HNd; subst.
      destruct HIn as [|HIn]; subst.
    -- constructor; auto.
    -- apply in_map_iff in HIn; destruct HIn as [m' [HEq HIn]]; subst.
       constructor.
    --- apply insert_origin in HIn. intros contra.
        apply HIn in contra. destruct contra; subst.
    ---- apply HNIn; simpl; auto.
    ---- contradiction.
    --- apply IHl'; auto. 
        intros contra; apply HNIn; simpl; auto.
Qed.


Lemma permutations_NoDup : forall {X} (l p: list X),
    In p (permutations l) ->
    NoDup l -> 
    NoDup p.
Proof.
    intros X l p HIn HNd.
    - generalize dependent p; induction l as [|x l']; 
      intros; simpl in HIn.
    -- destruct HIn; subst; auto. contradiction.
    -- inversion HNd; subst. 
       apply in_flat_map in HIn; destruct HIn as [p' [HP HI]].
       apply insert_NoDup with (a:=x) (l:= p'); auto.
       intros contra. apply H1.
       apply permutations_origin in HP; auto.
Qed.



Lemma Permutation_mSameset : forall {X} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (l m : list X),
    mSameset eqDec_X l m <->
    Permutation l m.
Proof.
    intros X eqDec_X l m. rewrite mSameset_universe. split; intros H.
    - apply Permutation_count_occ with (eq_dec := eqDec_X); intros x.
      repeat rewrite <- multiplicity_countOcc; auto.
    - intros x; repeat rewrite multiplicity_countOcc.
      apply Permutation_count_occ with (eq_dec := eqDec_X) (x:=x) in H; auto.
Qed.

Lemma permutations_cons_removeFirst : forall {X} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (xs xs' : list X) x',
    In x' xs ->
    In xs' (permutations (removeFirst_fix eqDec_X x' xs)) ->
    In (x'::xs') (permutations xs).
Proof.
    intros X eqDec_X xs xs' x' HIn HP.
    apply permutations_Permutation; apply Permutation_permutations in HP.
    rewrite <- Permutation_mSameset with (eqDec_X:=eqDec_X); rewrite <- Permutation_mSameset with (eqDec_X:=eqDec_X) in HP.
    rewrite mSameset_universe. rewrite mSameset_universe in HP.
    intros x; specialize HP with x.
    simpl; destruct (eqDec_X x x'); subst; rewrite <- HP.
    - apply multiplicity_removeFirst; auto.
    - apply multiplicity_removeFirst_neq; auto.
Qed.

Lemma find_Permutation : forall {X Y : Type} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2})
        (m m' : list (X * Y)),
    Permutation m m' ->
    NoDup (map fst m) ->
    forall k, find eqDec_X m k = find eqDec_X m' k.
Proof.
    intros X Y eqDec_X eqDec_Y m m' HPerm.
    induction HPerm as [|[x y] | [x y] [x0 y0]|]; intros HNd k; auto.
    - simpl in HNd; inversion HNd; subst; simpl.
      destruct (eqDec_X x k); subst; auto.
    - simpl in HNd; inversion HNd; subst; simpl.
      destruct (eqDec_X x0 k), (eqDec_X x k); subst; simpl; auto.
      exfalso; apply H1; simpl; auto.
    - rewrite <- IHHPerm2; 
      [ apply IHHPerm1; auto
      | eapply Permutation_NoDup; [apply Permutation_map|]; eauto].
Qed.

Lemma combine_fst_full : forall {X Y : Type} (xs : list X) (ys : list Y),
    le (length xs) (length ys) ->
    map fst (combine xs ys) = xs.
Proof.
    intros X Y xs. induction xs as [|x' xs']; intros ys HLen; simpl; auto.
    destruct ys as [|y' ys']; simpl in HLen.
    - inversion HLen.
    - simpl; rewrite IHxs'; auto.
      apply le_S_n; auto.
Qed.

Lemma combine_snd_full : forall {X Y : Type} (xs : list X) (ys : list Y),
    le (length ys) (length xs) ->
    map snd (combine xs ys) = ys.
Proof.
    intros X Y xs. induction xs as [|x' xs']; intros ys HLen; simpl.
    - destruct ys; simpl in HLen; auto. inversion HLen.
    - destruct ys as [|y' ys']; simpl in *; auto.
      rewrite IHxs'; auto. apply le_S_n; auto.
Qed.

Lemma combine_snd_mIncluded : forall {X Y : Type} (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2})
        (xs : list X) (ys : list Y),
    mIncluded eqDec_Y (map snd (combine xs ys)) ys.
Proof.
    intros X Y eqDec_Y xs. induction xs as [|x' xs']; intros ys;
    apply mIncluded_universe; intros y; simpl; auto.
    destruct ys as [|y' ys']; simpl; auto.
    specialize IHxs' with ys'; rewrite mIncluded_universe in IHxs'; specialize IHxs' with y.
    destruct (eqDec_Y y y'); subst; simpl; auto.
Qed.
      

Lemma getAllInjections_msetMap' : forall {X Y : Type} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2})
        (xs : list X) (ys : list Y),
    NoDup xs -> NoDup ys ->
    forall (m : list (X * Y)),
    (map fst m) = xs ->
    mIncluded eqDec_Y (map snd m) ys ->
    In m (getAllInjections xs ys).
Proof.
    intros X Y eqDec_X eqDec_Y xs ys HNd_X HNd_Y m HEq HI; subst.
    unfold getAllInjections. apply in_map_iff.
    generalize dependent ys. induction m as [|[x' y'] m']; intros; simpl in *.
    - exists ys; split; auto.
      apply permutations_Permutation; apply Permutation_refl.
    - inversion HNd_X; subst.
      pose proof (mIncluded_incl _ _ _ HI) as Hi.
      apply mIncluded_cons_removeFirst in HI.
      apply removeFirst_NoDup with (eq_dec := eqDec_Y) (a := y') in HNd_Y.
      pose proof (IHm' H2 _ HNd_Y HI) as IH; destruct IH as [ys' [HEq HIn]].
      exists (y' :: ys'); split.
    -- rewrite HEq; auto.
    -- apply permutations_cons_removeFirst with (eqDec_X:=eqDec_Y); auto.
       apply Hi; simpl; auto.
Qed.  


Definition prod_eqDec {A B : Type}
        (eqDec_A : forall x y : A, {x = y} + {x <> y})
        (eqDec_B : forall x y : B, {x = y} + {x <> y})
        (p1 p2 : A * B) : 
    {p1 = p2} + {p1 <> p2}.
Proof.
    decide equality.
Defined.

Lemma getAllInjections_msetMap'' : forall {X Y : Type} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2})
        (xs : list X) (ys : list Y),
    NoDup xs -> NoDup ys ->
    forall (m : list (X * Y)),
    mSameset eqDec_X (map fst m) xs ->
    mIncluded eqDec_Y (map snd m) ys ->
    (exists m', (In m' (getAllInjections xs ys)) /\ (mSameset (prod_eqDec eqDec_X eqDec_Y) m' m)).
Proof.
    intros X Y eqDec_X eqDec_Y xs ys HNd_X HNd_Y m HS HI.
    assert (Permutation xs (map fst m)) as HP
    by (apply Permutation_sym; apply Permutation_mSameset with (eqDec_X:=eqDec_X); auto).
    destruct (Permutation_map_inv fst m HP) as [m' [HEq HP']].
    assert (mIncluded eqDec_Y (map snd m') ys) as HI'.
    { apply mIncluded_transitive with (M2 := map snd m); auto.
      apply mIncluded_reflexive; apply mSameset_symmetric;
      apply Permutation_mSameset with (eqDec_X:=eqDec_Y);
      apply Permutation_map; auto. }
    exists m'; split.
    - apply (getAllInjections_msetMap' eqDec_X eqDec_Y); auto.
    - apply Permutation_mSameset with (eqDec_X:=prod_eqDec eqDec_X eqDec_Y);
      apply Permutation_sym; auto.
Qed.


Eval compute in (flat_map permutations (getAllInjections (0::1::nil) (6::7::8::nil))).


Lemma getAllInjections_msetMap : forall {X Y : Type} (eqDec_X : forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) (eqDec_Y : forall y1 y2 : Y, {y1 = y2} + {y1 <> y2})
        (xs : list X) (ys : list Y),
    NoDup xs -> NoDup ys ->
    forall (m : list (X * Y)),
    mSameset eqDec_X (map fst m) xs ->
    mIncluded eqDec_Y (map snd m) ys ->
    In m (flat_map permutations (getAllInjections xs ys)).
Proof.
    intros X Y eqDec_X eqDec_Y xs ys HNd_X HNd_Y m HS HI.
    apply in_flat_map.
    destruct (getAllInjections_msetMap'' eqDec_X eqDec_Y xs ys HNd_X HNd_Y m HS HI) as [m' [HIn HS']].
    exists m'; split; auto.
    apply permutations_Permutation; apply Permutation_mSameset with (eqDec_X:=prod_eqDec eqDec_X eqDec_Y); auto.
Qed.

