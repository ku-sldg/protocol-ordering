Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Require Import AttestationProtocolOrdering.utilities.nat_le.
Require Import AttestationProtocolOrdering.utilities.list_functions.
Require Import AttestationProtocolOrdering.utilities.list_facts.


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

Lemma permutations_Permutations : forall {X} (l p : list X),
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

    