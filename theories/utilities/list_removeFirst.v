
Require Import Coq.Lists.List.


(** If two lists are equal, then there lengths are equal. *)
Lemma listEq_length : forall {A : Type} (l m : list A),
    l = m ->
    length l = length m.
Proof.
    intros A l m H; 
    destruct l; subst; auto.
Qed.


(** removeFirst 
 ** 
 ** Removes the first occurence of x in l. *)
Fixpoint removeFirst {A : Type} 
        (eq_dec : forall x y : A, {x = y}+{x <> y}) 
        (x : A) 
        (l : list A) {struct l} : 
    list A :=
match l with
| y::l' => if (eq_dec x y) then l' else y::(removeFirst eq_dec x l')
| nil => nil
end.


Lemma removeFirst_lengthAdd : forall A eq_dec x (l : list A),
    In x l ->
    length (removeFirst eq_dec x l) + 1 = length l.
Proof.
    intros A eq_dec x l HIn; 
    induction l; [inversion HIn|]; simpl;
    destruct (eq_dec x a) as [Heqx|Heqx]; subst.
    - rewrite PeanoNat.Nat.add_1_r; auto.
    - destruct HIn as [HIn|HIn]; subst; simpl.
    -- exfalso; apply Heqx; auto.
    -- apply IHl in HIn; rewrite <- HIn; auto.
Qed.

Lemma removeFirst_lengthSub : forall A eq_dec x (l : list A),
    In x l ->
    length (removeFirst eq_dec x l) = length l - 1.
Proof.
    intros A eq_dec x l HIn; 
    induction l; [inversion HIn|]; simpl;
    destruct (eq_dec x a) as [Heqx|Heqx]; subst.
    - rewrite PeanoNat.Nat.sub_0_r; auto.
    - destruct HIn as [HIn|HIn]; subst; simpl.
    -- exfalso; apply Heqx; auto.
    -- assert (exists n, length l = S n) as Hl.
    { destruct l; [inversion HIn | simpl; exists (length l); auto]. }
    apply IHl in HIn; rewrite HIn;
    destruct Hl as [n Hl]; rewrite Hl;
    simpl; rewrite PeanoNat.Nat.sub_0_r; auto.
Qed.