
Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.utilities.mset.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.attackgraph_adversary.

Section AttackGraphOrdering. 
    Context {components : Type}.


(** simeq (Equivalence)
 **
 ** Attack graphs A and B are equivalent (i.e., A \simeq B)
 ** if and only if \pi(A) = \pi(B) and \tau(A) = \tau(B). *)

    Definition simeq (A B : attackgraph components) : Prop :=
        mSameset (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B)) /\
        mSameset (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)).

    Definition simeq_fix (A B : attackgraph components) : Prop :=
        if (mSamesetDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B)))
        then if (mSamesetDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)))
             then True
             else False
        else False.
    
    Hint Unfold simeq : core.

    Lemma simeq_same : forall A B,
        simeq_fix A B <-> simeq A B.
    Proof.
        unfold simeq_fix; intros; split; intros H.
        - destruct (mSamesetDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))),
                   (mSamesetDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)));
          try contradiction;
          split; apply mSameset_same'; auto.
        - destruct (mSamesetDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))) as [|Hp],
                   (mSamesetDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))) as [|Ht];
          auto; destruct H;
          try apply Hp; try apply Ht; apply mSameset_same'; auto.
    Qed.

    Lemma simeqDec : forall (A B : attackgraph components),
        {simeq_fix A B} + {~ simeq_fix A B}.
    Proof.
        unfold simeq_fix; intros A B;
        destruct (mSamesetDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))),
                 (mSamesetDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)));
        auto.
    Defined.

    Theorem simeq_reflexive : forall A,
        simeq A A.
    Proof.
        intros A; split; apply mSameset_reflexive.
    Qed.

    Theorem simeq_symmetric : forall A B,
        simeq A B ->
        simeq B A.
    Proof.
        intros A B H; destruct H; split;
        apply mSameset_symmetric; eapply mSameset_eqDec; eauto.
    Qed.

    Theorem simeq_transitive : forall A B C,
        simeq A B ->
        simeq B C ->
        simeq A C.
    Proof.
        intros A B C H H'; destruct H, H'; split;
        eapply mSameset_transitive; eapply mSameset_eqDec; eauto.
    Qed.

(** preceq (Partial order)
 **
 ** Attack graph A is less than or equal to B (i.e., A \preceq B)
 ** if and only if \pi(A) \subseteq \pi(B) and \tau(A) \subseteq \tau(B) *)

    Definition preceq (A B : attackgraph components) : Prop :=
        mIncluded (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B)) /\
        mIncluded (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)).

    Definition preceq_fix (A B : attackgraph components) : Prop :=
        if mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B)) 
        then if mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))
            then True
            else False
        else False.

    Hint Unfold preceq : core.

    Lemma preceq_same : forall A B,
        preceq_fix A B <-> preceq A B.
    Proof.
        unfold preceq_fix; intros; split; intros H.
        - destruct (mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))),
                   (mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)));
          try contradiction;
          split; apply mIncluded_same'; auto.
        - destruct (mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))) as [|Hp],
                   (mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))) as [|Ht];
          auto; destruct H;
          try apply Hp; try apply Ht; apply mIncluded_same'; auto.
    Qed.

    Lemma preceqDec : forall (A B : attackgraph components),
        {preceq_fix A B} + {~ preceq_fix A B}.
    Proof.
        unfold preceq_fix; intros A B;
        destruct (mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))),
                 (mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)));
        auto.
    Defined.

    Theorem preceq_reflexive : forall A B,
        simeq A B ->
        preceq A B.
    Proof.
        intros A B H; destruct H; split; apply mIncluded_reflexive; auto.
    Qed.

    Theorem preceq_antisymmetric : forall A B,
        preceq A B ->
        preceq B A ->
        simeq A B.
    Proof.
        intros A B H H'; destruct H, H'; split;
        apply mIncluded_antisymmetric; auto; eapply mIncluded_eqDec; eauto.
    Qed.

    Theorem preceq_transitive : forall A B C,
        preceq A B ->
        preceq B C ->
        preceq A C.
    Proof.
        intros A B C H H'; destruct H, H';
        split; eapply mIncluded_transitive; eauto; eapply mIncluded_eqDec; eauto.
    Qed.





(** prec (Strict partial order)
 **
 ** Attack graph A is strictly less than B (i.e., A \prec B)
 ** if and only if \pi(A) \subseteq \pi(B) and \tau(A) \subseteq \tau(B)
 ** and either \pi(A) \subset \pi(B) or \tau(A) \subset \tau(B). *)

    Definition prec (A B : attackgraph components) : Prop :=
        mIncluded (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B)) /\
        mIncluded (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)) /\
        ( mStrictIncluded (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B)) \/
          mStrictIncluded (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))).

    Definition prec_fix (A B : attackgraph components) : Prop :=
        if mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))
        then if mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))
             then if mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))
                  then True
                  else if mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))
                       then True
                  else False
             else False
        else False.

    Hint Unfold prec : core.

    Lemma prec_same : forall A B,
        prec_fix A B <-> prec A B.
    Proof.
        unfold prec_fix; intros; split; intros H.
        - destruct (mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))) as [Hp|Hp], 
                   (mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))) as [Ht|Ht],
                   (mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))) as [Hp'|Hp'], 
                   (mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))) as [Ht'|Ht'];
          try inversion H; repeat split; 
          try (eapply mIncluded_same'; eauto; fail);
          try (left; eapply mStrictIncluded_same'; eauto; fail);
          try (right; eapply mStrictIncluded_same'; eauto; fail). 
        - destruct (mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))) as [Hp|Hp], 
                   (mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))) as [Ht|Ht],
                   (mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))) as [HP|HP], 
                   (mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))) as [HT|HT];
          destruct H as [Hp' H]; destruct H as [Ht' H]; auto;
          try (apply Hp; eapply mIncluded_same'; eauto);
          try (apply Ht; eapply mIncluded_same'; eauto);
          destruct H; [apply HP | apply HT]; eapply mStrictIncluded_same'; eauto.
    Qed.

    Lemma precDec : forall (A B : attackgraph components),
        {prec_fix A B} + {~ prec_fix A B}.
    Proof.
        intros; unfold prec_fix; 
        destruct (mIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))), 
                 (mIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B))),
                 (mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (pi A)) (map (myLabel B) (pi B))), 
                 (mStrictIncludedDec (myEqDec_labels A) (map (myLabel A) (tau A)) (map (myLabel B) (tau B)));
        auto.
    Defined.

    Theorem prec_irreflexive : forall A B,
        simeq A B ->
        ~ prec A B.
    Proof.
        intros A B H H';
        destruct H as [H H0]; apply mSameset_correct in H, H0; destruct H, H0.
        destruct H' as [H' H0']; destruct H0' as [H0' HP];
        destruct HP as [HP|HP]; destruct HP; contradiction.
    Qed.

    Theorem prec_asymmetric : forall A B,
        prec A B ->
        ~ prec B A.
    Proof.
        intros A B HAB HBA;
        destruct HAB as [HpAB HAB]; destruct HAB as [HtAB HAB];
        destruct HBA as [HpBA HBA]; destruct HBA as [HtBA HBA];
        destruct HAB as [HAB|HAB];
        destruct HAB as [HAB contra];
        apply contra; eapply mIncluded_eqDec; eauto.
    Qed.

    Theorem prec_transitive : forall A B C,
        prec A B ->
        prec B C ->
        prec A C.
    Proof.
        intros A B C HAB HBC;
        destruct HAB as [HpAB HAB]; destruct HAB as [HtAB HAB];
        destruct HBC as [HpBC HBC]; destruct HBC as [HtBC HBC];
        eapply mIncluded_eqDec in HpBC, HtBC;
        repeat split;
        try (eapply mIncluded_transitive; eauto);
        destruct HAB; [ left | right ];
        eapply mStrictIncluded_mIncluded1; eauto.
    Qed.
    
    Lemma prec_simeq1 : forall A B C,
        simeq A B ->
        prec B C ->
        prec A C.
    Proof.
        intros A B C HAB HBC;
        destruct HAB as [HpAB HtAB]; apply mSameset_correct in HpAB, HtAB; destruct HpAB, HtAB;
        destruct HBC as [HpBC HBC]; destruct HBC as [HtBC HBC];
        repeat split;
        try (eapply mIncluded_transitive; eauto; eapply mIncluded_eqDec; eauto);
        destruct HBC; [ left | right ];
        eapply mStrictIncluded_mIncluded2; eauto; eapply mStrictIncluded_eqDec; eauto.
    Qed.

    Lemma prec_simeq2 : forall A B C,
        prec A B ->
        simeq B C ->
        prec A C.
    Proof.
        intros A B C HAB HBC;
        destruct HAB as [HpAB HAB]; destruct HAB as [HtAB HAB];
        destruct HBC as [HpBC HtBC]; apply mSameset_correct in HpBC, HtBC; destruct HpBC, HtBC;
        repeat split;
        try (eapply mIncluded_transitive; eauto; eapply mIncluded_eqDec; eauto);
        destruct HAB; [ left | right ];
        eapply mStrictIncluded_mIncluded1; eauto; eapply mIncluded_eqDec; eauto.
    Qed.


    Lemma preceq_correct : forall A B,
        preceq A B <->
        prec A B \/ simeq A B.
    Proof.
        intros A B; split; intros H. 
        - destruct H as [H H'].
          destruct (mIncludedDec (myEqDec_labels A) (map (myLabel B) (pi B)) (map (myLabel A) (pi A))) as [Hp|Hp];
          destruct (mIncludedDec (myEqDec_labels A) (map (myLabel B) (tau B)) (map (myLabel A) (tau A))) as [Ht|Ht];
          rewrite mIncluded_same' in Hp, Ht.
          -- right; split; apply mIncluded_antisymmetric; auto.
          -- left; repeat split; auto; right; split; auto.
          -- left; repeat split; auto; left; split; auto.
          -- left; repeat split; auto; left; split; auto.
        - destruct H as [H|H].
        -- destruct H as [H' H]; destruct H; split; auto. 
        -- destruct H; split; apply mIncluded_reflexive; auto.
    Qed.

End AttackGraphOrdering.

    
