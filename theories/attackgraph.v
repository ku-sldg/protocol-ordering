Require Import Coq.Lists.List.

(*************************
 ** ATTACK GRAPHS
 **
 ** A record containing a set of events, a set
 ** of directed edges representing chronological
 ** time, and an event labeling function. *)


(** (ms C1 C2) denotes the measurement of 
 ** component C2 by component C1. *)
Inductive measLabel (component : Type) : Type :=
| msp : component -> component -> measLabel component
| ms : measLabel component.


(** (cor C) and (rep C) denotes the corruption
 ** and repair respectively of component C. *)
Inductive advLabel (component : Type) : Type :=
| cor : component -> advLabel component
| rep : component -> advLabel component.


Record attackgraph (component : Type) : Type :=
{
  event : Type ;
  edges : list (event * event) ;
  label : event -> (measLabel component) + (advLabel component) ;

  eqDec_event :  forall (x y : event), {x = y} + {x <> y} ;
  eqDec_component : forall (x y : component), {x = y} + {x <> y}
}.


Section Notations.

    Context {component : Type}.
    Definition myEvent (A : attackgraph component) := A.(event _).
    Definition myEdges (A : attackgraph component) := A.(edges _).
    Definition myLabel (A : attackgraph component) := A.(label _).
    Definition myEqDec_event (A : attackgraph component) := A.(eqDec_event _).
    Definition myEqDec_component (A : attackgraph component) := A.(eqDec_component _).

    Definition eventT (A : attackgraph component) := A.(event _).
    Definition edgesT (A : attackgraph component) := list (eventT A * eventT A).
    Definition labelT (A : attackgraph component) := (eventT A) -> (measLabel component) + (advLabel component).


    Lemma myEqDec_labels : forall (A : attackgraph component),
        forall (x y : (measLabel component) + (advLabel component)),
        {x = y} + {x <> y}.
    Proof.
        intros A x y. destruct x as [m|a], y as [m'|a'];
        try (right; intros contra; inversion contra; contradiction).
        - destruct m as [c1 c2|], m' as [c1' c2'|];
          try (right; intros contra; inversion contra; contradiction);
          try (destruct (myEqDec_component A c1 c1'), (myEqDec_component A c2 c2'); subst);
          try (right; intros contra; inversion contra; contradiction);
          left; auto.
        - destruct a as [c|c], a' as [c'|c'];
          try (right; intros contra; inversion contra; contradiction);
          destruct (myEqDec_component A c c'); subst;
          try (right; intros contra; inversion contra; contradiction);
          left; auto.
    Defined.
    
End Notations.