Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.

Existing Class eq. 

Ltac resolve_eq := intros; 
                   progress (repeat (try reflexivity;
                   try eassumption;
                   cbn; try rewrite concat_refl;
                   try rewrite inv_inv;
                   try repeat eapply ap; 
                   try repeat eapply ap2)).

Hint Extern 100 (_ = _) => resolve_eq : typeclass_instances.

Hint Extern 10 (?e ?x = _ ) => eapply (ap e) : typeclass_instances.

Hint Extern 10 (?e ?x ?y = _ ) => eapply (ap2 e) : typeclass_instances.

Ltac clear_eq := cbn in *; repeat match goal with | [e: ?A = ?B |- _] => destruct e end.

Create HintDb equiv.
Hint Extern 0 (prod ?A ?B ) => split : typeclass_instances.

Hint Extern 0 unit => exact tt  : typeclass_instances.

Ltac etransitivity := refine (concat _ _).


Hint Extern 0 (e_inv' ?e (e_fun ?e ?x) = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 (e_fun ?e (e_inv' ?e ?x) = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_inv' ?e) ∘ (e_fun ?e) ?x = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_fun ?e) ∘ (e_inv' ?e) ?x = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 (e_inv (e_fun ?e) (e_fun ?e ?x) = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 (e_fun ?e (e_inv (e_fun ?e) ?x) = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_inv (e_fun ?e)) ∘ (e_fun ?e) ?x = _ ) =>
etransitivity ; [exact (e_sect (e_fun e) x) | idtac ] : equiv.

Hint Extern 0 ((e_fun ?e) ∘ (e_inv (e_fun ?e)) ?x = _ ) =>
etransitivity ; [exact (e_retr (e_fun e) x) | idtac ] : equiv.


Hint Extern 0 (?g (?f ?n) = _ ) =>
etransitivity ; [exact (e_sect f n) | idtac ] : equiv.

Hint Extern 0 (?f (?g ?n) = _ ) =>
etransitivity ; [exact (e_retr f n) | idtac ] : equiv.

Hint Extern 0 (_ = ?g (?f ?n)) => exact (e_sect f n)^ : equiv.

Hint Extern 0 (_ = ?f (?g ?n)) => exact (e_retr f n)^ : equiv.

Typeclasses Transparent e_inv'  univalent_transport. 
Hint Transparent e_inv'  univalent_transport. 
Hint Unfold e_inv'  univalent_transport. 


Ltac equiv_elim :=
  clear_eq;
  match goal with | [x: ?A |- _] => induction x; simpl; try typeclasses eauto with typeclass_instances end.

Hint Extern 0 => progress (cbn in *): typeclass_instances. 

Hint Extern 0 => eassumption : typeclass_instances. 

Tactic Notation "erefine" uconstr(c) := unshelve notypeclasses refine c.

Ltac change_eq_to_Logic_eq :=
  let e := fresh "e" in
  match goal with | |- ?X = ?Y =>
                    assert (e : Logic.eq X Y) ; [idtac | now destruct e]
  end.