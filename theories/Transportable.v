(************************************************************************)
(* The univalent relation on dependent product uses a framework of transportable type families
   in order to enhance effectiveness. 
   This file introduces the transportable type class and default instances *)
(************************************************************************)

Require Import HoTT.
 
Set Universe Polymorphism.

Class Transportable {A} (P:A -> Type) :=
  {
    transportable : forall x y, x = y -> P x ≃ P y;
    transportable_refl : forall x, transportable x x eq_refl = Equiv_id _
  }.


Definition Transportable_default {A} (P:A -> Type) : Transportable P.
Proof.
  unshelve econstructor.
  - intros x y e; destruct e. apply Equiv_id.
  - reflexivity.
Defined. 

Instance Transportable_Type (P:Type -> Type) : Transportable P :=
  Transportable_default P.

Instance Transportable_Forall_default A B (P: (forall x: A, B x) -> Type) : Transportable P :=
  Transportable_default P.


Instance Transportable_cst A B : Transportable (fun _ : A => B) :=
  {|
    transportable := fun (x y : A) _ => Equiv_id B;
    transportable_refl := fun x : A => eq_refl
  |}.
