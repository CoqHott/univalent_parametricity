Require Import HoTT String.

Set Universe Polymorphism.
Set Primitive Projections.


Definition eq_to_equiv A B : A = B -> A ≃ B :=
  fun e => e # (Equiv_id A).

Definition Funext := forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).

(* The frawework relies on the univalence axiom and functional extensionality *)

Axiom univalence : forall A B, IsEquiv (eq_to_equiv A B).
Axiom funext : Funext. 

Instance funext_isequiv A P (f g : forall x : A, P x) : IsEquiv (@apD10 _ _ f g) := funext _ _ _ _.

Instance univalence_isequiv A B : IsEquiv (eq_to_equiv A B) := univalence _ _.

Definition transport_apD10 A B (f g : forall x:A, B x)
           (P : forall x:A, B x -> Type)
           (e : f = g) x v: transport_eq (fun X => P x (X x))
                                                       e v
                                          = transport_eq (fun X => P x X)
                                                (apD10 e x) v.
  destruct e. reflexivity.
Defined. 


Definition transport_funext {A B} {f g : forall x:A, B x}
           (P : forall x:A, B x -> Type) x 
           (v : P x (f x)) (e : forall x, f x = g x)
            : transport_eq (fun X => P x (X x))
                                                       (e_inv apD10 e) v
                                          = transport_eq (fun X => P x X)
                                                (e x) v.
Proof.
  rewrite transport_apD10. rewrite e_retr. reflexivity.
Defined.


(* for minor differences between Prop and Type (coming from impredicativity)  *)
(* we need to state again univalence for Prop, even if in principle Prop is  *)
(* a subtype iof Type *)

Definition Equiv_id_P (A:Prop) : A ≃ A := 
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).

Definition eq_to_equiv_P (A B:Prop) : A = B -> A ≃ B :=
  fun e => @transport_eq Prop (fun X => A ≃ X) A B e (Equiv_id_P A).
             
Axiom univalence_P : forall (A B:Prop), IsEquiv (eq_to_equiv_P A B).
