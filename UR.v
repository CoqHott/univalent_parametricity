
(************************************************************************)
(* This file introduces the univalent logical relation   *)
(************************************************************************)

Require Import HoTT Tactics String.

Set Universe Polymorphism.
Set Primitive Projections.

Tactic Notation "erefine" uconstr(c) := unshelve notypeclasses refine c.

Definition eq_to_equiv A B : A = B -> A ≃ B :=
  fun e => e # (Equiv_id A).

Definition Funext := forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).

(* The frawework relies on the univalence axiom and functional extensionality *)

Axiom univalence : forall A B, IsEquiv (eq_to_equiv A B).
Axiom funext : Funext. 

(* for minor differences between Prop and Type (coming from impredicativity)  *)
(* we need to state again univalence for Prop, even if in principle Prop is  *)
(* a subtype iof Type *)

Definition Equiv_id_P (A:Prop) : A ≃ A := 
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)).

Definition eq_to_equiv_P (A B:Prop) : A = B -> A ≃ B :=
  fun e => @transport_eq Prop (fun X => A ≃ X) A B e (Equiv_id_P A).
             
Axiom univalence_P : forall (A B:Prop), IsEquiv (eq_to_equiv_P A B).


Class UR A B := {
  ur : A -> B -> Type 
}.

Arguments ur {_ _ _} _ _.

Notation "x ≈ y" := (ur x y) (at level 20).

Class UR_Coh@{i j k} A B (e : Equiv@{i j} A B) (H: UR@{i j k} A B) := {
  ur_coh : forall (a a':A), Equiv (a = a') (a ≈ (↑ a')) }.

Class UR_Type A B :=
  { equiv :> A ≃ B;
    Ur :> UR A B;
    Ur_Coh:> UR_Coh A B equiv Ur}.

Infix "⋈" := UR_Type (at level 25).

Arguments equiv {_ _} _.
Arguments Ur {_ _} _.
Arguments Ur_Coh {_ _} _.

Class Equiv_eff (A B:Type) (e:A ≃ B) := { }.

Class Equiv_eff_inv (A B:Type) (e:A ≃ B) := { }.

Class Equiv_eff_section (A B:Type) (e:A ≃ B) := { }.

Class Equiv_eff_retraction (A B:Type) (e:A ≃ B) := { }.

Class Equiv_eff_full (A B:Type) (e:A ≃ B) :=
  {
    equiv_eff :> Equiv_eff A B e;
    equiv_eff_inv :> Equiv_eff_inv A B e;
    equiv_eff_section :> Equiv_eff_section A B e;
    equiv_eff_retraction :> Equiv_eff_retraction A B e
  }.

(* Instance Equiv_eff_retraction_section_Equiv_eff A B e (H:@Equiv_eff_section A B e) (H' :@Equiv_eff_retraction A B e) *)
(*   : Equiv_eff A B e *)
(*   := {}. *)

Class Ur_Coh_eff (A B:Type) (UR:A ⋈ B):= { }.

Class UR_eff (A B:Type) (UR : A ⋈ B) :=
  {
    equiv_eff_full :> Equiv_eff_full A B (equiv UR);
    ur_Coh_eff :> Ur_Coh_eff A B UR
}.

(* Instance Equiv_eff_Ur_Coh_UR_eff A B (UR : A ⋈ B) `{@Equiv_eff A B (equiv UR)} `{@Ur_Coh_eff A B UR} : UR_eff A B UR *)
(*   := {}. *)

(* some facilities to create an instance of UR_Type *)

Definition UR_gen A : UR A A := {| ur := (eq A) |}.

Definition UR_inverse A B `{UR A B} : UR B A := {| ur := fun b a => ur a b |}.

Class URRefl@{i j k} A B (e : Equiv@{i j} A B) (H: UR@{i j k} A B) := {
  ur_refl_ : forall a : A,  a ≈ ↑ a 
}.

Arguments ur_refl_ {_ _ _ _ _} _.

Definition URIsEq@{i j k} A B (e : A ≃ B) (H: UR A B) (H:URRefl@{i j k} A B e H)
  :=  forall (a a':A), @IsEquiv (a = a') (a ≈ (↑ a'))
                                (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a)).

Existing Class URIsEq.
Typeclasses Transparent URIsEq.

Instance Ur_Coh_from_ur_refl A B (e:A ≃ B) (H:UR A B)
           (Hrefl : URRefl A B e H) : URIsEq A B e H Hrefl ->
                                       UR_Coh A B e H.
Proof.
  intros Hiseq. econstructor. intros a a'.
  exact (BuildEquiv _ _ (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a))
                     (Hiseq a a')).
Defined.

Definition alt_ur_coh {A B:Type} (H:A ⋈ B) (einv := Equiv_inverse (equiv H)):
           forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b).
Proof.
  intros a b. cbn. 
  refine (transport_eq (fun X => (a ≈ X) ≃ (a = univalent_transport b))
                       (e_sect _ b) _). apply Equiv_inverse. 
    unshelve refine (ur_coh _ _). 
Defined.

Definition ur_refl {A B: Type} {e : A ⋈ B} : forall a : A,  a ≈ ↑ a := fun a => 
  e_fun (ur_coh a a) eq_refl. 

Hint Extern 0 (_ ≈ _) => unshelve notypeclasses refine  (ur_refl _): typeclass_instances.


(* Definition of univalent relation for basic type constructors *)

(*! Universe !*)

Instance UR_Type_def@{i j} : UR@{j j j} Type@{i} Type@{i} :=
  {| ur := UR_Type@{i i i} |}.

(*! Forall !*)

Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.

Definition URForall A A' (B : A -> Type) (B' : A' -> Type) {HA : UR A A'}
           {HB: forall x y (H: x ≈ y), UR (B x) (B' y)} : UR (forall x, B x) (forall y, B' y) :=
  {| ur := fun f g => forall x y (H: x ≈ y), f x ≈ g y |}.

Hint Extern 0 (UR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

(*! Sigma !*)

Definition URSigma A A' (B : A -> Type)(B' : A' -> Type) `{UR A A'}
           `{forall x y (H: x ≈ y), UR (B x) (B' y)} : UR (sigT B) (sigT B')
  :=
  {| ur := fun x y => sigT (fun (_ : x.1 ≈ y.1) => x.2 ≈ y.2) |}.

Hint Extern 0 (UR ({x:_ & _}) ({x:_ & _})) =>
  erefine (@URSigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

(*! nat !*)

Instance UR_nat : UR nat nat := UR_gen nat. 

(*! bool !*)

Instance UR_bool : UR bool bool := UR_gen bool. 

