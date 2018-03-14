
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

Instance funext_isequiv A P (f g : forall x : A, P x) : IsEquiv (@apD10 _ _ f g) := funext _ _ _ _.

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

Class Canonical_eq@{i} (A:Type@{i}) :=
  { purify : forall (x y : A), x = y -> x = y ;
    purify_refl : forall x, purify x x eq_refl = eq_refl }.

Definition Canonical_eq_gen A : Canonical_eq A :=
  {| purify := fun x y e => e ;
     purify_refl := fun x => eq_refl |}.

Arguments purify {_} _.
Arguments purify_refl {_}.

Definition purify_eq {A} (e :Canonical_eq A) : e.(purify) = fun x y e => e.
Proof.
  apply funext; intros x. apply funext; intros y. apply funext; intro E.
  destruct E. apply purify_refl. 
Defined. 

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

Definition Canonical_eq_eq A (e e':Canonical_eq A)
           (H : e.(purify) = e'.(purify)) :
  (transport_eq (fun X => X = _) H  (purify_eq e) = (purify_eq e')) ->
  e = e'.
Proof.
  destruct e, e'. cbn in *. destruct H. cbn.
  unfold purify_eq. admit.
  (* intro H. destruct H. reflexivity. *)
Admitted.

Definition Canonical_contr A (e :Canonical_eq A) : e = Canonical_eq_gen A.
Proof.
  unshelve eapply Canonical_eq_eq.
  apply purify_eq.
  cbn. rewrite transport_paths_l. rewrite inv_inv.
  unfold purify_eq. cbn. apply inverse. 
  pose (@e_sect _ _ _ (funext _ _  (fun (x y : A) (e0 : eq A x y) => e0) (fun (x y : A) (e0 : eq A x y) => e0)) eq_refl).
  eapply concat; try apply e0. clear e0. apply ap. apply funext. intros. cbn.
  pose (@e_sect _ _ _ (funext _ _  (fun (y : A) (e0 : eq A x y) => e0) (fun (y : A) (e0 : eq A x y) => e0)) eq_refl).
  eapply concat; try apply e0. clear e0. apply ap. apply funext. intros y. cbn.
  pose (@e_sect _ _ _ (funext _ _  (fun (e0 : eq A x y) => e0) (fun (e0 : eq A x y) => e0)) eq_refl). 
  eapply concat; try apply e0. clear e0. apply ap. apply funext. intros e0. cbn.
  destruct e0. reflexivity.                  
Defined. 


Definition Canonical_eq_decidable A (Hdec:forall x y : A, (x=y) + ((x = y) -> False)) : Canonical_eq A.
  unshelve econstructor.
  - intros x y e.
    destruct (Hdec x y) as [e0 | n0].
    destruct e0. reflexivity. 
    destruct (n0 e).
  - intro x. cbn. destruct (Hdec x x); cbn.
    assert (e = eq_refl) by (eapply is_hset).
    rewrite X. reflexivity.
    destruct (f eq_refl).
    Unshelve. apply Hedberg. auto.
Defined.

Class UR_Type A B :=
  { equiv :> A ≃ B;
    Ur :> UR A B;
    Ur_Coh:> UR_Coh A B equiv Ur;
    Ur_Can_A :> Canonical_eq A;
    Ur_Can_B :> Canonical_eq B;
  }.

Infix "⋈" := UR_Type (at level 25).

Arguments equiv {_ _} _.
Arguments Ur {_ _} _.
Arguments Ur_Coh {_ _} _.
Arguments Ur_Can_A {_ _} _.
Arguments Ur_Can_B {_ _} _.

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

Instance URType_Refl : URRefl Type Type (Equiv_id _) _ :=
  {| ur_refl_ := _ |}.
Proof.
  intro A. cbn. unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.    
Defined.

Class Transportable {A} (P:A -> Type) :=
  {
    transportable :> forall x y, x = y -> P x ≃ P y;
    transportable_refl : forall x, transportable x x eq_refl = Equiv_id _
  }.

Definition Transportable_decidable {A} (P:A -> Type) (Hdec:forall x y : A, (x=y) + ((x = y) -> False)): Transportable P.
Proof.
  unshelve econstructor.
  - intros x y e. destruct (Hdec x y) as [e0 | n0].
    destruct e0. apply Equiv_id.
    destruct (n0 e).
  - intro x. cbn. destruct (Hdec x x); cbn.
    assert (e = eq_refl) by (eapply is_hset).
    rewrite X. reflexivity.
    destruct (f eq_refl).
    Unshelve. apply Hedberg. auto.
Defined. 

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

Class URForall_Type_class A A' {HA : UR A A'}  (P : A -> Type) (Q : A' -> Type) :=
  { transport_ :> Transportable P;
    ur_type :> forall x y (H:x ≈ y), P x ⋈ Q y}.

Arguments ur_type {_ _ _ _ _} _. 

Definition URForall_Type A A' {HA : UR A A'} :
  UR (A -> Type) (A' -> Type)
  :=
    {| ur := fun P Q => URForall_Type_class A A' P Q |}.

Definition URForall A A' (B : A -> Type) (B' : A' -> Type) {HA : UR A A'} 
           {HB: forall x y (H: x ≈ y), UR (B x) (B' y)} : UR (forall x, B x) (forall y, B' y)
  :=
  {| ur := fun f g => forall x y (H:x ≈ y), f x ≈ g y |}.

Hint Extern 0 (UR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall_Type A A' _); cbn in *; intros : typeclass_instances.

Hint Extern 1 (UR (forall x:?A, _) (forall x:?A', _)) =>
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


