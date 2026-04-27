(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)

Require Import HoTT CanonicalEq.
Require Import UnivalentParametricity.theories.Transportable.
Require Import URTactics.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

(* basic class for parametric relations *)

#[universes(collapse_sort_variables=no)]
Class PR A B : Type := {
  pr : A -> B -> Type 
}.

Arguments pr {_ _ _} _ _.

Notation "x ≈ y" := (pr x y) (at level 20).

(* basic classes for univalent relations *)

#[universes(collapse_sort_variables=no)]
Class UR_Coh A B (e : A ≃ B) (H: PR@{_ _ _ Type | _ _ _} A B) := {
  ur_coh : forall (a a':A), Equiv (a = a') (a ≈ ↑ a') }.
  (* ur_coh : forall (a a':A), Equiv (a = a') (a ≈ (↑ a')) }. *)

Class UR_Type A B {Ur: PR A B} :=
  { 
    equiv : A ≃ B;
    Ur_Coh : UR_Coh A B equiv Ur
  }.

Infix "⋈" := UR_Type (at level 25).

Arguments pr {_ _ _} _ _.
Arguments equiv {_ _ _} _.
Arguments Ur_Coh {_ _ _} _.

(* Arguments Ur_Can_A {_ _} _.
Arguments Ur_Can_B {_ _} _.*)

#[export] Hint Extern 100 (_ ≃ _) => unshelve notypeclasses refine (equiv _): typeclass_instances. 
#[export] Hint Extern 100 (UR_Coh _ _ _ _) => unshelve notypeclasses refine (Ur_Coh _): typeclass_instances. 

Definition equiv_sprop (P : Prop) (Q : SProp) : Type := (prod (P -> Q) (Q -> P)).

Notation "P ↔ Q" := (equiv_sprop P Q) (at level 50).

Instance PR_Prop : PR Prop SProp := {| pr := fun A B => A -> B -> SProp |}.

Class UR_Prop (P:Prop) (Q:SProp) {Ur: PR P Q} :=
  { 
    iff : P ↔ Q;
    pr_Coh : forall (p:P) (q:Q), p ≈ q
  }.

Arguments iff {_ _ _} _.
Arguments pr_Coh {_ _ _} _.

Infix "⋈P" := UR_Prop (at level 25).


(* some facilities to create an instance of UR_Type *)

#[universes(collapse_sort_variables=no)]
Definition UR_gen A : PR A A := {| pr := (path A) |}.

(*! Universe !*)

Instance PR_Type_def@{i j} : PR@{Type Type Type Type | j j j} Type@{i} Type@{i} :=
  Build_PR@{Type Type Type Type | j j j} _ _ PR@{Type Type Type Type |i i i}.


#[universes(collapse_sort_variables=no)]
Definition PR_inverse {A B} (ur: A ≈ B) : B ≈ A := {| pr := fun b a => pr a b |}.

(* This is the Black Box Property *)

Definition ur_refl {A B: Type} {pr: A ≈ B} (e : A ⋈ B) :forall a : A, a ≈ ↑ a.
Proof.
  destruct (Ur_Coh e) as [ur_coh]. 
  exact (fun a => (ur_coh a a) idpath).
Defined.  

#[export] Hint Extern 100 (_ ≈ _) => unshelve notypeclasses refine  (ur_refl _ _): typeclass_instances.

(*
Class URRefl@{i j k} A B (e : Equiv@{i j} A B) (H: PR@{Type Type Type Type;i j k} A B) := {
  ur_refl_ : forall a : A,  a ≈ ↑ a 
}.

Arguments ur_refl_ {_ _ _ _ _} _.


Definition URIsEq@{i j k} A B (e : A ≃ B) (H: PR@{Type Type Type Type;i j k} A B) (H:URRefl@{i j k} A B e H)
  :=  forall (a a':A), @IsEquiv (a = a') (a ≈ (↑ a'))
                                (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a)).

Existing Class URIsEq.
Typeclasses Transparent URIsEq.

Instance Ur_Coh_from_ur_refl A B (e:A ≃ B) (H:A ≈ B)
           (Hrefl : URRefl A B e H) : URIsEq A B e H Hrefl ->
                                      UR_Coh A B e H.
Proof.
  intros Hiseq. econstructor. intros a a'.
  exact (BuildEquiv _ _ (fun e => transport_eq (fun X => a ≈ (↑ X)) e (ur_refl_ a))
                     (Hiseq a a')).
Defined. 
*)

(* The definition of Ur_coh given in the paper is equivalent to *)
(* the definition given here, but technically, this one is more convenient to use *)

Definition alt_ur_coh {A B:Type} (e:A ≃ B) (H:A ≈ B) (HCoh : UR_Coh A B e H) (einv := Equiv_inverse e):
  forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b).
Proof.
  intros a b. cbn. 
  refine (transport_eq (fun X => (a ≈ X) ≃ (a = univalent_transport b))
                       (e_sect _ b) _). apply Equiv_inverse. 
  unshelve refine (ur_coh _ _). 
Defined.

Definition alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:A ≈ B) (einv := Equiv_inverse e)
           (HCoh : forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b)):
  UR_Coh A B e H.
Proof.
  refine (Build_UR_Coh _ _ _ _ _). intros a a'.
  apply Equiv_inverse. 
  refine (transport_eq (fun X => (a ≈ univalent_transport a') ≃ (a = X))
                       (e_sect _ a') _). 
  unshelve refine (HCoh _ _). 
Defined.


(* Definition of univalent relation for basic type constructors *)

(*! Forall !*)

#[export] Hint Extern 0 (?x ≈ ?y) => eassumption : typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition URForall_Type A A' {HA : A ≈ A'} :
  (A -> Type) ≈ (A' -> Type)
  :=
    {| pr := fun P Q => forall x y (H:x ≈ y), P x ≈ Q y |}.

#[universes(collapse_sort_variables=no)]
Definition URForall A A' (B : A -> Type) (B' : A' -> Type) {HA : A ≈ A'} 
           {HB: forall x y (H: x ≈ y), B x ≈ B' y} : PR (forall x, B x) (forall y, B' y)
  :=
  {| pr := fun f g => forall x y (H:x ≈ y), f x ≈ g y |}.

#[export] Hint Extern 0 (PR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall_Type A A' _); cbn in *; intros : typeclass_instances.

#[export] Hint Extern 1 (PR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

(* Definition ur_hprop A A' (H : A ⋈ A') (HA: forall x y:A, x = y) (x:A) (y:A')
  : x ≈ y. 
  intros. apply (alt_ur_coh _ _ _). apply HA. 
Defined. *)

(*
Definition UR_Type_equiv (A A' : Type) (eA : A ⋈ A') (eA': A ≃ A')
  (e  : equiv eA = eA') Coh:
  Ur_Coh eA = Some Coh ->
  eA =
  Build_UR_Type _ _ eA' (Ur eA)
                (Some (transport_eq (fun X => UR_Coh A A' X _) e Coh)). 
  destruct e, eA; cbn; inversion 1. reflexivity.
Defined. 
*)

(* Definition UR_Type_eq (A A' : Type) (eA eA': A ⋈ A')
           (equiv_eq  : equiv eA = equiv eA')
           (ur_eq  : Ur eA = Ur eA')
           (coh_eq  : transport_eq 
            (fun X => option (UR_Coh A A' _ X)) ur_eq 
            (transport_eq (fun X => option (UR_Coh A A' X _)) equiv_eq (Ur_Coh eA))
                      = Ur_Coh eA')
            (refl_eq : ur_refl_ eA = ur_refl_ eA')
  : eA = eA'. 
  destruct eA, eA'.
  cbn in *. rewrite <- coh_eq. destruct equiv_eq, ur_eq. cbn. 
  reflexivity.
Defined.                   *)

Definition  transport_Ur_Coh (A A': Type)
            (equiv : A ≃ A')
            (_pr _ur' : A -> A' -> Type)
            (ur_coh : forall a a' : A, (a = a') ≃ (_pr a (equiv a')))
            (e : _pr = _ur')
  :   transport_eq (fun X => UR_Coh A A' equiv {| pr := X |}) e
                   (Build_UR_Coh _ _ equiv {| pr := _pr |} ur_coh)
      =
      Build_UR_Coh _ _ equiv {| pr := _ur' |} (fun a a' => transport_eq (fun X =>
                                               (a = a') ≃ (X a (equiv a'))) e (ur_coh a a')).
  destruct e. reflexivity.
Defined.

Definition UR_Equiv_refl (A B:Type) (e:A ≃ B) (e_inv := Equiv_inverse e) `{A ≈ B} : B ≈ B :=
  {| pr := fun b b' => ↑ b ≈ b' |}.

(*! UR is symmetric on types !*)

Definition UR_Type_Inverse (A B : Type) (pr : A ≈ B) (pr' := PR_inverse pr): A ⋈ B -> B ⋈ A.
intro e. unshelve econstructor. 
- apply Equiv_inverse. typeclasses eauto. 
- econstructor.
  intros b b'. cbn. 
  eapply equiv_compose. apply isequiv_sym.
  eapply equiv_compose. apply (@isequiv_ap _ _ ( Equiv_inverse (equiv e))).
  eapply equiv_compose. apply ur_coh.
  cbn. unfold univalent_transport.
  refine (transport_eq (fun X => (_ ≈ X) ≃ _) (e_retr _ _)^ (Equiv_id _)).
Defined.

Definition compat_inverse (A A' B B':Type) (pA: A ≈ A') (pB: B ≈ B')
           (pA' := PR_inverse pA)
           (pB' := PR_inverse pB) (f : A -> B) (g : A' -> B') :
  f ≈ g -> g ≈ f.
  tc. 
Defined.

Definition compat_inverse2 {A A' B B' C C' :Type} {eA: A ≈ A'} (eA' := PR_inverse eA)
           {eB: B ≈ B'} (eB' := PR_inverse eB)
           {eC: C ≈ C'} (eC' := PR_inverse eC)
           {f : A -> B -> C} {g : A' -> B' -> C'} :
  f ≈ g -> g ≈ f.
  tc. 
Defined. 

(*! Canonical UR from a type equivalence !*)

Definition Canonical_PR (A B:Type) `{e : A ≃ B} (einv := Equiv_inverse e) : A ≈ B := ({| pr := fun a b => a = ↑ b |}).

Definition Canonical_UR (A B:Type) `{A ≃ B} (pr := Canonical_PR A B): A ⋈ B.
Proof.
  unshelve econstructor.
  - refine {| ur_coh := _ |}.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq (fun X => _ ≃ (a = X)) (e_sect' H _)^ _). apply Equiv_id.
Defined.      

(* alt_ur_coh is an equivalence UR_Coh A B e H ≃ forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b) *)

Instance is_equiv_alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:A ≈ B) : IsEquiv (alt_ur_coh e H). 
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intro. apply alt_ur_coh_inv. assumption.
  - intros [f]. apply (ap (Build_UR_Coh _ _ _ _)).
    apply funext. intro a. apply funext. intro a'. unfold alt_ur_coh, alt_ur_coh_inv.
    apply path_Equiv. apply funext. intro E.
    rewrite transport_inverse. rewrite <- transport_e_fun. cbn.
    unfold univalent_transport. rewrite transport_paths_r. cbn.
    change (Equiv_inverse (transport_eq (fun X : B => (a ≈ X) ≃ (a = e_inv e (e a'))) (e_retr e (e a')) (Equiv_inverse (f a (e_inv e (e a')))))
    (E @ (e_sect e a')^) = (f a a') E).
    rewrite transport_inverse'.
    rewrite Equiv_inverse_inverse. 
    rewrite e_adj. rewrite transport_ap. rewrite <- (transport_e_fun' _ _ (fun x => (a ≈ e x))). 
    rewrite (transport_fun_eq A a (fun x : A => (a ≈ e x)) (fun a' => e_fun (f a a'))).
    rewrite <- concat_p_pp. rewrite inv_inv. rewrite concat_refl. reflexivity.
  - intros f. apply funext. intro a. apply funext. intro a'.
    apply path_Equiv. apply funext. intro E. unfold alt_ur_coh, alt_ur_coh_inv. 
    cbn. rewrite Equiv_inverse_inverse.
    rewrite other_adj. rewrite transport_ap. unfold univalent_transport.
    rewrite (transport_double _ (fun X X' => (a ≈ X) ≃ (a = e_inv e X'))).
    reflexivity. 
Defined.

Definition ur_coh_equiv {A B:Type} (e:A ≃ B) (H:A ≈ B) (einv := Equiv_inverse e):
  UR_Coh A B e H ≃ forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b)
  := BuildEquiv _ _ (alt_ur_coh e H) _.


(* transport and path lemmas on UR_Type *)

(* 
Definition transport_UR_Type A B C (e: B = C) e1 e2 e3 :
  transport_eq (fun X : Type => A ⋈ X)
               e (Build_UR_Type A B e1 e2 e3) =
  Build_UR_Type A C (e # e1) (e#e2) (transportD2 _ _ (fun a b c => option (@UR_Coh A a b c)) e _ _ e3)
  :=
  match e with idpath => idpath end.
*)
  (*
 Definition transport_UR_Type' A B C (e: A = C) e1:
  transport_eq (fun X : Type => X ⋈ B)
               e (Build_UR_Type A B e1) =
  Build_UR_Type C B (e # e1) 
  :=
  match e with idpath => idpath end. *)

(* Definition path_UR_Type A B (X Y:UR_Type A B) (e1:X.(equiv) = Y.(equiv))
           (e2 : X.(Ur) = Y.(Ur))
           (e3 : forall a a',
               e_fun (@ur_coh _ _ _ _ (transport_eq (fun X => UR_Coh A B X _ ) e1
                                   (transport_eq (fun X => UR_Coh A B _ X ) e2 X.(Ur_Coh))) a a') =
               e_fun (@ur_coh _ _ _ _ Y.(Ur_Coh) a a'))
           (e4 : X.(Ur_Can_A) = Y.(Ur_Can_A))
           (e5 : X.(Ur_Can_B) = Y.(Ur_Can_B))
                               : X = Y. 
Proof.
  destruct X, Y. cbn in *. 
  destruct e1, e2, e4, e5. cbn.
  destruct Ur_Coh0, Ur_Coh1. 
  assert (ur_coh0 = ur_coh1).
  apply funext. intro a.
  apply funext. intro a'.
  apply path_Equiv. apply e3. destruct X. reflexivity. 
Defined. 
*)

Definition transport_UR A B C (e: B = C) e1 :
  transport_eq (fun X : Type => PR A X)
               e (Build_PR A B e1) =
  Build_PR A C (fun a x => e1 a ((eq_to_equiv _ _ e^).(e_fun) x))
  :=  match e with idpath => idpath end.

Definition transport_UR' A B C (e: A = C) e1 :
  transport_eq (fun X : Type => PR X B)
               e (Build_PR A B e1) =
  Build_PR C B (fun x b => e1 ((eq_to_equiv _ _ e^).(e_fun) x) b)
  :=  match e with idpath => idpath end.

Definition path_UR A B (X Y: PR A B) : (forall a b, @pr _ _ X a b = @pr _ _ Y a b) -> X = Y.
  intros e. pose ((funext _ _ _ _).(@e_inv _ _ _) (fun a => (funext _ _ _ _).(@e_inv _ _ _) (e a))).
  destruct X, Y. cbn in *. 
  destruct p. reflexivity. 
Defined.

(* some generic ways of getting UR instances *)

Definition UR_Equiv (A B C:Type) `{C ≃ B} (eAB:A ≈ B) : A ≈ C :=
  {| pr := fun a b => a ≈ ↑ b |}.

Definition UR_Equiv' (A B C:Type) `{C ≃ A} (eAB :A ≈ B) : C ≈ B :=
  {| pr := fun c b => ↑ c ≈  b |}.

Definition UR_Type_Equiv (A B C:Type) `{C ≃ B} {eAB : A ≈ B} `{A ⋈ B} (ur := UR_Equiv _ _ _ eAB): A ⋈ C.
Proof.
  cbn in *. unshelve econstructor.
  - apply (equiv_compose (equiv H0)). apply Equiv_inverse. exact H.
  - econstructor.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq (fun X => _ ≃ (a ≈ X)) (e_retr' H _)^ _). apply ur_coh.
Defined.     

Definition UR_Type_Equiv' (A B C:Type) `{C ≃ A} {eAB : A ≈ B} `{A ⋈ B} (ur := UR_Equiv' _ _ _ eAB) : C ⋈ B.
Proof.
    unshelve econstructor.
  - apply (equiv_compose H (equiv H0)).
  - econstructor. intros. cbn.
    unfold univalent_transport.
    pose (X:= isequiv_ap C A a a'). 
    eapply equiv_compose. apply X.
    apply ur_coh.
Defined. 

Definition UR_Equiv_gen (X:Type) (eX : X ≈ X) (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈ y) (H:A x ≈ A y)
  : B x ≈ B y.
Proof.
  unshelve refine (UR_Equiv _ _ _ _).
  unshelve refine (UR_Equiv' _ _ _ _).
  auto. 
Defined.

Definition UR_Type_Equiv_gen (X:Type) (eX : X ≈ X) (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈ y) (H:A x ≈ A y)
  (H':A x ⋈ A y)
  (ur := UR_Equiv_gen X eX A B HAB x y e H)
  : B x ⋈ B y.
Proof.
  unshelve refine (UR_Type_Equiv _ _ _).
  unshelve refine (UR_Type_Equiv' _ _ _).
Defined.  

