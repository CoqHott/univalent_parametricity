(************************************************************************)
(* This file proves the fundamental property for the main constructors of CIC *)
(************************************************************************)

Set Polymorphic Inductive Cumulativity. 

Set Universe Polymorphism.

Unset Universe Minimization ToSet.

Require Import HoTT CanonicalEq URTactics.
Require Export UnivalentParametricity.theories.UR.
Require Import UnivalentParametricity.theories.Transportable.

(*! Establishing FP for Type !*)

(* Definition UR_is_eq_equiv (A B:Type) (e:A ⋈ B) (a:A) (b:B) : (a = e_inv (e_fun (equiv e)) b) ≃ (a ≈ b).
Proof.
  eapply equiv_compose; try refine (ur_coh a _).
  refine (transport_eq (fun X =>  (a ≈ X) ≃ _) (e_retr _ b)^ (Equiv_id _)). 
Defined.  *)

Definition URType_Refl_can A : A ≈u A.
Proof.
  unshelve eexists.
  - apply UR_gen.
  - apply Equiv_id.
  - econstructor. intros; split; eauto.
Defined.

(* Definition URType_Refl : URRefl Type Type (Equiv_id _) _.
Proof.
  constructor; intro A.
  apply URType_Refl_can.
  (* apply Canonical_eq_gen. *)
Defined. *)

(* this requires univalence *)
(* Instance URType_IsEq : URIsEq Type Type (Equiv_id _) _ URType_Refl.
Proof.
  intros A B. 
  simpl.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply univalence. typeclasses eauto.
  - intros e; cbn.
    destruct e. simpl.
    exact (@e_sect _ _ _ (univalence _ _) idpath).
  - intro e; cbn.
    destruct e as [e eur ecoh ecanA ecanB].
    revert eur ecoh ecanA ecanB. rewrite <- (@e_retr _ _ _ (univalence _ _) _).
    set (eeq := (e_inv _ e)).
    clearbody eeq;clear e.
    destruct eeq. intros eur ecoh ecanA ecanB.
    simpl.
    destruct eur as [eur].
    destruct ecoh as [ecoh].
    simpl in *.
    change (Equiv_id A) with (eq_to_equiv A A idpath).
    rewrite (@e_sect _ _ _ (univalence _ _) _). simpl.
    unfold UR_gen.
    rewrite <- (@e_retr _ _ (e_fun (equiv_relation_equiv_fun _ _ _ _)) _ ecoh).
    set (p := (e_inv _ ecoh)).
    clearbody p. clear ecoh.
    destruct p.
    assert (ecanA = Canonical_eq_gen A) by apply Canonical_contr.
    assert (ecanB = Canonical_eq_gen A) by apply Canonical_contr.
    destruct X, X0. 
    reflexivity.
Defined. *)

Instance Canonical_eq_Type : Canonical_eq Type := Canonical_eq_gen _.

(* We avoid the use of univalence and use `None` for the coherence condition *) 

Definition FP_Type : Type ≈p Type := {| pr := UR_Type |}.

#[export] Hint Extern 0 (PR Set Set) => exact FP_Type : typeclass_instances. 

(* Axiom SPropProp : path@{_ Type; _} Type Prop SProp.*)

(* #[export] Hint Extern 0 (sigT _) => unshelve refine (existT _ _ _): typeclass_instances. *)

(*! FP for Dependent product !*)

(* isequiv_functor_forall can be found in
[https://github.com/HoTT/HoTT] *)

#[universes(collapse_sort_variables=no)]
Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (g : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun H b => g b (H (f b)).
  
Instance isequiv_functor_forall {A B} {P : A -> Type} {Q : B -> Type} (* (eP : Transportable P) *)
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - refine (functor_forall (e_inv f) _).
    intros a y.
    generalize (e_inv (g _) y). clear y.
    (* exact (transportable _ _ ((e_retr f a))). *)
    exact (fun t => transport_eq P (e_retr f a) t).
  - intros h. apply funext. intro a. unfold functor_forall.
    destruct (e_retr f a). (* rewrite transportable_refl. *) apply e_sect. 
  - intros h;apply funext. unfold functor_forall. intros b.
    rewrite e_adj. rewrite transport_ap.
    rewrite <- (@e_retr _ _ (g b) (H b) (h b)).
    apply ap. set (e_sect f b).
    set (e_inv f (f b)) in *. destruct p. cbn. reflexivity.
Defined.

Instance isequiv_functor_forall_ur {A B : Type} `{P : A -> Type} `{Q : B -> Type} (e : B ≈u A) 
  (e' :  forall x y (H:x ≈u y), Q x ≈u P y) 
: IsEquiv (functor_forall (equiv e)
                          (fun x => 
                    (e_inv' ((equiv (e' x (equiv e x) (ur_refl e x))))))). 
Proof.
  apply isequiv_functor_forall.
  - apply (equiv e).
  - intros b. unfold e_inv'.
    apply isequiv_inverse.
Defined.

Instance Equiv_forall (A A' : Type) (eA : A ≈u A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈u B') 
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  pose (e := UR_Type_Inverse _ _ eA). 
  pose (e' := fun x y E => UR_Type_Inverse _ _ (eB x y E)).
  assert (eB' : forall (x:A') (y:A) (H:@pr _ _ _ (Ur e) x y) , B' x ≈u B y). 
  { intros. exact (e' y x H). }
  unshelve refine
           (BuildEquiv _ _ (functor_forall (e_fun (equiv e))
                                           (fun x => (e_inv' ((equiv (eB' x (e_fun (equiv e) x) (ur_refl e x)))))))
                       _). 
Defined.

Definition FP_forall_ur_type (A A' : Type) (eA : A ≈u A') (B : A -> Type) (B' : A' -> Type) 
     (eB : B ≈u B') :
  (forall x : A, B x) ≈u (forall x : A', B' x).
  unshelve econstructor.
  - econstructor. intros f g. split; cbn. 
    + intros efg x y e. destruct efg. 
      destruct (Ur_Coh (eB _ y (ur_refl (UR_Type_Inverse A A' eA) y))) as [ur_coh].
      cbn in ur_coh.
      pose proof (fst (ur_coh (f _) (f _)) idpath).
      unfold univalent_transport in H.
      pose proof (snd (alt_ur_coh eA _ _) e).
      cbn in H0. destruct H0^. exact H.
    + intros e. apply funext. intros x. 
      destruct (Ur_Coh eA) as [ur_coh].  
      pose proof (fst (ur_coh x _) idpath).
      specialize (e _ _ H). unfold univalent_transport in *.
      destruct (Ur_Coh (eB _ _ H)) as [ur_cohB].
      eapply (snd (ur_cohB _ _)). clear ur_cohB. unfold univalent_transport. 
      pose proof (e_sect (equiv eA) x). 
      set (ur_refl (UR_Type_Inverse A A' eA)
            (equiv eA x)) in *. cbn in p. clearbody p.
      set (e_inv (equiv eA) (equiv eA x)) in *.
      clearbody a. destruct H0. exact e.
Defined.

Definition FP_forall_pr_type (A A' : Type) (eA : A ≈p A') (B : A -> Type) (B' : A' -> Type) 
     (eB : B ≈p B') :
  (forall x : A, B x) ≈p (forall x : A', B' x).
Proof. cbn. tc. Defined.

#[universes(collapse_sort_variables=no)]
Definition FP_forall_plain :
          (fun A B => forall x:A , B x) ≈p (fun A' B' => forall x:A', B' x).
Proof.
  cbn. tc.
Defined.

#[universes(collapse_sort_variables=no)]
Definition FP_forall_ur :
            (fun A B => forall x:A , B x) ≈u (fun A' B' => forall x:A', B' x).
Proof.
  intros A A' eA B B' eB. eapply FP_forall_ur_type; eauto.
Defined. 

#[universes(collapse_sort_variables=no)]
Definition FP_forall k :
          pr k (fun A B => forall x:A , B x) (fun A' B' => forall x:A', B' x).
Proof.
  destruct k.
  - apply FP_forall_plain.
  - eapply FP_forall_ur.
Defined.  

(* #[export] Hint Extern 0 (UR_Type (forall x:_ , _) (forall y:_, _)) => erefine (ur_type (FP_forall _ _ _) _ _ {| ur_type := _|}); cbn in *; intros : typeclass_instances.

#[export] Hint Extern 100 ((forall x:_ , _) ≃ (forall y:_, _)) => erefine (Equiv_forall _ _ _ _ _ {| ur_type := _|}); cbn in *; intros : typeclass_instances. *)

#[export] Hint Unfold pr : core. 
Typeclasses Transparent pr.
#[export] Hint Transparent pr : core. 

(* #[export] Hint Extern 0 (UR_Type (_ -> _) (_ -> _)) =>
  erefine ((FP_forall _ _ _) _ _ {| ur_type := _|} ); cbn in *; intros : typeclass_instances. *)

#[universes(collapse_sort_variables=no)]
Definition FP_forall_plain_Prop :
            (fun A (B:A->Prop) => forall x:A , B x) ≈p (fun A' (B':A'->SProp) => forall x:A', B' x).
Proof. 
  cbn. tc.
Defined. 


#[universes(collapse_sort_variables=no)]
Definition FP_forall_univ_Prop :
            (fun A (B:A->Prop) => forall x:A , B x) ≈u (fun A' (B':A'->SProp) => forall x:A', B' x).
Proof.
  intros A A' eA B B' eB.
  unshelve econstructor.
  - unfold pr in eB. tc.
  - split; intros.
    + destruct (Ur_Coh (UR_Type_Inverse _ _ eA)) as [ur_coh].
      pose proof (fst (ur_coh x x) idpath). 
      destruct (eB _ _ H0).
      eapply (fst equiv_P). eapply H.
    + destruct (Ur_Coh eA) as [ur_coh].
      pose proof (fst (ur_coh x x) idpath). 
      destruct (eB _ _ H0).
      apply (snd equiv_P). eapply H.
  - cbn; intros. destruct (eB _ _ H). eapply pr_Coh.  
Defined. 

Hint Extern 0 (UR_Prop (forall x:_ , _) (forall y:_, _)) => unshelve eapply FP_forall_univ_Prop; cbn; intros : typeclass_instances.

(* special cases for arrows *)

(* Definition Equiv_Arrow (A A' B B': Type)
           (eA: A ≈ A') (e' : B ≈ B') :
  (A -> B) ≃ (A' -> B') := Equiv_forall _ _ eA _ _ (fun _ => e').

#[export] Hint Extern 0 ((_ -> _) ≃ (_ -> _)) =>
  erefine (Equiv_Arrow _ _ _ _ _ _); cbn in *; intros : typeclass_instances. *)

(*
Instance Transportable_Arrow A (P Q: A -> Type)
         (HP_can : forall x, Canonical_eq (P x))
         (HQ_can : forall x, Canonical_eq (Q x))
         (HP : Transportable P) (HQ : Transportable Q) : Transportable (fun a => P a -> Q a).
Proof.
  unshelve econstructor. intros x y e. pose (inverse e).
  eapply Equiv_Arrow.
  { unshelve eexists.
    - apply transportable; auto. 
    - destruct e. apply UR_gen.
    - constructor. destruct e. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
    - auto.
    - auto.
  }
  { unshelve eexists.
    - apply transportable; auto.     
    - destruct e. apply UR_gen.
    - constructor. destruct e. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
    - auto.
    - auto.
  }
  intro a; cbn.
  unshelve refine (path_Equiv _).
  apply funext; intro f. apply funext; intro b. cbn.
  rewrite (@transportable_refl _ _ HQ a). cbn. apply ap.
  exact (apD10 (ap e_fun (ap Equiv_inverse (@transportable_refl _ _ HP a))) b).
Defined.
*)
