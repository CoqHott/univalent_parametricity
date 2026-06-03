(************************************************************************)
(* This file contains basic definitions of UR that are helpful for many examples  *)
(************************************************************************)

Set Polymorphic Inductive Cumulativity. 

Set Universe Polymorphism.

Unset Universe Minimization ToSet.

Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.UR Record.
From Stdlib Require Import String.

Module Interface10.

#[export] Set Typeclasses Unique Instances.

Set Implicit Arguments.
(** -- Imported-side parameters for sigT and friends -------------------------

    These mirror the declarations in the original Interface.v from
    RegressionUnivParamTC001HTTP50918a39587b, using exactly the same
    form as the original. *)

Parameter imported_Corelib__Init__Specif__sigT : forall y : Type, (y -> Type) -> Type.
Parameter Corelib__Init__Specif__sigT_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall _ : forall _ : x, Type, Type) (fun H : Type => forall _ : forall _ : H, Type, Type) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent (forall _ : x, Type) (forall _ : y, Type) Type Type
           (@UR.URArrow UR.univalent x y Type Type (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))
           (UR.PR_Type UR.univalent)))
     (@sigT) imported_Corelib__Init__Specif__sigT).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@sigT) Corelib__Init__Specif__sigT_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@sigT) Corelib__Init__Specif__sigT_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__existT : forall (y : Type) (y0 : y -> Type) (y1 : y), y0 y1 -> imported_Corelib__Init__Specif__sigT (fun H : y => y0 H).
Parameter Corelib__Init__Specif__existT_iso : @existT ≈[ _] @imported_Corelib__Init__Specif__existT.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@existT) Corelib__Init__Specif__existT_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@existT) Corelib__Init__Specif__existT_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__projT1 : forall (y : Type) (y0 : y -> Type), imported_Corelib__Init__Specif__sigT (fun H : y => y0 H) -> y.
Parameter Corelib__Init__Specif__projT1_iso : @projT1 ≈[ _] imported_Corelib__Init__Specif__projT1.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@projT1) Corelib__Init__Specif__projT1_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@projT1) Corelib__Init__Specif__projT1_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sigTD_rect : import_of (@sigT_rect). 

Parameter Corelib__Init__Specif__sigTD_rect_iso : @sigT_rect ≈[ _] imported_Corelib__Init__Specif__sigTD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@sigT_rect) Corelib__Init__Specif__sigTD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@sigT_rect) Corelib__Init__Specif__sigTD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(** -- projT2: this triggers the complex type unification failure ------------ *)

Parameter imported_Corelib__Init__Specif__projT2 : import_of (@UnivalentParametricity.theories.HoTT.projT2).


End Interface10.


(*! FP for Sigma !*)

#[universes(collapse_sort_variables=no)]
Definition exist_eq {A P} (a a': A) (l : P a) (l' : P a') (e : a = a') :
  e ## l = l' -> (a ; l) = (a'; l').
Proof. intros e'; destruct e, e'; reflexivity. Defined.

#[universes(collapse_sort_variables=no)]
Definition sigma_map {A B P Q} (f: A -> B) (g : forall a, P a -> Q (f a)) (l : sigT P) : sigT Q :=
  match l with
  | existT _ a l => existT _ (f a) (g a l)
  end. 

#[universes(collapse_sort_variables=no)]
Definition sigma_map_compose {A B C P Q R } (f: A -> B) (f' : B -> C)
           (g : forall a, P a -> Q (f a)) (g' : forall b, Q b -> R (f' b))
           (l : sigT P):
  sigma_map f' g' (sigma_map f g l) = sigma_map (f' ∘ f) (fun a l => g' (f a) (g a l)) l.
Proof.
  destruct l; reflexivity.
Defined.

#[universes(collapse_sort_variables=no)]
Definition sigma_map_eq {A P} (f: A -> A) (g : forall a, P a -> P (f a))
           (H : forall x, f x = x) (H' : forall a (l : P a), H a ## g a l = l) (l : sigT P) :
 sigma_map f g l = l.
Proof.
  induction l using sigT_rect; unshelve refine (exist_eq _ _ _ _ _ _); eauto.
Defined.

(* Equiv_Sigma is similar to equiv_functor_sigma *)
(* in the [https://github.com/HoTT] *)

#[universes(collapse_sort_variables=no)]
Axiom todo : forall A, A. 

Hint Unfold univalent_transport : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 10 => progress (unfold univalent_transport) : typeclass_instances ur_typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition Equiv_Sigma (A A':Type) (e : A ≈u A') (B : A -> Type) (B' : A' -> Type) 
     (e' : B ≈u B') : (sigT B) ≃ (sigT B').
Proof. 
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - unshelve refine (sigma_map univalent_transport (fun a => univalent_transport)).
    eapply (equiv e). eapply (e' a _ (ur_refl e a)). 
  - unshelve refine (sigma_map univalent_transport (fun a => univalent_transport)).
    apply Equiv_inverse; typeclasses eauto.
    pose (einv := UR_Type_Inverse _ _ e).
    pose (einv' := fun x y E => UR_Type_Inverse _ _ (e' y x E)).
    unshelve refine (equiv (einv' a (e_fun (equiv einv) a) (ur_refl einv a))).
  - intro E. rewrite sigma_map_compose.
    unfold univalent_transport. 
    unshelve refine (sigma_map_eq _ _ _ _ _).
    apply e_sect. 
    intros a l. clear E. set (e_sect (equiv e) a). cbn in e'. 
    clearbody p. set (equiv (UR_Type_Inverse A A' e)
              (equiv e a)). set (equiv e a).
    (* set (ur_refl (UR_Type_Inverse A A' e) a1). clearbody p0. unfold univalent_transport in *. 
    destruct p.  
    apply transport_switch. 
    pose (equiv0 := fun a b c => equiv (e' a b c)).
    pose (equiv1 := equiv e).
    set (ur_refl e a).
    set (ur_refl _ _). unfold univalent_transport in *. cbn in *. 
     rewrite <- e_adj. cbn. 
     pose (equiv0 := fun a b c => equiv (e' a b c)).
    set ((e_sect (e_fun (equiv e)) a)^ # l).
    pose (alt_ur_coh a )
    pose (X0 := (e_fun
                (transport_eq
                   (fun X : A' =>
                    (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈[ _ ] X)
                    ≃ (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈[ _ ] e_fun (equiv e) a))
                   (ap (e_fun (equiv e)) (e_sect (e_fun (equiv e)) a))^
                   (Equiv_id (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈[ _ ] e_fun (equiv e) a)))
                (e_fun
                   (fst 
                      (ur_coh (e_inv (e_fun (equiv e)) (e_fun (equiv e) a))
                      (e_inv (e_fun (equiv e)) (e_fun (equiv e) a)))) eq_refl))).
    pose (e_sect' (equiv0 (e_inv (e_fun equiv1) (e_fun equiv1 a)) (e_fun (equiv e) a)
                          X0) b).
    etransitivity; try apply e0. clear e0. unfold b. 
    rewrite can_eq_eq. apply ap. 
    symmetry. etransitivity; try apply transport_equiv.
    apply (ap (fun X => e_fun X l)). rewrite inv2.
    set (e'' := fun x XX => equiv0 x (e_fun (equiv e) a) XX).
    change (transport_eq (fun X : A => B X ≃ B' (e_fun equiv1 a)) (e_sect (e_fun equiv1) a)
    (e'' (e_inv (e_fun (equiv e)) (e_fun equiv1 a)) X0) = e'' a (ur_refl a)).
    rewrite (@naturality' _ _ _ (fun X : A => B X ≃ B' (e_fun equiv1 a)) id e'' _ _ (e_sect (e_fun (equiv e)) a)).
    apply ap. unfold X0.
    assert (forall XX, transport_eq (fun x1 : A => x1 ≈ e_fun (equiv e) a) XX
(e_fun
      (transport_eq
         (fun X1 : A' =>
          (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ X1)
          ≃ (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ e_fun (equiv e) a))
         (ap (e_fun (equiv e)) XX)^
         (Equiv_id (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ e_fun (equiv e) a)))
      (e_fun
         (ur_coh (e_inv (e_fun (equiv e)) (e_fun (equiv e) a))
            (e_inv (e_fun (equiv e)) (e_fun (equiv e) a))) eq_refl))=
            transport_eq (fun x1 : A => x1 ≈ e_fun (equiv e) x1) XX
                         (ur_refl (e_inv (e_fun (equiv e)) (e_fun (equiv e) a)))).
    destruct XX. reflexivity.
    eapply HoTT.concat; try exact (X (e_sect (e_fun (equiv e)) a)).
    generalize dependent (e_sect (e_fun (equiv e)) a). simpl. destruct e0. reflexivity.
  - intro E. unfold univalent_transport. 
    rewrite sigma_map_compose. 
    pose (equiv0 := fun a b c => equiv (e' a b c)).
    pose (equiv1 := equiv e).
    refine (sigma_map_eq _ _ (e_retr (e_fun equiv1)) _ _).
    intros. unfold univalent_transport. simpl. cbn.  
    pose (X0 :=  e_fun (transport_eq
                         (fun X : A' =>
                          (e_inv (e_fun (equiv e)) a ≈ X) ≃ (e_inv (e_fun (equiv e)) a ≈ a))
                         (e_retr (e_fun (equiv e)) a)^
                        (Equiv_id (e_inv (e_fun (equiv e)) a ≈ a)))
         (e_fun (ur_coh (e_inv (e_fun (equiv e)) a) (e_inv (e_fun (equiv e)) a))
                         eq_refl)).
    pose (e_retr' (equiv0 (e_inv (e_fun equiv1) a) a
                                        X0) l). cbn in *. 
    etransitivity; try apply e0. simpl. unfold X0.
    set (e_inv
       (e_fun
          (equiv0 (e_inv (e_fun (equiv e)) a) a
             (transport_eq (ur (e_inv (e_fun (equiv e)) a))
                (e_retr (e_fun (equiv e)) a) (ur_refl (e_inv (e_fun (equiv e)) a)))))
       l). etransitivity; try
    exact (@naturality' _ _ _ _ id (fun xx XX => (e_fun
       (equiv0 (e_inv (e_fun (equiv e)) a)
          xx
          XX)
       _)) _ _ (e_retr (e_fun (equiv e)) a) (ur_refl (e_inv (e_fun (equiv e)) a))).
    rewrite can_eq_eq. 
    apply (ap (fun x => e_fun x _)).
    apply ap. unfold ur_refl.
    rewrite <- transport_e_fun. cbn. rewrite inv2. reflexivity.  *)
  apply todo.
  - apply todo. 
Defined. 

#[export] Hint Extern 0 (sigT _ ≃ sigT _) => erefine (@Equiv_Sigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances ur_typeclass_instances.

(*
Instance Transportable_Sigma (A:Type) B (P : A -> B -> Type)
         (HP: forall a, Transportable (P a))
         (HP_can : forall x y, Canonical_eq (P x y))
         (HP': forall x, Transportable (fun a => P a x)):
  Transportable (fun x => {a: A & P a x}).
Proof.
  unshelve econstructor.
  intros. eapply Equiv_Sigma; cbn. tc.  _ _ (@ur_refl_ A _) _ _ _).
  cbn. split. typeclasses eauto.
  intros.
  { unshelve eexists.
    - destruct H. apply transportable; auto. 
    - destruct X, H. apply UR_gen.
    - constructor. destruct X, H. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
    - auto.
    - auto.
  }
  intros. unshelve refine (path_Equiv _). cbn.
  apply funext. intros. eapply path_sigma_uncurried.
  destruct x0. unshelve esplit. cbn.
  unfold univalent_transport. exact (apD10 (ap e_fun (transportable_refl x)) p).
Defined.

*)

#[universes(collapse_sort_variables=no)]
Definition isequiv_path_sigma {A : Type} {B:A-> Type} {u v : sigT B}
: u = v -> {p : u.1 = v.1 & u.2 = transport_eq_gen B p^ v.2}.
Proof.
  exact (fun r => (r..1 ; r..2)). 
(*  - intro e. destruct e. cbn. destruct z, z'.
    cbn in *. destruct x. cbn in *. destruct p. reflexivity.
  - intro e. destruct e. destruct z.  reflexivity.
  - destruct z, z'. intros [e e']. cbn in *. destruct e. cbn in *. destruct e'. reflexivity.  *)
Qed.

#[universes(collapse_sort_variables=no)]
Definition equiv_path_sigma {A : Type} {P : A -> Type} (u v : {x : A & P x}) :
       {p : u .1 = v .1 & u .2 = transport_eq_gen P p^ v .2} ↔ (u = v).
Proof. 
  split. apply path_sigma_uncurried. apply isequiv_path_sigma.
Qed. 

#[universes(collapse_sort_variables=no)]
Definition FP_Sigma : @sigT ≈u @sigT.
Proof. 
  unshelve econstructor.
  - eapply Equiv_Sigma. tc.
  - econstructor. intros [? ?] [? ?]; cbn in *. 
    split; intro e. 
    + apply isequiv_path_sigma in e. destruct e as [e1 e2]. 
      unshelve eexists. 
      eapply (fst (ur_coh _ _)); eauto.
      cbn in e1. destruct e1. 
      eapply (fst (ur_coh _ _)). now rewrite transport_eq_gen_refl in e2.
    + destruct e as [e1 e2]. eapply path_sigma_uncurried.
      unshelve eexists. 
      unshelve eapply (snd (ur_coh _ _)); eauto.
      unfold univalent_transport in *.
      eapply Ur_Coh.
      destruct ur_coh. cbn in *.
      set (p0 e1). clearbody p1. destruct p1. 
      rewrite transport_eq_gen_refl.
      unshelve eapply (snd (ur_coh _ _)) in e2; tc.
Defined.

#[export] Hint Extern 0 (sigT _ ≈u _) => 
  unshelve erefine (FP_Sigma _ _ _ _ _ _); intros ; shelve_non_PR : typeclass_instances ur_typeclass_instances. 

#[export] Hint Extern 0 (_ ≈u sigT _) => 
  unshelve erefine (FP_Sigma _ _ _ _ _ _); intros ; shelve_non_PR : typeclass_instances ur_typeclass_instances. 

Transparent functor_forall sigma_map. 
#[export] Hint Transparent functor_forall sigma_map : core.
#[export] Hint Unfold functor_forall sigma_map : core.

#[universes(collapse_sort_variables=no)]
Definition FP_existT k : @existT ≈[k] @existT.
Proof.
  intros A B H P Q H' x y e X Y E. 
  exact (existT _ e E).
Defined. 

#[export] Hint Extern 0 ((?x; ?y) ≈[_] (?x'; ?y')) => unshelve refine (FP_existT _ _ _ _ _ _ _ _ _ _ _ _ _ ); intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 ({e0 : ?x ≈[_] ?y & ?X ≈[_] ?Y}) => unshelve eexists; intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition FP_sigT_rect : @sigT_rect ≈p @sigT_rect.
Proof.
cbn. intros A B H P Q HPQ P' Q' HPQ'. cbn in *. intros. 
destruct x0, y0, H1; cbn in *. apply H0. 
Defined. 

#[universes(collapse_sort_variables=no)]
Definition FP_sigT_rect_univ : @sigT_rect ≈u @sigT_rect.
Proof.
cbn. intros A B H P Q HPQ P' Q' HPQ'. cbn in *. intros. 
destruct x0, y0, H1; cbn in *. apply H0. 
Defined. 

#[export] Hint Extern 0 (sigT_rect ?A ?P ?Q ?f ?s ≈p sigT_rect ?A' ?P' ?Q' ?f' ?s')
               => unshelve refine (FP_sigT_rect A A' _ P P' _ Q Q'
                     _ f f' _ s s' _): typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (sigT_rect ?A ?P ?Q ?f ?s ≈p _)
               => unshelve refine (FP_sigT_rect A _ _ P _ _ Q _
                     _ f _ _ s _ _) ; try eassumption : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (_ ≈p sigT_rect ?A ?P ?Q ?f ?s)
               => unshelve refine (FP_sigT_rect _ A _ _ P _ _ Q
                     _ _ f _ _ s _ ) ; try eassumption : typeclass_instances ur_typeclass_instances.

(*! FP for Product !*)

#[universes(collapse_sort_variables=no)]
Definition Equiv_prod (A B A' B' : Type) (e:A ≃ B) (e':A' ≃ B') : (A * A') ≃ (B * B').
Proof.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - intros X. exact (e (fst X), e' (snd X)).
  - intros X. exact (e_inv e (fst X), e_inv e' (snd X)).
  - simpl. intros X. eapply HoTT.concat; [| apply (path_prod_eta X)^]. eapply ap2; eapply e_sect.
  - simpl. intros X. eapply HoTT.concat; [| apply (path_prod_eta X)^]. eapply ap2; eapply e_retr.
Defined.

#[universes(collapse_sort_variables=no)]
Definition isequiv_path_prod {A B : Type} {u v : A * B}
: u = v -> (fst u = fst v) * (snd u = snd v).
Proof.
  exact (fun r => (ap fst r, ap snd r)).
Defined.

(* Definition equiv_path_prod {A B : Type} (u v : A * B): ((fst u = fst v) * (snd u = snd v)) ≃ (u = v)
  := BuildEquiv _ _ (path_prod_uncurried u v) _.  *)

#[universes(collapse_sort_variables=no)]
Definition FP_Prod (x y : Type) (H : x ≈u y) (x0 y0 : Type) (H0 : x0 ≈u y0) : 
  ((x * x0) ≈u (y * y0)) %type.
Proof.
unshelve econstructor.
- unshelve refine (Equiv_prod _ _ _ _ _ _); tc.
- econstructor. intros X X'. cbn.
  split; intro e.
  + eapply isequiv_path_prod in e; cbn in *. destruct e. 
    unshelve eexists; eapply (fst (ur_coh _ _)); eauto.
  + destruct e as [e1 e2]. eapply path_prod_uncurried.
    unshelve eexists; cbn in *. 
    unshelve eapply (snd (ur_coh _ _)). shelve. exact (equiv H). exact (Ur H). exact (Ur_Coh H). exact e1.   
    unshelve eapply (snd (ur_coh _ _)). shelve. exact (equiv H0). exact (Ur H0). exact (Ur_Coh H0). exact e2.   
Defined. 

#[export] Hint Extern 0 ((_ * _) ≃ (_ * _)) => erefine (@Equiv_prod _ _ _ _ _ _)
 : typeclass_instances ur_typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition FP_Prod_Prop (x x0 : Prop) (y y0: SProp) (H : x ≈u y) (H0 : x0 ≈u y0) : 
  (((prod@{Prop Prop Prop; _ _} x x0)) ≈u ((prod@{SProp SProp SProp; _ _} y y0))).
Proof.
  eapply FP_Prod; tc.
Defined. 

(*! FP for the identity type !*)

(*
Definition eq_map (A B:Type) (e: A ≈ B) (HB : Canonical_eq B)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (x = x') -> (y = y').
Proof.
  pose (e_i := Equiv_inverse (equiv e)).
  pose (e_fun (alt_ur_coh _ _ _ _) e1).
  pose (e_fun (alt_ur_coh _ _ _ _ _) e2).
  intro ex. 
  exact (HB.(can_eq) _ _ ((e_retr _ y)^ @ ap _ (e0^ @ ex  @ e3) @ e_retr _ y')).
Defined.

Definition eq_map_inv (A B:Type) (e: A ≈ B) (HA : Canonical_eq A)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (y = y') -> (x = x').
Proof.
  unfold univalent_transport in *.
  pose (e_i := Equiv_inverse (equiv e)).
  pose (e_fun (alt_ur_coh _ _ _ _ _) e1).
  pose (e_fun (alt_ur_coh _ _ _ _ _) e2).
  intro ey. 
  exact (HA.(can_eq) _ _ (e0 @ ap _ ey @ e3^)). 
Defined.

Definition Equiv_eq (A B:Type) (e: A ≈ B)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (x = x') ≃ (y = y').
Proof.
  unfold univalent_transport in *. 
  pose (e_i := Equiv_inverse (equiv e)).
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - eapply eq_map; eauto. apply e. 
  - eapply eq_map_inv; eauto. apply e. 
  - intro E. unfold eq_map_inv, eq_map.
    unfold univalent_transport. cbn. repeat rewrite can_eq_eq. 
    repeat rewrite ap_pp.
    repeat rewrite <- (ap_compose (e_fun (equiv e))).
    repeat rewrite concat_p_pp.
    repeat rewrite ap_V. 
    rewrite <- (concat_p_pp _ ((ap (e_inv (e_fun (equiv e))) (e_retr (e_fun (equiv e)) y))^)).
    rewrite <- concat_inv.
    pose (e_adj' (Equiv_inverse (equiv e)) y). simpl in e0.
    rewrite <- e0. clear e0.  
    rewrite (concat_A1p (f:=(fun x0 : A => e_inv (e_fun (equiv e)) (e_fun (equiv e) x0)))).
    rewrite concat_inv.
    repeat rewrite concat_p_pp.
    rewrite inv_inv'. cbn.
    rewrite (concat_Ap1 (f:=(fun x0 : A => e_inv (e_fun (equiv e)) (e_fun (equiv e) x0)) )).
    repeat rewrite <- concat_p_pp.
    pose (e_adj' (Equiv_inverse (equiv e)) y'). simpl in e0.
    rewrite <- e0. clear e0.  
    rewrite (concat_p_pp _ (e_sect (e_fun (equiv e)) (e_inv (e_fun (equiv e)) y'))).
    rewrite (concat_A1p (f := (fun x0 : A => e_inv (e_fun (equiv e)) (e_fun (equiv e) x0)))).
    repeat rewrite <- concat_p_pp.
    rewrite inv_inv'. rewrite concat_refl. rewrite inv_inv. apply concat_refl.    
  - intro E. cbn. unfold eq_map_inv, eq_map. repeat rewrite can_eq_eq. 
    repeat rewrite <- concat_p_pp. rewrite inv_inv.
    rewrite concat_refl.
    rewrite (concat_p_pp _ _ (ap univalent_transport E)).
    rewrite inv_inv. cbn. repeat rewrite <- (ap_compose _ (e_fun (equiv e))).
    rewrite (concat_A1p (f:=(fun x0 : B => e_fun (equiv e) (e_inv (e_fun (equiv e)) x0))) _ E).
    rewrite concat_p_pp. rewrite inv_inv. reflexivity. 
Defined.

#[export] Hint Extern 0 ((_ = _) ≃ (_ = _)) => erefine (Equiv_eq _ _ _ _ _ _ _ _ _) : typeclass_instances ur_typeclass_instances.

Definition alt_ur_coh' {A B:Type} (H:A ⋈ B) :
           forall (a:A) (b:B), (a ≈ b) ≃ (↑a = b).
Proof.
  intros a b. cbn.
  eapply equiv_compose. apply alt_ur_coh. apply H. unfold univalent_transport. 
  eapply equiv_compose. apply isequiv_ap. 
  unshelve refine (transport_eq (fun X => (_ = X) ≃ (_ = _))
                       (e_retr _ b)^ _). apply Equiv_id. 
Defined.

Definition UR_eq_equiv (A B : Type) P
           (x : A) (y : B) (H : P x y)
           (x' : A) (y' : B) (H' : P x' y') (X : x = x') (Y:y=y') :
  UR_eq A B P x y H x' y' H' X Y ≃
        (transport_eq (P _) Y (transport_eq (fun X => P X _) X H) = H').
Proof.
  unshelve econstructor. intros XX.
  destruct XX. reflexivity.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros eH.
    destruct X, Y, eH. apply UR_idpath. 
  - cbn. intros XX. destruct XX. reflexivity.
  - cbn. intros eH; destruct X, Y, eH. reflexivity.
Defined. 

Definition alt_ur_coh_transport_r A B H (x1 x2 :A) (y:B) H1 (XX:x1=x2) :
  (alt_ur_coh _ _ _  x2 y) (transport_eq (fun X : A => X ≈ y) XX H1)
  = XX^ @ alt_ur_coh _ _ _  x1 y H1.
destruct XX; reflexivity.
Defined. 

Definition alt_ur_coh_transport_l A B H (x :A) (y1 y2:B) H1 (XX:y1=y2) :
  (alt_ur_coh _ _ _ x y2) (transport_eq (ur x) XX H1)
  = alt_ur_coh _ _ _ x y1 H1 @ ap _ XX.
destruct XX. cbn. apply inverse, concat_refl.
Defined. 
*)

#[universes(collapse_sort_variables=no)]
Definition FP_eq : @eq ≈p @path.
Proof. 
  econstructor. eapply (PR_eq _ _ (@pr _ _ _ H)); eauto.
Defined.

#[universes(collapse_sort_variables=no)]
Definition univ_eq : @eq ≈u @path.
Proof.
  cbn. intros. unshelve econstructor.
  - eapply Equiv_iff_Prop. split; intro e.
    + eapply (snd (alt_ur_coh _ _ _)) in H0.   
      eapply (snd (alt_ur_coh _ _ _)) in H1.
      destruct e. 
      pose proof (H1^@ H0)^. eapply ap_inv_equiv; eauto. eapply e_isequiv.
    + eapply (snd (alt_ur_coh _ _ _)) in H0.   
      eapply (snd (alt_ur_coh _ _ _)) in H1.
      destruct (H0@ ap _ e @ H1^); reflexivity.
  - econstructor. intros e e'. split; intro E.
    + cbn. destruct E, e. cbn in *.
      match goal with | |- PR_eq _ _ _ _ _ _ _ _ _ _ ?X => set (X) end.
      destruct p. econstructor. 
    + eapply PI.
Defined.


#[universes(collapse_sort_variables=no)]
Definition univ_eq' : forall (x : Prop) (y:SProp) (H : x ≈u y), @eq x ≈u @path y.
Proof. 
intros. cbn. intros. unshelve econstructor.
  - eapply Equiv_iff_Prop. split; intro e.
    + reflexivity.
    + eapply (snd (alt_ur_coh _ _ _)) in H0.   
      eapply (snd (alt_ur_coh _ _ _)) in H1.
      destruct (H0@ ap _ e @ H1^); reflexivity.
  - econstructor. intros e e'. split; intro E.
    + cbn. destruct E, e. cbn in *.
      match goal with | |- PR_eq _ _ _ _ _ _ _ _ _ _ ?X => set (X) end.
      destruct p. econstructor. 
    + eapply PI.
Defined.

#[export] Hint Extern 0 (UR_Type (eq _ _) _) => 
  unshelve first [eapply univ_eq' | eapply univ_eq] ; intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (eq _ _ ≈[ _] _) => 
  unshelve first [eapply univ_eq' | eapply univ_eq] ; intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (eq _ _ ≈[ _] _) => 
  unshelve first [eapply univ_eq' | eapply univ_eq] ; intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.

(* Hint Extern 0 (nat ≈u nat) => exact FP_nat : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (UR_Type nat nat) => exact FP_nat : typeclass_instances ur_typeclass_instances. *)

Section TestCase.

  Parameter nat' : Set.

  #[universes(collapse_sort_variables=no)]
  Definition pr_nat : nat ≈u nat'.
  Admitted.

  Hint Extern 0 (nat ≈u nat') => exact pr_nat : typeclass_instances ur_typeclass_instances.
  Hint Extern 0 (UR_Type nat nat') => exact pr_nat : typeclass_instances ur_typeclass_instances.
  Hint Extern 0 (nat ≈u nat') => exact pr_nat : ur_typeclass_instances.
  Hint Extern 0 (UR_Type nat nat') => exact pr_nat : ur_typeclass_instances.

  Parameter plus' : nat' -> nat' -> nat'.

  #[universes(collapse_sort_variables=no)]
  Definition pr_plus : plus ≈u plus'.
  cbn.
  Admitted.

  Hint Extern 0 (plus _ _ ≈u plus' _ _) => unshelve eapply pr_plus  : typeclass_instances ur_typeclass_instances.

  Lemma plus0 : forall m, eq (m + 0) m.
  Proof. 
  induction m; cbn. 
  - reflexivity.
  - f_equal ;tc.
  Qed.

  Lemma plusS : forall m n, eq (S (m + n)) (m + S n).
  Proof.
  induction m; cbn; intros.
  - reflexivity.
  - f_equal; tc.
  Qed.   

  Lemma comm_plus : forall n m, eq (n + m) (m + n).
  Proof.
    induction n; intros. 
    - symmetry. apply plus0.
    - cbn. eapply eq_trans; [|apply plusS]. 
      f_equal; eauto.
  Qed.
  
  Lemma comm_plus' : forall n m, plus' n m = plus' m n.
  Proof. 
    unshelve eapply (equiv _ _); [| | exact comm_plus]. tc. 
  Qed. 

End TestCase.

(* Definition FP_eq_rect : @path_Has_Leibniz_J_@{Type Prop| _ _ _} ≈ @path_Has_Leibniz_J_@{Type SProp| _ _ _}.
Proof.
  cbn; intros. destruct H4. assumption.
Defined. *)


Axiom SPropProp : Prop = SProp.

Instance SPropProp_equiv : Prop ≃ SProp :=
  transport_eq (fun X => Prop ≃ X) SPropProp (Equiv_id Prop).

Instance PropSProp_equiv : SProp ≃ Prop := Equiv_inverse SPropProp_equiv.

Section SoftwareFoundations.

  Axiom state: Type.

  Axiom state': Type. 

  #[universes(collapse_sort_variables=no)]
  Definition stateϵ : state ≈u state'.
  Admitted.

  Hint Extern 0 (state ≈u state') => exact stateϵ  : typeclass_instances ur_typeclass_instances.
  Hint Extern 0 (UR_Type state state') => exact stateϵ  : typeclass_instances ur_typeclass_instances.

  Axiom dcom: Type.

  Axiom dcom': Type. 

  #[universes(collapse_sort_variables=no)]
  Definition dcomϵ : dcom ≈u dcom'.
  Admitted.

  Hint Extern 0 (UR_Type dcom dcom') => exact dcomϵ  : typeclass_instances ur_typeclass_instances.
  Hint Extern 0 (dcom ≈u dcom') => exact dcomϵ  : typeclass_instances ur_typeclass_instances.

  Definition Assertion := state -> Prop.

  Definition Assertion' := state' -> SProp.

  Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

  (* Axiom decorated' : Type. *)
  (* Axiom Decorated' : Assertion' -> dcom' -> decorated'.  *)

  Inductive decorated' : Type :=
  | Decorated' : Assertion' -> dcom' -> decorated'.

  Hint Extern 0 (PR _ Assertion Assertion') => unfold Assertion, Assertion' : typeclass_instances ur_typeclass_instances.

  Inductive decoratedϵ : decorated -> decorated' -> SProp :=
  | Decoratedϵ : forall (a:Assertion) (a':Assertion') (aϵ : a ≈u a') 
      (d : dcom) (d':dcom') (dϵ : d ≈u d'),
     decoratedϵ (Decorated a d) (Decorated' a' d').

  Definition dec_fun : decorated -> decorated'.
  Proof. 
    induction 1. refine (Decorated' (fun s => _) (↑ d)).
    pose proof (equiv (UR_Type_Inverse _ _ stateϵ)).
    exact (↑ (a (↑ s))).
  Defined.

  Definition dec_fun' : decorated' -> decorated.
  Proof. 
    induction 1. pose proof (equiv (UR_Type_Inverse _ _ dcomϵ)). 
    refine (Decorated (fun s => _) (↑ d)).
    exact (↑ (a (↑ s))).
  Defined.

  Instance dec_eq : decorated ≃ decorated'.
  Proof. 
  unshelve econstructor.
  - apply dec_fun. 
  - unshelve eapply isequiv_adjointify.
    + apply dec_fun'.
    + intro x; destruct x. cbn. eapply ap2.
      * eapply funext. intro s. unfold univalent_transport.
        now repeat rewrite e_sect.         
      * apply e_sect.
    + intro x; destruct x. cbn. eapply ap2.
      * eapply funext. intro s. unfold univalent_transport.
        now repeat rewrite e_retr.         
      * apply e_retr.
  Defined.

  #[universes(collapse_sort_variables=no)]
  Definition PR_decorated : decorated ≈p decorated'.
  Proof. 
  cbn. 
  unshelve econstructor. exact (fun d d' => ↑ d = d').
  Defined.

  Goal decorated ≈u decorated'.
  Proof. 
  unshelve econstructor.
  - exact PR_decorated.
  - econstructor; intros. cbn.
    split.
    + eapply ap.
    + eapply ap_inv_equiv. apply dec_eq.
  Defined.        

End SoftwareFoundations.



(*! nat !*)

Hint Extern 0 (0 ≈[ _] 0) => exact Oϵ : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (natϵ 0 0) => exact Oϵ : typeclass_instances ur_typeclass_instances.

Definition Sϵ' n m: n ≈p m -> S n ≈p S m := Sϵ.

Hint Extern 0 (S _ ≈[ _] S _) => apply Sϵ' : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (natϵ (S _) (S _)) => apply Sϵ' : typeclass_instances ur_typeclass_instances.

Definition FP_nat : nat ≈u nat.
Proof.
  unshelve econstructor.
  - eapply Equiv_id.
  - econstructor. intros n m; split.
    + destruct 1. induction n; intros; econstructor; eauto.
    + cbn. induction 1; [econstructor | apply ap; eauto].
Defined. 

Hint Extern 0 (nat ≈u nat) => exact FP_nat : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (UR_Type nat nat) => exact FP_nat : typeclass_instances ur_typeclass_instances.

(*! FP for nat_rect !*)

Definition FP_nat_rect : nat_rect ≈p nat_rect : SProp.
Proof.
  intros X X' H P P' e0 Q Q' e_S n n' en.
  induction en; eauto. eapply e_S; tc.
Defined.

(*! bool !*)

Definition FP_bool : bool ≈u bool.
Proof.
  unshelve econstructor.
  - eapply Equiv_id.
  - econstructor. intros b b'; split.
    + destruct 1. destruct b; intros; econstructor; eauto.
    + cbn. induction 1; econstructor.
Defined. 

(*! False !*)

Definition FP_Empty : (Empty:Type) ≈u (Empty:Type).
Proof. 
unshelve econstructor.
  - eapply Equiv_id.
  - econstructor. intros b b'; split.
    + destruct 1. destruct b; intros; econstructor; eauto.
    + cbn. induction 1; econstructor.
Defined. 

(*! True !*)

(*Instance DecidableEq_eq_True : DecidableEq True.
Proof.
  econstructor. intros [] []. exact (inl idpath). 
Defined.

Instance FP_True : True ⋈ True := URType_Refl_decidable True DecidableEq_eq_True.
*)
(*! List !*)

(* Definition inversion_cons {A a a'} {l l':list A} (X: a::l = a'::l') :
  {p : (a = a') * (l = l') & X = ap2 cons (fst p) (snd p)}
  := match X with
       | idpath => ((idpath ,idpath) ; idpath) end. *)

(*
Instance Transportable_list A (P: list A -> Type)
         (HP : forall (P:A->Type), Transportable P) : Transportable P.
Proof.
  unshelve econstructor.
  - intros n m. revert P; revert m.
    induction n; intro m; destruct m; intros P e. 
    + apply Equiv_id.
    + inversion e.
    + inversion e.
    + pose (inversion_cons e).1. specialize (IHn _ (fun n => P (a :: n)) (snd p)).
      cbn in IHn. eapply equiv_compose; try exact IHn. apply (HP (fun x => P (x :: m))).
      exact (fst p). 
  - cbn. intro n; revert P; induction n; cbn; intro P. 
    + reflexivity.
    + rewrite transportable_refl. rewrite (IHn (fun n => P (a :: n))).
      apply path_Equiv. reflexivity.
Defined. 
*)

(* Instance Equiv_List A B (e:A ≃ B) : list A ≃ list B.
Proof.
    equiv_pind2 (@list_rect _) (@nil _) (@cons _).
Defined. *)

(* Instance Equiv_UR_list A B (R R' : A -> B -> Type)
         (e:forall a b, R a b ≃ R' a b) : forall l l' , PR_list R l l' ≃ PR_list R' l l'.
Proof.
  intros. 
  equiv_pind2 (@PR_list_rect _ _ _) (@PR_list_nil _ _ _) (@PR_list_cons _ _ _).
Defined. *)

(* Definition eq_nil_refl {A} {l:list A} (e : [] = l) :
  match l return [] = l -> Type with [] => fun e => e = idpath | _ => fun _ => False end e.
Proof.
  destruct e. reflexivity. 
Defined. *)

(*
Definition transport_UR_list_cons A B {equ:A ≃ B} (einv := Equiv_inverse equ)
           (a :A) a' a'' (l l': list A ) (l'':list B) (h:a'=a) (e:l'=l)
  (E: a = ↑ a'') (E': UR_list (fun a b => a = ↑b) l l''):
   transport_eq
    (fun X => UR_list  (fun a b => a = ↑b) X (a''::l''))
    (ap2 cons h e)^ (UR_list_cons _ E E')  =
  UR_list_cons (fun a b => a = ↑b) (transport_eq (fun X => eq A X _) h^ E)
               (transport_eq (fun X : list A => UR_list _ X _) e^ E').
  destruct h, e. reflexivity.
Defined.


Definition UR_List_is_eq A B {e:A ≃ B} (e_inv := Equiv_inverse e) :
  forall l l' , UR_list (fun a b => a = ↑b) l l' ≃ (l = ↑ l').
Proof.
  intros l l'. 
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  induction 1; typeclasses eauto. 
  intro x. refine (transport_eq (fun X => UR_list _ X l') x^ _).
  clear x. induction l'; typeclasses eauto. 
  cbn. intro x. induction x; cbn.
  typeclasses eauto. etransitivity. apply transport_UR_list_cons.
  apply ap2. rewrite transport_paths_l. rewrite concat_refl. apply inv2.
  exact IHx.
  cbn. intro x. generalize dependent l'.  
  induction l; cbn; intro l'; destruct l'; intro X.
  cbn. pose (X0 := eq_nil_refl X). cbn in *. rewrite X0. reflexivity. 
  inversion X. inversion X. 
  cbn in *. pose (inversion_cons X). destruct s as [s s']. 
  rewrite s'. etransitivity. apply ap. apply transport_UR_list_cons.
  cbn. apply (ap2 (fun e e' => ap2 cons e e')).
  rewrite transport_paths_l. rewrite concat_refl. apply inv2.
  apply IHl. 
Defined. 

    
Definition URIsUR_list {A B : Type} {H : ur A B} (l l':list A) : (l = l') ≃ (l ≈ (↑ l')).
Proof.
  pose (einv := Equiv_inverse (equiv H)). 
  eapply Equiv_inverse. eapply equiv_compose. 
  unshelve apply Equiv_UR_list.
  exact (fun a b => a = ↑ b).
  intros. cbn. apply alt_ur_coh. apply H. 
  eapply equiv_compose. eapply UR_List_is_eq.
  refine (transport_eq (fun X => (l = X) ≃ _) (e_sect _ l')^ _). refine (Equiv_id _).
Defined. 
*)
 (*
Definition FP_list : list ≈u list.
  unshelve econstructor.
  - econstructor. intros l l'; split.
    + destruct 1. induction l; intros; econstructor; eauto. eapply (fst (ur_coh _ _) idpath). 
    + unfold univalent_transport. pose (e_sect (Equiv_List x y (equiv H)) l').
      set (l'' := Equiv_List _ _ _ _) in *. rewrite <- p. clear p; clearbody l''. 
      induction 1; cbn; intros.
      * reflexivity.
      * apply ap2; eauto. eapply (snd (alt_ur_coh _ _ _) r).
Defined.

#[export] Hint Extern 0 (UR_Type (list ?A) (list ?B)) => unshelve notypeclasses refine (@FP_list _ _ _): typeclass_instances. 
#[export] Hint Extern 0 (list ?A ≈u list ?B) => unshelve notypeclasses refine (@FP_list _ _ _): typeclass_instances. 

Definition FP_cons : @cons ≈u @cons. 
Proof.
  cbn; intros. econstructor; tc.
Defined.

Definition FP_nil : @nil ≈u @nil.
Proof. 
  cbn; intros. econstructor; tc.
Defined.

Hint Extern 0 ([] ≈u []) => eapply FP_nil : typeclass_instances ur_typeclass_instances.
Hint Extern 0 ([] ≈p []) => eapply PR_list_nil : typeclass_instances ur_typeclass_instances.

Hint Extern 0 (cons _ _ ≈u cons _ _) => apply FP_cons : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (cons _ _ ≈p cons _ _) => apply PR_list_cons : typeclass_instances ur_typeclass_instances.

Definition FP_List_rect : @list_rect ≈u @list_rect.
Proof.
  cbn. intros A B e X X' eX P P' P_nil Q Q' Q_cons l l' el. 
  induction el; tc.
Defined.

Definition FP_List_rect' : @list_rect ≈p @list_rect : SProp.
Proof.
  intros A B e X X' eX P P' P_nil Q Q' Q_cons l l' el.
  induction el; cbn; tc.
Defined.

#[export] Hint Extern 0 (list_rect _ ?X ?P ?Q ?l ≈u list_rect _ ?X' ?P' ?Q' ?l') =>
unshelve notypeclasses refine (FP_List_rect _ _ _ X X' _ P P' _ Q Q' _ l l' _); 
shelve_non_PR; intros
 : typeclass_instances ur_typeclass_instances.


#[universes(collapse_sort_variables=no)]
Goal list Type ≈p list Type.
 cbn. tc.
Defined.

#[universes(collapse_sort_variables=no)]
Goal list Type ≈u list Type.
eapply FP_list; cbn. 
(* would require univalence *)
Fail tc.
Abort.

#[universes(collapse_sort_variables=no)]
Goal list (nat -> nat) ≈u list (nat -> nat).
unshelve eapply FP_list; cbn.
unshelve eapply FP_forall_ur; cbn; intros; tc.
Defined.

#[universes(collapse_sort_variables=no)]
Goal list (nat -> Type) ≈u list (nat -> Type).
unshelve eapply FP_list; cbn.
unshelve eapply FP_forall_ur; cbn; intros; try tc.
(* woudl require univalence *)  
Fail tc. 
Abort.

Definition Equiv_Vector_not_eff A B (e:A ≃ B) n n' (en :n = n') : Vector.t A n ≃ Vector.t B n'.
Proof.
  equiv_pind2 (@Vector.t_rect _) (@Vector.nil _) (@Vector.cons _).
Defined.

Definition Equiv_Vector_fun A B (e:A ≃ B) n n' (en : n = n') : Vector.t A n -> Vector.t B n'.
Proof.
  intros v; generalize dependent n'. 
  induction v; destruct n'; intros. 
  apply_cons (@Vector.nil _).
  destruct (zeroS _ en).
  destruct (zeroS _ en^).
  apply univalent_transport in h. 
  unshelve eapply (@Vector.cons _ h _ _).
  apply IHv. 
  exact  (inversionS _ _ en).
Defined.

Instance Equiv_Vector A B (e:A ≃ B) n n' (en :n = n') : Vector.t A n ≃ Vector.t B n'.
Proof.
unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  apply  Equiv_Vector_fun; auto.
  pose (Equiv_inverse e); pose en^. apply  Equiv_Vector_fun; auto.
  intro v. destruct en. induction v; intros; cbn.  reflexivity.
  apply (ap2 (fun a => @Vector.cons _ a _)). 
  typeclasses eauto with equiv typeclass_instances. auto. 
  intro v. destruct en. induction v; intros; cbn.  reflexivity.
  apply (ap2 (fun a => @Vector.cons _ a _)). 
  typeclasses eauto with equiv typeclass_instances. auto.
Defined.


Definition length {A} (l:list A) : nat := list_rect _ (fun _ => nat) O (fun _ _ n => S n) l.

Fixpoint vector_to_list A B (e: A ≃ B) (n m:nat) (en : n = m) :
  vector A n -> {l : list B & length l = m}.
   refine (
  match n, m return n = m -> vector A n -> {l : list B & length l = m} with
  | O,O => fun en _ => ([]; _)
  | S n, S m => fun en v => let IHn :=  vector_to_list A B e n m _ (Vector.tl v) in
           (e (Vector.hd v) :: IHn.1 ; ap S (IHn.2))
  |  _ , _ => _ end en).
   - destruct en. reflexivity.
   - inversion 1.
   - inversion 1.
   - apply inversionS; auto.
Defined. 

Fixpoint list_to_vector_ A B (e: A ≃ B) (n m:nat) (en : n = m) (l:list A) (H : length l = n) {struct n}: Vector.t B m.
  destruct n, m.
  - exact vnil.
  - inversion en. 
  - inversion en. 
  - destruct l.
    + destruct (zeroS _ H).
    + exact (vcons (e a) (list_to_vector_ _ _ e _ _ (inversionS _ _ en) l (inversionS _ _ H))).
Defined. 

Definition list_to_vector A B (e: A ≃ B) (n m:nat) (en: n = m) : {l : list A & length l = n} -> Vector.t B m
  := fun x => list_to_vector_ A B e n m en x.1 x.2.
                                                                                 
Definition transport_vector A n a (s:vector A n) k (e : n = k):
  ap S e # vcons a s  = vcons a (e # s).
  destruct e. reflexivity.
Defined.

Definition tl {A} (l:list A) : list A:=
    match l with
      | [] => []
      | a :: m => m
    end.

Definition S_length :
  forall (A : Type) (l : list A) (n: nat),
    length l = S n -> length (tl l) = n.
  intros; induction l; inversion H; simpl; reflexivity.
Defined.

Instance IsEquiv_vector_list A B e n m en  : IsEquiv (vector_to_list A B e n m en).
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - exact (list_to_vector B A (Equiv_inverse e) m n en^). 
  - (* Sect (nvector_to_nlist a) (nlist_to_nvector a) *)
    destruct en. induction n.
    + intro v. apply Vector.case0. reflexivity.
    + intro v. revert IHn. 
      refine (Vector.caseS (fun n v => (forall x : vector A n,
                                      list_to_vector _ _ _ n _ _ (vector_to_list _ _ _ n _ _ x) = x)
                                    -> list_to_vector _ _ _ (S n) _ _ (vector_to_list _ _ _ (S n) _ _ v) = v) _ _).
      clear. intros. simpl. unfold list_to_vector. cbn. 
      apply (ap2 vcons). exact (e_sect e h). exact (H t).
  - (* Sect (nlist_to_nvector a) (nvector_to_nlist a) *)
    destruct en. induction n.
    + intro rl. simpl. destruct rl as [l Hl].
      destruct l; try inversion Hl. reflexivity.
    + intro rl. destruct rl as [l Hl].
      destruct l. inversion Hl. cbn. 
      eapply path_sigma_SProp. cbn. eapply ap2.
      exact (e_retr e b). cbn in Hl. pose (X := inversionS _ _ Hl).  
      exact ((IHn (l;X))..1).
Defined.

Typeclasses Opaque vector_to_list list_to_vector.

#[export] Hint Extern 0 (length _ ≈[ _] _)=> progress (unfold length)  : typeclass_instances ur_typeclass_instances.




Instance Equiv_vector_list (A B:Type) {H: A ≃ B} (n n':nat) (en : n = n')
  : Vector.t A n ≃ {l : list B & length l = n'}
    := BuildEquiv _ _ _ (IsEquiv_vector_list A B H n n' en).

Definition Equiv_Vector_id A n :Equiv_Vector A A (Equiv_id A) n n  idpath = Equiv_id (Vector.t A n).
apply path_Equiv, funext. intro v.
induction v. reflexivity. cbn. apply ap. exact IHv. 
Defined. 

Definition Equiv_vector_list_
  : Vector.t ≈u (fun A n => {l : list A & length l = n}).
  intros A B e n n' en. cbn in en. eapply (snd (alt_ur_coh FP_nat _ _)) in en.
  unshelve econstructor.
  - econstructor.
    intros v l. exact ((vector_to_list A B (equiv e) n n' en v) = l).
  - econstructor. intros v v'. cbn.
    split; intros.
    + now eapply ap.
    + eapply ap_inv_equiv; tc.
Defined. 
*)
Require Import Ltac2Utils.

#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances ur_typeclass_instances.

From Stdlib Require Import Derive BinNums BinInt.

Fixpoint iterate1@{s|u|} {A : Type@{s|u}} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S n => @iterate1 A f n (f x)
  end.
Definition iterate1Z@{s|u|} {A : Type@{s|u}} (f : A -> A) (n : Z) (x : A) : A := @iterate1 A f (Z.to_nat n) x.

Lemma silly2_eauto : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  sigT@{_ Prop _; _ _} (fun y : _ => P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eauto.
Qed.

#[local] Unset Universe Polymorphism.

Module Type Args. End Args.

Module Type Interface (Import args : Args).

Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall n : nat, P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0 => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.

Definition nat_ind_tidy := build_proof.


Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__O_iso : 0 ≈[ _] imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__S_iso : S ≈[ _] imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__ex : forall y : Type, (y -> SProp) -> SProp.
Parameter Corelib__Init__Logic__ex_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall _ : forall _ : x, Prop, Prop) (fun H : Type => forall _ : forall _ : H, SProp, SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent (forall _ : x, Prop) (forall _ : y, SProp) Prop SProp
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))
           (UR.PR_Type UR.univalent)))
     ex imported_Corelib__Init__Logic__ex).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__Z : Type.
Parameter Corelib__Numbers__BinNums__Z_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) BinNums.Z imported_Corelib__Numbers__BinNums__Z).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_IsomorphismChecker__EqualityLemmas__iterate1Z : forall y : Type, (y -> y) -> imported_Corelib__Numbers__BinNums__Z -> y -> y.
Parameter IsomorphismChecker__EqualityLemmas__iterate1Z_iso : @iterate1Z ≈[ _] imported_IsomorphismChecker__EqualityLemmas__iterate1Z.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@iterate1Z) IsomorphismChecker__EqualityLemmas__iterate1Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@iterate1Z) IsomorphismChecker__EqualityLemmas__iterate1Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__Auto__silly2D_eauto : import_of (@silly2_eauto).
Parameter LF__Auto__silly2D_eauto_iso : iso_statement (@silly2_eauto) imported_LF__Auto__silly2D_eauto.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@silly2_eauto) LF__Auto__silly2D_eauto_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@silly2_eauto) LF__Auto__silly2D_eauto_iso goal_lhs : typeclass_instances ur_typeclass_instances.
End Interface.


Module Type Interface' (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : Set.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : imported_Corelib__Init__Datatypes__nat.

Parameter Corelib__Init__Datatypes__O_iso : 0 ≈[ _] imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__S_iso : forall (x1 : nat) (x2 : imported_Corelib__Init__Datatypes__nat),
  x1 ≈u x2 -> S x1 ≈u imported_Corelib__Init__Datatypes__S x2.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Parameter imported_LF__IndProp__ev : imported_Corelib__Init__Datatypes__nat -> SProp.
Parameter LF__IndProp__ev_iso : ev ≈u imported_LF__IndProp__ev.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@ev) LF__IndProp__ev_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (ev) LF__IndProp__ev_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__evD_0 : import_of (@ev_0).
Parameter LF__IndProp__evD_0_iso : iso_statement (ev_0) imported_LF__IndProp__evD_0.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (ev_0) LF__IndProp__evD_0_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (ev_0) LF__IndProp__evD_0_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface'.

Lemma equal_f {X Y} {f g : X -> Y} a : eq f g -> eq (f a) (g a).
destruct 1. reflexivity.
Qed.

Parameter imported_equal_f : import_of (@equal_f).

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Reserved Notation "s =~ re" (at level 80).
(* 
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2) :
             (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1) :
                s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2) :
                s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re)) :
                 (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).
 *)
 
Require Import Eqdep.

Module Type Interface'' (Import args : Args).



Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_rect : import_of (@Corelib.Init.Logic.eq_rect).
Parameter Corelib__Init__Logic__eqD_rect_iso : iso_statement (@Corelib.Init.Logic.eq_rect) imported_Corelib__Init__Logic__eqD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq : import_of (@eq_rect_eq).
Parameter Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso : iso_statement (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq_Prop : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso_Prop : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq_Prop).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Axiom proof_irrelevance : forall (P : Prop) (p q : P), eq p q.

Parameter imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance : import_of (@proof_irrelevance).
Parameter Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso : iso_statement (@proof_irrelevance) imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@proof_irrelevance) Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@proof_irrelevance) Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) False imported_Corelib__Init__Logic__False).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__iff_iso : (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Prop SProp (forall _ : Prop, Prop) (forall _ : SProp, SProp) (UR.PR_Type UR.univalent)
        (@UR.URArrow UR.univalent Prop SProp Prop SProp (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)))
     iff imported_Corelib__Init__Logic__iff).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__regD_exp : Type -> Type.
Parameter LF__IndProp__regD_exp_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) reg_exp
     imported_LF__IndProp__regD_exp).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__EmptySet : forall y : Type, imported_LF__IndProp__regD_exp y.
Parameter LF__IndProp__EmptySet_iso : @EmptySet ≈[ _] imported_LF__IndProp__EmptySet.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@EmptySet) LF__IndProp__EmptySet_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@EmptySet) LF__IndProp__EmptySet_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__Poly__list : Type -> Type.
Parameter LF__Poly__list_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) list
     imported_LF__Poly__list).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(*
Parameter imported_LF__IndProp__expD_match : forall y : Type, imported_LF__Poly__list y -> imported_LF__IndProp__regD_exp y -> SProp.
Parameter LF__IndProp__expD_match_iso : @exp_match ≈[ _] imported_LF__IndProp__expD_match.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@LF.IndProp.exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@LF.IndProp.exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) Ascii.ascii imported_Stdlib__Strings__Ascii__ascii).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__string : Type.
Parameter LF__IndProp__string_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) IndProp.string imported_LF__IndProp__string).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@LF.IndProp.string) LF__IndProp__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@LF.IndProp.string) LF__IndProp__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__nullD_matchesD_none : import_of (@LF.IndProp.null_matches_none).
Parameter LF__IndProp__nullD_matchesD_none_iso : iso_statement (@LF.IndProp.null_matches_none) imported_LF__IndProp__nullD_matchesD_none.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@LF.IndProp.null_matches_none) LF__IndProp__nullD_matchesD_none_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@LF.IndProp.null_matches_none) LF__IndProp__nullD_matchesD_none_iso goal_lhs : typeclass_instances ur_typeclass_instances.
*)
End Interface''.

Module Type Interface2 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_rect : import_of (@Corelib.Init.Logic.eq_rect).
Parameter Corelib__Init__Logic__eqD_rect_iso : iso_statement (@Corelib.Init.Logic.eq_rect) imported_Corelib__Init__Logic__eqD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq : import_of (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq).
Parameter Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso : iso_statement (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface2.

Module Type Interface3 (Import args : Args).

Inductive Singleton (A : Type) : A -> Type :=
  MkSingleton : forall a, Singleton a.

Parameter imported_parseque__Running__Singleton : forall y : Type, y -> Type.
Parameter parseque__Running__Singleton_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall _ : x, Type) (fun H : Type => forall _ : H, Type) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y Type Type (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent)))
     (@Singleton) imported_parseque__Running__Singleton).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Singleton) parseque__Running__Singleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Singleton) parseque__Running__Singleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_parseque__Running__MkSingleton : forall (y : Type) (y0 : y), imported_parseque__Running__Singleton y0.
Parameter parseque__Running__MkSingleton_iso : @MkSingleton ≈[ _] imported_parseque__Running__MkSingleton.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@MkSingleton) parseque__Running__MkSingleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@MkSingleton) parseque__Running__MkSingleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_parseque__Running__SingletonD_ind : import_of (@Singleton_ind).
Parameter parseque__Running__SingletonD_ind_iso : iso_statement (@Singleton_ind) imported_parseque__Running__SingletonD_ind.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Singleton_ind) parseque__Running__SingletonD_ind_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Singleton_ind) parseque__Running__SingletonD_ind_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface3.

Module Type Interface4 (Import args : Args).


Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : false ≈[ _] imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__negb : imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__negb_iso : negb ≈[ _] imported_Corelib__Init__Datatypes__negb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.negb) Corelib__Init__Datatypes__negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.negb) Corelib__Init__Datatypes__negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : bool_rect ≈[ _] imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Bool__Bool__eqb : imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool.
Parameter Stdlib__Bool__Bool__eqb_iso : Bool.eqb ≈[ _] imported_Stdlib__Bool__Bool__eqb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Bool.Bool.eqb) Stdlib__Bool__Bool__eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Bool.Bool.eqb) Stdlib__Bool__Bool__eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Lemma eqb_neg_distr_r: forall b1 b2,
    eq (Bool.eqb b1 (negb b2)) (negb (Bool.eqb b1 b2)).
Proof. intros. destruct b1, b2; simpl; reflexivity. Qed.


Parameter imported_SECF__Noninterference__eqbD_negD_distrD_r : import_of (@eqb_neg_distr_r).
Parameter SECF__Noninterference__eqbD_negD_distrD_r_iso : iso_statement (@eqb_neg_distr_r) imported_SECF__Noninterference__eqbD_negD_distrD_r.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@eqb_neg_distr_r) SECF__Noninterference__eqbD_negD_distrD_r_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@eqb_neg_distr_r) SECF__Noninterference__eqbD_negD_distrD_r_iso goal_lhs : typeclass_instances ur_typeclass_instances.






Lemma eqb_true_b : forall b : bool, eq (Bool.eqb true b) b.
Proof.
destruct b; reflexivity.
Qed.

Parameter imported_Stalmarck__Algorithm__BoolAux__eqbD_trueD_b : import_of (@eqb_true_b).
Parameter Stalmarck__Algorithm__BoolAux__eqbD_trueD_b_iso : iso_statement (@eqb_true_b) imported_Stalmarck__Algorithm__BoolAux__eqbD_trueD_b.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@eqb_true_b) Stalmarck__Algorithm__BoolAux__eqbD_trueD_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@eqb_true_b) Stalmarck__Algorithm__BoolAux__eqbD_trueD_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.


End Interface4.

Lemma eqb_true_b : forall b : bool, eq (Bool.eqb true b) b.
Proof. now destruct b. Qed.

Module Type Interface5 (Import args : Args).

  Parameter imported_bool : Type.
  Parameter bool_iso :
    @UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_bool.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for (@bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
    tc_hint_for (@bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_false : imported_bool.
  Parameter false_iso : false ≈[ _ ] imported_false.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for (@false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
    tc_hint_for (@false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_true : imported_bool.
  Parameter true_iso : true ≈[ _ ] imported_true.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for (@true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
    tc_hint_for (@true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_bool_rect :
    forall y : imported_bool -> Type,
      y imported_true ->
      y imported_false ->
      forall y0 : imported_bool, y y0.
  Parameter bool_rect_iso : bool_rect ≈[ _ ] imported_bool_rect.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for (@bool_rect) bool_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
    tc_hint_for (@bool_rect) bool_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_eq : forall y : Type, y -> y -> SProp.
  Parameter eq_iso :
    @UR.pr _ _ _
      (@UR.URForall UR.univalent Type Type
         (fun x : Type => forall (_ : x) (_ : x), Prop)
         (fun H : Type => forall (_ : H) (_ : H), SProp)
         (UR.PR_Type UR.univalent)
         (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
            @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp)
              (UR.PR_Type_gen UR.univalent x y H)
              (
                 @UR.URArrow UR.univalent x y Prop SProp
                   (UR.PR_Type_gen UR.univalent x y H)
                   (
                      UR.PR_Type UR.univalent))))
      (@eq) imported_eq.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for (@eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
    tc_hint_for (@eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_eqb :
    imported_bool -> imported_bool -> imported_bool.
  Parameter eqb_iso : Bool.eqb ≈[ _ ] imported_eqb.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for (@Bool.eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
    tc_hint_for (@Bool.eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_eqb_true_b : import_of (eqb_true_b).
  Parameter eqb_true_b_iso : iso_statement eqb_true_b imported_eqb_true_b.
  #[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (eqb_true_b) eqb_true_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (eqb_true_b) eqb_true_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.
End Interface5.


Module Type Interface6 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : false ≈[ _] imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : Type -> Type.
Parameter Corelib__Init__Datatypes__option_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) option
     imported_Corelib__Init__Datatypes__option).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__Some : forall y : Type, y -> imported_Corelib__Init__Datatypes__option y.
Parameter Corelib__Init__Datatypes__Some_iso : @Some ≈[ _] imported_Corelib__Init__Datatypes__Some.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : bool_rect ≈[ _] imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) False imported_Corelib__Init__Logic__False).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) String.string imported_Stdlib__Strings__String__string).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition total_map (A : Type) : Type := string -> A.

(* #[export] Hint Extern 1 => progress (unfold total_map) : typeclass_instances ur_typeclass_instances.
Defnition imported_SECF__Maps__totalD_map A := imported_Stdlib__Strings__String__string -> A. *)

Parameter imported_SECF__Maps__totalD_map : Type -> Type.
Parameter SECF__Maps__totalD_map_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) total_map
     imported_SECF__Maps__totalD_map). 
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@total_map) SECF__Maps__totalD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@total_map) SECF__Maps__totalD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances. 


Definition partial_map (A : Type) := total_map (option A).

(* #[export] Hint Extern 1 => progress (unfold partial_map) : typeclass_instances ur_typeclass_instances.
Definition imported_SECF__Maps__partialD_map A := imported_SECF__Maps__totalD_map (imported_Corelib__Init__Datatypes__option A). *)

Parameter imported_SECF__Maps__partialD_map : Type -> Type.
Parameter SECF__Maps__partialD_map_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent))
     partial_map imported_SECF__Maps__partialD_map). 
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@partial_map) SECF__Maps__partialD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@partial_map) SECF__Maps__partialD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances. 

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, eq (m x) (Some v) -> eq (m' x) (Some v).


Parameter imported_SECF__Maps__includedin : forall y : Type,
  (imported_SECF__Maps__partialD_map y) -> (imported_SECF__Maps__partialD_map  y) -> SProp.
Parameter SECF__Maps__includedin_iso : @includedin ≈[ _] imported_SECF__Maps__includedin.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) : string -> A :=
  fun x' => if String.eqb x x' then v else m x'.

Definition t_update' {A : Type} (m : total_map A)
                    (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Parameter imported_SECF__Maps__tD_update : forall y : Type, (imported_SECF__Maps__totalD_map y) -> imported_Stdlib__Strings__String__string -> y -> imported_Stdlib__Strings__String__string -> y.
Parameter SECF__Maps__tD_update_iso : @t_update ≈[ _] imported_SECF__Maps__tD_update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Notation "'__' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v constr at level 100, right associativity).

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  eq ((x !-> v ; m) x) v.
Proof.
  (* FILL IN HERE *) Admitted.

Parameter imported_SECF__Maps__tD_updateD_eq : forall (y : Type) (y0 : imported_SECF__Maps__totalD_map y) (y1 : imported_Stdlib__Strings__String__string) (y2 : y),
  imported_Corelib__Init__Logic__eq (imported_SECF__Maps__tD_update y0 y1 y2 y1) y2.
Parameter SECF__Maps__tD_updateD_eq_iso : t_update_eq ≈[ _] imported_SECF__Maps__tD_updateD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  eq ((x1 !-> v ; m) x2) (m x2).
Proof.
  (* FILL IN HERE *) Admitted.

#[universes(polymorphic,collapse_sort_variables=no)]
Goal {B : _ & PR univalent (forall (A : Type) (m : total_map A) (x1 x2 : string) (v : A),
x1 <> x2 -> eq ((x1 !-> v; m) x2) (m x2)) B}.
eexists. Fail tc. 
Abort.

End Interface6.


Module Type Interface7 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : false ≈[ _] imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : Type -> Type.
Parameter Corelib__Init__Datatypes__option_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) option
     imported_Corelib__Init__Datatypes__option).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__Some : forall y : Type, y -> imported_Corelib__Init__Datatypes__option y.
Parameter Corelib__Init__Datatypes__Some_iso : @Some ≈[ _] imported_Corelib__Init__Datatypes__Some.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : bool_rect ≈[ _] imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) False imported_Corelib__Init__Logic__False).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) String.string imported_Stdlib__Strings__String__string).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition total_map (A : Type) : Type := string -> A.

#[export] Hint Extern 1 => progress (unfold total_map) : typeclass_instances ur_typeclass_instances.
Definition imported_SECF__Maps__totalD_map A := imported_Stdlib__Strings__String__string -> A.

Definition partial_map (A : Type) := total_map (option A).

#[export] Hint Extern 1 => progress (unfold partial_map) : typeclass_instances ur_typeclass_instances.
Definition imported_SECF__Maps__partialD_map A := imported_SECF__Maps__totalD_map (imported_Corelib__Init__Datatypes__option A).

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, eq (m x) (Some v) -> eq (m' x) (Some v).


Parameter imported_SECF__Maps__includedin : forall y : Type,
  (imported_SECF__Maps__partialD_map y) -> (imported_SECF__Maps__partialD_map  y) -> SProp.
Parameter SECF__Maps__includedin_iso : @includedin ≈[ _] imported_SECF__Maps__includedin.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) : string -> A :=
  fun x' => if String.eqb x x' then v else m x'.

Definition t_update' {A : Type} (m : total_map A)
                    (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Parameter imported_SECF__Maps__tD_update : forall y : Type, (imported_SECF__Maps__totalD_map y) -> imported_Stdlib__Strings__String__string -> y -> imported_Stdlib__Strings__String__string -> y.
Parameter SECF__Maps__tD_update_iso : @t_update ≈[ _] imported_SECF__Maps__tD_update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Notation "'__' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v constr at level 100, right associativity).

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  eq ((x !-> v ; m) x) v.
Proof.
  (* FILL IN HERE *) Admitted.

Parameter imported_SECF__Maps__tD_updateD_eq : forall (y : Type) (y0 : imported_SECF__Maps__totalD_map y) (y1 : imported_Stdlib__Strings__String__string) (y2 : y),
  imported_Corelib__Init__Logic__eq (imported_SECF__Maps__tD_update y0 y1 y2 y1) y2.
Parameter SECF__Maps__tD_updateD_eq_iso : t_update_eq ≈[ _] imported_SECF__Maps__tD_updateD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  eq ((x1 !-> v ; m) x2) (m x2).
Proof.
  (* FILL IN HERE *) Admitted.
Parameter imported_SECF__Maps__tD_updateD_neq : forall (y : Type) (y0 : imported_SECF__Maps__totalD_map y) (y1 y2 : imported_Stdlib__Strings__String__string) (y3 : y),
  (imported_Corelib__Init__Logic__eq y1 y2 -> imported_Corelib__Init__Logic__False) ->
  imported_Corelib__Init__Logic__eq (imported_SECF__Maps__tD_update y0 y1 y3 y2) (y0 y2).
Parameter SECF__Maps__tD_updateD_neq_iso : t_update_neq ≈[ _]  imported_SECF__Maps__tD_updateD_neq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@t_update_neq) SECF__Maps__tD_updateD_neq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@t_update_neq) SECF__Maps__tD_updateD_neq_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Parameter imported_SECF__Maps__update : forall y : Type,
  (imported_Stdlib__Strings__String__string -> imported_Corelib__Init__Datatypes__option y) ->
  imported_Stdlib__Strings__String__string -> y -> imported_Stdlib__Strings__String__string -> imported_Corelib__Init__Datatypes__option y.
Parameter SECF__Maps__update_iso : @update ≈[ _] imported_SECF__Maps__update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@update) SECF__Maps__update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@update) SECF__Maps__update_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Definition empty {A : Type} : partial_map A :=
  t_empty None.
(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Admitted. 
From Ltac2 Require Import Bool.

Parameter imported_SECF__Maps__includedinD_update : import_of (@includedin_update).
Parameter SECF__Maps__includedinD_update_iso : iso_statement (@includedin_update) imported_SECF__Maps__includedinD_update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@includedin_update) SECF__Maps__includedinD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@includedin_update) SECF__Maps__includedinD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface7.

Inductive STrue : SProp := SI.

Definition STrue_UR : True ≈u STrue.
Proof. 
cbn. unshelve econstructor. 
- econstructor. intros. exact STrue.
- eapply Equiv_iff_Prop. split; intros; econstructor.
- econstructor; intros; split; intros; cbn in *; try econstructor. destruct a, a'; reflexivity.
Defined. 

Hint Extern 1 (UR_Type True _) => eapply STrue_UR : typeclass_instances ur_typeclass_instances.

#[universes(polymorphic,collapse_sort_variables=no)]
Goal 
{B : _& @UR.pr _ _ _ (UR.PR_Type UR.univalent) True B}.
Proof.
eexists. tc.
Show Proof. 
Abort. 


Module Interface8. 
(** -- Original-side definitions ------------------------------------------- *)

(** [pred] and [eq_axiom] mirror [ssrbool.pred] and
    [eqtype.eq_axiom] from mathcomp / Corelib.ssr. *)

Definition pred (T : Type) : Type := T -> bool.
Definition addb (b1 b2 : bool) : bool := if b2 then negb b1 else b1.
Definition eqb (b : bool) : bool -> bool := addb (negb b).
Definition eq_axiom (T : Type) (e : T -> pred T) :=
  forall x y : T, reflect (@Corelib.Init.Logic.eq T x y) (e x y).

Axiom eqbP : eq_axiom eqb.
(** i.e. [eqbP : forall x y : bool, reflect (@eq bool x y) (eqb x y)] *)

(** -- Imported-side parameters -------------------------------------------- *)

Parameter imported_bool : Type.
Parameter bool_iso : @UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_bool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_false : imported_bool.
Parameter false_iso : false ≈[_] imported_false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_negb : imported_bool -> imported_bool.
Parameter negb_iso : negb ≈[_] imported_negb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.negb) negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.negb) negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_true : imported_bool.
Parameter true_iso : true ≈[_] imported_true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_False : SProp.
Parameter False_iso : @UR.pr _ _ _ (UR.PR_Type UR.univalent) False imported_False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.False) False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.False) False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_eq : forall y : Type, y -> y -> SProp.
Parameter eq_iso :
  (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type
        (fun x : Type => forall (_ : x) (_ : x), Prop)
        (fun H : Type => forall (_ : H) (_ : H), SProp)
        (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop)
           (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp
              (UR.PR_Type_gen UR.univalent x y H)
              (UR.PR_Type UR.univalent))))
     (@eq) imported_eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_not : SProp -> SProp.
Parameter not_iso :
  (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Prop SProp Prop SProp (UR.PR_Type UR.univalent)
        (UR.PR_Type UR.univalent))
     not imported_not).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.not) not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.not) not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_reflect : SProp -> imported_bool -> Type.
Parameter reflect_iso : reflect ≈[_] imported_reflect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.reflect) reflect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.reflect) reflect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_addb : imported_bool -> imported_bool -> imported_bool.
Parameter addb_iso : addb ≈[_] imported_addb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@addb) addb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@addb) addb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_eqb : imported_bool -> imported_bool -> imported_bool.
Parameter eqb_iso : eqb ≈[_] imported_eqb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
(* #[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances. *)

#[export] Hint Extern 1 (eqb ≈[ _ ] _) =>
  first [ eapply eqb_iso
        | let H := fresh "H" in pose proof (H := eqb_iso); 
          repeat (intros x y e; specialize (H x y e)); cbn; ltac2:(print_ur ()) ]
 : typeclass_instances ur_typeclass_instances.


(** [imported_pred] corresponds to [ssrbool.pred] on the imported side.
    The key structural requirement: [imported_eq_axiom] must use
    [imported_pred y] (not [imported_bool -> imported_bool]) so that
    the URForall PR for [eq_axiom_iso] is well-typed. *)
Parameter imported_pred : Type -> Type.
Parameter pred_iso :
  (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Type Type Type Type
        (UR.PR_Type UR.univalent)
        (UR.PR_Type UR.univalent))
     pred imported_pred).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@pred) pred_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@pred) pred_iso goal_lhs : typeclass_instances ur_typeclass_instances. 
(* 
#[export] Hint Extern 1 => progress (unfold pred) : typeclass_instances ur_typeclass_instances.
Definition imported_pred := fun T => T -> imported_bool. *)

Parameter imported_eq_axiom : forall y : Type, (y -> imported_pred y) -> Type.
Parameter eq_axiom_iso : eq_axiom ≈[_] imported_eq_axiom.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@eq_axiom) eq_axiom_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@eq_axiom) eq_axiom_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(** -- The partial-application unification failure -------------------------

    [import_of (@eqbP)] creates a fresh evar [f2 : ?T] and elaborates
    [@UR.pr univalent (eq_axiom eqb) _ _ eqbP f2].  Since [eq_axiom]
    is NOT unfolded, TC resolution applies [eq_axiom_iso] via
    [eapply], which decomposes [eq_axiom eqb ≈[_] ?B] into subgoals
    including [eqb ≈[_] ?e'] (the second argument of eq_axiom, typed
    [T -> pred T]).  URArrow then decomposes this into
    [eqb x ≈[_] ?e' y] for bound variables x, y.  The [eqb_iso] hint
    fires (key match on [eqb]) but [eapply eqb_iso] fails: it provides
    the fully-applied [eqb ?a ?b ≈[_] imported_eqb ?c ?d] while the
    goal has [eqb x ≈[_] ?Goal] (one argument, partially applied).

    Expected error (approximately):
      Unable to unify
        "forall ... eqb x ≈[ _] imported_eqb y"
      with
        "eqb x ≈[ _] ?Goal0@{X:=y}" *)

#[universes(polymorphic,collapse_sort_variables=no)]
Goal {B : _ & PR univalent (eq_axiom eqb) B}.
Proof.
eexists. Fail tc. 
Abort.    

Fail Parameter imported_eqbP : import_of (@eqbP).

End Interface8.

Module Interface9. 

Unset Implicit Arguments.

(** ---- Original definitions (axiomatized) ---- *)

Definition key := nat.

Axiom tree : Type -> Type.
Axiom bound : forall V : Type, key -> tree V -> bool.
Axiom lookup : forall V : Type, V -> key -> tree V -> V.

Axiom bound_value :
  forall (V : Type) (k : key) (t : tree V),
    @Corelib.Init.Logic.eq _ (bound V k t) true ->
    @ex V (fun v => forall d : V, @Corelib.Init.Logic.eq _ (lookup V d k t) v).

(** ---- Imported counterparts (axiomatized) ---- *)

Parameter imported_bool : Type.
Parameter bool_iso :
  (@UR.pr _ _ _ (UR.PR_Type UR.univalent)
     bool imported_bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.bool)
    bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.bool)
    bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_nat : Type.
Parameter nat_iso :
  (@UR.pr _ _ _ (UR.PR_Type UR.univalent)
     nat imported_nat).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.nat)
    nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.nat)
    nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_true : imported_bool.
Parameter true_iso : true ≈[_] imported_true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.true)
    true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Datatypes.true)
    true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_eq : forall y : Type, y -> y -> SProp.
Parameter eq_iso :
  (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type
        (fun x : Type => forall (_ : x) (_ : x), Prop)
        (fun H : Type => forall (_ : H) (_ : H), SProp)
        (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop)
           (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp
              (UR.PR_Type_gen UR.univalent x y H)
              (UR.PR_Type UR.univalent))))
     (@eq) imported_eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.eq)
    eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.eq)
    eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_ex : forall y : Type, (y -> SProp) -> SProp.
Parameter ex_iso :
  (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type
        (fun x : Type => forall _ : forall _ : x, Prop, Prop)
        (fun H : Type => forall _ : forall _ : H, SProp, SProp)
        (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent (forall _ : x, Prop) (forall _ : y, SProp)
           Prop SProp
           (@UR.URArrow UR.univalent x y Prop SProp
              (UR.PR_Type_gen UR.univalent x y H)
              (UR.PR_Type UR.univalent))
           (UR.PR_Type UR.univalent)))
     ex imported_ex).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.ex)
    ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@Corelib.Init.Logic.ex)
    ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_key : Type.
Parameter key_iso :
  (@UR.pr _ _ _ (UR.PR_Type UR.univalent)
     key imported_key).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@key)
    key_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@key)
    key_iso goal_lhs : typeclass_instances ur_typeclass_instances.


(* Definition imported_key := nat. 

#[export] Hint Extern 1 => progress (unfold key) : typeclass_instances ur_typeclass_instances. *)

Parameter imported_tree : Type -> Type.
Parameter tree_iso :
  (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Type Type Type Type
        (UR.PR_Type UR.univalent)
        (UR.PR_Type UR.univalent))
     tree imported_tree).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@tree)
    tree_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@tree)
    tree_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_bound : import_of (@bound).
Parameter bound_iso : iso_statement (@bound) imported_bound.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@bound)
    bound_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@bound)
    bound_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_lookup : import_of (@lookup).
Parameter lookup_iso : iso_statement (@lookup) imported_lookup.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@lookup)
    lookup_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) =>
  tc_hint_for (@lookup)
    lookup_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(** ---- The failing declarations ---- *)

(** [import_of] triggers TC resolution for
    [PR univalent
       (forall (V : Type) (k : key) (t : tree V),
        eq (bound V k t) true ->
        exists v : V, forall d : V, eq (lookup V d k t) v)
       ?B].

    TC resolution decomposes through [URForall] for [V], [URArrow]
    for [k] and [t], then hits [eq (bound V k t) true].  Building the
    relation for [bound V k t] (a [bool]) requires a parametricity
    translation for the application [bound V k t], but [bound] and
    [lookup] only have *relational* hints (for the head constant),
    not full parametricity translations.  The dependent structure --
    the equality hypothesis feeding into an existential -- makes the
    resolution especially difficult. *)

Parameter imported_bound_value : import_of (@bound_value).

End Interface9.



Module Type Interface11 (Import args : Args).

Parameter imported_Corelib__Init__Logic__True : SProp.
(* Parameter Corelib__Init__Logic__True_iso : (UR_Type@{Type Type Type SProp Type Type Prop; _ _ _ _ _ _} True imported_Corelib__Init__Logic__True). *)

Parameter Corelib__Init__Logic__True_iso : @UR.pr _ _ _ (UR.PR_Type UR.univalent) True imported_Corelib__Init__Logic__True. 
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.True) Corelib__Init__Logic__True_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.True) Corelib__Init__Logic__True_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__and : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__and_iso : (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Prop SProp (forall _ : Prop, Prop) (forall _ : SProp, SProp) (UR.PR_Type UR.univalent)
        (@UR.URArrow UR.univalent Prop SProp Prop SProp (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)))
     and imported_Corelib__Init__Logic__and).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem match_ex2 : and True True.
Proof.
  match goal with
  | [ |- True ] => apply I
  | [ |- and True True ] => split; apply I
  end.
Qed.

Parameter imported_LF__AltAuto__matchD_ex2 : import_of (@match_ex2).
Parameter LF__AltAuto__matchD_ex2_iso : iso_statement (@match_ex2) imported_LF__AltAuto__matchD_ex2.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@match_ex2) LF__AltAuto__matchD_ex2_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@match_ex2) LF__AltAuto__matchD_ex2_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface11.


Module Type Interface12 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter win64: bool.

Parameter imported_compcert__x86D_64__Archi__win64 : imported_Corelib__Init__Datatypes__bool.
Parameter compcert__x86D_64__Archi__win64_iso : win64 ≈[ _] imported_compcert__x86D_64__Archi__win64.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@win64) compcert__x86D_64__Archi__win64_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@win64) compcert__x86D_64__Archi__win64_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface12.

Module Type Interface13 (Import args : Args).

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) False imported_Corelib__Init__Logic__False).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
Parameter imported_Corelib__Init__Logic__eq_Prop : forall y : SProp, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso_Prop : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Prop SProp (fun x : Prop => forall (_ : x) (_ : x), Prop) (fun H : SProp => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x : Prop) (y : SProp) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (fun A : Prop => @eq A) imported_Corelib__Init__Logic__eq_Prop).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__iff_iso : (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Prop SProp (forall _ : Prop, Prop) (forall _ : SProp, SProp) (UR.PR_Type UR.univalent)
        (@UR.URArrow UR.univalent Prop SProp Prop SProp (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)))
     Logic.iff imported_Corelib__Init__Logic__iff).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : SProp -> SProp.
Parameter Corelib__Init__Logic__not_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Prop SProp Prop SProp (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) not
     imported_Corelib__Init__Logic__not).

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.
Reserved Notation "s =~ re" (at level 80).
     
Parameter imported_LF__IndProp__regD_exp : Type -> Type.
Parameter LF__IndProp__regD_exp_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) reg_exp
     imported_LF__IndProp__regD_exp).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__Char : forall y : Type, y -> imported_LF__IndProp__regD_exp y.
Parameter LF__IndProp__Char_iso : @Char ≈[ _] imported_LF__IndProp__Char.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Char) LF__IndProp__Char_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Char) LF__IndProp__Char_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_LF__Poly__list : Type -> Type.
Parameter LF__Poly__list_iso : (@UR.pr _ _ _ (@UR.URArrow UR.univalent Type Type Type Type (UR.PR_Type UR.univalent) (UR.PR_Type UR.univalent)) Datatypes.list
     imported_LF__Poly__list).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Datatypes.list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Datatypes.list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Local Open Scope list_scope.
From Stdlib Require Import List. 
Import ListNotations.
Inductive exp_match {T} : Datatypes.list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : x :: [] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2) :
             (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1) :
                s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2) :
                s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re)) :
                 (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

From Stdlib Require Import Ascii. 

Notation "A <-> B" := (Logic.iff A B) : type_scope.

Lemma char_nomatch_char :
  forall (a b : ascii) s, (eq b a -> False) -> ((b :: s =~ Char a) <-> False).
Proof. Admitted. 

Parameter imported_LF__IndProp__expD_match : forall y : Type, imported_LF__Poly__list y -> imported_LF__IndProp__regD_exp y -> SProp.
Parameter LF__IndProp__expD_match_iso : @exp_match ≈[ _] imported_LF__IndProp__expD_match.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__Poly__cons : forall y : Type, y -> imported_LF__Poly__list y -> imported_LF__Poly__list y.
Parameter LF__Poly__cons_iso : @Datatypes.cons ≈[ _] imported_LF__Poly__cons.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Datatypes.cons) LF__Poly__cons_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Datatypes.cons) LF__Poly__cons_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) Ascii.ascii imported_Stdlib__Strings__Ascii__ascii).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__charD_nomatchD_char : import_of (@char_nomatch_char).
Parameter LF__IndProp__charD_nomatchD_char_iso : iso_statement (@char_nomatch_char) imported_LF__IndProp__charD_nomatchD_char.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@char_nomatch_char) LF__IndProp__charD_nomatchD_char_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@char_nomatch_char) LF__IndProp__charD_nomatchD_char_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface13.

Module Type Interface14 (Import args : Args).

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.


Parameter imported_Autosubst__AutosubstD_Basics__funcomp : forall y y0 y1 : Type, (y -> y0) -> (y0 -> y1) -> y -> y1.
Parameter Autosubst__AutosubstD_Basics__funcomp_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (B C : Type) (_ : forall _ : x, B) (_ : forall _ : B, C) (_ : x), C)
        (fun H : Type => forall (y y0 : Type) (_ : forall _ : H, y) (_ : forall _ : y, y0) (_ : H), y0) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URForall UR.univalent Type Type (fun x0 : Type => forall (C : Type) (_ : forall _ : x, x0) (_ : forall _ : x0, C) (_ : x), C)
           (fun y0 : Type => forall (y1 : Type) (_ : forall _ : y, y0) (_ : forall _ : y0, y1) (_ : y), y1) (UR.PR_Type UR.univalent)
           (fun (x0 y0 : Type) (H0 : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x0 y0) =>
            @UR.URForall UR.univalent Type Type (fun x1 : Type => forall (_ : forall _ : x, x0) (_ : forall _ : x0, x1) (_ : x), x1)
              (fun y1 : Type => forall (_ : forall _ : y, y0) (_ : forall _ : y0, y1) (_ : y), y1) (UR.PR_Type UR.univalent)
              (fun (x1 y1 : Type) (H1 : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x1 y1) =>
               @UR.URArrow UR.univalent (forall _ : x, x0) (forall _ : y, y0) (forall (_ : forall _ : x0, x1) (_ : x), x1) (forall (_ : forall _ : y0, y1) (_ : y), y1)
                 (@UR.URArrow UR.univalent x y x0 y0 (UR.PR_Type_gen UR.univalent x y H)
                    (UR.PR_Type_gen UR.univalent x0 y0 H0))
                 (@UR.URArrow UR.univalent (forall _ : x0, x1) (forall _ : y0, y1) (forall _ : x, x1) (forall _ : y, y1)
                    (@UR.URArrow UR.univalent x0 y0 x1 y1 (UR.PR_Type_gen UR.univalent x0 y0 H0)
                       (UR.PR_Type_gen UR.univalent x1 y1 H1))
                    (                     @UR.URArrow UR.univalent x y x1 y1 (UR.PR_Type_gen UR.univalent x y H)
                       (UR.PR_Type_gen UR.univalent x1 y1 H1)))))))
     (@funcomp) imported_Autosubst__AutosubstD_Basics__funcomp).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition var := nat.

Parameter imported_Autosubst__AutosubstD_Basics__var : Type.
Parameter Autosubst__AutosubstD_Basics__var_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) var imported_Autosubst__AutosubstD_Basics__var).

(* Definition imported_Autosubst__AutosubstD_Basics__var := imported_Corelib__Init__Datatypes__nat.*)
#[export] Hint Extern 1 => progress (unfold var) : typeclass_instances ur_typeclass_instances.  

Definition lift (x y : var) : var := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )").


Parameter imported_Autosubst__AutosubstD_Basics__lift : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Autosubst__AutosubstD_Basics__lift_iso : (@UR.pr _ _ _
     (@UR.URArrow UR.univalent nat imported_Corelib__Init__Datatypes__nat (forall _ : nat, nat) (forall _ : imported_Corelib__Init__Datatypes__nat, imported_Corelib__Init__Datatypes__nat)
        (@UR.PR_Type_univ_univ nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
        (@UR.URArrow UR.univalent nat imported_Corelib__Init__Datatypes__nat nat imported_Corelib__Init__Datatypes__nat
           (@UR.PR_Type_univ_univ nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
           (@UR.PR_Type_univ_univ nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)))
     lift imported_Autosubst__AutosubstD_Basics__lift).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp) (UR.PR_Type UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type UR.univalent) x y) =>
         @UR.URArrow UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen UR.univalent x y H)
           (@UR.URArrow UR.univalent x y Prop SProp (UR.PR_Type_gen UR.univalent x y H) (UR.PR_Type UR.univalent))))
     (@eq) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Nat__add : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Nat__add_iso : Nat.add ≈[ _] imported_Corelib__Init__Nat__add.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep : forall (y : Type) (y0 : y -> Type) (y1 : forall y1 : y, y0 y1) (y2 : forall y2 : y, y0 y2),
  (forall y3 : y, imported_Corelib__Init__Logic__eq (y1 y3) (y2 y3)) -> imported_Corelib__Init__Logic__eq y1 y2.

Parameter Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep_iso : @FunctionalExtensionality.functional_extensionality_dep ≈[ _] imported_Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep) Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep) Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Delimit Scope subst_scope with subst.
Open Scope subst_scope.


Reserved Notation "sigma >> tau" (at level 56, left associativity).
Notation "f >>> g" := (funcomp f g)
  (at level 56, left associativity) : subst_scope.


Section LemmasForFun.

Context {A B : Type}.
Implicit Types (x : A) (f : var -> A) (g : A -> B) (n m : var).

Lemma lift_compR n m f : eq ((+n) >>> ((+m) >>> f)) ((+m+n) >>> f).
Admitted.

End LemmasForFun.


Parameter imported_Autosubst__AutosubstD_Basics__liftD_compR : import_of (@lift_compR).
Parameter Autosubst__AutosubstD_Basics__liftD_compR_iso : iso_statement (@lift_compR) imported_Autosubst__AutosubstD_Basics__liftD_compR.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@lift_compR) Autosubst__AutosubstD_Basics__liftD_compR_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@lift_compR) Autosubst__AutosubstD_Basics__liftD_compR_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface14.



Module DString.

(** Difference lists for fast append. *)
Definition t : Set := string -> string.

End DString.

Module Type Interface15 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) Ascii.ascii imported_Stdlib__Strings__Ascii__ascii).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) String.string imported_Stdlib__Strings__String__string).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Ceres__CeresString__DString__t : import_of (@DString.t).
Parameter Ceres__CeresString__DString__t_iso : iso_statement (@DString.t) imported_Ceres__CeresString__DString__t.

End Interface15.
(*
Module Type Interface15 (Import args : Args).

Parameter imported_Corelib__Numbers__BinNums__positive : import_of (@Corelib.Numbers.BinNums.positive).
Parameter Corelib__Numbers__BinNums__positive_iso : iso_statement (@Corelib.Numbers.BinNums.positive) imported_Corelib__Numbers__BinNums__positive.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_VFA__Color__M__key : import_of (@VFA.Color.M.key).
Parameter VFA__Color__M__key_iso : iso_statement (@VFA.Color.M.key) imported_VFA__Color__M__key.
#[export] Hint Extern 1 => progress (unfold VFA.Color.M.key) : typeclass_instances ur_typeclass_instances.

End Interface15.

#[universes(polymorphic,collapse_sort_variables=no)]
Goal PR plain (forall A : Prop, A -> A -> Prop) (forall y : SProp, y -> y -> SProp).
tc.
*)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.





Require Import Ltac.


Module Type Interface19 (Import args : Args).

Set Implicit Arguments.

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.
Parameter imported_Autosubst__AutosubstD_Basics__funcomp : import_of (@funcomp).
Parameter Autosubst__AutosubstD_Basics__funcomp_iso : iso_statement (@funcomp) imported_Autosubst__AutosubstD_Basics__funcomp.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : import_of (@Corelib.Init.Datatypes.nat).
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement (@Corelib.Init.Datatypes.nat) imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition iterate := fix iterate {A} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f(iterate f n' a)
  end.
Arguments iterate {A} f n a : simpl never.


Parameter imported_Autosubst__AutosubstD_Basics__iterate : import_of (@iterate).
Parameter Autosubst__AutosubstD_Basics__iterate_iso : iso_statement (@iterate) imported_Autosubst__AutosubstD_Basics__iterate.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@iterate) Autosubst__AutosubstD_Basics__iterate_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@iterate) Autosubst__AutosubstD_Basics__iterate_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition var := nat.

Parameter imported_Autosubst__AutosubstD_Basics__var : import_of (@var).
Parameter Autosubst__AutosubstD_Basics__var_iso : iso_statement (@var) imported_Autosubst__AutosubstD_Basics__var.
#[export] Hint Extern 1 => progress (unfold var) : typeclass_instances ur_typeclass_instances.

Definition lift (x y : var) : var := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )").


Parameter imported_Autosubst__AutosubstD_Basics__lift : import_of (@lift).
Parameter Autosubst__AutosubstD_Basics__lift_iso : iso_statement (@lift) imported_Autosubst__AutosubstD_Basics__lift.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition scons {X : Type} (s : X) (sigma : var -> X) (x : var) : X :=
  match x with S y => sigma y | _ => s end.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at level 56, right associativity) : subst_scope.
Parameter imported_Autosubst__AutosubstD_Basics__scons : import_of (@scons).
Parameter Autosubst__AutosubstD_Basics__scons_iso : iso_statement (@scons) imported_Autosubst__AutosubstD_Basics__scons.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@scons) Autosubst__AutosubstD_Basics__scons_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@scons) Autosubst__AutosubstD_Basics__scons_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Class Ids (term : Type) := ids : var -> term.

Arguments ids {_ _} x : simpl never.

Parameter imported_Autosubst__AutosubstD_Classes__Ids : import_of (@Ids).
Parameter Autosubst__AutosubstD_Classes__Ids_iso : iso_statement (@Ids) imported_Autosubst__AutosubstD_Classes__Ids.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Ids) Autosubst__AutosubstD_Classes__Ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Ids) Autosubst__AutosubstD_Classes__Ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Class Rename (term : Type) := rename : (var -> var) -> term -> term.
Arguments rename {_ _} xi !s /.

Parameter imported_Autosubst__AutosubstD_Classes__Rename : import_of (@Rename).
Parameter Autosubst__AutosubstD_Classes__Rename_iso : iso_statement (@Rename) imported_Autosubst__AutosubstD_Classes__Rename.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Rename) Autosubst__AutosubstD_Classes__Rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Rename) Autosubst__AutosubstD_Classes__Rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Autosubst__AutosubstD_Classes__ids : import_of (@ids).
Parameter Autosubst__AutosubstD_Classes__ids_iso : iso_statement (@ids) imported_Autosubst__AutosubstD_Classes__ids.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@ids) Autosubst__AutosubstD_Classes__ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@ids) Autosubst__AutosubstD_Classes__ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Autosubst__AutosubstD_Classes__rename : import_of (@rename).
Parameter Autosubst__AutosubstD_Classes__rename_iso : iso_statement (@rename) imported_Autosubst__AutosubstD_Classes__rename.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@rename) Autosubst__AutosubstD_Classes__rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@rename) Autosubst__AutosubstD_Classes__rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Delimit Scope subst_scope with subst.
Open Scope subst_scope.
Reserved Notation "sigma >> tau" (at level 56, left associativity).
Notation "f >>> g" := (funcomp f g)
  (at level 56, left associativity) : subst_scope.

Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at level 56, right associativity) : subst_scope.

Definition up {T} `{Ids T} `{Rename T} (sigma : var -> T) : var -> T :=
  ids 0 .: sigma >>> rename (+1).
Arguments up {T _ _} sigma x : simpl never.

Parameter imported_Autosubst__AutosubstD_Classes__up : import_of (@up).
Parameter Autosubst__AutosubstD_Classes__up_iso : iso_statement (@up) imported_Autosubst__AutosubstD_Classes__up.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@up) Autosubst__AutosubstD_Classes__up_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@up) Autosubst__AutosubstD_Classes__up_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : import_of (@Corelib.Init.Datatypes.O).
Parameter Corelib__Init__Datatypes__O_iso : iso_statement (@Corelib.Init.Datatypes.O) imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : import_of (@Corelib.Init.Datatypes.S).
Parameter Corelib__Init__Datatypes__S_iso : iso_statement (@Corelib.Init.Datatypes.S) imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Nat__add : import_of (@Corelib.Init.Nat.add).
Parameter Corelib__Init__Nat__add_iso : iso_statement (@Corelib.Init.Nat.add) imported_Corelib__Init__Nat__add.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Notation upn := (iterate up) (only parsing).

Section LemmasForSubst.

Context {term : Type} {Ids_term : Ids term}
        {Rename_term : Rename term}.

Implicit Types (s t : term) (sigma tau theta : var -> term) (xi : var -> var).


Lemma fold_up_upn n sigma : eq (up (upn n sigma)) (upn (S n) sigma).
Admitted. 
End LemmasForSubst.

Parameter imported_Autosubst__AutosubstD_Tactics__foldD_upD_upn : import_of (@fold_up_upn).
Parameter Autosubst__AutosubstD_Tactics__foldD_upD_upn_iso : iso_statement (@fold_up_upn) imported_Autosubst__AutosubstD_Tactics__foldD_upD_upn.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@fold_up_upn) Autosubst__AutosubstD_Tactics__foldD_upD_upn_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@fold_up_upn) Autosubst__AutosubstD_Tactics__foldD_upD_upn_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface19.

Module Type Interface16 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_rect : import_of (@Corelib.Init.Logic.eq_rect).
Parameter Corelib__Init__Logic__eqD_rect_iso : iso_statement (@Corelib.Init.Logic.eq_rect) imported_Corelib__Init__Logic__eqD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__rewD_const : import_of (@Corelib.Init.Logic.rew_const).

End Interface16.

Unset Universe Polymorphism.

Inductive atomT : Type :=
| NBool : forall (p : Prop), option (p \/ ~ p) -> atomT
| TBool : forall (b: bool) (p: Prop), p <-> is_true b -> atomT.

Module Type Interface17 (Import args : Args).
(* 
#[universes(polymorphic,collapse_sort_variables=no)]
Goal {B : _ & PR univalent
                Type@{}
                  B}. *)

Parameter imported_Cdcl__Formula__atomT : import_of (@atomT:Type).
Parameter Cdcl__Formula__atomT_iso : iso_statement (@atomT:Type) imported_Cdcl__Formula__atomT.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@atomT:Type) Cdcl__Formula__atomT_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@atomT:Type) Cdcl__Formula__atomT_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : import_of (@Corelib.Init.Datatypes.option).
Parameter Corelib__Init__Datatypes__option_iso : iso_statement (@Corelib.Init.Datatypes.option) imported_Corelib__Init__Datatypes__option.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : import_of (@Corelib.Init.Logic.False).
Parameter Corelib__Init__Logic__False_iso : iso_statement (@Corelib.Init.Logic.False) imported_Corelib__Init__Logic__False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__or : import_of (@Corelib.Init.Logic.or).
Parameter Corelib__Init__Logic__or_iso : iso_statement (@Corelib.Init.Logic.or) imported_Corelib__Init__Logic__or.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.or) Corelib__Init__Logic__or_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Logic.or) Corelib__Init__Logic__or_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Fail Parameter imported_Cdcl__Formula__NBool : import_of (@NBool).

Parameter imported_Corelib__Init__Datatypes__option' : import_of (@Corelib.Init.Datatypes.option : Prop -> Type).
Parameter Corelib__Init__Datatypes__option_iso' : iso_statement (@Corelib.Init.Datatypes.option) imported_Corelib__Init__Datatypes__option'.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso' goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso' goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Cdcl__Formula__NBool : import_of (@NBool).
Parameter Cdcl__Formula__NBool_iso : iso_statement (@NBool) imported_Cdcl__Formula__NBool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for (@NBool) Cdcl__Formula__NBool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr _ ?goal_lhs _) => tc_hint_for (@NBool) Cdcl__Formula__NBool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface17.

(*
#[export] Hint Extern 0 (Vector.t ?A ?n ≃ _) =>
erefine (ur_type (Equiv_vector_list A _ n)) : typeclass_instances ur_typeclass_instances.

Instance Equiv_list_vector (A B:Type) {H : ur B A} n :
  {l : list A & length l = n} ≃ Vector.t B n | 1 := Equiv_inverse _.

Definition Equiv_list_vector_ : (fun A n => {l : list A & length l = n}) ≈ Vector.t.
  cbn. intros A B e.
  split. tc.  intros. apply UR_Type_Inverse. apply Equiv_vector_list_.
  apply UR_Type_Inverse. tc. symmetry. tc. 
Defined.

Definition UrEq_S n n' e m m' e' X Y : UR_eq nat nat (eq nat) n n' e m m' e' X Y ->
                                       UR_eq nat nat (eq nat) (S n) (S n') (ap S e)
                                             (S m) (S m') (ap S e') (ap S X) (ap S Y).
Proof.
  destruct 1. econstructor.
Defined.

Definition IsIrr_UrEq_nat n n' e m m' e' X Y :
  UR_eq nat nat (eq nat) n n' e m m' e' X Y.
  destruct e, e', X. assert (Y = idpath). apply is_hset. rewrite X. econstructor.
Defined. 

Definition IsHProp_UrEq_nat_B {n n' e m m' e' X Y p p' e'' X' Y'}
           (Hm:m = p) (Hm' : m' = p')
           (He : Hm # Hm' # e' = e'')
           (HX : Hm # X = X')
           (HY : Hm' # Y = Y')
           (B : UR_eq nat nat (eq nat) n n' e p p' e'' X' Y')
  : UR_eq nat nat (eq nat) n n' e m m' e' X Y.
  pose (transport_eq (fun XX => UR_eq nat nat (eq nat) n n' e p p' XX _ _) He^
        (transport_eq (fun XX => UR_eq nat nat (eq nat) n n' e p p' e'' XX _) HX^
         (transport_eq (fun XX => UR_eq nat nat (eq nat) n n' e p p' e'' X'  XX) HY^ B))).
  cbn in u. clearbody u. clear HX He HY B.
  destruct Hm, Hm'. 
  exact u.
Defined. 

Definition IsHProp_UrEq_nat_gen {n n' e m m' e' X Y p p' e'' X' Y'}
           (Hm:m = p) (Hm' : m' = p')
           (He : Hm # Hm' # e' = e'')
           (HX : Hm # X = X')
           (HY : Hm' # Y = Y')
           (A : UR_eq nat nat (eq nat) n n' e m m' e' X Y)
           (B : UR_eq nat nat (eq nat) n n' e p p' e'' X' Y')
  : A = IsHProp_UrEq_nat_B Hm Hm' He HX HY B. 
  destruct A, B. cbn in *. revert He HX HY. 
  assert (Hm = idpath). apply is_hset. rewrite X. clear X. 
  assert (Hm' = idpath). apply is_hset. rewrite X. clear X. cbn.
  intros.
  assert (He = idpath). apply IsIrr_IsHprop'. intros X Y. apply is_hset. rewrite X. clear X. 
  assert (HX = idpath). apply IsIrr_IsHprop'. intros X Y. apply is_hset. rewrite X. clear X. 
  assert (HY = idpath). apply IsIrr_IsHprop'. intros X Y. apply is_hset. rewrite X. clear X. 
  reflexivity. 
Defined.

Definition IsHProp_UrEq_nat n n' e m m' e' X Y (A B :
  UR_eq nat nat (eq nat) n n' e m m' e' X Y) : A = B :=
  IsHProp_UrEq_nat_gen idpath idpath idpath idpath idpath A B.

Definition UR_sized_list_irr A B {X:A ⋈ B}
           (n n':nat) (en : n = n')
           (s : {l : list A & length l = n})
           (s' : {l : list B & length l = n'})                  
  : 
   (s.1 ≈ s'.1) ≃ (s ≈ s').
Proof.
  cbn. set (Hl := s.2). set (Hl' := s'.2). set (l := s.1) in *. set (l' := s'.1) in *.
  clearbody Hl Hl' l l'. destruct en. clear s s'. cbn in Hl. destruct Hl.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - intro urlist. unshelve eexists. induction urlist; try econstructor; auto.
    apply IsIrr_UrEq_nat.
  - apply projT1.
  - intro urlist; destruct urlist; reflexivity.
  - intros [urlist UR_eq_list]. apply path_sigma_uncurried.
    unshelve eexists. cbn. destruct urlist; reflexivity.
    cbn. apply IsHProp_UrEq_nat.
Defined.

Definition ap_S_section {n m} en : (en = ap S (inversionS n m en)).
  apply is_hset.
Defined.

Definition ap_S_retraction {n m} (en:n=m) : (en = inversionS _ _ (ap S en)).
  apply is_hset.
Defined. 

Definition transport_UR_vector_cons A B {X:A ⋈ B} (X_inv := UR_Type_Inverse _ _ X)
           n n' (en:n = n')
           (a :A) a' a'' (v v': Vector.t A n) (v'':Vector.t B n') (h:a'=a) (e:v'=v)
  (E: ur a a'') (E': UR_vector ur n n' en v v''):
   transport_eq
    (fun X => UR_vector ur (S n) (S n') (ap S en) X (vcons a'' v''))
    (ap2 vcons h e)^ (UR_vector_cons ur en E E')  =
  UR_vector_cons ur en (transport_eq (fun X => ur X _) h^ E)
               (transport_eq (fun X => UR_vector ur _ _ en X _) e^ E').
  destruct h, e. reflexivity.
Defined.

Definition transport_UR_vector_cons_eq (A B:Type) {X:A ⋈ B} (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en en':n = n') (a:A) (a':B) (e:en' = en)
           (v: Vector.t A n) (v':Vector.t B n')
  (E: ur a a') (E': UR_vector ur n n' en v v'):
   transport_eq
    (fun X => UR_vector ur (S n) (S n') X (vcons a v) (vcons a' v'))
    (ap (ap S) e)^ (UR_vector_cons ur en E E')  =
   UR_vector_cons ur _ E (transport_eq (fun X => UR_vector ur _ _ X _ _) e^ E').
  destruct e. reflexivity.
Defined.

Definition UR_vector_list_is_eq_fun A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en : n = n')
           (en_inv : n' = n := inverse en)
           (v : t A n)
           (v' : t B n') :
  UR_vector ur n n' en v v'
  -> UR_list ur (vector_to_list A A (Equiv_id A) n n idpath v) .1
      (vector_to_list B B (Equiv_id B) n' n' idpath v') .1.
  induction 1; cbn; econstructor; auto.
Defined.


Definition UR_list_decompose {A B} (R:A->B->Type) l l' (e : UR_list R l l') :
  match l,l' return UR_list R l l' -> Type
  with [],[] => fun e => e = UR_list_nil R
  | a::l,a'::l' => fun e => { X : (R a a') * UR_list R l l' & e = UR_list_cons R (fst X) (snd X)}
  | _,_ => fun _ => False end e.
Proof.
  destruct e. reflexivity. exists (r,e). reflexivity. 
Defined.

Definition UR_vector_list_is_eq_inv A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en : n = n')
           (en_inv : n' = n := inverse en)
           (v : t A n)
           (v' : t B n')
           (canA := ur_refl A)
           (canB := ur_refl B)
  :
UR_list ur (vector_to_list A A (Equiv_id A) n n idpath v) .1
        (vector_to_list B B (Equiv_id B) n' n' idpath v') .1 ->
UR_vector ur n n' en v v'.
intros Hlist. clear en_inv. generalize dependent n'.
    induction v; destruct v'; intros.
    + assert (en = idpath). apply is_hset.
      rewrite X0. econstructor.
    + destruct (zeroS _ en).
    + destruct (zeroS _ en^).
    + cbn in Hlist.
      pose (UR_list_decompose ur _ _ Hlist). cbn in y. destruct y as [(r,r') _].
      refine (transport_eq (fun X => UR_vector ur (S n) (S n0) X _ _) (ap_S_section en)^ _).
      econstructor; auto.
Defined.


Definition UR_vector_list_is_eq_inv_eq A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en en': n = n') (e : en' = en)
           (en_inv : n' = n := inverse en)
           (v : t A n)
           (v' : t B n') XX:
  transport_eq (fun X0 : n ≈ n' => UR_vector ur n n' X0 v v') e
  (UR_vector_list_is_eq_inv A B n n' _ v v' XX) =
  UR_vector_list_is_eq_inv A B n n' en v v' XX.
destruct e. reflexivity. 
Defined.

Definition UR_vector_list_is_eq A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en : n = n')
           (en_inv : n' = n := inverse en)
           (canA := ur_refl A)
           (canB := ur_refl B)
  : 
  forall (v:t A n) (v' : t B n') ,
    let l := ↑ v : {l : list A & length l = n} in
    let l' := ↑ v' : {l : list B & length l = n'} in 
    (UR_vector ur n n' en v v') ≃ 
    (l ≈ l').
Proof.
  intros. cbn. eapply equiv_compose; try apply UR_sized_list_irr.
  cbn. 
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - apply UR_vector_list_is_eq_fun.
  - apply UR_vector_list_is_eq_inv. 
  - intro Hv. simpl. induction Hv.
    + reflexivity.
    + simpl. assert (ap_S_section (ap S en) = ap (ap S) (ap_S_retraction en)). 
      apply IsIrr_IsHprop'. unfold IsIrr. intros. apply is_hset.
      rewrite X0. clear X0. eapply concat. 
      apply transport_UR_vector_cons_eq. apply ap.
      rewrite UR_vector_list_is_eq_inv_eq. auto.  
  - intro Hl. generalize dependent n'. induction v; destruct v'; intros; simpl. 
    + assert (en = idpath). apply is_hset. rewrite X0. cbn in *.
      symmetry. exact (UR_list_decompose _ _ _ Hl). 
    + destruct (zeroS _ en).
    + destruct (zeroS _ en^).
    + destruct (UR_list_decompose ur (h :: (vector_to_list A A (Equiv_id A) n n idpath v) .1)
                                  (h0 :: (vector_to_list B B (Equiv_id B) n0 n0 idpath v') .1) Hl).
      destruct x. rewrite e. clear e Hl.
      pose (ap_S_section en). rewrite e. set (inversionS n n0 en).
      clearbody e0. clear e en en_inv. rename e0 into en. 
      assert (ap_S_section (ap S en) = ap (ap S) (ap_S_retraction en)). 
       apply IsIrr_IsHprop'. unfold IsIrr. intros. apply is_hset.
       rewrite X0. eapply concat. apply ap. apply transport_UR_vector_cons_eq. 
       simpl. apply ap. simpl in IHv. specialize (IHv n0 en v' u0).
       rewrite UR_vector_list_is_eq_inv_eq. exact IHv. 
Defined.

Instance UR_vector_ A B `{UR A B} n n' en : UR (t A n) (t B n') :=
  {| ur := UR_vector ur _ _ en |}.

Definition URIsUR_vector {A B : Type} {H : ur A B}  (n n':nat) (en : n ≈ n')
           (v v':t A n) : (v = v') ≃ (v ≈ (↑ v')).
Proof.
  pose (einv := Equiv_inverse (equiv H)).
  eapply Equiv_inverse.
  eapply equiv_compose. eapply UR_vector_list_is_eq. 
  unfold univalent_transport. 
  pose (canA := ur_refl A). pose (canB := ur_refl B).
  refine (transport_eq (fun X => (Equiv_vector_list A A n n idpath v
   ≈ Equiv_vector_list B B n' n' idpath (Equiv_Vector A B (equiv H) n n' en v')) ≃ (X = _))
                       (e_sect (vector_to_list A A _ n n _) v) _).
  refine (transport_eq (fun X => (Equiv_vector_list A A n n idpath v
   ≈ Equiv_vector_list B B n' n' idpath (Equiv_Vector A B (equiv H) n n' en v')) ≃ (_ = X))
                       (e_sect (vector_to_list A A _ n n _) v') _).
  assert (vector_to_list B B (Equiv_id B) n' n' idpath
                         (Equiv_Vector_fun A B (equiv H) n n' en v')
          = ↑ (vector_to_list A A (Equiv_id A) n n idpath v')).
  { clear. destruct en. apply path_sigma_uncurried.
    unshelve eexists; [idtac | apply is_hset]. 
    destruct v'. reflexivity. cbn. apply ap. induction v'; cbn.
    - reflexivity.
    - apply ap. exact IHv'.   
  }
  cbn. rewrite X; clear X.
  set (vector_to_list A A (Equiv_id A) n n idpath v).
  set (vector_to_list A A (Equiv_id A) n n idpath v'). 
  clearbody s s0. clear v v'.
  eapply equiv_compose.
  apply Equiv_inverse. exact (@ur_coh _ _ _ _ (Ur_Coh (@FP_sized_list_ A B H n n' en)) s s0).
  apply (@isequiv_ap _ _ (@Equiv_list_vector A A canA n)). 
Defined.

Definition FP_Vector : Vector.t ≈ Vector.t.
  intros A B e. cbn in e. split. tc. 
  intros n n' en.
  unshelve eexists.
  - unshelve econstructor. refine (URIsUR_vector n n' en).  
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined.

Instance Equiv_Vector_instance : forall x y : Type, x ⋈ y -> forall n n' (e:n=n'), (Vector.t x n) ⋈ (Vector.t y n') :=
  fun x y e n n' en => ur_type (FP_Vector x y e) n n' en. 


#[export] Hint Extern 0 (Vector.t _ _ ⋈ _) => apply Equiv_vector_list_; simpl : typeclass_instances ur_typeclass_instances. 



(*! FP ap !*)

Instance UR_type_of_ap : UR (forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y)(forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y).
    typeclasses eauto with typeclass_instances. 
Defined. 

Definition FP_ap:  @ap ≈ @ap.
  intros A A' eA B B' eB f f' ef x x' ex y y' ey p p' ep. 
  cbn in *.
  induction ep. apply UR_idpath. 
Defined.


(*! FP Equiv !*)

(** The record [IsEquiv] has four components, so [issig4] can prove that it is equivalent to an iterated Sigma-type. *)

Instance issig_isequiv {A B : Type} (f : A -> B):
{ e_inv : B -> A & {
    e_sect : forall x : A, e_inv (f x) = x & {
    e_retr : forall y : B, f (e_inv y) = y &
    forall x : A, e_retr (f x) = ap f (e_sect x) }}} ≃ IsEquiv f.
issig (BuildIsEquiv A B f) (@e_inv A B f) (@e_sect A B f) (@e_retr A B f) (@e_adj A B f).
Defined. 

Instance issig_isequiv_inv {A B : Type} (f : A -> B):
  IsEquiv f ≃
{ e_inv : B -> A & {
    e_sect : forall x : A, e_inv (f x) = x & {
    e_retr : forall y : B, f (e_inv y) = y &
    forall x : A, e_retr (f x) = ap f (e_sect x) }}} := Equiv_inverse _.

Instance issig_equiv A B : { e_fun : A -> B &  IsEquiv e_fun }
                               ≃ (A ≃ B).
  issig (BuildEquiv A B) (@e_fun A B) (@e_isequiv A B).
Defined.

Instance issig_equiv' A B :  (A ≃ B) ≃ { e_fun : A -> B &  IsEquiv e_fun } :=
  Equiv_inverse _.

#[export] Hint Extern 0 (UR_eq _ _ _ _ _ _ _ _ _ _ _ ) => 
  erefine (FP_ap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) : typeclass_instances ur_typeclass_instances.

Definition FP_IsEquiv : @IsEquiv ≈ @IsEquiv.
Proof.
  cbn. split ; [typeclasses eauto | ]; intros.
  unshelve refine (UR_Type_Equiv _ _ _). cbn.
  unshelve refine (UR_Type_Equiv' _ _ _).
  erefine ((ur_type (@FP_Sigma _ _ _) _ _ _)); cbn ; intros .
  typeclasses eauto with typeclass_instances.
  split.
  typeclasses eauto with typeclass_instances.
  intros. erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn; intros.
  typeclasses eauto with typeclass_instances.
  split.
  typeclasses eauto with typeclass_instances.
  intros. erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn; intros.
  typeclasses eauto with typeclass_instances.
  split.
  typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
Defined. 

#[export] Hint Extern 0 (IsEquiv _ ⋈ IsEquiv _) => refine (ur_type (FP_IsEquiv _ _ _ _ _ _) _ _ _) : typeclass_instances ur_typeclass_instances. 

Definition FP_Equiv : @Equiv ≈ @Equiv.
Proof.
  cbn;   split ; [typeclasses eauto | ]; intros.
  unshelve refine (UR_Type_Equiv _ _ _). cbn. 
  unshelve refine (UR_Type_Equiv' _ _ _).
  erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn ; intros. tc.
  split; tc. 
Defined. 

#[export] Hint Extern 0 (UR (_ ≃ _) (_ ≃ _)) => refine (Ur (ur_type (FP_Equiv _ _ _) _ _ _)) : typeclass_instances ur_typeclass_instances.

(*! FP univalence !*)

Definition Isequiv_ur_hprop A A' B B' (H : A ⋈ A')(H' : B ⋈ B') (f:A->B) (g:A'->B')
           (e : IsEquiv f) (e' : IsEquiv g)
           (efg:f ≈ g) : e ≈ e'. 
  intros; apply ur_hprop. apply isequiv_hprop. 
Defined.   


Definition FP_Equiv_id : @Equiv_id ≈ @Equiv_id.
  intros A A' eA. unshelve eexists. cbn. auto.
  apply Isequiv_ur_hprop.
Defined. 


Definition FP_eq_to_equiv : @eq_to_equiv ≈ @eq_to_equiv.
  intros A A' eA B B' eB f f' ef. destruct ef. 
  apply FP_Equiv_id. 
Defined. 

Opaque eq_to_equiv. 

#[export] Hint Extern 0 (eq_to_equiv _ _ ≈ eq_to_equiv _ _) => refine (FP_eq_to_equiv _ _ _ _ _ _ _ _ _) : typeclass_instances ur_typeclass_instances.



Instance UR_univalence_type : UR (forall A B, IsEquiv (eq_to_equiv A B))
     (forall A B, IsEquiv (eq_to_equiv A B)).
unshelve erefine (@URForall _ _ _ _ _ _); cbn in *; intros .
tc. 
unshelve erefine (@URForall _ _ _ _ _ _); cbn in *; intros .
tc.
unshelve refine (Ur (ur_type (FP_IsEquiv _ _ _ _ _ _) _ _ _)).
tc. cbn; intros. refine (ur_type (FP_Equiv _ _ _) _ _ _); tc.
apply FP_eq_to_equiv.
Defined.

(* FP univalence *)

Definition FP_univalence : univalence ≈ univalence.
  intros A A' eA B B' eB. 
  apply Isequiv_ur_hprop.
Defined. 



#[export] Hint Extern 0 (URForall_Type_class ?A ?B ?F ?G) =>
(is_ground A; is_ground B; is_ground F; is_ground G; econstructor)
: typeclass_instances.


(* FP for fixpoints on nats *)

Definition fix_nat_1 : (fun P X0 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | S n => XS n (f n)
  end) ≈
       (fun P X0 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | S n => XS n (f n)
  end).
Proof. 
  cbn; intros. equiv_elim. 
Defined. 

Definition fix_nat_2 : (fun P X0 X1 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | S n => XS n (f n)
  end) ≈
       (fun P X0 X1 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | S n => XS n (f n)
  end).
Proof. 
  cbn; intros. repeat equiv_elim.
Defined. 

Definition fix_nat_3 : (fun P X0 X1 X2 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | 2 => X2
  | S n => XS n (f n)
  end) ≈
       (fun P X0 X1 X2 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | 2 => X2
  | S n => XS n (f n)
  end).
Proof. 
  cbn; intros. repeat equiv_elim.
Defined.

(* FP for canonical eq *)

Definition Canonical_eq_sig A :=   {can_eq : forall (x y : A), x = y -> x = y &
    forall x, can_eq x x idpath = idpath }.

Instance issig_Canonical_eq A : Canonical_eq_sig A ≃ Canonical_eq A.
Proof.
  unfold Canonical_eq_sig.  
  issig (Build_Canonical_eq A) (@can_eq A) (@can_idpath A).
Defined.

Instance issig_Canonical_eq_inv A : Canonical_eq A ≃ Canonical_eq_sig A :=
  Equiv_inverse _.

#[export] Hint Extern 0 => progress (unfold Canonical_eq_sig)  : typeclass_instances ur_typeclass_instances.

Definition FP_Canonical_eq : Canonical_eq ≈ Canonical_eq.
  univ_param_record.
Defined.

#[export] Hint Extern 0 (Canonical_eq _ ⋈ Canonical_eq _) => erefine (ur_type FP_Canonical_eq _ _ _); simpl
 : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (Canonical_eq _ ≃ Canonical_eq _) => erefine (ur_type FP_Canonical_eq _ _ _).(equiv); simpl
 : typeclass_instances ur_typeclass_instances.

Definition Svector A := {n : nat & t A n}.

Definition Snil {A} : Svector A := (O ; nil A).

Definition Svcons {A} a v : Svector A := (S v.1; vcons a v.2).

Instance Equiv_Svector_list (A B:Type) {H: A ≃ B} : Svector A ≃ list B.
Proof.
  unshelve econstructor; [idtac | unshelve eapply isequiv_adjointify].
  - intro v. exact (vector_to_list _ _ _ v.1 v.1 idpath v.2).1.
  - intro l. apply Equiv_inverse in H. exact (length l; list_to_vector _ _ _ (length l) _ idpath (l;idpath)).
  - intros [n v].
    pose proof (e_sect' (Equiv_vector_list _ _ n n idpath) v). cbn in X. 
    cbn. eapply path_sigma_uncurried.
    unshelve eexists.
    + exact ((vector_to_list A B H n n idpath v) .2).
    + cbn.
      change ((fun X : {l : list B & length l = n} =>
                list_to_vector B A (Equiv_inverse H) (length X.1)
    (length X.1) idpath
    (X.1; idpath) = transport_eq (fun n0 : nat => t A n0) (X.2)^ v)
                (vector_to_list A B H n n idpath v)).
      destruct (vector_to_list A B H n n idpath v).
      destruct e. cbn. exact X.
  - intro l. cbn.
    exact ((e_retr' (Equiv_vector_list _ _ (length l) _  idpath) (l;idpath))..1).
Defined. 

Instance Equiv_list_Svector (A B:Type) (H: A ≃ B) (H' := Equiv_inverse H)
  : list A ≃ Svector B := Equiv_inverse _.

Inductive UR_list_vect {A B} (R : A -> B -> Type) : list A -> Svector B -> Type :=
  UR_list_vect_nil : UR_list_vect R [] Snil
| UR_list_vect_cons : forall {a b l l'},
    (R a b) -> (UR_list_vect R l l') ->
    UR_list_vect R (a::l) (Svcons b l').

#[export] Hint Extern 0 (UR (list ?A) (Svector ?B)) => unshelve notypeclasses refine (@UR_list_vect _ _ _): typeclass_instances. 

#[export] Hint Extern 0 (UR_list_vect ?R [] Snil) => exact (UR_list_vect_nil R)  : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (UR_list_vect ?R (_::_) (Svcons _ _)) => unshelve refine (UR_list_vect_cons R _ _) : typeclass_instances ur_typeclass_instances.

Definition Equiv_list_length {A B:Type} (e : A ≈ B) (l:list B) :
  let l' := e_inv (Equiv_List A B (equiv e)) l in
  length l' = length l.
Proof.
  induction l; tc.
Defined.

Definition list_to_vector_Equiv_list (A B:Type) (e : A ≈ B) (l:list B) :
  let l' := e_inv (Equiv_List A B (equiv e)) l in
  (length l' ; list_to_vector A B (equiv e) (length l') (length l') idpath (l'; idpath))
  =
  (length l; list_to_vector B B (Equiv_id B) (length l) (length l) idpath (l; idpath)).
  apply path_sigma_uncurried. exists (Equiv_list_length e l).
  induction l; cbn.
  - reflexivity.
  - rewrite <- ap_inv. rewrite transport_vector. rewrite e_retr. now apply ap.
Defined. 

Definition UR_list_Svector_fun (A B:Type) (e : A ≈ B) (l : list A) (l':list B) :
  UR_list ur l l' ->
  UR_list_vect ur l
      (length l'; list_to_vector B B (Equiv_id B) (length l') (length l') idpath (l'; idpath)).
Proof.
  induction 1; cbn; try econstructor. cbn in IHX. 
  match goal with | H : UR_list_vect _ _ ?X |- _ => set (s := X) in * end.
  eapply (@UR_list_vect_cons _ _ _ _ _ _ s); auto.
Defined.

Definition UR_list_vect_decompose {A B} (R:A->B->Type) l v (e : UR_list_vect R l v) :
  match v return UR_list_vect R l v -> Type
  with (n;v) =>
       match l in list _, v as v in t _ n return UR_list_vect R l (n;v) -> Type
       with [],nil _ => fun e => e = UR_list_vect_nil R
       | a::l, cons _ a' n' v => fun e => { X : (R a a') * UR_list_vect R l (n';v) & e = UR_list_vect_cons R (fst X) (snd X)}
        | _,_ => fun _ => False end end e.
Proof.
  destruct e. reflexivity. cbn. destruct l'. exists (r,e). reflexivity.
Defined.

Definition UR_list_Svector_inv (A B:Type) (e : A ≈ B) (l : list A) (l':list B) :
  UR_list_vect ur l
      (length l'; list_to_vector B B (Equiv_id B) (length l') (length l') idpath (l'; idpath))
  -> UR_list ur l l'.
Proof.
  revert l'. 
  induction l;destruct l'; cbn; intro H. 
  - econstructor.
  - inversion H.
  - inversion H.
  - pose (H' := UR_list_vect_decompose _ _ _ H); cbn in H'.  econstructor.
    + exact (fst H'.1).
    + apply IHl. exact (snd H'.1).
Defined.

Definition FP_list_Svector
  : list ≈ Svector.
  unshelve econstructor. tc. intros A B e.
  unshelve refine {| equiv := Equiv_list_Svector _ _ e.(equiv) ; Ur := {| ur := @UR_list_vect A B _ |} |}.
  - apply ur. 
  - econstructor. intros.  
    eapply equiv_compose. apply (ur_coh (UR_Coh := Ur_Coh (FP_List.(ur_type) _ _ e))).
    cbn. refine (transport_eq (fun X => UR_list ur a
    (list_rect A (fun _ : list A => list B) []
       (fun (H0 : A) (_ : list A) (H2 : list B) => univalent_transport H0 :: H2) a') ≃ UR_list_vect ur a
      (length X;
      list_to_vector A B (Equiv_inverse (Equiv_inverse (equiv e))) (length X) 
                     (length X) idpath (X; idpath))) (e_sect' (Equiv_List _  _ _) a') _).
    match goal with | |- UR_list _ _ ?X ≃ _ => set X in * end. cbn in l. 
    change (UR_list ur a l
  ≃ UR_list_vect ur a
      (length (e_inv (Equiv_List A B (equiv e)) l);
      list_to_vector A B (Equiv_inverse (Equiv_inverse (equiv e)))
        (length (e_inv (Equiv_List A B (equiv e)) l))
        (length (e_inv (Equiv_List A B (equiv e)) l)) idpath
        (e_inv (Equiv_List A B (equiv e)) l; idpath))).
    rewrite Equiv_inverse_inverse. set (l' :=e_inv (Equiv_List A B (equiv e)) l).
    unfold l'. rewrite list_to_vector_Equiv_list. clearbody l. clear l' a'. 
    cbn. unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
    + apply UR_list_Svector_fun; auto.
    + apply UR_list_Svector_inv; auto.
    + intro H. induction H.
      * reflexivity. 
      * cbn. apply ap. exact IHUR_list.
    + revert l; induction a; destruct l; intro H.
      * symmetry. exact (UR_list_vect_decompose _ _ _ H).
      * inversion H.
      * inversion H.
      * pose (H' := UR_list_vect_decompose _ _ _ H). cbn in H'.
        eapply concat; try exact H'.2^. cbn. apply ap.
        exact (IHa l (snd H'.1)). 
  - apply Canonical_eq_gen.
Defined. 

#[export] Hint Extern 0 (list _ ⋈ Svector _) => apply FP_list_Svector : typeclass_instances ur_typeclass_instances. 

Definition FP_Svector_list
  : Svector ≈ list.
  econstructor. tc. intros A B e.
  pose (UR_Type_Inverse _ _ e).
  eapply UR_Type_Inverse. tc.
Defined. 

#[export] Hint Extern 0 (Svector _ ⋈ list _) => apply FP_Svector_list : typeclass_instances ur_typeclass_instances. 

Definition Svect_rect : forall (A : Type) (P : Svector A -> Type),
    P Snil -> (forall (a : A) (l : Svector A), P l -> P (Svcons a l)) -> forall l : Svector A, P l.
Proof.
  intros A P Pnil Pcons [n v].  induction v as [ | a n v IH].
  - exact Pnil. 
  - exact (Pcons a (n;v) IH).
Defined. 

Definition FP_List_vect_rect : @list_rect ≈ @Svect_rect.
Proof.
  cbn. intros.
  induction H3.
  - tc.
  - destruct l'.  typeclasses eauto with typeclass_instances. 
Defined. 


*)