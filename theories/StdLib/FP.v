(************************************************************************)
(* This file contains basic definitions of UR that are helpful for many examples  *)
(************************************************************************)

Set Polymorphic Inductive Cumulativity.

Set Universe Polymorphism.

Unset Universe Minimization ToSet.

Set Warnings "+bad-template-constraint".

Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.UR Record.
From Stdlib Require Import String.

Module Interface10.

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
  tc_hint_for univalent (@sigT) Corelib__Init__Specif__sigT_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@sigT) Corelib__Init__Specif__sigT_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__existT : forall (y : Type) (y0 : y -> Type) (y1 : y), y0 y1 -> imported_Corelib__Init__Specif__sigT (fun H : y => y0 H).
Parameter Corelib__Init__Specif__existT_iso : iso_statement (@existT) (@imported_Corelib__Init__Specif__existT).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@existT) Corelib__Init__Specif__existT_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@existT) Corelib__Init__Specif__existT_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__projT1 : forall (y : Type) (y0 : y -> Type), imported_Corelib__Init__Specif__sigT (fun H : y => y0 H) -> y.
Parameter Corelib__Init__Specif__projT1_iso : iso_statement (@projT1) (@imported_Corelib__Init__Specif__projT1).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@projT1) Corelib__Init__Specif__projT1_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@projT1) Corelib__Init__Specif__projT1_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sigTD_rect : import_of (@sigT_rect).

Parameter Corelib__Init__Specif__sigTD_rect_iso : @sigT_rect ≈[ _] imported_Corelib__Init__Specif__sigTD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@sigT_rect) Corelib__Init__Specif__sigTD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@sigT_rect) Corelib__Init__Specif__sigTD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(** -- projT2: this triggers the complex type unification failure ------------ *)

Parameter imported_Corelib__Init__Specif__projT2 : import_of (@UnivalentParametricity.theories.HoTT.projT2).


End Interface10.


(*! FP for Sigma !*)

#[universes(collapse_sort_variables=no)]
Definition exist_eq {A P} (a a':A) (l : P a) (l' : P a') (e : a = a') :
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
    intros a l. clear E. set (e_sect (e_fun (equiv e)) a). cbn in e'.
    clearbody p. set (e_fun (equiv (UR_Type_Inverse A A' e))
              (e_fun (equiv e) a)). set (e_fun (equiv e) a).
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
  - unshelve erefine (@PRSigma _ _ _ _ _ _ _); intros; shelve_non_PR. eapply H. eapply H0. tc. 
  - eapply Equiv_Sigma. tc.
  - intros [? ?] [? ?]; cbn in *.
    split; intro e.
    + apply isequiv_path_sigma in e. destruct e as [e1 e2].
      unshelve eexists.
      eapply (fst (Ur_Coh _ _ _)); eauto.
      cbn in e1. destruct e1.
      eapply (fst (Ur_Coh _ _ _)). now rewrite transport_eq_gen_refl in e2.
    + destruct e as [e1 e2]. eapply path_sigma_uncurried.
      unshelve eexists; cbn.
      unshelve eapply (snd (Ur_Coh _ _ _)); eauto.
      unfold univalent_transport in *.
      unshelve eapply (snd (Ur_Coh _ _ _)); cbn.
      2:{ eapply H0; eauto. } 
      unfold univalent_transport.
      pose proof (snd (Ur_Coh _ _ _) e1). revert x2 e1 e2. 
      rewrite H1. intros x2 e1 e2.
      rewrite transport_eq_gen_refl.
      pose (Ur_Coh (H0 x3 (univalent_transport x3) e1)).
      revert e2.
      now rewrite <- (Ur_Irr _ _ H _ _ (ur_refl H x3) e1).
  - intros [? ?] [? ?] [? ?] [? ?]; cbn in *.
    eapply path_sigma_uncurried; unshelve eexists; cbn; eapply Ur_Irr.
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
intros A B H P Q HPQ P' Q' HPQ'. cbn in *. intros.
destruct x0, y0, H1; cbn in *. apply H0.
Defined.

#[universes(collapse_sort_variables=no)]
Definition FP_sigT_rect_univ : @sigT_rect ≈u @sigT_rect.
Proof.
intros A B H P Q HPQ P' Q' HPQ'. cbn in *. intros.
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
  - intros X. exact (e_fun e (fst X), e_fun e' (snd X)).
  - intros X. exact (e_inv (e_fun e) (fst X), e_inv (e_fun e') (snd X)).
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
- unshelve erefine (@PRProd _ _ _ _ _ _ _); intros; shelve_non_PR. eapply H. eapply H0.
- unshelve refine (Equiv_prod _ _ _ _ _ _); tc.
- intros X X'. cbn.
  split; intro e.
  + eapply isequiv_path_prod in e; cbn in *. destruct e.
    unshelve eexists; eapply (fst (Ur_Coh _ _ _)); eauto.
  + destruct e as [e1 e2]. eapply path_prod_uncurried.
    unshelve eexists; cbn in *.
    unshelve eapply (snd (Ur_Coh _ _ _)). shelve. exact H. exact e1.
    unshelve eapply (snd (Ur_Coh _ _ _)). shelve. exact H0. exact e2.
- intros [? ?] [? ?] [? ?] [? ?]; cbn in *.
  eapply path_prod_uncurried; unshelve eexists; cbn; eapply Ur_Irr.
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

#[universes(collapse_sort_variables=no)]
Definition univ_eq : (fun A => @eq A) ≈u @path.
Proof.
cbn; intros. unshelve econstructor.
  - eapply Equiv_iff_Prop. split; intro e.
    + eapply (snd (alt_UR_Coh _ _ _)) in H0.
      eapply (snd (alt_UR_Coh _ _ _)) in H1.
      destruct e.
      pose proof (H1^@ H0)^. eapply ap_inv_equiv; eauto. eapply e_isequiv.
    + eapply (snd (alt_UR_Coh _ _ _)) in H0.
      eapply (snd (alt_UR_Coh _ _ _)) in H1.
      destruct (H0@ ap _ e @ H1^); reflexivity.
  - intros e e'. split; intro E.
    + cbn. destruct E, e. cbn in *.
      match goal with | |- PR_eq _ _ _ _ _ _ _ _ _ _ ?X => set (X) end.
      destruct p. rewrite (Ur_Irr _ _ _ _ _ H0 H1). econstructor.
    + eapply PI.
  - intros ? ? ?. reflexivity.
Defined.

#[universes(collapse_sort_variables=no)]
Definition univ_eq' : 
  (fun A : Prop => @eq A) ≈u @path.
Proof.
cbn; intros. unshelve econstructor.
  - eapply Equiv_iff_Prop. split; intro e.
    + reflexivity.
    + eapply (snd (alt_UR_Coh _ _ _)) in H0.
      eapply (snd (alt_UR_Coh _ _ _)) in H1.
      destruct (H0@ ap _ e @ H1^); reflexivity.
  - intros e e'. split; intro E.
    + cbn. destruct E, e. cbn in *.
      match goal with | |- PR_eq _ _ _ _ _ _ _ _ _ _ ?X => set (X) end.
      destruct p. rewrite (Ur_Irr _ _ _ _ _ H0 H1). econstructor.
    + eapply PI.
  - intros ? ? ?. reflexivity.
Defined.

(* #[export] Hint Extern 0 (UR_Type (eq _ _) _) =>
  unshelve first [eapply univ_eq' | eapply univ_eq] ; intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (eq _ _ ≈[ _] _) =>
  unshelve first [eapply univ_eq' | eapply univ_eq] ; intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.
 *)
#[universes(collapse_sort_variables=no)]
Definition FP_eq : (fun A => @eq A) ≈p @path.
Proof.
cbn; intros. eapply PREq; tc.
Defined.

From Stdlib Require Import Logic.JMeq.

#[universes(collapse_sort_variables=no)]
Inductive SJMeq (A : Type) (x : A) : forall (B : Type), B -> SProp :=
  SJMeq_refl : @SJMeq A x A x.

Arguments SJMeq_refl {A x}.
Arguments SJMeq {A} x {B} _.

#[universes(collapse_sort_variables=no)]
Inductive PR_JMeq (A_1 A_2 : Type) (A_R : A_1 -> A_2 -> Type) 
    (x_1 : A_1) (x_2 : A_2) (x_R : A_R x_1 x_2)
  :
   forall (B_1 B_2 : Type) (B_R : B_1 -> B_2 -> Type)
          (y_1 : B_1) (y_2 : B_2), B_R y_1 y_2 ->
   JMeq x_1 y_1 -> SJMeq x_2 y_2 -> SProp :=
   PR_JM_refl : PR_JMeq A_1 A_2 A_R x_1 x_2 x_R A_1 A_2 A_R x_1 x_2 x_R JMeq_refl SJMeq_refl.

#[universes(collapse_sort_variables=no)]
Instance PJMEq (A_1 A_2 : Type) (A_R : A_1 ≈p A_2)
  (x_1 : A_1) (x_2 : A_2) (x_R : x_1 ≈p x_2)
  (B_1 B_2 : Type) (B_R : B_1 ≈p B_2)
  (y_1 : B_1) (y_2 : B_2) (y_R : y_1 ≈p y_2) : 
  PR@{Prop SProp SProp;_ _ _} plain (JMeq x_1 y_1) (SJMeq x_2 y_2)  :=
  {| pr := fun e e' => PR_JMeq _ _ _ _ _ x_R _ _ _ _ _ y_R e e' |}.

Lemma JMeq_eq_dep (A : Type) (x : A) (B : Type) (y : B) :
  JMeq x y -> {e : A = B & e # x = y}.
Proof.
  intros e. destruct e. exists idpath. reflexivity.
Qed.

Lemma eq_dep_JMeq (A : Type) (x : A) (B : Type) (y : B) :
  {e : A = B & e # x = y} -> JMeq x y.
Proof.
  intros [e e']. destruct e. cbn in *. destruct e'. 
  econstructor.
Qed.

Lemma SJMeq_eq_dep (A : Type) (x : A) (B : Type) (y : B) :
  SJMeq x y -> {e : A = B & e # x = y}:SProp.
Proof.
  intros e. destruct e. exists idpath. reflexivity.
Qed.

Lemma eq_dep_SJMeq (A : Type) (x : A) (B : Type) (y : B) :
  ({e : A = B & e # x = y}:SProp) -> SJMeq x y.
Proof.
  intros [e e']. destruct e. cbn in *. destruct e'. 
  econstructor.
Qed.

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

(*
  Lemma comm_plus' : forall n m, plus' n m = plus' m n.
  Proof.
    unshelve eapply (e_fun (equiv _) _); [| | exact comm_plus]; tc.
  Qed.
*)
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

  #[universes(collapse_sort_variables=no)]
  Goal decorated ≈u decorated'.
  Proof.
  unshelve econstructor.
  - exact PR_decorated.
  - intros ? ? . cbn.
    split.
    + eapply ap.
    + eapply ap_inv_equiv. apply dec_eq.
  - intros ? ? ?; reflexivity. 
  Defined.

End SoftwareFoundations.

(*! nat !*)

Hint Extern 0 (0 ≈[ _] 0) => exact Oϵ : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (natϵ 0 0) => exact Oϵ : typeclass_instances ur_typeclass_instances.

Definition Sϵ' n m: n ≈p m -> S n ≈p S m := Sϵ.

Hint Extern 0 (S _ ≈[ _] S _) => apply Sϵ' : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (natϵ (S _) (S _)) => apply Sϵ' : typeclass_instances ur_typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition FP_nat : nat ≈u nat.
Proof.
  unshelve econstructor.
  - eapply Equiv_id.
  - intros n m; split.
    + destruct 1. induction n; intros; econstructor; eauto.
    + cbn. induction 1; [econstructor | apply ap; eauto].
  - intros ? ? ?; reflexivity.
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

#[universes(collapse_sort_variables=no)]
Definition FP_bool : bool ≈u bool.
Proof.
  unshelve econstructor.
  - eapply Equiv_id.
  - intros b b'; split.
    + destruct 1. destruct b; intros; econstructor; eauto.
    + cbn. induction 1; econstructor.
  - intros ? ? ?; reflexivity.
Defined.

(*! False !*)

#[universes(collapse_sort_variables=no)]
Definition FP_Empty : (Empty:Type) ≈u (Empty:Type).
Proof.
unshelve econstructor.
  - eapply Equiv_id.
  - intros b b'; split.
    + destruct 1. destruct b; intros; econstructor; eauto.
    + cbn. induction 1; econstructor.
  - intros ? ? ?; reflexivity.
Defined.

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


Parameter imported_Corelib__Init__Datatypes__nat : import_of nat.
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement nat imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : import_of 0.
Parameter Corelib__Init__Datatypes__O_iso : iso_statement 0 imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : import_of (S).
Parameter Corelib__Init__Datatypes__S_iso : iso_statement S imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__ex : import_of (@ex).
Parameter Corelib__Init__Logic__ex_iso : iso_statement (@ex) imported_Corelib__Init__Logic__ex.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Corelib__Numbers__BinNums__Z : Type.
Parameter Corelib__Numbers__BinNums__Z_iso : iso_statement BinNums.Z imported_Corelib__Numbers__BinNums__Z.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_IsomorphismChecker__EqualityLemmas__iterate1Z : forall y : Type, (y -> y) -> imported_Corelib__Numbers__BinNums__Z -> y -> y.
Parameter IsomorphismChecker__EqualityLemmas__iterate1Z_iso : @iterate1Z ≈[ _] imported_IsomorphismChecker__EqualityLemmas__iterate1Z.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@iterate1Z) IsomorphismChecker__EqualityLemmas__iterate1Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@iterate1Z) IsomorphismChecker__EqualityLemmas__iterate1Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__Auto__silly2D_eauto : import_of (@silly2_eauto).
Parameter LF__Auto__silly2D_eauto_iso : iso_statement (@silly2_eauto) imported_LF__Auto__silly2D_eauto.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@silly2_eauto) LF__Auto__silly2D_eauto_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@silly2_eauto) LF__Auto__silly2D_eauto_iso goal_lhs : typeclass_instances ur_typeclass_instances.
End Interface.


Module Type Interface' (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : import_of nat.
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement nat imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : import_of 0.

Parameter Corelib__Init__Datatypes__O_iso : iso_statement 0 imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : import_of S.
Parameter Corelib__Init__Datatypes__S_iso : iso_statement S imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Parameter imported_LF__IndProp__ev : imported_Corelib__Init__Datatypes__nat -> SProp.
Parameter LF__IndProp__ev_iso : ev ≈u imported_LF__IndProp__ev.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@ev) LF__IndProp__ev_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@ev) LF__IndProp__ev_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__evD_0 : import_of (@ev_0).
Parameter LF__IndProp__evD_0_iso : iso_statement (ev_0) imported_LF__IndProp__evD_0.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@ev_0) LF__IndProp__evD_0_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@ev_0) LF__IndProp__evD_0_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface'.

Lemma equal_f {X Y} {f g : X -> Y} a : eq f g -> eq (f a) (g a).
Proof. 
destruct 1. reflexivity.
Qed.

(* Parameter imported_equal_f : import_of (@equal_f).*)

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
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_rect : import_of (@Corelib.Init.Logic.eq_rect).
Parameter Corelib__Init__Logic__eqD_rect_iso : iso_statement (@Corelib.Init.Logic.eq_rect) imported_Corelib__Init__Logic__eqD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq : import_of (@eq_rect_eq).
Parameter Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso : iso_statement (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq_Prop : import_of (fun A:Prop => @Corelib.Init.Logic.eq A).
Parameter Corelib__Init__Logic__eq_iso_Prop : iso_statement (fun A:Prop => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq_Prop.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A:Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A:Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Axiom proof_irrelevance : forall (P : Prop) (p q : P), eq p q.

Parameter imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance : import_of (@proof_irrelevance).
Parameter Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso : iso_statement (@proof_irrelevance) imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@proof_irrelevance) Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@proof_irrelevance) Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : iso_statement (@Corelib.Init.Logic.False) imported_Corelib__Init__Logic__False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__iff_iso : iso_statement (@Corelib.Init.Logic.iff) imported_Corelib__Init__Logic__iff.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__regD_exp : import_of (@reg_exp).
Parameter LF__IndProp__regD_exp_iso : iso_statement (@reg_exp) imported_LF__IndProp__regD_exp.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Set Warnings "-bad-template-constraint".

Parameter imported_LF__IndProp__EmptySet : forall y : Type, imported_LF__IndProp__regD_exp y.
Parameter LF__IndProp__EmptySet_iso : iso_statement (@EmptySet) imported_LF__IndProp__EmptySet.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun T => @EmptySet T) LF__IndProp__EmptySet_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun T => @EmptySet T) LF__IndProp__EmptySet_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Set Warnings "+bad-template-constraint".

Parameter imported_LF__Poly__list : Type -> Type.
Parameter LF__Poly__list_iso : iso_statement (@list) imported_LF__Poly__list.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(*
Parameter imported_LF__IndProp__expD_match : forall y : Type, imported_LF__Poly__list y -> imported_LF__IndProp__regD_exp y -> SProp.
Parameter LF__IndProp__expD_match_iso : @exp_match ≈[ _] imported_LF__IndProp__expD_match.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@LF.IndProp.exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@LF.IndProp.exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) Ascii.ascii imported_Stdlib__Strings__Ascii__ascii).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__string : Type.
Parameter LF__IndProp__string_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) IndProp.string imported_LF__IndProp__string).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@LF.IndProp.string) LF__IndProp__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@LF.IndProp.string) LF__IndProp__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__nullD_matchesD_none : import_of (@LF.IndProp.null_matches_none).
Parameter LF__IndProp__nullD_matchesD_none_iso : iso_statement (@LF.IndProp.null_matches_none) imported_LF__IndProp__nullD_matchesD_none.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@LF.IndProp.null_matches_none) LF__IndProp__nullD_matchesD_none_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@LF.IndProp.null_matches_none) LF__IndProp__nullD_matchesD_none_iso goal_lhs : typeclass_instances ur_typeclass_instances.
*)
End Interface''.

Module Type Interface2 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_rect : import_of (@Corelib.Init.Logic.eq_rect).
Parameter Corelib__Init__Logic__eqD_rect_iso : iso_statement (@Corelib.Init.Logic.eq_rect) imported_Corelib__Init__Logic__eqD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq : import_of (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq).
Parameter Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso : iso_statement (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) imported_Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq) Stdlib__Logic__Eqdep__EqD_rectD_eq__eqD_rectD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface2.

Module Type Interface3 (Import args : Args).

Inductive Singleton (A : Type) : A -> Type :=
  MkSingleton : forall a, Singleton a.

Parameter imported_parseque__Running__Singleton : forall y : Type, y -> Type.
Parameter parseque__Running__Singleton_iso : iso_statement (@Singleton) imported_parseque__Running__Singleton.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Singleton) parseque__Running__Singleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Singleton) parseque__Running__Singleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_parseque__Running__MkSingleton : forall (y : Type) (y0 : y), imported_parseque__Running__Singleton y0.
Parameter parseque__Running__MkSingleton_iso : iso_statement (@MkSingleton) imported_parseque__Running__MkSingleton.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@MkSingleton) parseque__Running__MkSingleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@MkSingleton) parseque__Running__MkSingleton_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_parseque__Running__SingletonD_ind : import_of (@Singleton_ind).
Parameter parseque__Running__SingletonD_ind_iso : iso_statement (@Singleton_ind) imported_parseque__Running__SingletonD_ind.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Singleton_ind) parseque__Running__SingletonD_ind_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Singleton_ind) parseque__Running__SingletonD_ind_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface3.

Module Type Interface4 (Import args : Args).


Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : iso_statement (@Corelib.Init.Datatypes.bool) imported_Corelib__Init__Datatypes__bool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : false ≈[ _] imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__negb : imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__negb_iso : negb ≈[ _] imported_Corelib__Init__Datatypes__negb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.negb) Corelib__Init__Datatypes__negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.negb) Corelib__Init__Datatypes__negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : iso_statement (@Corelib.Init.Datatypes.bool_rect) imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent(@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent(@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Bool__Bool__eqb : imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool.
Parameter Stdlib__Bool__Bool__eqb_iso : Bool.eqb ≈[ _] imported_Stdlib__Bool__Bool__eqb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent(@Stdlib.Bool.Bool.eqb) Stdlib__Bool__Bool__eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Bool.Bool.eqb) Stdlib__Bool__Bool__eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Lemma eqb_neg_distr_r: forall b1 b2,
    eq (Bool.eqb b1 (negb b2)) (negb (Bool.eqb b1 b2)).
Proof. intros. destruct b1, b2; simpl; reflexivity. Qed.


Parameter imported_SECF__Noninterference__eqbD_negD_distrD_r : import_of (@eqb_neg_distr_r).
Parameter SECF__Noninterference__eqbD_negD_distrD_r_iso : iso_statement (@eqb_neg_distr_r) imported_SECF__Noninterference__eqbD_negD_distrD_r.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent(@eqb_neg_distr_r) SECF__Noninterference__eqbD_negD_distrD_r_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@eqb_neg_distr_r) SECF__Noninterference__eqbD_negD_distrD_r_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Lemma eqb_true_b : forall b : bool, eq (Bool.eqb true b) b.
Proof.
destruct b; reflexivity.
Qed.

Parameter imported_Stalmarck__Algorithm__BoolAux__eqbD_trueD_b : import_of (@eqb_true_b).
Parameter Stalmarck__Algorithm__BoolAux__eqbD_trueD_b_iso : iso_statement (@eqb_true_b) imported_Stalmarck__Algorithm__BoolAux__eqbD_trueD_b.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent(@eqb_true_b) Stalmarck__Algorithm__BoolAux__eqbD_trueD_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@eqb_true_b) Stalmarck__Algorithm__BoolAux__eqbD_trueD_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface4.

Lemma eqb_true_b : forall b : bool, eq (Bool.eqb true b) b.
Proof. now destruct b. Qed.

Module Type Interface5 (Import args : Args).

  Parameter imported_bool : Type.
  Parameter bool_iso :
    @UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_bool.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for univalent (@bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
    tc_hint_for k (@bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_false : imported_bool.
  Parameter false_iso : false ≈[ _ ] imported_false.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for univalent (@false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
    tc_hint_for k (@false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_true : imported_bool.
  Parameter true_iso : true ≈[ _ ] imported_true.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for univalent (@true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
    tc_hint_for k (@true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_bool_rect :
    forall y : imported_bool -> Type,
      y imported_true ->
      y imported_false ->
      forall y0 : imported_bool, y y0.
  Parameter bool_rect_iso : bool_rect ≈[ _ ] imported_bool_rect.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for univalent (@bool_rect) bool_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
    tc_hint_for k (@bool_rect) bool_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_eq : forall y : Type, y -> y -> SProp.
  Parameter eq_iso : iso_statement (@eq) imported_eq.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for univalent (@eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
    tc_hint_for k (@eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_eqb :
    imported_bool -> imported_bool -> imported_bool.
  Parameter eqb_iso : Bool.eqb ≈[ _ ] imported_eqb.
  #[local] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
    tc_hint_for univalent (@Bool.eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[local] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
    tc_hint_for k (@Bool.eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

  Parameter imported_eqb_true_b : import_of (eqb_true_b).
  Parameter eqb_true_b_iso : iso_statement eqb_true_b imported_eqb_true_b.
  #[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (eqb_true_b) eqb_true_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (eqb_true_b) eqb_true_b_iso goal_lhs : typeclass_instances ur_typeclass_instances.
End Interface5.


Module Type Interface6 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : iso_statement (@Corelib.Init.Datatypes.bool) imported_Corelib__Init__Datatypes__bool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : iso_statement (@Corelib.Init.Datatypes.false) imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : Type -> Type.
Parameter Corelib__Init__Datatypes__option_iso : iso_statement (@Corelib.Init.Datatypes.option) imported_Corelib__Init__Datatypes__option.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__Some : forall y : Type, y -> imported_Corelib__Init__Datatypes__option y.
Parameter Corelib__Init__Datatypes__Some_iso : iso_statement (@Corelib.Init.Datatypes.Some) imported_Corelib__Init__Datatypes__Some.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : bool_rect ≈[ _] imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : iso_statement (@Corelib.Init.Logic.False) imported_Corelib__Init__Logic__False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : iso_statement (@Stdlib.Strings.String.string) imported_Stdlib__Strings__String__string.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition total_map (A : Type) : Type := string -> A.

(* #[export] Hint Extern 1 => progress (unfold total_map) : typeclass_instances ur_typeclass_instances.
Defnition imported_SECF__Maps__totalD_map A := imported_Stdlib__Strings__String__string -> A. *)

Parameter imported_SECF__Maps__totalD_map : Type -> Type.
Parameter SECF__Maps__totalD_map_iso : iso_statement (@total_map) imported_SECF__Maps__totalD_map.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@total_map) SECF__Maps__totalD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@total_map) SECF__Maps__totalD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Definition partial_map (A : Type) := total_map (option A).

(* #[export] Hint Extern 1 => progress (unfold partial_map) : typeclass_instances ur_typeclass_instances.
Definition imported_SECF__Maps__partialD_map A := imported_SECF__Maps__totalD_map (imported_Corelib__Init__Datatypes__option). *)

Parameter imported_SECF__Maps__partialD_map : Type -> Type.
Parameter SECF__Maps__partialD_map_iso : iso_statement (@partial_map) imported_SECF__Maps__partialD_map.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@partial_map) SECF__Maps__partialD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@partial_map) SECF__Maps__partialD_map_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, eq (m x) (Some v) -> eq (m' x) (Some v).


Parameter imported_SECF__Maps__includedin : forall y : Type,
  (imported_SECF__Maps__partialD_map y) -> (imported_SECF__Maps__partialD_map  y) -> SProp.
Parameter SECF__Maps__includedin_iso : iso_statement (@includedin) imported_SECF__Maps__includedin.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) : string -> A :=
  fun x' => if String.eqb x x' then v else m x'.

Definition t_update' {A : Type} (m : total_map A)
                    (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Parameter imported_SECF__Maps__tD_update : forall y : Type, (imported_SECF__Maps__totalD_map y) -> imported_Stdlib__Strings__String__string -> y -> imported_Stdlib__Strings__String__string -> y.
Parameter SECF__Maps__tD_update_iso : iso_statement (@t_update) imported_SECF__Maps__tD_update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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

Parameter imported_SECF__Maps__tD_updateD_eq : import_of t_update_eq.
Parameter SECF__Maps__tD_updateD_eq_iso : t_update_eq ≈[ _] imported_SECF__Maps__tD_updateD_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  eq ((x1 !-> v ; m) x2) (m x2).
Proof.
  (* FILL IN HERE *) Admitted.

Fail Parameter imported_SECF__Maps__tD_updateD_neq : import_of t_update_neq.

End Interface6.


Module Type Interface7 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : false ≈[ _] imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : Type -> Type.
Parameter Corelib__Init__Datatypes__option_iso : iso_statement (@option) imported_Corelib__Init__Datatypes__option.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__Some : forall y : Type, y -> imported_Corelib__Init__Datatypes__option y.
Parameter Corelib__Init__Datatypes__Some_iso : iso_statement (@Some) imported_Corelib__Init__Datatypes__Some.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.Some) Corelib__Init__Datatypes__Some_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : bool_rect ≈[ _] imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool_rect) Corelib__Init__Datatypes__boolD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : iso_statement (@False) imported_Corelib__Init__Logic__False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : iso_statement (@String.string) imported_Stdlib__Strings__String__string.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@includedin) SECF__Maps__includedin_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) : string -> A :=
  fun x' => if String.eqb x x' then v else m x'.

Definition t_update' {A : Type} (m : total_map A)
                    (x : string) (v : A) : total_map A :=
  fun x' => if String.eqb x x' then v else m x'.

Parameter imported_SECF__Maps__tD_update : forall y : Type, (imported_SECF__Maps__totalD_map y) -> imported_Stdlib__Strings__String__string -> y -> imported_Stdlib__Strings__String__string -> y.
Parameter SECF__Maps__tD_update_iso : @t_update ≈[ _] imported_SECF__Maps__tD_update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@t_update) SECF__Maps__tD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@t_update_eq) SECF__Maps__tD_updateD_eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  eq ((x1 !-> v ; m) x2) (m x2).
Proof.
  (* FILL IN HERE *) Admitted.
Parameter imported_SECF__Maps__tD_updateD_neq : import_of t_update_neq.
Parameter SECF__Maps__tD_updateD_neq_iso : iso_statement t_update_neq imported_SECF__Maps__tD_updateD_neq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@t_update_neq) SECF__Maps__tD_updateD_neq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@t_update_neq) SECF__Maps__tD_updateD_neq_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Parameter imported_SECF__Maps__update : import_of (@update).
Parameter SECF__Maps__update_iso : iso_statement (@update) imported_SECF__Maps__update.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@update) SECF__Maps__update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@update) SECF__Maps__update_iso goal_lhs : typeclass_instances ur_typeclass_instances.


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
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@includedin_update) SECF__Maps__includedinD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@includedin_update) SECF__Maps__includedinD_update_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface7.

Definition STrue_UR : True ≈u Squash True.
Proof.
cbn. unshelve econstructor.
- econstructor. intros. exact (Squash True).
- eapply Equiv_iff_Prop. split; intros; repeat econstructor.
- intros ?; split; intros; cbn in *; try repeat econstructor. destruct a, a'; reflexivity.
- intros ?; reflexivity.
Defined.

Hint Extern 1 (UR_Type True _) => eapply STrue_UR : typeclass_instances ur_typeclass_instances.

#[universes(polymorphic,collapse_sort_variables=no)]
Goal
{B : _& @UR.pr _ _ _ (UR.PR_Type UR.univalent) (True) B}.
Proof.
eexists. cbn; tc.
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
  tc_hint_for univalent (@Corelib.Init.Datatypes.bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.bool) bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_false : imported_bool.
Parameter false_iso : false ≈u imported_false.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Datatypes.false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.false) false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_negb : imported_bool -> imported_bool.
Parameter negb_iso : negb ≈[_] imported_negb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Datatypes.negb) negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.negb) negb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_true : imported_bool.
Parameter true_iso : true ≈[_] imported_true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Datatypes.true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.true) true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_False : SProp.
Parameter False_iso : @UR.pr _ _ _ (UR.PR_Type UR.univalent) False imported_False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Logic.False) False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Logic.False) False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
     (fun A => @eq A) imported_eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Logic.eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Logic.eq) eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_not : SProp -> SProp.
Parameter not_iso :
  (@UR.pr _ _ _
     (@UR.URArrow UR.univalent Prop SProp Prop SProp (UR.PR_Type UR.univalent)
        (UR.PR_Type UR.univalent))
     not imported_not).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Logic.not) not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Logic.not) not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_reflect : SProp -> imported_bool -> Type.
Parameter reflect_iso : reflect ≈[_] imported_reflect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Datatypes.reflect) reflect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.reflect) reflect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_addb : imported_bool -> imported_bool -> imported_bool.
Parameter addb_iso : addb ≈[_] imported_addb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@addb) addb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@addb) addb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_eqb : imported_bool -> imported_bool -> imported_bool.
Parameter eqb_iso : eqb ≈[_] imported_eqb.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@eqb) eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
  tc_hint_for univalent (@pred) pred_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@pred) pred_iso goal_lhs : typeclass_instances ur_typeclass_instances.
(*
#[export] Hint Extern 1 => progress (unfold pred) : typeclass_instances ur_typeclass_instances.
Definition imported_pred := fun T => T -> imported_bool. *)

Parameter imported_eq_axiom : forall y : Type, (y -> imported_pred y) -> Type.
Parameter eq_axiom_iso : eq_axiom ≈u imported_eq_axiom.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for (@eq_axiom) eq_axiom_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@eq_axiom) eq_axiom_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
  tc_hint_for univalent (@Corelib.Init.Datatypes.bool)
    bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.bool)
    bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_nat : Type.
Parameter nat_iso :
  (@UR.pr _ _ _ (UR.PR_Type UR.univalent)
     nat imported_nat).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Datatypes.nat)
    nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.nat)
    nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_true : imported_bool.
Parameter true_iso : true ≈[_] imported_true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Datatypes.true)
    true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Datatypes.true)
    true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_eq : forall y : Type, y -> y -> SProp.
Parameter eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Logic.eq)
    eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Logic.eq)
    eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_ex : forall y : Type, (y -> SProp) -> SProp.
Parameter ex_iso : iso_statement (@Corelib.Init.Logic.ex) imported_ex.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@Corelib.Init.Logic.ex)
    ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@Corelib.Init.Logic.ex)
    ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_key : Type.
Parameter key_iso : iso_statement key imported_key.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@key)
    key_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@key)
    key_iso goal_lhs : typeclass_instances ur_typeclass_instances.


(* Definition imported_key := nat.

#[export] Hint Extern 1 => progress (unfold key) : typeclass_instances ur_typeclass_instances. *)

Parameter imported_tree : Type -> Type.
Parameter tree_iso : iso_statement (@tree) imported_tree.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@tree)
    tree_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@tree)
    tree_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_bound : import_of (@bound).
Parameter bound_iso : iso_statement (@bound) imported_bound.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@bound)
    bound_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@bound)
    bound_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_lookup : import_of (@lookup).
Parameter lookup_iso : iso_statement (@lookup) imported_lookup.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) =>
  tc_hint_for univalent (@lookup)
    lookup_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for k (@lookup)
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

Parameter imported_Corelib__Init__Logic__True : import_of True.
Parameter Corelib__Init__Logic__True_iso : iso_statement True imported_Corelib__Init__Logic__True.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.True) Corelib__Init__Logic__True_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.True) Corelib__Init__Logic__True_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__and : import_of (@and).
Parameter Corelib__Init__Logic__and_iso : iso_statement (@and) imported_Corelib__Init__Logic__and.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem match_ex2 : and True True.
Proof.
  match goal with
  | [ |- True ] => apply I
  | [ |- and True True ] => split; apply I
  end.
Qed.
 
Parameter imported_LF__AltAuto__matchD_ex2 : import_of (@match_ex2).
Parameter LF__AltAuto__matchD_ex2_iso : iso_statement (@match_ex2) imported_LF__AltAuto__matchD_ex2.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@match_ex2) LF__AltAuto__matchD_ex2_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@match_ex2) LF__AltAuto__matchD_ex2_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface11.


Module Type Interface12 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter win64: bool.

Parameter imported_compcert__x86D_64__Archi__win64 : imported_Corelib__Init__Datatypes__bool.
Parameter compcert__x86D_64__Archi__win64_iso : win64 ≈[ _] imported_compcert__x86D_64__Archi__win64.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@win64) compcert__x86D_64__Archi__win64_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@win64) compcert__x86D_64__Archi__win64_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface12.

Module Type Interface13 (Import args : Args).

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : iso_statement False imported_Corelib__Init__Logic__False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
Parameter imported_Corelib__Init__Logic__eq_Prop : forall y : SProp, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso_Prop : iso_statement (fun A : Prop => @eq A) imported_Corelib__Init__Logic__eq_Prop.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Check Corelib__Init__Logic__eq_iso_Prop.

Parameter imported_Corelib__Init__Logic__iff : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__iff_iso : iso_statement Logic.iff imported_Corelib__Init__Logic__iff.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : SProp -> SProp.
Parameter Corelib__Init__Logic__not_iso : iso_statement not imported_Corelib__Init__Logic__not.

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
Parameter LF__IndProp__regD_exp_iso : iso_statement (@reg_exp) imported_LF__IndProp__regD_exp.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@reg_exp) LF__IndProp__regD_exp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__Char : forall y : Type, y -> imported_LF__IndProp__regD_exp y.
Parameter LF__IndProp__Char_iso : iso_statement (@Char) imported_LF__IndProp__Char.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Char) LF__IndProp__Char_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Char) LF__IndProp__Char_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_LF__Poly__list : Type -> Type.
Parameter LF__Poly__list_iso : iso_statement (@Datatypes.list) imported_LF__Poly__list.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Datatypes.list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Datatypes.list) LF__Poly__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
Parameter LF__IndProp__expD_match_iso : iso_statement (@exp_match) imported_LF__IndProp__expD_match.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@exp_match) LF__IndProp__expD_match_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__Poly__cons : forall y : Type, y -> imported_LF__Poly__list y -> imported_LF__Poly__list y.
Parameter LF__Poly__cons_iso : iso_statement (@Datatypes.cons) imported_LF__Poly__cons.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Datatypes.cons) LF__Poly__cons_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Datatypes.cons) LF__Poly__cons_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : iso_statement Ascii.ascii imported_Stdlib__Strings__Ascii__ascii.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_LF__IndProp__charD_nomatchD_char : import_of (@char_nomatch_char).
Parameter LF__IndProp__charD_nomatchD_char_iso : iso_statement (@char_nomatch_char) imported_LF__IndProp__charD_nomatchD_char.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@char_nomatch_char) LF__IndProp__charD_nomatchD_char_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@char_nomatch_char) LF__IndProp__charD_nomatchD_char_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface13.

Module Type Interface14 (Import args : Args).

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.


Parameter imported_Autosubst__AutosubstD_Basics__funcomp : forall y y0 y1 : Type, (y -> y0) -> (y0 -> y1) -> y -> y1.
Parameter Autosubst__AutosubstD_Basics__funcomp_iso : iso_statement (@funcomp) imported_Autosubst__AutosubstD_Basics__funcomp.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement nat imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition var := nat.

Parameter imported_Autosubst__AutosubstD_Basics__var : Type.
Parameter Autosubst__AutosubstD_Basics__var_iso : iso_statement var imported_Autosubst__AutosubstD_Basics__var.

(* Definition imported_Autosubst__AutosubstD_Basics__var := imported_Corelib__Init__Datatypes__nat.*)
#[export] Hint Extern 1 => progress (unfold var) : typeclass_instances ur_typeclass_instances.

Definition lift (x y : var) : var := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )").


Parameter imported_Autosubst__AutosubstD_Basics__lift : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Autosubst__AutosubstD_Basics__lift_iso : iso_statement lift imported_Autosubst__AutosubstD_Basics__lift.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (fun y => @eq y) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun y => @eq y) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun y => @eq y) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Nat__add : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Nat__add_iso : iso_statement Nat.add imported_Corelib__Init__Nat__add.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep : forall (y : Type) (y0 : y -> Type) (y1 : forall y1 : y, y0 y1) (y2 : forall y2 : y, y0 y2),
  (forall y3 : y, imported_Corelib__Init__Logic__eq (y1 y3) (y2 y3)) -> imported_Corelib__Init__Logic__eq y1 y2.
Parameter Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep_iso : iso_statement (@FunctionalExtensionality.functional_extensionality_dep) imported_Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep) Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep) Stdlib__Logic__FunctionalExtensionality__functionalD_extensionalityD_dep_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Delimit Scope subst_scope with subst.
Open Scope subst_scope.


Reserved Notation "sigma >> tau" (at level 56, left associativity).
Notation "f >>> g" := (funcomp f g)
  (at level 56, left associativity) : subst_scope.


Section LemmasForFun.

Context {A B : Type}.
Implicit Types (x : A) (f : var -> A) (g : A -> B) (n m : var).

Lemma lift_compR n m f : eq ((+n) >>> ((+m) >>> f)) ((+m+n) >>> f).
Proof. 
Admitted.

End LemmasForFun.


Parameter imported_Autosubst__AutosubstD_Basics__liftD_compR : import_of (@lift_compR).
Parameter Autosubst__AutosubstD_Basics__liftD_compR_iso : iso_statement (@lift_compR) imported_Autosubst__AutosubstD_Basics__liftD_compR.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@lift_compR) Autosubst__AutosubstD_Basics__liftD_compR_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@lift_compR) Autosubst__AutosubstD_Basics__liftD_compR_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface14.



Module DString.

(** Difference lists for fast append. *)
Definition t : Set := string -> string.

End DString.

Module Type Interface15 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : iso_statement bool imported_Corelib__Init__Datatypes__bool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : iso_statement Ascii.ascii imported_Stdlib__Strings__Ascii__ascii.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.Ascii.ascii) Stdlib__Strings__Ascii__ascii_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : iso_statement String.string imported_Stdlib__Strings__String__string.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Ceres__CeresString__DString__t : import_of (@DString.t).
Parameter Ceres__CeresString__DString__t_iso : iso_statement (@DString.t) imported_Ceres__CeresString__DString__t.

End Interface15.
(*
Module Type Interface15 (Import args : Args).

Parameter imported_Corelib__Numbers__BinNums__positive : import_of (@Corelib.Numbers.BinNums.positive).
Parameter Corelib__Numbers__BinNums__positive_iso : iso_statement (@Corelib.Numbers.BinNums.positive) imported_Corelib__Numbers__BinNums__positive.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_VFA__Color__M__key : import_of (@VFA.Color.M.key).
Parameter VFA__Color__M__key_iso : iso_statement (@VFA.Color.M.key) imported_VFA__Color__M__key.
#[export] Hint Extern 1 => progress (unfold VFA.Color.M.key) : typeclass_instances ur_typeclass_instances.

End Interface15.

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
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@funcomp) Autosubst__AutosubstD_Basics__funcomp_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : import_of (@Corelib.Init.Datatypes.nat).
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement (@Corelib.Init.Datatypes.nat) imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition iterate := fix iterate {A} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f(iterate f n' a)
  end.
Arguments iterate {A} f n a : simpl never.


Parameter imported_Autosubst__AutosubstD_Basics__iterate : import_of (@iterate).
Parameter Autosubst__AutosubstD_Basics__iterate_iso : iso_statement (@iterate) imported_Autosubst__AutosubstD_Basics__iterate.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@iterate) Autosubst__AutosubstD_Basics__iterate_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@iterate) Autosubst__AutosubstD_Basics__iterate_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition var := nat.

Parameter imported_Autosubst__AutosubstD_Basics__var : import_of (@var).
Parameter Autosubst__AutosubstD_Basics__var_iso : iso_statement (@var) imported_Autosubst__AutosubstD_Basics__var.
#[export] Hint Extern 1 => progress (unfold var) : typeclass_instances ur_typeclass_instances.

Definition lift (x y : var) : var := plus x y.
Arguments lift x y/.
Notation "( + x )" := (lift x) (format "( + x )").


Parameter imported_Autosubst__AutosubstD_Basics__lift : import_of (@lift).
Parameter Autosubst__AutosubstD_Basics__lift_iso : iso_statement (@lift) imported_Autosubst__AutosubstD_Basics__lift.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@lift) Autosubst__AutosubstD_Basics__lift_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition scons {X : Type} (s : X) (sigma : var -> X) (x : var) : X :=
  match x with S y => sigma y | _ => s end.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at level 56, right associativity) : subst_scope.
Parameter imported_Autosubst__AutosubstD_Basics__scons : import_of (@scons).
Parameter Autosubst__AutosubstD_Basics__scons_iso : iso_statement (@scons) imported_Autosubst__AutosubstD_Basics__scons.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@scons) Autosubst__AutosubstD_Basics__scons_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@scons) Autosubst__AutosubstD_Basics__scons_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Class Ids (term : Type) := ids : var -> term.

Arguments ids {_ _} x : simpl never.

Parameter imported_Autosubst__AutosubstD_Classes__Ids : import_of (@Ids).
Parameter Autosubst__AutosubstD_Classes__Ids_iso : iso_statement (@Ids) imported_Autosubst__AutosubstD_Classes__Ids.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Ids) Autosubst__AutosubstD_Classes__Ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Ids) Autosubst__AutosubstD_Classes__Ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Class Rename (term : Type) := rename : (var -> var) -> term -> term.
Arguments rename {_ _} xi !s /.

Parameter imported_Autosubst__AutosubstD_Classes__Rename : import_of (@Rename).
Parameter Autosubst__AutosubstD_Classes__Rename_iso : iso_statement (@Rename) imported_Autosubst__AutosubstD_Classes__Rename.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Rename) Autosubst__AutosubstD_Classes__Rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Rename) Autosubst__AutosubstD_Classes__Rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Autosubst__AutosubstD_Classes__ids : import_of (@ids).
Parameter Autosubst__AutosubstD_Classes__ids_iso : iso_statement (@ids) imported_Autosubst__AutosubstD_Classes__ids.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@ids) Autosubst__AutosubstD_Classes__ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@ids) Autosubst__AutosubstD_Classes__ids_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Autosubst__AutosubstD_Classes__rename : import_of (@rename).
Parameter Autosubst__AutosubstD_Classes__rename_iso : iso_statement (@rename) imported_Autosubst__AutosubstD_Classes__rename.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@rename) Autosubst__AutosubstD_Classes__rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@rename) Autosubst__AutosubstD_Classes__rename_iso goal_lhs : typeclass_instances ur_typeclass_instances.

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
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@up) Autosubst__AutosubstD_Classes__up_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@up) Autosubst__AutosubstD_Classes__up_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : import_of (@Corelib.Init.Datatypes.O).
Parameter Corelib__Init__Datatypes__O_iso : iso_statement (@Corelib.Init.Datatypes.O) imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : import_of (@Corelib.Init.Datatypes.S).
Parameter Corelib__Init__Datatypes__S_iso : iso_statement (@Corelib.Init.Datatypes.S) imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Nat__add : import_of (@Corelib.Init.Nat.add).
Parameter Corelib__Init__Nat__add_iso : iso_statement (@Corelib.Init.Nat.add) imported_Corelib__Init__Nat__add.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Nat.add) Corelib__Init__Nat__add_iso goal_lhs : typeclass_instances ur_typeclass_instances.


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
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@fold_up_upn) Autosubst__AutosubstD_Tactics__foldD_upD_upn_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@fold_up_upn) Autosubst__AutosubstD_Tactics__foldD_upD_upn_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface19.

Module Type Interface16 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_rect : import_of (@Corelib.Init.Logic.eq_rect).
Parameter Corelib__Init__Logic__eqD_rect_iso : iso_statement (@Corelib.Init.Logic.eq_rect) imported_Corelib__Init__Logic__eqD_rect.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq_rect) Corelib__Init__Logic__eqD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__rewD_const : import_of (@Corelib.Init.Logic.rew_const).

End Interface16.

Unset Universe Polymorphism.

Inductive atomT : Type :=
| NBool : forall (p : Prop), option (p \/ ~ p) -> atomT
| TBool : forall (b: bool) (p: Prop), p <-> is_true b -> atomT.

Module Type Interface17 (Import args : Args).

Parameter imported_Cdcl__Formula__atomT : import_of (@atomT:Type).
Parameter Cdcl__Formula__atomT_iso : iso_statement (@atomT:Type) imported_Cdcl__Formula__atomT.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@atomT:Type) Cdcl__Formula__atomT_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@atomT:Type) Cdcl__Formula__atomT_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : import_of (@Corelib.Init.Datatypes.option).
Parameter Corelib__Init__Datatypes__option_iso : iso_statement (@Corelib.Init.Datatypes.option) imported_Corelib__Init__Datatypes__option.

Parameter imported_Corelib__Init__Datatypes__option' : import_of (fun A : Prop => @Corelib.Init.Datatypes.option A).
Parameter Corelib__Init__Datatypes__option_iso' : iso_statement (fun A : Prop => @Corelib.Init.Datatypes.option A) imported_Corelib__Init__Datatypes__option'.

#[export] Hint Extern 1 (UR.UR_Type _ _) => ltac2: (
  match! goal with [ |- UR.UR_Type ?goal_lhs _] => tc_hint_for_list 'univalent true false '(@Corelib.Init.Datatypes.option) ['Corelib__Init__Datatypes__option_iso;'Corelib__Init__Datatypes__option_iso' ] goal_lhs end) : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => ltac2: (
  match! goal with [ |- UR.pr ?k ?goal_lhs _] => tc_hint_for_list k true false '(@Corelib.Init.Datatypes.option) ['Corelib__Init__Datatypes__option_iso;'Corelib__Init__Datatypes__option_iso' ] goal_lhs end) : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : import_of (@Corelib.Init.Logic.False).
Parameter Corelib__Init__Logic__False_iso : iso_statement (@Corelib.Init.Logic.False) imported_Corelib__Init__Logic__False.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__or : import_of (@Corelib.Init.Logic.or).
Parameter Corelib__Init__Logic__or_iso : iso_statement (@Corelib.Init.Logic.or) imported_Corelib__Init__Logic__or.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.or) Corelib__Init__Logic__or_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.or) Corelib__Init__Logic__or_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Cdcl__Formula__NBool : import_of (@NBool).
Parameter Cdcl__Formula__NBool_iso : iso_statement (@NBool) imported_Cdcl__Formula__NBool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@NBool) Cdcl__Formula__NBool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@NBool) Cdcl__Formula__NBool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface17.

Module Type Interface18 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : import_of (@Corelib.Init.Logic.iff).
Parameter Corelib__Init__Logic__iff_iso : iso_statement (@Corelib.Init.Logic.iff) imported_Corelib__Init__Logic__iff.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Axiom propositional_extensionality : forall (P Q : Prop), (P <-> Q) -> eq P Q.

Parameter imported_Stdlib__Logic__PropExtensionality__propositionalD_extensionality : import_of (@propositional_extensionality).
Parameter Stdlib__Logic__PropExtensionality__propositionalD_extensionality_iso : iso_statement (@propositional_extensionality) imported_Stdlib__Logic__PropExtensionality__propositionalD_extensionality.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@propositional_extensionality) Stdlib__Logic__PropExtensionality__propositionalD_extensionality_iso goal_lhs : typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@propositional_extensionality) Stdlib__Logic__PropExtensionality__propositionalD_extensionality_iso goal_lhs : typeclass_instances.

End Interface18.

Module Type Interface20 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__prod : import_of (fun A B => @Corelib.Init.Datatypes.prod A B).
Parameter Corelib__Init__Datatypes__prod_iso : iso_statement
     (fun A B => Corelib.Init.Datatypes.prod A B) imported_Corelib__Init__Datatypes__prod.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A B => Corelib.Init.Datatypes.prod A B) Corelib__Init__Datatypes__prod_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A B => Corelib.Init.Datatypes.prod A B) Corelib__Init__Datatypes__prod_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__prod' : SProp -> SProp -> SProp.
Parameter Corelib__Init__Datatypes__prod_iso' : iso_statement
     (fun A B : Prop => Corelib.Init.Datatypes.prod A B) imported_Corelib__Init__Datatypes__prod'.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A B : Prop => Corelib.Init.Datatypes.prod A B) Corelib__Init__Datatypes__prod_iso' goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A B : Prop => Corelib.Init.Datatypes.prod A B) Corelib__Init__Datatypes__prod_iso' goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Corelib__Init__Logic__and : import_of (@Corelib.Init.Logic.and).
Parameter Corelib__Init__Logic__and_iso : iso_statement (@Corelib.Init.Logic.and) imported_Corelib__Init__Logic__and.

#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : import_of (@Corelib.Init.Logic.iff).
Parameter Corelib__Init__Logic__iff_iso : iso_statement (@Corelib.Init.Logic.iff) imported_Corelib__Init__Logic__iff.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Require Import ssrbool.

Parameter imported_Corelib__ssr__ssrbool__pairD_andP : import_of (@Corelib.ssr.ssrbool.pair_andP).
Parameter Corelib__ssr__ssrbool__pairD_andP_iso : iso_statement (@Corelib.ssr.ssrbool.pair_andP) imported_Corelib__ssr__ssrbool__pairD_andP.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.ssr.ssrbool.pair_andP) Corelib__ssr__ssrbool__pairD_andP_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.ssr.ssrbool.pair_andP) Corelib__ssr__ssrbool__pairD_andP_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface20.

From Ltac2 Require Import Ltac2.
Ltac2 missing_iso_warning () :=
  let goal_lhs :=
    lazy_match! goal with
    | [ |- UR.UR_Type ?goal_lhs _ ] => goal_lhs
    | [ |- UR.pr _ ?goal_lhs _ ] => goal_lhs
    end in
  let (h, _) := Constr.decompose_app_nocast goal_lhs in
  if Constr.has_evar h
  then Control.zero Match_failure
  else
    match Reference.of_constr_opt h with
    | None => throw "Failed to find iso for non-reference %t (in %t with context %a)" h (Control.goal ()) (fun () a => a) (Control.fprint_context ())
    | Some (Std.VarRef id) => throw "Failed to find iso for variable %a (in %t with context %a)" (fun () => Message.of_ident) id (Control.goal ()) (fun () a => a) (Control.fprint_context ())
    | Some r => throw "Missing iso for %a (in %t)" (fun () => Reference.pr_qualified) r (Control.goal ())
    end.
#[export] Hint Extern 1000 (UR.UR_Type _ _) => missing_iso_warning () : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1000 (UR.pr _ _ _) => missing_iso_warning () : typeclass_instances ur_typeclass_instances.

Require Import Ltac.
Module Type Interface21 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : iso_statement Corelib.Init.Datatypes.bool imported_Corelib__Init__Datatypes__bool.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option : Type -> Type.
Parameter Corelib__Init__Datatypes__option_iso : iso_statement (Corelib.Init.Datatypes.option) imported_Corelib__Init__Datatypes__option.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (Corelib.Init.Datatypes.option) Corelib__Init__Datatypes__option_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__ssr__ssrbool__true : import_of (@True).
Parameter Corelib__ssr__ssrbool__pairD_true_iso : iso_statement (@True) imported_Corelib__ssr__ssrbool__true.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@True) Corelib__ssr__ssrbool__pairD_true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@True) Corelib__ssr__ssrbool__pairD_true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__option_Prop : SProp -> Type.
Parameter Corelib__Init__Datatypes__option_iso_Prop : iso_statement (fun A : Prop => Corelib.Init.Datatypes.option A) imported_Corelib__Init__Datatypes__option_Prop.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A: Prop => Corelib.Init.Datatypes.option A) Corelib__Init__Datatypes__option_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A: Prop => Corelib.Init.Datatypes.option A) Corelib__Init__Datatypes__option_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Definition test := None : option True.

Parameter foo_test :  import_of (@test).

Definition has_boolb (b: bool) (o: option bool) :=
    match o with
    | None => true
    | Some b' =>  Bool.eqb b  b'
    end.

Definition lift_has_boolb (b:bool) (o : option (option bool)) :=
  match o with
  | None => false
  | Some o' => has_boolb b o'
  end.

Parameter foo :  import_of (@lift_has_boolb).
Parameter bar :  iso_statement (@lift_has_boolb) foo.

End Interface21.

Module Type Interface22 (Import args : Args).

Parameter imported_Corelib__Init__Logic__ex : forall y : Type, (y -> SProp) -> SProp.
Parameter Corelib__Init__Logic__ex_iso : iso_statement (@Corelib.Init.Logic.ex) imported_Corelib__Init__Logic__ex.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
Monomorphic Definition imported_Corelib__Init__Logic__ex_Prop : forall y : SProp, (y -> SProp) -> SProp.
Admitted.
Monomorphic Definition Corelib__Init__Logic__ex_iso_Prop : (fun A : Prop => @Corelib.Init.Logic.ex A) ≈u imported_Corelib__Init__Logic__ex_Prop.
Admitted.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface22.

Module Type Interface23 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement Corelib.Init.Datatypes.nat imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : iso_statement Stdlib.Strings.String.string imported_Stdlib__Strings__String__string.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Strings.String.string) Stdlib__Strings__String__string_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition total_map (A : Type) : Type := string -> A.

Parameter imported_LF__Maps__totalD_map : Type -> Type.
Parameter LF__Maps__totalD_map_iso : iso_statement total_map imported_LF__Maps__totalD_map.
#[export] Hint Extern 1 => progress (unfold total_map) : typeclass_instances ur_typeclass_instances.

Definition state := total_map nat.

Parameter imported_LF__Imp__state : import_of (@state).
Parameter LF__Imp__state_iso : iso_statement (@state) imported_LF__Imp__state.
#[export] Hint Extern 1 => progress (unfold state) : typeclass_instances ur_typeclass_instances.

End Interface23.

Section Relation_Definition.

  Variable A : Type.

  Definition relation := A -> A -> Prop.
End Relation_Definition.

Set Universe Polymorphism.
Definition relation' (A:Type) := A -> A -> Prop.

Module Type Interface24 (Import args : Args).

Require Import Morphisms.
Parameter imported_Corelib__Init__Datatypes__nat : import_of nat.
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement nat imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : import_of Logic.iff.
Parameter Corelib__Init__Logic__iff_iso : iso_statement Logic.iff imported_Corelib__Init__Logic__iff.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : import_of (fun n : nat => S n).
Parameter Corelib__Init__Datatypes__S_iso : iso_statement Corelib.Init.Datatypes.S imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 1 => progress (unfold Proper) : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 => progress (unfold respectful) : typeclass_instances ur_typeclass_instances.

End Interface24.

Module Type Interface25 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq_Prop : import_of (fun A : Prop => @Corelib.Init.Logic.eq A).
Parameter Corelib__Init__Logic__eq_iso_Prop : iso_statement (fun A : Prop => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq_Prop.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

From Stdlib Require Import Logic.Hurkens.
Fail Parameter imported_Stdlib__Logic__Hurkens__NoRetractToImpredicativeUniverse__paradox : import_of (@Stdlib.Logic.Hurkens.NoRetractToImpredicativeUniverse.paradox).

End Interface25.

Module Type Interface26 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : import_of (@Corelib.Init.Datatypes.nat).
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement (@Corelib.Init.Datatypes.nat) imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : import_of (@Corelib.Init.Datatypes.S).
Parameter Corelib__Init__Datatypes__S_iso : iso_statement (@Corelib.Init.Datatypes.S) imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq_Prop : import_of (fun A : Prop => @Corelib.Init.Logic.eq A).
Parameter Corelib__Init__Logic__eq_iso_Prop : iso_statement (fun A : Prop => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq_Prop.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : import_of (@Corelib.Init.Logic.iff).
Parameter Corelib__Init__Logic__iff_iso : iso_statement (@Corelib.Init.Logic.iff) imported_Corelib__Init__Logic__iff.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Relations__RelationD_Definitions__relation : import_of (@Corelib.Relations.Relation_Definitions.relation).
Parameter Corelib__Relations__RelationD_Definitions__relation_iso : iso_statement (@Corelib.Relations.Relation_Definitions.relation)
     imported_Corelib__Relations__RelationD_Definitions__relation.
#[export] Hint Extern 1 => progress (unfold Corelib.Relations.Relation_Definitions.relation) : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Classes__Morphisms__Proper : forall y : Type, (y -> y -> SProp) -> y -> SProp.
Parameter Corelib__Classes__Morphisms__Proper_iso : iso_statement (@Corelib.Classes.Morphisms.Proper) imported_Corelib__Classes__Morphisms__Proper. 
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Classes.Morphisms.Proper) Corelib__Classes__Morphisms__Proper_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Classes.Morphisms.Proper) Corelib__Classes__Morphisms__Proper_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Classes__Morphisms__respectful : import_of (@Corelib.Classes.Morphisms.respectful).
Parameter Corelib__Classes__Morphisms__respectful_iso : iso_statement (@Corelib.Classes.Morphisms.respectful) imported_Corelib__Classes__Morphisms__respectful.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Classes.Morphisms.respectful) Corelib__Classes__Morphisms__respectful_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Classes.Morphisms.respectful) Corelib__Classes__Morphisms__respectful_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Arith__PeanoNat__Nat__centralD_induction : import_of (@Stdlib.Arith.PeanoNat.Nat.central_induction).
Parameter Stdlib__Arith__PeanoNat__Nat__centralD_induction_iso : iso_statement (@Stdlib.Arith.PeanoNat.Nat.central_induction) imported_Stdlib__Arith__PeanoNat__Nat__centralD_induction.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Arith.PeanoNat.Nat.central_induction) Stdlib__Arith__PeanoNat__Nat__centralD_induction_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Arith.PeanoNat.Nat.central_induction) Stdlib__Arith__PeanoNat__Nat__centralD_induction_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface26.


Module Type Interface27 (Import args : Args).

#[projections(primitive)]
Record product (A B : Type) := mk_prod { fst : A; snd : B }.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__product : import_of product.
Parameter Corelib__Init__Datatypes__product_iso : iso_statement product imported_Corelib__Init__Datatypes__product.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for @product Corelib__Init__Datatypes__product_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@product) Corelib__Init__Datatypes__product_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__fst : import_of fst.
Parameter Corelib__Init__Datatypes__fst_iso : iso_statement fst imported_Corelib__Init__Datatypes__fst.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for @fst Corelib__Init__Datatypes__fst_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@fst) Corelib__Init__Datatypes__fst_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__snd : import_of snd.
Parameter Corelib__Init__Datatypes__snd_iso : iso_statement snd imported_Corelib__Init__Datatypes__snd.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for @snd Corelib__Init__Datatypes__snd_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@snd) Corelib__Init__Datatypes__snd_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Lemma app_fst : (forall A B (x y:product A B), eq x y -> eq (fst x) (fst y)).
Proof.
intros. now destruct H.
Qed.

Parameter imported_Corelib__Init__Datatypes__app_fst : import_of app_fst.
Parameter Corelib__Init__Datatypes__app_fst_iso : iso_statement app_fst imported_Corelib__Init__Datatypes__app_fst.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for @app_fst Corelib__Init__Datatypes__app_fst_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@app_fst) Corelib__Init__Datatypes__app_fst_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface27.

Module Type Interface28 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : import_of nat.
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement nat imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Nat__max : import_of Nat.max. 
Parameter Corelib__Init__Nat__max_iso : iso_statement Nat.max imported_Corelib__Init__Nat__max.
#[export] Hint Extern 10 => progress (unfold Corelib.Init.Nat.max) : typeclass_instances ur_typeclass_instances. 

Parameter imported_Corelib__Init__Peano__le : import_of Peano.le. 
Parameter Corelib__Init__Peano__le_iso : iso_statement Peano.le imported_Corelib__Init__Peano__le.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Peano.le) Corelib__Init__Peano__le_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Peano.le) Corelib__Init__Peano__le_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition max_l: forall n m : nat,  Peano.le m n -> eq (max n m)  n.
Admitted.

Fail Parameter imported_Corelib__Init__max__l : import_of (@max_l).

#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Nat.max) Corelib__Init__Nat__max_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Nat.max) Corelib__Init__Nat__max_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__max__l : import_of (@max_l).

End Interface28.


Module Type Interface29 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : import_of (@Corelib.Init.Datatypes.nat).
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement (@Corelib.Init.Datatypes.nat) imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__positive : import_of (@Corelib.Numbers.BinNums.positive).
Parameter Corelib__Numbers__BinNums__positive_iso : iso_statement (@Corelib.Numbers.BinNums.positive) imported_Corelib__Numbers__BinNums__positive.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.

From Corelib Require Import Floats.SpecFloat. 

Parameter imported_Corelib__Floats__SpecFloat__iterD_pos : import_of (@Corelib.Floats.SpecFloat.iter_pos).
Parameter Corelib__Floats__SpecFloat__iterD_pos_iso : iso_statement (@Corelib.Floats.SpecFloat.iter_pos) imported_Corelib__Floats__SpecFloat__iterD_pos.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Floats.SpecFloat.iter_pos) Corelib__Floats__SpecFloat__iterD_pos_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Floats.SpecFloat.iter_pos) Corelib__Floats__SpecFloat__iterD_pos_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Fixpoint iter_nat {A} (f:A->A) (n : nat) (x : A) {struct n} : A :=
  match n with
  | S n' => iter_nat f n' (f x)
  | O => x
  end.

Parameter imported_Flocq__Core__Zaux__iterD_nat : import_of (@iter_nat).
Parameter Flocq__Core__Zaux__iterD_nat_iso : iso_statement (@iter_nat) imported_Flocq__Core__Zaux__iterD_nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@iter_nat) Flocq__Core__Zaux__iterD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@iter_nat) Flocq__Core__Zaux__iterD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

From Stdlib Require Import PArith.BinPos.

Parameter imported_Stdlib__PArith__BinPos__Pos__toD_nat : import_of (@Stdlib.PArith.BinPos.Pos.to_nat).
Parameter Stdlib__PArith__BinPos__Pos__toD_nat_iso : iso_statement (@Stdlib.PArith.BinPos.Pos.to_nat) imported_Stdlib__PArith__BinPos__Pos__toD_nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.PArith.BinPos.Pos.to_nat) Stdlib__PArith__BinPos__Pos__toD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.PArith.BinPos.Pos.to_nat) Stdlib__PArith__BinPos__Pos__toD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter imported_Stdlib__PArith__BinPos__Pos__toD_pos_iter : import_of (@Stdlib.PArith.BinPos.Pos.iter).
Parameter Stdlib__PArith__BinPos__Pos__toD_pos_iter_iso : iso_statement (@Stdlib.PArith.BinPos.Pos.iter) imported_Stdlib__PArith__BinPos__Pos__toD_pos_iter.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.PArith.BinPos.Pos.iter) Stdlib__PArith__BinPos__Pos__toD_pos_iter_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.PArith.BinPos.Pos.iter) Stdlib__PArith__BinPos__Pos__toD_pos_iter_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Lemma iter_pos_nat :
  forall A f (p : positive) (x : A),
  eq (iter_pos A f x p) (iter_nat f (Pos.to_nat p) x).
Admitted. 

Parameter imported_Flocq__Core__Zaux__iterD_posD_nat : import_of (@iter_pos_nat).
Parameter Flocq__Core__Zaux__iterD_posD_nat_iso : iso_statement (@iter_pos_nat) imported_Flocq__Core__Zaux__iterD_posD_nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@iter_pos_nat) Flocq__Core__Zaux__iterD_posD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@iter_pos_nat) Flocq__Core__Zaux__iterD_posD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface29.

Ltac2 is_var_nocast(c: constr) :=
  match Unsafe.kind_nocast c with
  | Unsafe.Var _ => true
  | _ => false
  end.

Ltac2 clean_hyp () := repeat (match! goal with | [ h : _ ≈[_] _ |- _ ] =>  match Control.hyp_value h with
  | Some v => if is_var_nocast v then Std.clear [h] else Control.zero Match_failure
  | None => Control.zero Match_failure
  end end).

Module Type Interface30 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

From Stdlib Require Import Logic.ProofIrrelevance.

Fail Parameter imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance : import_of (@Stdlib.Logic.ProofIrrelevance.proof_irrelevance).

Parameter imported_Corelib__Init__Logic__eq' : import_of (fun A : Prop => @Corelib.Init.Logic.eq A).
Parameter Corelib__Init__Logic__eq_iso' : iso_statement (fun A : Prop => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq'.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso' goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A : Prop => @Corelib.Init.Logic.eq A) Corelib__Init__Logic__eq_iso' goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance : import_of (@Stdlib.Logic.ProofIrrelevance.proof_irrelevance).
Parameter Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso : iso_statement (@Stdlib.Logic.ProofIrrelevance.proof_irrelevance) imported_Stdlib__Logic__ProofIrrelevance__proofD_irrelevance.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Logic.ProofIrrelevance.proof_irrelevance) Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Logic.ProofIrrelevance.proof_irrelevance) Stdlib__Logic__ProofIrrelevance__proofD_irrelevance_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface30.

Module Type Interface31 (Import args : Args).

From Stdlib Require Import PropExtensionality.
From UnivalentParametricity Require Import theories.UR theories.FP.

#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : import_of (@Corelib.Init.Logic.eq).
Parameter Corelib__Init__Logic__eq_iso : iso_statement (@Corelib.Init.Logic.eq) imported_Corelib__Init__Logic__eq.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__iff : import_of (@Corelib.Init.Logic.iff).
(* Parameter Corelib__Init__Logic__iff_iso : iso_statement (@Corelib.Init.Logic.iff) imported_Corelib__Init__Logic__iff.
 *)
Parameter Corelib__Init__Logic__iff_iso : (@UR.pr UR.univalent _ _
     (@UR.URArrow UR.univalent Prop SProp (forall _ : Prop, Prop) (forall _ : SProp, SProp) _
        (@UR.URArrow UR.univalent Prop SProp Prop SProp _ (UR.PR_Type UR.univalent)))
     (@Corelib.Init.Logic.iff) imported_Corelib__Init__Logic__iff).

#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.iff) Corelib__Init__Logic__iff_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Logic__PropExtensionality__propositionalD_extensionality : import_of (@Stdlib.Logic.PropExtensionality.propositional_extensionality).

End Interface31.

Module Type Interface32 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__list : import_of (@Corelib.Init.Datatypes.list).
Parameter Corelib__Init__Datatypes__list_iso : iso_statement (@Corelib.Init.Datatypes.list) imported_Corelib__Init__Datatypes__list.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.list) Corelib__Init__Datatypes__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.list) Corelib__Init__Datatypes__list_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : import_of (@Corelib.Init.Datatypes.nat).
Parameter Corelib__Init__Datatypes__nat_iso : iso_statement (@Corelib.Init.Datatypes.nat) imported_Corelib__Init__Datatypes__nat.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

From Stdlib Require Import List.
Import ListNotations.
Inductive sorted: Datatypes.list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted (i::[])
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Parameter imported_VFA__Selection__sorted : import_of (@sorted).
Parameter VFA__Selection__sorted_iso : iso_statement (@sorted) imported_VFA__Selection__sorted.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@sorted) VFA__Selection__sorted_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@sorted) VFA__Selection__sorted_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface32.

Module Type Interface33 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__prod : import_of (fun A B => @Corelib.Init.Datatypes.prod A B).
Parameter Corelib__Init__Datatypes__prod_iso : iso_statement (fun A B => @Corelib.Init.Datatypes.prod A B) imported_Corelib__Init__Datatypes__prod.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A B => @Corelib.Init.Datatypes.prod A B) Corelib__Init__Datatypes__prod_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A B => @Corelib.Init.Datatypes.prod A B) Corelib__Init__Datatypes__prod_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition curry3 A1 A2 A3 B (f : Corelib.Init.Datatypes.prod (Corelib.Init.Datatypes.prod A1  A2) A3 -> B) : A1 -> A2 -> A3 -> B :=
  fun x1 x2 x3 => f (Corelib.Init.Datatypes.pair (Corelib.Init.Datatypes.pair x1 x2) x3).

Parameter imported_TLC__LibProd__curry3 : import_of (@curry3).
Parameter TLC__LibProd__curry3_iso : iso_statement (@curry3) imported_TLC__LibProd__curry3.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@curry3) TLC__LibProd__curry3_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@curry3) TLC__LibProd__curry3_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface33.

Module Type Interface34 (Import args : Args).

Parameter imported_Corelib__Init__Logic__not : import_of (@Corelib.Init.Logic.not).
Parameter Corelib__Init__Logic__not_iso : iso_statement (@Corelib.Init.Logic.not) imported_Corelib__Init__Logic__not.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__ssr__ssrbool__implies : import_of (fun A B => @Corelib.ssr.ssrbool.implies A B).
Parameter Corelib__ssr__ssrbool__implies_iso : iso_statement (fun A B => @Corelib.ssr.ssrbool.implies A B) imported_Corelib__ssr__ssrbool__implies.
#[export] Hint Extern 2 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A B => @Corelib.ssr.ssrbool.implies A B) Corelib__ssr__ssrbool__implies_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 2 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A B => @Corelib.ssr.ssrbool.implies A B) Corelib__ssr__ssrbool__implies_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__ssr__ssrbool__implies_Prop_Prop : import_of ((fun P Q : Prop => Corelib.ssr.ssrbool.implies P Q)).
Parameter Corelib__ssr__ssrbool__implies_iso_Prop_Prop : iso_statement ((fun P Q : Prop => Corelib.ssr.ssrbool.implies P Q)) imported_Corelib__ssr__ssrbool__implies_Prop_Prop.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent ((fun P Q : Prop => Corelib.ssr.ssrbool.implies P Q)) Corelib__ssr__ssrbool__implies_iso_Prop_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k ((fun P Q : Prop => Corelib.ssr.ssrbool.implies P Q)) Corelib__ssr__ssrbool__implies_iso_Prop_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__ssr__ssrbool__implies_Type_Prop : import_of (fun (P : Type) (Q : Prop) => ssrbool.implies P Q).
Parameter Corelib__ssr__ssrbool__implies_iso_Type_Prop : iso_statement (fun (P : Type) (Q : Prop) => ssrbool.implies P Q) imported_Corelib__ssr__ssrbool__implies_Type_Prop.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent ((fun (P : Type) (Q : Prop) => Corelib.ssr.ssrbool.implies P Q)) Corelib__ssr__ssrbool__implies_iso_Type_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k ((fun (P : Type) (Q : Prop) => Corelib.ssr.ssrbool.implies P Q)) Corelib__ssr__ssrbool__implies_iso_Type_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

(*
Parameter imported_Corelib__ssr__ssrbool__impliesPn : import_of (@Corelib.ssr.ssrbool.impliesPn).
Parameter Corelib__ssr__ssrbool__impliesPn_iso : iso_statement (@Corelib.ssr.ssrbool.impliesPn) imported_Corelib__ssr__ssrbool__impliesPn.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.ssr.ssrbool.impliesPn) Corelib__ssr__ssrbool__impliesPn_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.ssr.ssrbool.impliesPn) Corelib__ssr__ssrbool__impliesPn_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.ssr.ssrbool.impliesPn)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
*)
End Interface34.

Module Type Interface35 (Import args : Args).
From Stdlib Require Import Reals.ROrderedType.
Parameter imported_Stdlib__Reals__ROrderedType__RD_asD_OT__t : import_of (@Stdlib.Reals.ROrderedType.R_as_OT.t).
Parameter Stdlib__Reals__ROrderedType__RD_asD_OT__t_iso : iso_statement (@Stdlib.Reals.ROrderedType.R_as_DT.t) imported_Stdlib__Reals__ROrderedType__RD_asD_OT__t.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Reals.ROrderedType.R_as_OT.t) Stdlib__Reals__ROrderedType__RD_asD_OT__t_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Reals.ROrderedType.R_as_OT.t) Stdlib__Reals__ROrderedType__RD_asD_OT__t_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface35.

(*
Module Type Interface36 (Import args : Args).

From Stdlib Require Import Formula. 
Parameter imported_Cdcl__Formula__IntMap__ptrie : Type -> Type -> Type.
Parameter Cdcl__Formula__IntMap__ptrie_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (forall _ : Type, Type) (forall _ : Type, Type) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)))
     Formula.IntMap.ptrie imported_Cdcl__Formula__IntMap__ptrie).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Cdcl.Formula.IntMap.ptrie) Cdcl__Formula__IntMap__ptrie_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Cdcl.Formula.IntMap.ptrie) Cdcl__Formula__IntMap__ptrie_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Cdcl.Formula.IntMap.ptrie)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Init.Datatypes.nat)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__prod : Type -> Type -> Type.
Parameter Corelib__Init__Datatypes__prod_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (forall _ : Type, Type) (forall _ : Type, Type) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)))
     prod imported_Corelib__Init__Datatypes__prod).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.prod) Corelib__Init__Datatypes__prod_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.prod) Corelib__Init__Datatypes__prod_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Init.Datatypes.prod)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__Z : Type.
Parameter Corelib__Numbers__BinNums__Z_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) BinNums.Z imported_Corelib__Numbers__BinNums__Z).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Numbers.BinNums.Z)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int : Type.
Parameter Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.Cyclic.Int63.PrimInt63.int) Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.Cyclic.Int63.PrimInt63.int) Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Numbers.Cyclic.Int63.PrimInt63.int)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Cdcl__Formula__hmap : Type.
Parameter Cdcl__Formula__hmap_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) Formula.hmap imported_Cdcl__Formula__hmap).
#[export] Hint Extern 1 => progress (unfold Cdcl.Formula.hmap) : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Init.Datatypes.bool)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__eqb : imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int -> imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int -> imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Numbers__Cyclic__Int63__PrimInt63__eqb_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
        (forall _ : Corelib.Numbers.Cyclic.Int63.PrimInt63.int, bool) (forall _ : imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int, imported_Corelib__Init__Datatypes__bool)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int bool
           imported_Corelib__Init__Datatypes__bool
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
              Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} bool imported_Corelib__Init__Datatypes__bool Corelib__Init__Datatypes__bool_iso)))
     Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__eqb).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb) Corelib__Numbers__Cyclic__Int63__PrimInt63__eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb) Corelib__Numbers__Cyclic__Int63__PrimInt63__eqb_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__land : imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int -> imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int -> imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int.
Parameter Corelib__Numbers__Cyclic__Int63__PrimInt63__land_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
        (forall _ : Corelib.Numbers.Cyclic.Int63.PrimInt63.int, Corelib.Numbers.Cyclic.Int63.PrimInt63.int)
        (forall _ : imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int, imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
              Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
              Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)))
     Corelib.Numbers.Cyclic.Int63.PrimInt63.land imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__land).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.Cyclic.Int63.PrimInt63.land) Corelib__Numbers__Cyclic__Int63__PrimInt63__land_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.Cyclic.Int63.PrimInt63.land) Corelib__Numbers__Cyclic__Int63__PrimInt63__land_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Numbers.Cyclic.Int63.PrimInt63.land)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__lsr : imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int -> imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int -> imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int.
Parameter Corelib__Numbers__Cyclic__Int63__PrimInt63__lsr_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
        (forall _ : Corelib.Numbers.Cyclic.Int63.PrimInt63.int, Corelib.Numbers.Cyclic.Int63.PrimInt63.int)
        (forall _ : imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int, imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
              Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Corelib.Numbers.Cyclic.Int63.PrimInt63.int imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__int
              Corelib__Numbers__Cyclic__Int63__PrimInt63__int_iso)))
     Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr imported_Corelib__Numbers__Cyclic__Int63__PrimInt63__lsr).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr) Corelib__Numbers__Cyclic__Int63__PrimInt63__lsr_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr) Corelib__Numbers__Cyclic__Int63__PrimInt63__lsr_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__micromega__ZifyClasses__InjTyp : Type -> Type -> Type.
Parameter Stdlib__micromega__ZifyClasses__InjTyp_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (forall _ : Type, Type) (forall _ : Type, Type) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)))
     ZifyClasses.InjTyp imported_Stdlib__micromega__ZifyClasses__InjTyp).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.micromega.ZifyClasses.InjTyp) Stdlib__micromega__ZifyClasses__InjTyp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.micromega.ZifyClasses.InjTyp) Stdlib__micromega__ZifyClasses__InjTyp_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Stdlib.micromega.ZifyClasses.InjTyp)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
Definition plain_imported_Stdlib__micromega__ZifyClasses__InjTyp : Type -> Type -> Type := imported_Stdlib__micromega__ZifyClasses__InjTyp.
Parameter Stdlib__micromega__ZifyClasses__InjTyp_iso_plain : plain_iso_statement (@Stdlib.micromega.ZifyClasses.InjTyp) plain_imported_Stdlib__micromega__ZifyClasses__InjTyp.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.micromega.ZifyClasses.InjTyp) Stdlib__micromega__ZifyClasses__InjTyp_iso_plain goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.micromega.ZifyClasses.InjTyp) Stdlib__micromega__ZifyClasses__InjTyp_iso_plain goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Stdlib.micromega.ZifyClasses.InjTyp)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__micromega__ZifyUint63__InjD_intD_Z : import_of (@Stdlib.micromega.ZifyUint63.Inj_int_Z).
Parameter Stdlib__micromega__ZifyUint63__InjD_intD_Z_iso : iso_statement (@Stdlib.micromega.ZifyUint63.Inj_int_Z) imported_Stdlib__micromega__ZifyUint63__InjD_intD_Z.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.micromega.ZifyUint63.Inj_int_Z) Stdlib__micromega__ZifyUint63__InjD_intD_Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.micromega.ZifyUint63.Inj_int_Z) Stdlib__micromega__ZifyUint63__InjD_intD_Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor (@Stdlib.micromega.ZifyUint63.Inj_int_Z)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

End Interface37.
*)
Module Type Interface36 (Import args : Args).

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Parameter imported_ExtLib__Structures__Monad__Monad : (Type -> Type) -> Type.
Parameter ExtLib__Structures__Monad__Monad_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : Type, Type) (forall _ : Type, Type) Type Type
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     Monad imported_ExtLib__Structures__Monad__Monad).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Monad) ExtLib__Structures__Monad__Monad_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Monad) ExtLib__Structures__Monad__Monad_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Definition plain_imported_ExtLib__Structures__Monad__Monad : (Type -> Type) -> Type := imported_ExtLib__Structures__Monad__Monad.
Parameter ExtLib__Structures__Monad__Monad_iso_plain : iso_statement (@Monad) plain_imported_ExtLib__Structures__Monad__Monad.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Monad) ExtLib__Structures__Monad__Monad_iso_plain goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Monad) ExtLib__Structures__Monad__Monad_iso_plain goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter IO : Type -> Type.

Parameter imported_SimpleIO__IOD_Monad__IO : Type -> Type.
Parameter SimpleIO__IOD_Monad__IO_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     IO imported_SimpleIO__IOD_Monad__IO).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@IO) SimpleIO__IOD_Monad__IO_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@IO) SimpleIO__IOD_Monad__IO_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter IObind : forall {a b}, IO a -> (a -> IO b) -> IO b.

Parameter imported_SimpleIO__IOD_Monad__IO__bind : forall y y0 : Type, imported_SimpleIO__IOD_Monad__IO y -> (y -> imported_SimpleIO__IOD_Monad__IO y0) -> imported_SimpleIO__IOD_Monad__IO y0.
Parameter SimpleIO__IOD_Monad__IO__bind_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall (b : Type) (_ : IO x) (_ : forall _ : x, IO b), IO b)
        (fun H : Type => forall (y : Type) (_ : imported_SimpleIO__IOD_Monad__IO H) (_ : forall _ : H, imported_SimpleIO__IOD_Monad__IO y), imported_SimpleIO__IOD_Monad__IO y)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x0 : Type => forall (_ : IO x) (_ : forall _ : x, IO x0), IO x0)
           (fun y0 : Type => forall (_ : imported_SimpleIO__IOD_Monad__IO y) (_ : forall _ : y, imported_SimpleIO__IOD_Monad__IO y0), imported_SimpleIO__IOD_Monad__IO y0)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
           (fun (x0 y0 : Type) (H0 : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x0 y0) =>
            @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (IO x) (imported_SimpleIO__IOD_Monad__IO y) (forall _ : forall _ : x, IO x0, IO x0)
              (forall _ : forall _ : y, imported_SimpleIO__IOD_Monad__IO y0, imported_SimpleIO__IOD_Monad__IO y0)
              (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (IO x) (imported_SimpleIO__IOD_Monad__IO y) (@SimpleIO__IOD_Monad__IO_iso x y H))
              (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : x, IO x0) (forall _ : y, imported_SimpleIO__IOD_Monad__IO y0) 
                 (IO x0) (imported_SimpleIO__IOD_Monad__IO y0)
                 (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (IO x0) (imported_SimpleIO__IOD_Monad__IO y0)
                    (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
                    (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (IO x0) (imported_SimpleIO__IOD_Monad__IO y0) (@SimpleIO__IOD_Monad__IO_iso x0 y0 H0)))
                 (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (IO x0) (imported_SimpleIO__IOD_Monad__IO y0) (@SimpleIO__IOD_Monad__IO_iso x0 y0 H0))))))
     (@IObind) imported_SimpleIO__IOD_Monad__IO__bind).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@IObind) SimpleIO__IOD_Monad__IO__bind_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@IObind) SimpleIO__IOD_Monad__IO__bind_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter IOret : forall {a}, a -> IO a.

Parameter imported_SimpleIO__IOD_Monad__IO__ret : forall y : Type, y -> imported_SimpleIO__IOD_Monad__IO y.
Parameter SimpleIO__IOD_Monad__IO__ret_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall _ : x, IO x)
        (fun H : Type => forall _ : H, imported_SimpleIO__IOD_Monad__IO H) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (IO x) (imported_SimpleIO__IOD_Monad__IO y)
           (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (IO x) (imported_SimpleIO__IOD_Monad__IO y) (@SimpleIO__IOD_Monad__IO_iso x y H))))
     (@IOret) imported_SimpleIO__IOD_Monad__IO__ret).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@IOret) SimpleIO__IOD_Monad__IO__ret_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@IOret) SimpleIO__IOD_Monad__IO__ret_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Global Instance Monad_IO : Monad IO := {
  ret _ := IOret;
  bind _ _ := IObind;
}.

Parameter imported_SimpleIO__IOD_Monad__MonadD_IO : import_of (@Monad_IO).
Parameter SimpleIO__IOD_Monad__MonadD_IO_iso : iso_statement (@Monad_IO) imported_SimpleIO__IOD_Monad__MonadD_IO.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Monad_IO) SimpleIO__IOD_Monad__MonadD_IO_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface36.

Module Type Interface37 (Import args : Args).

Parameter imported_Corelib__Init__Logic__and : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__and_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp (forall _ : Prop, Prop) (forall _ : SProp, SProp) (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Prop SProp (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))
     and imported_Corelib__Init__Logic__and).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.
 
Parameter imported_Corelib__Init__Logic__ex : forall y : Type, (y -> SProp) -> SProp.
Parameter Corelib__Init__Logic__ex_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall _ : forall _ : x, Prop, Prop)
        (fun H : Type => forall _ : forall _ : H, SProp, SProp) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : x, Prop) (forall _ : y, SProp) Prop SProp
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
           (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))
     (fun A => @ex A) imported_Corelib__Init__Logic__ex).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__subrelation : forall y y0 : Type, (y -> y0 -> SProp) -> (y -> y0 -> SProp) -> SProp.
Parameter Corelib__Init__Logic__subrelation_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type
        (fun x : Type => forall (B : Type) (_ : forall (_ : x) (_ : B), Prop) (_ : forall (_ : x) (_ : B), Prop), Prop)
        (fun H : Type => forall (y : Type) (_ : forall (_ : H) (_ : y), SProp) (_ : forall (_ : H) (_ : y), SProp), SProp) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type
           (fun x0 : Type => forall (_ : forall (_ : x) (_ : x0), Prop) (_ : forall (_ : x) (_ : x0), Prop), Prop)
           (fun y0 : Type => forall (_ : forall (_ : y) (_ : y0), SProp) (_ : forall (_ : y) (_ : y0), SProp), SProp) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
           (fun (x0 y0 : Type) (H0 : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x0 y0) =>
            @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall (_ : x) (_ : x0), Prop) (forall (_ : y) (_ : y0), SProp)
              (forall _ : forall (_ : x) (_ : x0), Prop, Prop) (forall _ : forall (_ : y) (_ : y0), SProp, SProp)
              (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (forall _ : x0, Prop) (forall _ : y0, SProp)
                 (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
                 (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x0 y0 Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x0 y0 H0)
                    (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))
              (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall (_ : x) (_ : x0), Prop) (forall (_ : y) (_ : y0), SProp) Prop SProp
                 (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (forall _ : x0, Prop) (forall _ : y0, SProp)
                    (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
                    (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x0 y0 Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x0 y0 H0)
                       (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))
                 (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))))
     subrelation imported_Corelib__Init__Logic__subrelation).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.subrelation) Corelib__Init__Logic__subrelation_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.subrelation) Corelib__Init__Logic__subrelation_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__unique : forall y : Type, (y -> SProp) -> y -> SProp.
Parameter Corelib__Init__Logic__unique_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall (_ : forall _ : x, Prop) (_ : x), Prop)
        (fun H : Type => forall (_ : forall _ : H, SProp) (_ : H), SProp) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : x, Prop) (forall _ : y, SProp) (forall _ : x, Prop) (forall _ : y, SProp)
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))))
     unique imported_Corelib__Init__Logic__unique).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.unique) Corelib__Init__Logic__unique_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.unique) Corelib__Init__Logic__unique_iso goal_lhs : typeclass_instances ur_typeclass_instances.

From Stdlib Require Import Logic.RelationalChoice.

Parameter imported_Stdlib__Logic__RelationalChoice__relationalD_choice : import_of (@Stdlib.Logic.RelationalChoice.relational_choice).
Parameter Stdlib__Logic__RelationalChoice__relationalD_choice_iso : iso_statement (@Stdlib.Logic.RelationalChoice.relational_choice) imported_Stdlib__Logic__RelationalChoice__relationalD_choice.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Logic.RelationalChoice.relational_choice) Stdlib__Logic__RelationalChoice__relationalD_choice_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Logic.RelationalChoice.relational_choice) Stdlib__Logic__RelationalChoice__relationalD_choice_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface37.

Module Type Interface38 (Import args : Args).

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__ex : forall y : Type, (y -> SProp) -> SProp.
Parameter Corelib__Init__Logic__ex_iso : iso_statement
     (@ex) imported_Corelib__Init__Logic__ex.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.ex) Corelib__Init__Logic__ex_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Parameter imported_LF__Basics__bool : Type.
Parameter LF__Basics__bool_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) bool imported_LF__Basics__bool).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@bool) LF__Basics__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@bool) LF__Basics__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Inductive Toy : Type := 
  | con1 : bool -> Toy
  | con2 : nat -> Toy -> Toy.

Parameter imported_LF__IndPrinciples__Toy : Type.
Parameter LF__IndPrinciples__Toy_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) Toy imported_LF__IndPrinciples__Toy).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Toy) LF__IndPrinciples__Toy_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Toy) LF__IndPrinciples__Toy_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Admitted. 

Parameter imported_LF__IndPrinciples__ToyD_correct : import_of (@Toy_correct).
Parameter LF__IndPrinciples__ToyD_correct_iso : iso_statement (@Toy_correct) imported_LF__IndPrinciples__ToyD_correct.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Toy_correct) LF__IndPrinciples__ToyD_correct_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Toy_correct) LF__IndPrinciples__ToyD_correct_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface38.

Module Type Interface39 (Import args : Args).

Class BagBinds A B T := { binds : T -> A -> B -> Prop }.

Parameter imported_SLF__LibContainer__BagBinds : import_of BagBinds.
Parameter SLF__LibContainer__BagBinds_iso : iso_statement BagBinds imported_SLF__LibContainer__BagBinds.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@BagBinds) SLF__LibContainer__BagBinds_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@BagBinds) SLF__LibContainer__BagBinds_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_SLF__LibContainer__BuildD_BagBinds : import_of (@Build_BagBinds).
Parameter SLF__LibContainer__BuildD_BagBinds_iso : iso_statement (@Build_BagBinds) imported_SLF__LibContainer__BuildD_BagBinds.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Build_BagBinds) SLF__LibContainer__BuildD_BagBinds_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Build_BagBinds) SLF__LibContainer__BuildD_BagBinds_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface39.


Module Type Interface40 (Import args : Args).

Class NatDed (A: Type) := mkNatDed {
  andp: A -> A -> A;
  orp: A -> A -> A;
  exp: forall {T:Type}, (T -> A) -> A;
  allp: forall {T:Type}, (T -> A) -> A;
  imp: A -> A -> A;
  prop: Prop -> A;
  derives: A -> A -> Prop;
  pred_ext: forall P Q, derives P Q -> derives Q P -> P=Q;
  derives_refl: forall P, derives P P;
  derives_trans: forall P Q R, derives P Q -> derives Q R -> derives P R;
  TT := prop True;
  FF := prop False;
  andp_right:  forall X P Q:A, derives X P -> derives X Q -> derives X (andp P Q);
  andp_left1:  forall P Q R:A, derives P R -> derives (andp P Q) R;
  andp_left2:  forall P Q R:A, derives Q R -> derives (andp P Q) R;
  orp_left: forall P Q R, derives P R -> derives Q R -> derives (orp P Q) R;
  orp_right1: forall P Q R, derives P Q -> derives P (orp Q R);
  orp_right2: forall P Q R, derives P R -> derives P (orp Q R);
  exp_right: forall {B: Type} (x:B) (P: A) (Q: B -> A),
                        derives P (Q x) -> derives P (exp Q);
  exp_left: forall {B: Type} (P: B -> A) (Q: A),
                      (forall x, derives (P x) Q) -> derives (exp P) Q;
  allp_left: forall {B}(P: B -> A) x Q, derives (P x) Q -> derives (allp P) Q;
  allp_right: forall {B}(P: A) (Q: B -> A),  (forall v, derives P (Q v)) -> derives P (allp Q);
  imp_andp_adjoint: forall P Q R, derives (andp P Q) R <-> derives P (imp Q R);
  prop_left: forall (P: Prop) Q, (P -> derives TT Q) -> derives (prop P) Q;
  prop_right: forall (P: Prop) Q, P -> derives Q (prop P);
  prop_imp_prop_left: forall (P Q: Prop), derives (imp (prop P) (prop Q)) (prop (P -> Q));
  allp_prop_left: forall {B: Type} (P: B -> Prop), derives (allp (fun b => prop (P b))) (prop (forall b, P b))
(* not_prop_right: forall (P:) (Q: Prop), (Q -> derives P FF) -> derives P (prop (not Q)) *)
}.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))))
     (fun A => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq).
Parameter imported_Corelib__Init__Logic__eq_Prop : forall y : SProp, y -> y -> SProp.

Parameter imported_VST__msl__seplog__NatDed : Type -> Type.
Parameter VST__msl__seplog__NatDed_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     NatDed imported_VST__msl__seplog__NatDed).
Definition plain_imported_VST__msl__seplog__NatDed : Type -> Type := imported_VST__msl__seplog__NatDed.
Parameter VST__msl__seplog__NatDed_iso_plain : iso_statement (@NatDed) plain_imported_VST__msl__seplog__NatDed.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@NatDed) VST__msl__seplog__NatDed_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@NatDed) VST__msl__seplog__NatDed_iso goal_lhs : typeclass_instances ur_typeclass_instances.


Parameter plain_imported_VST__msl__seplog__TT : import_of (@TT).
Parameter VST__msl__seplog__TT_iso_plain : iso_statement (@TT) plain_imported_VST__msl__seplog__TT.

End Interface40.

Module Type Interface41 (Import args : Args).

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : (@UR.pr _ _ _ (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent) False imported_Corelib__Init__Logic__False).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.False) Corelib__Init__Logic__False_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__and : SProp -> SProp -> SProp.
Parameter Corelib__Init__Logic__and_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp (forall _ : Prop, Prop) (forall _ : SProp, SProp) (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Prop SProp (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))
     and imported_Corelib__Init__Logic__and).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.and) Corelib__Init__Logic__and_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))))
     (fun A : Type => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 1 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.eq) Corelib__Init__Logic__eq_iso goal_lhs : typeclass_instances ur_typeclass_instances.
Parameter imported_Corelib__Init__Logic__eq_Prop : forall y : SProp, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso_Prop : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp (fun x : Prop => forall (_ : x) (_ : x), Prop) (fun H : SProp => forall (_ : H) (_ : H), SProp)
        (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (fun (x : Prop) (y : SProp) (H : @UR.pr _ _ _ (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type SProp Prop SProp ; _ _ _ _ _ _ _ _ _} UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen@{SProp Prop SProp ; _ _ _ _} UR.univalent x y H)
           (@UR.URArrow@{Type Type Type SProp Prop SProp ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{SProp Prop SProp ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))))
     (fun A : Prop => @Corelib.Init.Logic.eq A) imported_Corelib__Init__Logic__eq_Prop).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent ((fun A : Prop => @Corelib.Init.Logic.eq A)) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k ((fun A : Prop => @Corelib.Init.Logic.eq A)) Corelib__Init__Logic__eq_iso_Prop goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : SProp -> SProp.
Parameter Corelib__Init__Logic__not_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Prop SProp (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
     Logic.not imported_Corelib__Init__Logic__not).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Logic.not) Corelib__Init__Logic__not_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.nat) Corelib__Init__Datatypes__nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__O_iso : (@UR.pr _ _ _ (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso) O imported_Corelib__Init__Datatypes__O).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.O) Corelib__Init__Datatypes__O_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__S_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat nat imported_Corelib__Init__Datatypes__nat
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso))
     S imported_Corelib__Init__Datatypes__S).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.S) Corelib__Init__Datatypes__S_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sig : import_of (fun A P => @sig A P).
Parameter Corelib__Init__Specif__sig_iso : iso_statement
     (fun A P => @sig A P) (@imported_Corelib__Init__Specif__sig).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A P => @sig A P) Corelib__Init__Specif__sig_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A P => @sig A P) Corelib__Init__Specif__sig_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__exist : import_of (fun A P => @exist A P).
Parameter Corelib__Init__Specif__exist_iso : iso_statement
     (fun A P => @exist A P) (@imported_Corelib__Init__Specif__exist).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A P => @exist A P) Corelib__Init__Specif__exist_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A P => @Corelib.Init.Specif.exist A P) Corelib__Init__Specif__exist_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__proj1D_sig : import_of (@proj1_sig). 
Parameter Corelib__Init__Specif__proj1D_sig_iso : iso_statement (@proj1_sig) imported_Corelib__Init__Specif__proj1D_sig.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Specif.proj1_sig) Corelib__Init__Specif__proj1D_sig_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Specif.proj1_sig) Corelib__Init__Specif__proj1D_sig_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sigD_rect : forall (y : Type) (y0 : y -> SProp) (y1 : imported_Corelib__Init__Specif__sig y0 -> Type),
  (forall (y2 : y) (y3 : y0 y2), y1 (imported_Corelib__Init__Specif__exist y0 y2 y3)) -> forall y2 : imported_Corelib__Init__Specif__sig y0, y1 y2.
Parameter Corelib__Init__Specif__sigD_rect_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type
        (fun x : Type => forall (P : forall _ : x, Prop) (P0 : forall _ : @sig x P, Type) (_ : forall (x0 : x) (p : P x0), P0 (@exist x P x0 p)) (s : @sig x P), P0 s)
        (fun H : Type =>
         forall (y : forall _ : H, SProp) (y0 : forall _ : @imported_Corelib__Init__Specif__sig H y, Type) (_ : forall (y1 : H) (y2 : y y1), y0 (@imported_Corelib__Init__Specif__exist H y y1 y2))
           (y1 : @imported_Corelib__Init__Specif__sig H y),
         y0 y1)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : x, Prop) (forall _ : y, SProp)
           (fun x0 : forall _ : x, Prop => forall (P0 : forall _ : @sig x x0, Type) (_ : forall (x1 : x) (p : x0 x1), P0 (@exist x x0 x1 p)) (s : @sig x x0), P0 s)
           (fun y0 : forall _ : y, SProp =>
            forall (y1 : forall _ : @imported_Corelib__Init__Specif__sig y y0, Type) (_ : forall (y2 : y) (y3 : y0 y2), y1 (@imported_Corelib__Init__Specif__exist y y0 y2 y3))
              (y2 : @imported_Corelib__Init__Specif__sig y y0),
            y1 y2)
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
           (fun (x0 : forall _ : x, Prop) (y0 : forall _ : y, SProp)
              (H0 : @UR.pr _ _ _
                      (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
                         (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
                      x0 y0) =>
            @UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : @sig x x0, Type) (forall _ : @imported_Corelib__Init__Specif__sig y y0, Type)
              (fun x1 : forall _ : @sig x x0, Type => forall (_ : forall (x2 : x) (p : x0 x2), x1 (@exist x x0 x2 p)) (s : @sig x x0), x1 s)
              (fun y1 : forall _ : @imported_Corelib__Init__Specif__sig y y0, Type =>
               forall (_ : forall (y2 : y) (y3 : y0 y2), y1 (@imported_Corelib__Init__Specif__exist y y0 y2 y3)) (y2 : @imported_Corelib__Init__Specif__sig y y0), y1 y2)
              (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) Type Type
                 (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) (@Corelib__Init__Specif__sig_iso x y H x0 y0 H0))
                 (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
              (fun (x1 : forall _ : @sig x x0, Type) (y1 : forall _ : @imported_Corelib__Init__Specif__sig y y0, Type)
                 (H1 : @UR.pr _ _ _
                         (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) Type Type
                            (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) (@Corelib__Init__Specif__sig_iso x y H x0 y0 H0))
                            (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
                         x1 y1) =>
               @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall (x2 : x) (p : x0 x2), x1 (@exist x x0 x2 p))
                 (forall (y2 : y) (y3 : y0 y2), y1 (@imported_Corelib__Init__Specif__exist y y0 y2 y3)) (forall s : @sig x x0, x1 s) (forall y2 : @imported_Corelib__Init__Specif__sig y y0, y1 y2)
                 (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (fun x2 : x => forall p : x0 x2, x1 (@exist x x0 x2 p))
                    (fun y2 : y => forall y3 : y0 y2, y1 (@imported_Corelib__Init__Specif__exist y y0 y2 y3)) (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
                    (fun (x2 : x) (y2 : y) (H2 : @UR.pr _ _ _ (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H) x2 y2) =>
                     @UR.URForall@{Type Type Type SProp Prop SProp ; _ _ _ _ _ _ _ _ _} UR.univalent (x0 x2) (y0 y2) (fun x3 : x0 x2 => x1 (@exist x x0 x2 x3))
                       (fun y3 : y0 y2 => y1 (@imported_Corelib__Init__Specif__exist y y0 y2 y3)) (@UR.PR_Type_univ_univ@{SProp Prop SProp ; _ _ _ _} (x0 x2) (y0 y2) (H0 x2 y2 H2))
                       (fun (x3 : x0 x2) (y3 : y0 y2) (H3 : @UR.pr _ _ _ (@UR.PR_Type_univ_univ@{SProp Prop SProp ; _ _ _ _} (x0 x2) (y0 y2) (H0 x2 y2 H2)) x3 y3) =>
                        @UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (x1 (@exist x x0 x2 x3)) (y1 (@imported_Corelib__Init__Specif__exist y y0 y2 y3))
                          (H1 (@exist x x0 x2 x3) (@imported_Corelib__Init__Specif__exist y y0 y2 y3) (@Corelib__Init__Specif__exist_iso x y H x0 y0 H0 x2 y2 H2 x3 y3 H3)))))
                 (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) x1 y1
                    (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) (@Corelib__Init__Specif__sig_iso x y H x0 y0 H0))
                    (fun (x2 : @sig x x0) (y2 : @imported_Corelib__Init__Specif__sig y y0)
                       (H2 : @UR.pr _ _ _ (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (@sig x x0) (@imported_Corelib__Init__Specif__sig y y0) (@Corelib__Init__Specif__sig_iso x y H x0 y0 H0))
                               x2 y2) =>
                     @UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (x1 x2) (y1 y2) (H1 x2 y2 H2)))))))
     sig_rect imported_Corelib__Init__Specif__sigD_rect).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Specif.sig_rect) Corelib__Init__Specif__sigD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Specif.sig_rect) Corelib__Init__Specif__sigD_rect_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sumbool : SProp -> SProp -> Type.
Parameter Corelib__Init__Specif__sumbool_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp (forall _ : Prop, Type) (forall _ : SProp, Type) (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Type Type (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)))
     sumbool imported_Corelib__Init__Specif__sumbool).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Specif.sumbool) Corelib__Init__Specif__sumbool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Specif.sumbool) Corelib__Init__Specif__sumbool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sumor : Type -> SProp -> Type.
Parameter Corelib__Init__Specif__sumor_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (forall _ : Prop, Type) (forall _ : SProp, Type) (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Type Type (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
           (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)))
     (fun A B => sumor A B) imported_Corelib__Init__Specif__sumor).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (fun A B => @Corelib.Init.Specif.sumor A B) Corelib__Init__Specif__sumor_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (fun A B => @Corelib.Init.Specif.sumor A B) Corelib__Init__Specif__sumor_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__positive : Type.
Parameter Corelib__Numbers__BinNums__positive_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) BinNums.positive imported_Corelib__Numbers__BinNums__positive).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.positive) Corelib__Numbers__BinNums__positive_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__Z : Type.
Parameter Corelib__Numbers__BinNums__Z_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) BinNums.Z imported_Corelib__Numbers__BinNums__Z).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.Z) Corelib__Numbers__BinNums__Z_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__Zpos : imported_Corelib__Numbers__BinNums__positive -> imported_Corelib__Numbers__BinNums__Z.
Parameter Corelib__Numbers__BinNums__Zpos_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent BinNums.positive imported_Corelib__Numbers__BinNums__positive BinNums.Z imported_Corelib__Numbers__BinNums__Z
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} BinNums.positive imported_Corelib__Numbers__BinNums__positive Corelib__Numbers__BinNums__positive_iso)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} BinNums.Z imported_Corelib__Numbers__BinNums__Z Corelib__Numbers__BinNums__Z_iso))
     BinNums.Zpos imported_Corelib__Numbers__BinNums__Zpos).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.Zpos) Corelib__Numbers__BinNums__Zpos_iso goal_lhs : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.Zpos) Corelib__Numbers__BinNums__Zpos_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__xH : imported_Corelib__Numbers__BinNums__positive.
Parameter Corelib__Numbers__BinNums__xH_iso : (@UR.pr _ _ _ (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} BinNums.positive imported_Corelib__Numbers__BinNums__positive Corelib__Numbers__BinNums__positive_iso) BinNums.xH
     imported_Corelib__Numbers__BinNums__xH).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Numbers.BinNums.xH) Corelib__Numbers__BinNums__xH_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Numbers.BinNums.xH) Corelib__Numbers__BinNums__xH_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Arith__PeanoNat__Nat__pow : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Stdlib__Arith__PeanoNat__Nat__pow_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat (forall _ : nat, nat)
        (forall _ : imported_Corelib__Init__Datatypes__nat, imported_Corelib__Init__Datatypes__nat)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat nat imported_Corelib__Init__Datatypes__nat
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)))
     PeanoNat.Nat.pow imported_Stdlib__Arith__PeanoNat__Nat__pow).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Arith.PeanoNat.Nat.pow) Stdlib__Arith__PeanoNat__Nat__pow_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Arith.PeanoNat.Nat.pow) Stdlib__Arith__PeanoNat__Nat__pow_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__PArith__BinPos__Pos__ofD_nat : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Numbers__BinNums__positive.
Parameter Stdlib__PArith__BinPos__Pos__ofD_nat_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat BinNums.positive imported_Corelib__Numbers__BinNums__positive
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} BinNums.positive imported_Corelib__Numbers__BinNums__positive Corelib__Numbers__BinNums__positive_iso))
     BinPos.Pos.of_nat imported_Stdlib__PArith__BinPos__Pos__ofD_nat).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.PArith.BinPos.Pos.of_nat) Stdlib__PArith__BinPos__Pos__ofD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.PArith.BinPos.Pos.of_nat) Stdlib__PArith__BinPos__Pos__ofD_nat_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__QArith__QArithD_base__Q : Type.
Parameter Stdlib__QArith__QArithD_base__Q_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.QArith.QArith_base.Q) Stdlib__QArith__QArithD_base__Q_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.QArith.QArith_base.Q) Stdlib__QArith__QArithD_base__Q_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__QArith__QArithD_base__Qmake : imported_Corelib__Numbers__BinNums__Z -> imported_Corelib__Numbers__BinNums__positive -> imported_Stdlib__QArith__QArithD_base__Q.
Parameter Stdlib__QArith__QArithD_base__Qmake_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent BinNums.Z imported_Corelib__Numbers__BinNums__Z (forall _ : BinNums.positive, QArith_base.Q)
        (forall _ : imported_Corelib__Numbers__BinNums__positive, imported_Stdlib__QArith__QArithD_base__Q)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} BinNums.Z imported_Corelib__Numbers__BinNums__Z Corelib__Numbers__BinNums__Z_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent BinNums.positive imported_Corelib__Numbers__BinNums__positive QArith_base.Q
           imported_Stdlib__QArith__QArithD_base__Q
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} BinNums.positive imported_Corelib__Numbers__BinNums__positive Corelib__Numbers__BinNums__positive_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q Stdlib__QArith__QArithD_base__Q_iso)))
     QArith_base.Qmake imported_Stdlib__QArith__QArithD_base__Qmake).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.QArith.QArith_base.Qmake) Stdlib__QArith__QArithD_base__Qmake_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.QArith.QArith_base.Qmake) Stdlib__QArith__QArithD_base__Qmake_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__QArith__QArithD_base__Qplus : imported_Stdlib__QArith__QArithD_base__Q -> imported_Stdlib__QArith__QArithD_base__Q -> imported_Stdlib__QArith__QArithD_base__Q.
Parameter Stdlib__QArith__QArithD_base__Qplus_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q (forall _ : QArith_base.Q, QArith_base.Q)
        (forall _ : imported_Stdlib__QArith__QArithD_base__Q, imported_Stdlib__QArith__QArithD_base__Q)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q Stdlib__QArith__QArithD_base__Q_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q Stdlib__QArith__QArithD_base__Q_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q Stdlib__QArith__QArithD_base__Q_iso)))
     QArith_base.Qplus imported_Stdlib__QArith__QArithD_base__Qplus).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.QArith.QArith_base.Qplus) Stdlib__QArith__QArithD_base__Qplus_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.QArith.QArith_base.Qplus) Stdlib__QArith__QArithD_base__Qplus_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Reals__ClassicalDedekindReals__sigD_forallD_dec : forall y : imported_Corelib__Init__Datatypes__nat -> SProp,
  (forall y0 : imported_Corelib__Init__Datatypes__nat, imported_Corelib__Init__Specif__sumbool (y y0) (imported_Corelib__Init__Logic__not (y y0))) ->
  imported_Corelib__Init__Specif__sumor (imported_Corelib__Init__Specif__sig (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Logic__not (y y0)))
    (forall x : imported_Corelib__Init__Datatypes__nat, y x).
Parameter Stdlib__Reals__ClassicalDedekindReals__sigD_forallD_dec_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : nat, Prop) (forall _ : imported_Corelib__Init__Datatypes__nat, SProp)
        (fun x : forall _ : nat, Prop => forall _ : forall n : nat, sumbool (x n) (Logic.not (x n)), sumor (@sig nat (fun n : nat => Logic.not (x n))) (forall n : nat, x n))
        (fun H : forall _ : imported_Corelib__Init__Datatypes__nat, SProp =>
         forall _ : forall y : imported_Corelib__Init__Datatypes__nat, imported_Corelib__Init__Specif__sumbool (H y) (imported_Corelib__Init__Logic__not (H y)),
         imported_Corelib__Init__Specif__sumor
           (@imported_Corelib__Init__Specif__sig imported_Corelib__Init__Datatypes__nat (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Logic__not (H y0)))
           (forall x : imported_Corelib__Init__Datatypes__nat, H x))
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat Prop SProp
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso) (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
        (fun (x : forall _ : nat, Prop) (y : forall _ : imported_Corelib__Init__Datatypes__nat, SProp)
           (H : @UR.pr _ _ _
                  (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat Prop SProp
                     (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
                     (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
                  x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall n : nat, sumbool (x n) (Logic.not (x n)))
           (forall y0 : imported_Corelib__Init__Datatypes__nat, imported_Corelib__Init__Specif__sumbool (y y0) (imported_Corelib__Init__Logic__not (y y0)))
           (sumor (@sig nat (fun n : nat => Logic.not (x n))) (forall n : nat, x n))
           (imported_Corelib__Init__Specif__sumor
              (@imported_Corelib__Init__Specif__sig imported_Corelib__Init__Datatypes__nat (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Logic__not (y y0)))
              (forall x0 : imported_Corelib__Init__Datatypes__nat, y x0))
           (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat (fun x0 : nat => sumbool (x x0) (Logic.not (x x0)))
              (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Specif__sumbool (y y0) (imported_Corelib__Init__Logic__not (y y0)))
              (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso)
              (fun (x0 : nat) (y0 : imported_Corelib__Init__Datatypes__nat)
                 (H0 : @UR.pr _ _ _ (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso) x0 y0) =>
               @UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (sumbool (x x0) (Logic.not (x x0))) (imported_Corelib__Init__Specif__sumbool (y y0) (imported_Corelib__Init__Logic__not (y y0)))
                 (@Corelib__Init__Specif__sumbool_iso (x x0) (y y0) (H x0 y0 H0) (Logic.not (x x0)) (imported_Corelib__Init__Logic__not (y y0))
                    (@Corelib__Init__Logic__not_iso (x x0) (y y0) (H x0 y0 H0)))))
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} (sumor (@sig nat (fun n : nat => Logic.not (x n))) (forall n : nat, x n))
              (imported_Corelib__Init__Specif__sumor
                 (@imported_Corelib__Init__Specif__sig imported_Corelib__Init__Datatypes__nat (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Logic__not (y y0)))
                 (forall x0 : imported_Corelib__Init__Datatypes__nat, y x0))
              (@Corelib__Init__Specif__sumor_iso (@sig nat (fun n : nat => Logic.not (x n)))
                 (@imported_Corelib__Init__Specif__sig imported_Corelib__Init__Datatypes__nat (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Logic__not (y y0)))
                 (@Corelib__Init__Specif__sig_iso nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso (fun n : nat => Logic.not (x n))
                    (fun y0 : imported_Corelib__Init__Datatypes__nat => imported_Corelib__Init__Logic__not (y y0))
                    (fun (x0 : nat) (y0 : imported_Corelib__Init__Datatypes__nat)
                       (H0 : @UR.pr _ _ _ (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent nat imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso) x0 y0) =>
                     @Corelib__Init__Logic__not_iso (x x0) (y y0) (H x0 y0 H0)))
                 (forall n : nat, x n) (forall x0 : imported_Corelib__Init__Datatypes__nat, y x0)
                 (FP.FP_forall_ur@{Prop SProp SProp Type Type Type ; _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} nat
                    imported_Corelib__Init__Datatypes__nat Corelib__Init__Datatypes__nat_iso x y H)))))
     Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec imported_Stdlib__Reals__ClassicalDedekindReals__sigD_forallD_dec).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec) Stdlib__Reals__ClassicalDedekindReals__sigD_forallD_dec_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec) Stdlib__Reals__ClassicalDedekindReals__sigD_forallD_dec_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R : Type.
Parameter Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) Rdefinitions.RbaseSymbolsImpl.R imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Reals.Rdefinitions.RbaseSymbolsImpl.R) Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Reals.Rdefinitions.RbaseSymbolsImpl.R) Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Reals__Rdefinitions__Rle : imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R -> imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R -> SProp.
Parameter Stdlib__Reals__Rdefinitions__Rle_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Rdefinitions.RbaseSymbolsImpl.R imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R
        (forall _ : Rdefinitions.RbaseSymbolsImpl.R, Prop) (forall _ : imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R, SProp)
        (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Rdefinitions.RbaseSymbolsImpl.R imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R
           Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R_iso)
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Rdefinitions.RbaseSymbolsImpl.R imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R Prop SProp
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} Rdefinitions.RbaseSymbolsImpl.R imported_Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R
              Stdlib__Reals__Rdefinitions__RbaseSymbolsImpl__R_iso)
           (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)))
     Rdefinitions.Rle imported_Stdlib__Reals__Rdefinitions__Rle).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Reals.Rdefinitions.Rle) Stdlib__Reals__Rdefinitions__Rle_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Reals.Rdefinitions.Rle) Stdlib__Reals__Rdefinitions__Rle_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.bool) Corelib__Init__Datatypes__bool_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : (@UR.pr _ _ _ (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} bool imported_Corelib__Init__Datatypes__bool Corelib__Init__Datatypes__bool_iso) false imported_Corelib__Init__Datatypes__false).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.false) Corelib__Init__Datatypes__false_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : (@UR.pr _ _ _ (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} bool imported_Corelib__Init__Datatypes__bool Corelib__Init__Datatypes__bool_iso) true imported_Corelib__Init__Datatypes__true).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.Init.Datatypes.true) Corelib__Init__Datatypes__true_iso goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Reals__ClassicalDedekindReals__isLowerCut : (imported_Stdlib__QArith__QArithD_base__Q -> imported_Corelib__Init__Datatypes__bool) -> SProp.
Parameter Stdlib__Reals__ClassicalDedekindReals__isLowerCut_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent (forall _ : QArith_base.Q, bool)
        (forall _ : imported_Stdlib__QArith__QArithD_base__Q, imported_Corelib__Init__Datatypes__bool) Prop SProp
        (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q bool imported_Corelib__Init__Datatypes__bool
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} QArith_base.Q imported_Stdlib__QArith__QArithD_base__Q Stdlib__QArith__QArithD_base__Q_iso)
           (@UR.PR_Type_univ_univ@{Type Type Type ; _ _ _ _} bool imported_Corelib__Init__Datatypes__bool Corelib__Init__Datatypes__bool_iso))
        (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
     ClassicalDedekindReals.isLowerCut imported_Stdlib__Reals__ClassicalDedekindReals__isLowerCut).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Reals.ClassicalDedekindReals.isLowerCut) Stdlib__Reals__ClassicalDedekindReals__isLowerCut_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Reals.ClassicalDedekindReals.isLowerCut) Stdlib__Reals__ClassicalDedekindReals__isLowerCut_iso goal_lhs : typeclass_instances ur_typeclass_instances.

(* Parameter imported_Stdlib__Reals__ClassicalDedekindReals__DReal : Type.
Parameter Stdlib__Reals__ClassicalDedekindReals__DReal_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) ClassicalDedekindReals.DReal imported_Stdlib__Reals__ClassicalDedekindReals__DReal).
 *)
 #[export] Hint Extern 1 => progress (unfold Stdlib.Reals.ClassicalDedekindReals.DReal) : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Reals__ClassicalDedekindReals__DRealQlimExp2 : import_of (@Stdlib.Reals.ClassicalDedekindReals.DRealQlimExp2).
Parameter Stdlib__Reals__ClassicalDedekindReals__DRealQlimExp2_iso : iso_statement (@Stdlib.Reals.ClassicalDedekindReals.DRealQlimExp2) imported_Stdlib__Reals__ClassicalDedekindReals__DRealQlimExp2.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Stdlib.Reals.ClassicalDedekindReals.DRealQlimExp2) Stdlib__Reals__ClassicalDedekindReals__DRealQlimExp2_iso goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Stdlib.Reals.ClassicalDedekindReals.DRealQlimExp2) Stdlib__Reals__ClassicalDedekindReals__DRealQlimExp2_iso goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface41.

Module Type Interface42 (Import args : Args).

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : iso_statement (fun (A : Type) (x x0 : A) => @Corelib.Init.Logic.eq A x x0) imported_Corelib__Init__Logic__eq.
Parameter imported_Corelib__Init__Logic__eq_Prop : forall y : SProp, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso_Prop : iso_statement  (fun (A : Prop) (x x0 : A) => @Corelib.Init.Logic.eq A x x0) imported_Corelib__Init__Logic__eq_Prop.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_hlist  univalent(@Corelib.Init.Logic.eq) [(* ((fun A : Prop => @Corelib.Init.Logic.eq A)) *) Corelib__Init__Logic__eq_iso_Prop; Corelib__Init__Logic__eq_iso] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => 
  tc_hint_for_ur_plain_list k (@Corelib.Init.Logic.eq) [@Corelib__Init__Logic__eq_iso_Prop; @Corelib__Init__Logic__eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__ssr__ssrunder__UnderD_rel__UnderD_rel : forall y : Type, (y -> y -> SProp) -> y -> y -> SProp.
Parameter Corelib__ssr__ssrunder__UnderD_rel__UnderD_rel_iso : iso_statement (@ssrunder.Under_rel.Under_rel) imported_Corelib__ssr__ssrunder__UnderD_rel__UnderD_rel.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => 
  tc_hint_for_ur_plain_hlist univalent (@Corelib.ssr.ssrunder.Under_rel.Under_rel) [Corelib__ssr__ssrunder__UnderD_rel__UnderD_rel_iso] goal_lhs : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) =>
  tc_hint_for_ur_plain_list k (@Corelib.ssr.ssrunder.Under_rel.Under_rel) 
    [@Corelib__ssr__ssrunder__UnderD_rel__UnderD_rel_iso] 
    [] goal_lhs: typeclass_instances ur_typeclass_instances.

#[universes(polymorphic,collapse_sort_variables=no)]
Goal {B :_ & PR univalent (forall (A : Type) (eqA : A -> A -> Prop),
eq (ssrunder.Under_rel.Under_rel A eqA) eqA) B}.
Proof. 
  eexists. tc.
Abort.


Parameter imported_Corelib__ssr__ssrunder__UnderD_rel__UnderD_relE : import_of (@Corelib.ssr.ssrunder.Under_rel.Under_relE).
Parameter Corelib__ssr__ssrunder__UnderD_rel__UnderD_relE_iso : iso_statement (@Corelib.ssr.ssrunder.Under_rel.Under_relE) imported_Corelib__ssr__ssrunder__UnderD_rel__UnderD_relE.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for univalent (@Corelib.ssr.ssrunder.Under_rel.Under_relE) Corelib__ssr__ssrunder__UnderD_rel__UnderD_relE_iso [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k (@Corelib.ssr.ssrunder.Under_rel.Under_relE) Corelib__ssr__ssrunder__UnderD_rel__UnderD_relE_iso [] goal_lhs : typeclass_instances ur_typeclass_instances.

End Interface42.

Module Type Interface43 (Import args : Args).

Require Import List. 

Parameter imported_Corelib__Init__Datatypes__list : import_of list.
Parameter Corelib__Init__Datatypes__list_iso : iso_statement
 (fun A : Type => list A) imported_Corelib__Init__Datatypes__list.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.list) [Corelib__Init__Datatypes__list_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.list) [Corelib__Init__Datatypes__list_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.list)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__cons : import_of (@cons).
Parameter Corelib__Init__Datatypes__cons_iso : iso_statement (@cons) imported_Corelib__Init__Datatypes__cons.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.cons) [Corelib__Init__Datatypes__cons_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.cons) [Corelib__Init__Datatypes__cons_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.cons)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nil : forall y : Type, imported_Corelib__Init__Datatypes__list y.
Parameter Corelib__Init__Datatypes__nil_iso : (fun T : Type => nil) ≈[ _] imported_Corelib__Init__Datatypes__nil.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.nil) [Corelib__Init__Datatypes__nil_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.nil) [Corelib__Init__Datatypes__nil_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.nil)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eq : forall y : Type, y -> y -> SProp.
Parameter Corelib__Init__Logic__eq_iso : (@UR.pr _ _ _
     (@UR.URForall@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type (fun x : Type => forall (_ : x) (_ : x), Prop) (fun H : Type => forall (_ : H) (_ : H), SProp)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (fun (x y : Type) (H : @UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) x y) =>
         @UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y (forall _ : x, Prop) (forall _ : y, SProp) (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
           (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent x y Prop SProp (UR.PR_Type_gen@{Type Type Type ; _ _ _ _} UR.univalent x y H)
              (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))))
     (fun (A : Type) (x x0 : A) => @Corelib.Init.Logic.eq A x x0) imported_Corelib__Init__Logic__eq).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Logic.eq) [Corelib__Init__Logic__eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Logic.eq) [Corelib__Init__Logic__eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Logic.eq)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_refl : forall (y : Type) (y0 : y), imported_Corelib__Init__Logic__eq y0 y0.
Parameter Corelib__Init__Logic__eqD_refl_iso : (fun (A : Type) (x : A) => Logic.eq_refl) ≈[ _] imported_Corelib__Init__Logic__eqD_refl.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Logic.eq_refl) [Corelib__Init__Logic__eqD_refl_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Logic.eq_refl) [Corelib__Init__Logic__eqD_refl_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Logic.eq_refl)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__eqD_ind : forall (y : Type) (y0 : y) (y1 : y -> SProp), y1 y0 -> forall y2 : y, imported_Corelib__Init__Logic__eq y0 y2 -> y1 y2.
Parameter Corelib__Init__Logic__eqD_ind_iso : (fun (A : Type) (x : A) (P : A -> Prop) (eq_refl : P x) (y : A) (e : Corelib.Init.Logic.eq x y) => Logic.eq_ind x P eq_refl y e) ≈[ _] imported_Corelib__Init__Logic__eqD_ind.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Logic.eq_ind) [Corelib__Init__Logic__eqD_ind_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Logic.eq_ind) [Corelib__Init__Logic__eqD_ind_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Logic.eq_ind)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__bool : Type.
Parameter Corelib__Init__Datatypes__bool_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) bool imported_Corelib__Init__Datatypes__bool).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.bool) [Corelib__Init__Datatypes__bool_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.bool) [Corelib__Init__Datatypes__bool_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.bool)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__negb : imported_Corelib__Init__Datatypes__bool -> imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__negb_iso : (fun b : bool => negb b) ≈[ _] imported_Corelib__Init__Datatypes__negb.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.negb) [Corelib__Init__Datatypes__negb_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.negb) [Corelib__Init__Datatypes__negb_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.negb)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Lists__List__filter : forall y : Type, (y -> imported_Corelib__Init__Datatypes__bool) -> imported_Corelib__Init__Datatypes__list y -> imported_Corelib__Init__Datatypes__list y.
Parameter Stdlib__Lists__List__filter_iso : (fun (A : Type) (f : A -> bool) (l : list A) => List.filter f l) ≈[ _] imported_Stdlib__Lists__List__filter.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Stdlib.Lists.List.filter) [Stdlib__Lists__List__filter_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Stdlib.Lists.List.filter) [Stdlib__Lists__List__filter_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Stdlib.Lists.List.filter)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.


Variant atom : Set :=
| Num (n : Z)       (* Integers. *)
| Str (s : string)  (* Literal strings. *)
| Raw (s : string)  (* Simple atoms (e.g., ADT tags). *)
                    (* Should fit in this alphabet: [A-Za-z0-9-_.']. *)
.

Parameter imported_Ceres__CeresS__atom : Type.
Parameter Ceres__CeresS__atom_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) atom imported_Ceres__CeresS__atom).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@atom) [Ceres__CeresS__atom_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@atom) [Ceres__CeresS__atom_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@atom)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Inductive sexp_ (A : Type) :=
| Atom_ (a : A)
| List (xs : list (sexp_ A))
.

Parameter imported_Ceres__CeresS__sexpD_ : Type -> Type.
Parameter Ceres__CeresS__sexpD__iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     (fun A : Type => sexp_ A) imported_Ceres__CeresS__sexpD_).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@sexp_) [Ceres__CeresS__sexpD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@sexp_) [Ceres__CeresS__sexpD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@sexp_)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__Z : Type.
Parameter Corelib__Numbers__BinNums__Z_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) BinNums.Z imported_Corelib__Numbers__BinNums__Z).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Numbers.BinNums.Z) [Corelib__Numbers__BinNums__Z_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Numbers.BinNums.Z) [Corelib__Numbers__BinNums__Z_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Numbers.BinNums.Z)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Numbers__BinNums__positive : Type.
Parameter Corelib__Numbers__BinNums__positive_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) BinNums.positive imported_Corelib__Numbers__BinNums__positive).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Numbers.BinNums.positive) [Corelib__Numbers__BinNums__positive_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Numbers.BinNums.positive) [Corelib__Numbers__BinNums__positive_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Numbers.BinNums.positive)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__Ascii__ascii : Type.
Parameter Stdlib__Strings__Ascii__ascii_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) Ascii.ascii imported_Stdlib__Strings__Ascii__ascii).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Stdlib.Strings.Ascii.ascii) [Stdlib__Strings__Ascii__ascii_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Stdlib.Strings.Ascii.ascii) [Stdlib__Strings__Ascii__ascii_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Stdlib.Strings.Ascii.ascii)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Stdlib__Strings__String__string : Type.
Parameter Stdlib__Strings__String__string_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) String.string imported_Stdlib__Strings__String__string).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Stdlib.Strings.String.string) [Stdlib__Strings__String__string_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Stdlib.Strings.String.string) [Stdlib__Strings__String__string_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Stdlib.Strings.String.string)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__nat : Type.
Parameter Corelib__Init__Datatypes__nat_iso : (@UR.pr _ _ _ (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent) nat imported_Corelib__Init__Datatypes__nat).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.nat) [Corelib__Init__Datatypes__nat_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.nat) [Corelib__Init__Datatypes__nat_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.nat)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__O : imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__O_iso : 0 ≈[ _] imported_Corelib__Init__Datatypes__O.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.O) [Corelib__Init__Datatypes__O_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.O) [Corelib__Init__Datatypes__O_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.O)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Peano__lt : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> SProp.
Parameter Corelib__Init__Peano__lt_iso : (fun n m : nat => n < m) ≈[ _] imported_Corelib__Init__Peano__lt.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Peano.lt) [Corelib__Init__Peano__lt_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Peano.lt) [Corelib__Init__Peano__lt_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Peano.lt)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__length : forall y : Type, imported_Corelib__Init__Datatypes__list y -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__length_iso : (fun (A : Type) (x : list A) => length x) ≈[ _] imported_Corelib__Init__Datatypes__length.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.length) [Corelib__Init__Datatypes__length_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.length) [Corelib__Init__Datatypes__length_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.length)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Peano__le : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat -> SProp.
Parameter Corelib__Init__Peano__le_iso : (fun n x : nat => (n <= x)%nat) ≈[ _] imported_Corelib__Init__Peano__le.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Peano.le) [Corelib__Init__Peano__le_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Peano.le) [Corelib__Init__Peano__le_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Peano.le)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

(*
Parameter imported_HTTP__Tcp__filterD_length : forall (y : Type) (y0 : y -> imported_Corelib__Init__Datatypes__bool) (y1 : imported_Corelib__Init__Datatypes__list y),
  imported_Corelib__Init__Peano__le (imported_Corelib__Init__Datatypes__length (imported_Stdlib__Lists__List__filter y0 y1)) (imported_Corelib__Init__Datatypes__length y1).
Parameter HTTP__Tcp__filterD_length_iso : (fun (A : Type) (f : A -> bool) (l : list A) => Tcp.filter_length f l) ≈[ _] imported_HTTP__Tcp__filterD_length.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@HTTP.Tcp.filter_length) [HTTP__Tcp__filterD_length_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k_ur_plain_list (@HTTP.Tcp.filter_length) [HTTP__Tcp__filterD_length_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@HTTP.Tcp.filter_length)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
*)
Parameter imported_Corelib__Init__Datatypes__false : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__false_iso : false ≈[ _] imported_Corelib__Init__Datatypes__false.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.false) [Corelib__Init__Datatypes__false_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.false) [Corelib__Init__Datatypes__false_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.false)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__true : imported_Corelib__Init__Datatypes__bool.
Parameter Corelib__Init__Datatypes__true_iso : true ≈[ _] imported_Corelib__Init__Datatypes__true.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.true) [Corelib__Init__Datatypes__true_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.true) [Corelib__Init__Datatypes__true_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.true)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__boolD_rect : forall y : imported_Corelib__Init__Datatypes__bool -> Type,
  y imported_Corelib__Init__Datatypes__true -> y imported_Corelib__Init__Datatypes__false -> forall y0 : imported_Corelib__Init__Datatypes__bool, y y0.
Parameter Corelib__Init__Datatypes__boolD_rect_iso : (fun (P : bool -> Type) (true : P true) (false : P false) (b : bool) => bool_rect P true false b) ≈[ _] imported_Corelib__Init__Datatypes__boolD_rect.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.bool_rect) [Corelib__Init__Datatypes__boolD_rect_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.bool_rect) [Corelib__Init__Datatypes__boolD_rect_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.bool_rect)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__S : imported_Corelib__Init__Datatypes__nat -> imported_Corelib__Init__Datatypes__nat.
Parameter Corelib__Init__Datatypes__S_iso : (fun x : nat => S x) ≈[ _] imported_Corelib__Init__Datatypes__S.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.S) [Corelib__Init__Datatypes__S_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.S) [Corelib__Init__Datatypes__S_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.S)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Peano__leD_nD_S : forall y y0 : imported_Corelib__Init__Datatypes__nat,
  imported_Corelib__Init__Peano__le y y0 -> imported_Corelib__Init__Peano__le (imported_Corelib__Init__Datatypes__S y) (imported_Corelib__Init__Datatypes__S y0).
Parameter Corelib__Init__Peano__leD_nD_S_iso : (fun (n m : nat) (x : (n <= m)%nat) => le_n_S n m x) ≈[ _] imported_Corelib__Init__Peano__leD_nD_S.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Peano.le_n_S) [Corelib__Init__Peano__leD_nD_S_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Peano.le_n_S) [Corelib__Init__Peano__leD_nD_S_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Peano.le_n_S)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sumbool : import_of (@sumbool).
Parameter Corelib__Init__Specif__sumbool_iso : iso_statement (@sumbool) imported_Corelib__Init__Specif__sumbool.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Specif.sumbool) [Corelib__Init__Specif__sumbool_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Specif.sumbool) [Corelib__Init__Specif__sumbool_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Specif.sumbool)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__left : forall y y0 : SProp, y -> imported_Corelib__Init__Specif__sumbool y y0.
Parameter Corelib__Init__Specif__left_iso : (fun (A B : Prop) (x : A) => left x) ≈[ _] imported_Corelib__Init__Specif__left.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Specif.left) [Corelib__Init__Specif__left_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Specif.left) [Corelib__Init__Specif__left_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Specif.left)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__right : forall y y0 : SProp, y0 -> imported_Corelib__Init__Specif__sumbool y y0.
Parameter Corelib__Init__Specif__right_iso : (fun (A B : Prop) (x : B) => right x) ≈[ _] imported_Corelib__Init__Specif__right.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Specif.right) [Corelib__Init__Specif__right_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Specif.right) [Corelib__Init__Specif__right_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Specif.right)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Specif__sumboolD_rect : forall (y y0 : SProp) (y1 : imported_Corelib__Init__Specif__sumbool y y0 -> Type),
  (forall y2 : y, y1 (imported_Corelib__Init__Specif__left y0 y2)) ->
  (forall y2 : y0, y1 (imported_Corelib__Init__Specif__right y y2)) -> forall y2 : imported_Corelib__Init__Specif__sumbool y y0, y1 y2.
Parameter Corelib__Init__Specif__sumboolD_rect_iso : (fun (A B : Prop) (P : {A} + {B} -> Type) (left : forall a : A, P (left a)) (right : forall b : B, P (right b)) (s : {A} + {B}) => sumbool_rect P left right s)
  ≈[ _] imported_Corelib__Init__Specif__sumboolD_rect.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Specif.sumbool_rect) [Corelib__Init__Specif__sumboolD_rect_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Specif.sumbool_rect) [Corelib__Init__Specif__sumboolD_rect_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Specif.sumbool_rect)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__False : SProp.
Parameter Corelib__Init__Logic__False_iso : (@UR.pr _ _ _ (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent) False imported_Corelib__Init__Logic__False).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Logic.False) [Corelib__Init__Logic__False_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Logic.False) [Corelib__Init__Logic__False_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Logic.False)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__not : SProp -> SProp.
Parameter Corelib__Init__Logic__not_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Prop SProp (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent))
     (fun A : Prop => Logic.not A) imported_Corelib__Init__Logic__not).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Logic.not) [Corelib__Init__Logic__not_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Logic.not) [Corelib__Init__Logic__not_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Logic.not)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 => progress (unfold Corelib.Init.Logic.not) : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__ssr__ssrbool__decidable : SProp -> Type.
Parameter Corelib__ssr__ssrbool__decidable_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Type Type (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     (fun P : Prop => ssrbool.decidable P) imported_Corelib__ssr__ssrbool__decidable).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.ssr.ssrbool.decidable) [Corelib__ssr__ssrbool__decidable_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.ssr.ssrbool.decidable) [Corelib__ssr__ssrbool__decidable_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.ssr.ssrbool.decidable)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 1 => progress (unfold Corelib.ssr.ssrbool.decidable) : typeclass_instances ur_typeclass_instances.

Class Dec (P : Prop) : Type := { dec : ssrbool.decidable P }.
Parameter imported_QuickChick__Decidability__Dec : SProp -> Type.
Parameter QuickChick__Decidability__Dec_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Prop SProp Type Type (UR.PR_Type@{Prop SProp SProp ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     (fun P : Prop => Dec P) imported_QuickChick__Decidability__Dec).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent(@Dec) [QuickChick__Decidability__Dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Dec) [QuickChick__Decidability__Dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Dec)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_QuickChick__Decidability__dec : forall y : SProp, imported_QuickChick__Decidability__Dec y -> imported_Corelib__Init__Specif__sumbool y (y -> imported_Corelib__Init__Logic__False).
Parameter QuickChick__Decidability__dec_iso : iso_statement (@dec) imported_QuickChick__Decidability__dec.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@dec) [QuickChick__Decidability__dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@dec) [QuickChick__Decidability__dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@dec)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_QuickChick__Decidability__BuildD_Dec : forall y : SProp, imported_Corelib__Init__Specif__sumbool y (y -> imported_Corelib__Init__Logic__False) -> imported_QuickChick__Decidability__Dec y.
Parameter QuickChick__Decidability__BuildD_Dec_iso : (fun (P : Prop) (dec : ssrbool.decidable P) => {| dec := dec |}) ≈[ _] imported_QuickChick__Decidability__BuildD_Dec.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Build_Dec) [QuickChick__Decidability__BuildD_Dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Build_Dec) [QuickChick__Decidability__BuildD_Dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Build_Dec)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Class Dec_Eq (A : Type) :=
       {
         dec_eq : forall (x y : A), ssrbool.decidable (eq x y)
       }.
Parameter imported_QuickChick__Decidability__DecD_Eq : Type -> Type.
Parameter QuickChick__Decidability__DecD_Eq_iso : (@UR.pr _ _ _
     (@UR.URArrow@{Type Type Type Type Type Type ; _ _ _ _ _ _ _ _ _} UR.univalent Type Type Type Type (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent)
        (UR.PR_Type@{Type Type Type ; _ _ _ _} UR.univalent))
     (fun A : Type => Dec_Eq A) imported_QuickChick__Decidability__DecD_Eq).
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Dec_Eq) [QuickChick__Decidability__DecD_Eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Dec_Eq) [QuickChick__Decidability__DecD_Eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Dec_Eq)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_QuickChick__Decidability__decD_eq : forall y : Type,
  imported_QuickChick__Decidability__DecD_Eq y ->
  forall y0 y1 : y, imported_Corelib__Init__Specif__sumbool (imported_Corelib__Init__Logic__eq y0 y1) (imported_Corelib__Init__Logic__eq y0 y1 -> imported_Corelib__Init__Logic__False).
Parameter QuickChick__Decidability__decD_eq_iso : (fun (A : Type) (Dec_Eq : Dec_Eq A) (x y : A) => dec_eq x y) ≈[ _] imported_QuickChick__Decidability__decD_eq.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@dec_eq) [QuickChick__Decidability__decD_eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@dec_eq) [QuickChick__Decidability__decD_eq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@dec_eq)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Instance Dec_Eq_implies_DecEq {A} `{H : Dec_Eq A} (x y : A) : Dec (eq x y).
Admitted.

Parameter imported_QuickChick__Decidability__DecD_EqD_impliesD_DecEq : forall y : Type, imported_QuickChick__Decidability__DecD_Eq y -> forall y0 y1 : y, imported_QuickChick__Decidability__Dec (imported_Corelib__Init__Logic__eq y0 y1).
Parameter QuickChick__Decidability__DecD_EqD_impliesD_DecEq_iso : (fun (A : Type) (H : Dec_Eq A) (x y : A) => Dec_Eq_implies_DecEq x y) ≈[ _] imported_QuickChick__Decidability__DecD_EqD_impliesD_DecEq.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Dec_Eq_implies_DecEq) [QuickChick__Decidability__DecD_EqD_impliesD_DecEq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Dec_Eq_implies_DecEq) [QuickChick__Decidability__DecD_EqD_impliesD_DecEq_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Dec_Eq_implies_DecEq)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

(* Parameter imported_HTTP__Tcp__nodupD_funcD_obligationD_1 : import_of (@HTTP.Tcp.nodup_func_obligation_1).
Parameter HTTP__Tcp__nodupD_funcD_obligationD_1_iso : iso_statement (@HTTP.Tcp.nodup_func_obligation_1) imported_HTTP__Tcp__nodupD_funcD_obligationD_1.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@HTTP.Tcp.nodup_func_obligation_1) [HTTP__Tcp__nodupD_funcD_obligationD_1_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for k_ur_plain_list (@HTTP.Tcp.nodup_func_obligation_1) [HTTP__Tcp__nodupD_funcD_obligationD_1_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@HTTP.Tcp.nodup_func_obligation_1)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
 *)
End Interface43.



Module Type Interface44 (Import args : Args).

Class Decision (P : Prop) := decide : {P} + {not P}.

Parameter imported_stdpp__base__Decision : import_of (@Decision).
Parameter stdpp__base__Decision_iso : iso_statement (@Decision) imported_stdpp__base__Decision.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Decision) [stdpp__base__Decision_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Decision) [stdpp__base__Decision_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Decision)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__prod : import_of (@Corelib.Init.Datatypes.prod).
Parameter Corelib__Init__Datatypes__prod_iso : iso_statement (@Corelib.Init.Datatypes.prod) imported_Corelib__Init__Datatypes__prod.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.prod) [Corelib__Init__Datatypes__prod_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.prod) [Corelib__Init__Datatypes__prod_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.prod)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Datatypes__uncurry : import_of (@Corelib.Init.Datatypes.uncurry).
Parameter Corelib__Init__Datatypes__uncurry_iso : iso_statement (@Corelib.Init.Datatypes.uncurry) imported_Corelib__Init__Datatypes__uncurry.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Corelib.Init.Datatypes.uncurry) [Corelib__Init__Datatypes__uncurry_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Corelib.Init.Datatypes.uncurry) [Corelib__Init__Datatypes__uncurry_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Datatypes.uncurry)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Instance uncurry_dec A B P `(P_dec : forall (x : A) (y : B), Decision (P x y)) p :
    Decision (uncurry P p).
Admitted.

Parameter imported_stdpp__decidable__uncurryD_dec : import_of (@uncurry_dec).
Parameter stdpp__decidable__uncurryD_dec_iso : iso_statement (@uncurry_dec) imported_stdpp__decidable__uncurryD_dec.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@uncurry_dec) [stdpp__decidable__uncurryD_dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@uncurry_dec) [stdpp__decidable__uncurryD_dec_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@uncurry_dec)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

End Interface44.

Module Type Interface45 (Import args : Args).

Definition binary (A : Type) := A -> A -> Prop.
Class Gt (A : Type) := { gt : binary A }.

Parameter imported_TLC__LibOrder__Gt : import_of Gt.
Parameter TLC__LibOrder__Gt_iso : iso_statement (@Gt) imported_TLC__LibOrder__Gt.
Parameter TLC__LibOrder__Gt_iso_plain : plain_iso_statement (@Gt) imported_TLC__LibOrder__Gt.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Gt) [TLC__LibOrder__Gt_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr univalent ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Gt) [TLC__LibOrder__Gt_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr plain ?goal_lhs _) => tc_hint_for_ur_plain_list plain (@Gt) [TLC__LibOrder__Gt_iso_plain] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.plain (@Gt)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Definition irrefl A (R:binary A) :=
  forall x, ~ (R x x).

Class Gt_irrefl A `{Gt A} :=
  { gt_irrefl : @irrefl A gt }.

Parameter plain_imported_TLC__LibOrder__GtD_irrefl : plain_import_of (@Gt_irrefl).
Parameter TLC__LibOrder__GtD_irrefl_iso_plain : plain_iso_statement (@Gt_irrefl) plain_imported_TLC__LibOrder__GtD_irrefl.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list univalent (@Gt_irrefl) [] [TLC__LibOrder__GtD_irrefl_iso_plain] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr ?k ?goal_lhs _) => tc_hint_for_ur_plain_list k (@Gt_irrefl) [] [TLC__LibOrder__GtD_irrefl_iso_plain] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.plain (@Gt_irrefl)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

End Interface45.

Module Interface46.

  (* context *)
  Inductive kind : Set := isProp | isBool.
  Inductive sTrue : SProp := sI.
  Definition rtyp (k : kind) : Type := match k with isProp => Prop | isBool => bool end.
  Definition hold (k : kind) : rtyp k -> Prop :=
    match k return rtyp k -> Prop with
    | isProp => (fun x => x)
    | isBool => (fun _ : bool => True)
    end.
  Definition eval_bf {A} (ea : forall k, A -> rtyp k) (k : kind) (f : A) : rtyp k := ea k f.

  (* Import Kind. *)
  Parameter imported_kind : plain_import_of (@kind).
  Parameter kind_iso : plain_iso_statement (@kind) imported_kind.
  #[export] Hint Extern 1 (PR plain ?g _) => tc_hint_for plain (@kind) kind_iso g : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr ?k ?g _) => tc_hint_for k (@kind) kind_iso g : typeclass_instances ur_typeclass_instances.


  (* Import isProp *)
  Parameter imported_isProp : plain_import_of (@isProp).
  Parameter isProp_iso : plain_iso_statement (@isProp) imported_isProp.
  #[export] Hint Extern 1 (PR plain ?g _) => tc_hint_for plain (@isProp) isProp_iso g : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr ?k ?g _) => tc_hint_for k (@isProp) isProp_iso g : typeclass_instances ur_typeclass_instances.

    (* Import isBool *)
  Parameter imported_isBool : plain_import_of (@isBool).
  Parameter isBool_iso : plain_iso_statement (@isBool) imported_isBool.
  #[export] Hint Extern 1 (PR plain ?g _) => tc_hint_for plain (@isBool) isBool_iso g : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr ?k ?g _) => tc_hint_for k (@isBool) isBool_iso g : typeclass_instances ur_typeclass_instances.

  (* [imported_rtyp : imported_kind -> Type]: opaque constant does not reduce on imported_isProp. *)
  Parameter imported_rtyp : plain_import_of (@rtyp).
  Parameter rtyp_iso : plain_iso_statement (@rtyp) imported_rtyp.
  #[export] Hint Extern 1 (PR plain ?g _) => tc_hint_for plain (@rtyp) rtyp_iso g : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr ?k ?g _) => tc_hint_for k (@rtyp) rtyp_iso g : typeclass_instances ur_typeclass_instances.

  (* import hold *)
  Parameter imported_hold : plain_import_of (fun k x => @hold k x).
  Parameter hold_iso : plain_iso_statement (fun k x => @hold k x) imported_hold.
  #[export] Hint Extern 1 (PR plain ?g _) => tc_hint_for plain (fun k x => @hold k x) hold_iso g : typeclass_instances ur_typeclass_instances.
  #[export] Hint Extern 1 (UR.pr plain ?g _) => tc_hint_for plain (fun k x => @hold k x) hold_iso g : typeclass_instances ur_typeclass_instances.

  (* Import eval_bf *)
  Parameter imported_eval_bf : plain_import_of (fun A ea k f => @eval_bf A ea k f).
  Parameter eval_bf_iso : plain_iso_statement (@eval_bf) imported_eval_bf.
  Parameter imported_eval_bf_isProp : plain_import_of (fun A ea f => @eval_bf A ea isProp f).
  Parameter eval_bf_iso_isProp : plain_iso_statement (fun A ea f => @eval_bf A ea isProp f) imported_eval_bf_isProp.

  #[export] Hint Extern 1 (UR.pr plain ?g _) => tc_hint_for_ur_plain_list plain (@eval_bf) [eval_bf_iso;eval_bf_iso_isProp] [] g : typeclass_instances ur_typeclass_instances.

  (* If a term of type [imported_rtyp isProp] is expected, [eval_bf] should be translated as usual *)
  Goal forall (A A' : Type) (AR : A ≈p A')
        (ea  : forall k, A  -> rtyp k)
        (ea' : forall k' : imported_kind, A' -> imported_rtyp k')
        (eaR : ea ≈p ea')
        (f : A) (f' : A') (fR : f ≈p f'),
      { B : _ & (hold isProp (@eval_bf A ea isProp f)) ≈p B }.
  Proof.
    intros. eexists. tc.
  Qed.

  #[universes(polymorphic,collapse_sort_variables=no)]
  Goal forall (A A' : Type) (AR : A ≈p A')
        (ea  : forall k, A  -> rtyp k)
        (ea' : forall k' : imported_kind, A' -> imported_rtyp k')
        (eaR : ea ≈p ea')
        (f : A) (f' : A') (fR : f ≈p f'),
      { B : _ & (hold isProp (@eval_bf A ea isProp f)) ≈p B }.
  Proof.
    intros.
unshelve refine (let f : {B : _ & PR plain
   (forall (k : kind) (_ : A), rtyp k) 
   B} := _ in _).
    eexists. tc.
    (* this failure is weird *)
    Fail unshelve refine (let t' := _ : _ in let t'' : @pr plain _ _ _ ea t' := _ in _); shelve_non_PR.
  Abort. 

  (* However, as a type it fail as the type of [imported_eval_bf] is [imported_rtype imported_isProp]
     which does not compute since [imported_rtype] is abstract *)
  #[universes(polymorphic,collapse_sort_variables=no)]
  Goal forall (A A' : Type) (AR : A ≈p A')
        (ea  : forall k, A  -> rtyp k)
        (ea' : _)
        (eaR : ea ≈p ea')
        (f : A) (f' : A') (fR : f ≈p f'),
        { B : _ & (@eval_bf A ea isProp f) ≈p B }. 
  Proof.
    intros. 
    eexists. 
    Fail tc.  
  Abort.

  #[export] Hint Extern 1 (UR.pr ?k ?g _) => tc_hint_for_specialize_arg (@eval_bf) eval_bf_iso_isProp g : typeclass_instances ur_typeclass_instances.

  (* The usual example still works *)
  Goal forall (A A' : Type) (AR : A ≈p A')
      (ea  : forall k, A  -> rtyp k)
      (ea' : forall k' : imported_kind, A' -> imported_rtyp k')
      (eaR : ea ≈p ea')
      (f : A) (f' : A') (fR : f ≈p f'),
      { B : _ & (hold isProp (@eval_bf A ea isProp f)) ≈p B }.
  Proof.
    intros. eexists. tc.
  Qed.

  (* It now succeds in a sort position due to new hint  *)
  Goal forall (A A' : Type) (AR : A ≈p A')
      (ea  : forall k, A  -> rtyp k)
      (ea' : forall k' : imported_kind, A' -> imported_rtyp k')
      (eaR : ea ≈p ea')
      (f : A) (f' : A') (fR : f ≈p f'),
      { B : _ & (@eval_bf A ea isProp f) ≈p B }.
  Proof.
    intros. eexists. tc.
  Qed.

End Interface46.

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
  -> UR_list ur (vector_to_list A A (Equiv_id) n n idpath v) .1
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
           (canA := ur_refl)
           (canB := ur_refl B)
  :
UR_list ur (vector_to_list A A (Equiv_id) n n idpath v) .1
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
           (canA := ur_refl)
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
    + destruct (UR_list_decompose ur (h :: (vector_to_list A A (Equiv_id) n n idpath v) .1)
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
  pose (canA := ur_refl). pose (canB := ur_refl B).
  refine (transport_eq (fun X => (Equiv_vector_list A A n n idpath v
   ≈ Equiv_vector_list B B n' n' idpath (Equiv_Vector A B (equiv H) n n' en v')) ≃ (X = _))
                       (e_sect (vector_to_list A A _ n n _) v) _).
  refine (transport_eq (fun X => (Equiv_vector_list A A n n idpath v
   ≈ Equiv_vector_list B B n' n' idpath (Equiv_Vector A B (equiv H) n n' en v')) ≃ (_ = X))
                       (e_sect (vector_to_list A A _ n n _) v') _).
  assert (vector_to_list B B (Equiv_id B) n' n' idpath
                         (Equiv_Vector_fun A B (equiv H) n n' en v')
          = ↑ (vector_to_list A A (Equiv_id) n n idpath v')).
  { clear. destruct en. apply path_sigma_uncurried.
    unshelve eexists; [idtac | apply is_hset].
    destruct v'. reflexivity. cbn. apply ap. induction v'; cbn.
    - reflexivity.
    - apply ap. exact IHv'.
  }
  cbn. rewrite X; clear X.
  set (vector_to_list A A (Equiv_id) n n idpath v).
  set (vector_to_list A A (Equiv_id) n n idpath v').
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

Instance UR_type_of_ap : UR (forall (A B : Type) (f : A -> B) (x y :), x = y -> f x = f y)(forall (A B : Type) (f : A -> B) (x y :), x = y -> f x = f y).
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

Definition Canonical_eq_sig A :=   {can_eq : forall (x y :), x = y -> x = y &
    forall x, can_eq x x idpath = idpath }.

Instance issig_Canonical_eq A : Canonical_eq_sig A ≃ Canonical_eq A.
Proof.
  unfold Canonical_eq_sig.
  issig (Build_Canonical_eq) (@can_eq) (@can_idpath).
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

Definition Snil {A} : Svector A := (O ; nil).

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

Definition UR_list_Svector_fun (A B:Type) (e : A ≈ B) (l : list) (l':list B) :
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

Definition UR_list_Svector_inv (A B:Type) (e : A ≈ B) (l : list) (l':list B) :
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
       (fun (H0 :) (_ : list) (H2 : list B) => univalent_transport H0 :: H2) a') ≃ UR_list_vect ur a
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
    P Snil -> (forall (a :) (l : Svector), P l -> P (Svcons a l)) -> forall l : Svector A, P l.
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