(************************************************************************)
(* This file contains basic definitions of UR that are helpful for many examples  *)
(************************************************************************)

Set Polymorphic Inductive Cumulativity. 

Set Universe Polymorphism.

Unset Universe Minimization ToSet.

Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.UR Record.

(*! FP for Sigma !*)

Definition exist_eq {A P} (a a': A) (l : P a) (l' : P a') (e : a = a') :
  e # l = l' -> existT _ a l = (a'; l').
Proof. intros e'; destruct e, e'; reflexivity. Defined.

Definition sigma_map {A B P Q} (f: A -> B) (g : forall a, P a -> Q (f a)) (l : sigT P) : sigT Q :=
  match l with
  | existT _ a l => existT _ (f a) (g a l)
  end. 

Definition sigma_map_compose {A B C P Q R } (f: A -> B) (f' : B -> C)
           (g : forall a, P a -> Q (f a)) (g' : forall b, Q b -> R (f' b))
           (l : sigT P):
  sigma_map f' g' (sigma_map f g l) = sigma_map (f' ∘ f) (fun a l => g' (f a) (g a l)) l.
Proof.
  destruct l; reflexivity.
Defined.

Definition sigma_map_eq {A P} (f: A -> A) (g : forall a, P a -> P (f a))
           (H : forall x, f x = x) (H' : forall a (l : P a), H a # g a l = l) (l : sigT P) :
 sigma_map f g l = l.
Proof.
  induction l using sigT_rect; unshelve refine (exist_eq _ _ _ _ _ _); eauto.
Defined.

(* Equiv_Sigma is similar to equiv_functor_sigma *)
(* in the [https://github.com/HoTT] *)

#[universes(collapse_sort_variables=no)]
Axiom todo : forall A, A. 

Definition Equiv_Sigma (A A':Type) (e : A ≈u A') (B : A -> Type) (B' : A' -> Type) 
     (e' : B ≈u B') : (sigT B) ≃ (sigT B').          
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - unshelve refine (sigma_map univalent_transport (fun a => univalent_transport)); tc. 
    (* eapply (equiv e). eapply (e' a _ (ur_refl_ e a)). *)
  - unshelve refine (sigma_map univalent_transport (fun a => univalent_transport)).
    apply Equiv_inverse; typeclasses eauto.
    pose (einv := UR_Type_Inverse _ _ e).
    pose (einv' := fun x y E => UR_Type_Inverse _ _ (e' y x E)).
    unshelve refine (equiv (einv' a (e_fun (equiv einv) a) (ur_refl einv a))).
  - intro E. rewrite sigma_map_compose.
    unfold univalent_transport. simpl. 
    unshelve refine (sigma_map_eq _ _ _ _ _).
    apply e_sect. 
    intros a l. clear E. apply transport_switch.
    apply todo.
    (* cbn. 
    rewrite <- e_adj. cbn. 
    pose (equiv0 := fun a b c => equiv (e' a b c)).
    pose (equiv1 := equiv e).
    pose ((e_sect (e_fun (equiv e)) a)^ # l).
    unshelve epose (X0 := (e_fun
                (transport_eq
                   (fun X : A' =>
                    (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ X)
                    ≃ (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ e_fun (equiv e) a))
                   (ap (e_fun (equiv e)) (e_sect (e_fun (equiv e)) a))^
                   (Equiv_id (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ e_fun (equiv e) a)))
                _)).
    { rewrite e_retr, e_sect. eapply ur_refl. }
    pose (e_sect' (equiv0 (e_inv (e_fun equiv1) (e_fun equiv1 a)) (e_fun (equiv e) a)
                          X0) b).
    etransitivity; try apply p. clear p. unfold b. 
    cbn. unfold X0, equiv0, equiv1. 
    (* apply ap. 
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
            (e_inv (e_fun (equiv e)) (e_fun (equiv e) a))) idpath))=
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
                         idpath)).
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
    rewrite <- transport_e_fun. cbn. rewrite inv2. reflexivity. *)
    admit.
  - admit.*)
  - apply todo. 
Defined. 

#[export] Hint Extern 0 (sigT _ ≃ sigT _) => erefine (@Equiv_Sigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

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

Definition isequiv_path_sigma {A : Type} {B:A-> Type} {u v : sigT B}
: u = v -> {p : u.1 = v.1 & u.2 = transport_eq B p^ v.2}.
Proof.
  - exact (fun r => (r..1 ; r..2)). 
(*  - intro e. destruct e. cbn. destruct z, z'.
    cbn in *. destruct x. cbn in *. destruct p. reflexivity.
  - intro e. destruct e. destruct z.  reflexivity.
  - destruct z, z'. intros [e e']. cbn in *. destruct e. cbn in *. destruct e'. reflexivity.  *)
Qed.

Definition equiv_path_sigma {A : Type} {P : A -> Type} (u v : {x : A & P x}) :
       {p : u .1 = v .1 & u .2 = transport_eq P p^ v .2} ↔ (u = v).
  split. apply path_sigma_uncurried. apply isequiv_path_sigma.
Qed. 

#[universes(collapse_sort_variables=no)]
Definition FP_Sigma : @sigT ≈u @sigT.
  cbn; intros. unshelve econstructor.
  - eapply PRSigma. tc.
  - eapply Equiv_Sigma; tc. 
  - econstructor. intros [? ?] [? ?]; cbn in *. 
    split; cbn; intro e. 
    + apply isequiv_path_sigma in e. destruct e as [e1 e2]. cbn in *. 
      unshelve eexists. 
      eapply (fst (ur_coh _ _)); eauto.
      destruct e1. cbn in *. 
      eapply (fst (ur_coh _ _)); eauto.
    + destruct e as [e1 e2]. eapply path_sigma_uncurried.
      unshelve eexists; cbn in *. 
      unshelve eapply (snd (ur_coh _ _)); eauto.
      unfold univalent_transport in *.
      destruct ur_coh. cbn in *.
      set (p0 e1). clearbody p1. destruct p1. cbn.
      unshelve eapply (snd (ur_coh _ _)) in e2; tc.
Defined.

#[export] Hint Extern 0 (PR univalent (sigT _) (sigT _)) => 
  unshelve erefine (PR_Type_univ_univ (FP_Sigma _ _ _ _ _ _)); intros : typeclass_instances. 

Transparent functor_forall sigma_map. 
#[export] Hint Transparent functor_forall sigma_map : core.
#[export] Hint Unfold functor_forall sigma_map : core.

#[export] Hint Extern 0 (PR _ (?A -> _) (?A' -> _)) =>
  erefine (@URForall_Type A A' _); cbn in *; intros : typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition FP_existT : @existT ≈p @existT.
  intros A B H P Q H' x y e X Y E. 
  exact (existT _ e E).
Defined. 

#[universes(collapse_sort_variables=no)]
Definition FP_existT_univ : @existT ≈u @existT.
  intros A B H P Q H' x y e X Y E. 
  exact (existT _ e E).
Defined. 

#[export] Hint Extern 0 ((?x; ?y) ≈u (?x'; ?y')) => unshelve refine (FP_existT _ _ _ _ _ _ _ _ _ _ _ _ ): typeclass_instances.
#[export] Hint Extern 0 ({e0 : ?x ≈[_] ?y & ?X ≈[_] ?Y}) => unshelve refine (FP_existT _ _ _ _ _ _ _ _ _ _ _ _ ): typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition FP_sigT_rect : @sigT_rect ≈p @sigT_rect.
Proof.
cbn. intros A B H P Q HPQ P' Q' HPQ'. cbn in *. intros. 
destruct x0, y0, H1; cbn in *. apply H0. 
Defined. 

Definition FP_sigT_rect_univ : @sigT_rect ≈u @sigT_rect.
Proof.
cbn. intros A B H P Q HPQ P' Q' HPQ'. cbn in *. intros. 
destruct x0, y0, H1; cbn in *. apply H0. 
Defined. 

#[export] Hint Extern 0 (sigT_rect ?A ?P ?Q ?f ?s ≈p sigT_rect ?A' ?P' ?Q' ?f' ?s')
               => unshelve refine (FP_sigT_rect A A' _ P P' _ Q Q'
                     _ f f' _ s s' _): typeclass_instances.

#[export] Hint Extern 0 (sigT_rect ?A ?P ?Q ?f ?s ≈p _)
               => unshelve refine (FP_sigT_rect A _ _ P _ _ Q _
                     _ f _ _ s _ _) ; try eassumption : typeclass_instances.

#[export] Hint Extern 0 (_ ≈p sigT_rect ?A ?P ?Q ?f ?s)
               => unshelve refine (FP_sigT_rect _ A _ _ P _ _ Q
                     _ _ f _ _ s _ ) ; try eassumption : typeclass_instances.

(*! FP for Product !*)

Definition Equiv_prod (A B A' B' : Type) (e:A ≃ B) (e':A' ≃ B') : (A * A') ≃ (B * B').
Proof.
  clear_eq;
  match goal with
    e : ?ty ≃ ?ty'  , e1 : ?ty1 ≃ ?ty1' |- _ =>
  let e' := fresh in set (e' := Equiv_inverse e);
  let e'' := fresh in set (e'' := Equiv_inverse e1);
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _))
  end. 
  define_map A (@prod_rect _ _) (@pair _ _).
  define_map B (@prod_rect _ _) (@pair _ _).
  simpl. intros l. induction l using prod_rect; simpl. eapply ap2; typeclasses eauto with equiv typeclass_instances.
  simpl. intros l. induction l using prod_rect; simpl. eapply ap2; typeclasses eauto with equiv typeclass_instances.
  (* equiv_pind (@prod_rect _ _) (@pair _ _). *)
Defined.

Definition isequiv_path_prod {A B : Type} {u v : A * B}
: u = v -> (fst u = fst v) * (snd u = snd v).
Proof.
  exact (fun r => (ap fst r, ap snd r)).
Defined.

(* Definition equiv_path_prod {A B : Type} (u v : A * B): ((fst u = fst v) * (snd u = snd v)) ≃ (u = v)
  := BuildEquiv _ _ (path_prod_uncurried u v) _.  *)

Definition FP_Prod (x y : Type) (H : x ≈u y) (x0 y0 : Type) (H0 : x0 ≈u y0) : 
  ((x * x0) ≈u (y * y0)) %type.
Proof.
unshelve econstructor.
- unshelve refine (Equiv_prod _ _ _ _ _ _); tc.
- econstructor. intros [X Y] [X' Y']. cbn.
  split; intro e.
  + eapply isequiv_path_prod in e; cbn in *. destruct e. 
    unshelve eexists; eapply (fst (ur_coh _ _)); eauto.
  + destruct e as [e1 e2]. eapply path_prod_uncurried.
    unshelve eexists; cbn in *; unshelve eapply (snd (ur_coh _ _)); eauto.
Defined. 

#[export] Hint Extern 0 ((_ * _) ≃ (_ * _)) => erefine (@Equiv_prod _ _ _ _ _ _)
:  typeclass_instances.

Definition FP_Prod_Prop (x x0 : Prop) (y y0: SProp) (H : x ≈u y) (H0 : x0 ≈u y0) : 
  (((prod@{Prop Prop Prop; _ _} x x0)) ≈u ((y * y0):SProp)).
Proof.
unshelve econstructor.
- split; intros X.
  + split. 
    * eapply (fst (equiv_P H)). eapply (fst X).
    * eapply (fst (equiv_P H0)). eapply (snd X).
  + split. 
    * eapply (snd (equiv_P H)). eapply (fst X).
    * eapply (snd (equiv_P H0)). eapply (snd X).
- intros; split; eapply pr_Coh; tc.
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

#[export] Hint Extern 0 ((_ = _) ≃ (_ = _)) => erefine (Equiv_eq _ _ _ _ _ _ _ _ _) : typeclass_instances.

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
  econstructor. eapply (PR_eq _ _ (@pr _ _ _ H)); eauto.
Defined.

#[universes(collapse_sort_variables=no)]
Definition univ_eq : @eq ≈u @path.
Proof.
  cbn. intros. unshelve econstructor.
  - split; intro e.
    + eapply (snd (alt_ur_coh _ _ _)) in H0.   
      eapply (snd (alt_ur_coh _ _ _)) in H1.
      destruct e. 
      pose proof (H1^@ H0)^. eapply ap_inv_equiv; tc.
    + eapply (snd (alt_ur_coh _ _ _)) in H0.   
      eapply (snd (alt_ur_coh _ _ _)) in H1.
      destruct (H0@ ap _ e @ H1^); reflexivity.
  - intros e e'; destruct e, e'. econstructor.
Defined.

#[export] Hint Extern 0 (UR_Prop (eq _ _) (_ = _)) => unshelve eapply univ_eq : typeclass_instances.

Hint Extern 0 (natϵ 0 0) => exact Oϵ : typeclass_instances.

Hint Extern 0 (natϵ (S _) (S _)) => apply Sϵ : typeclass_instances.

Definition FP_nat : nat ≈u nat.
Proof.
  unshelve econstructor.
  - eapply Equiv_id.
  - econstructor. intros n m; split.
    + destruct 1. induction n; intros; econstructor; eauto.
    + cbn. induction 1; [econstructor | apply ap; eauto].
Defined. 

(* Hint Extern 0 (nat ≈u nat) => exact FP_nat : typeclass_instances.
Hint Extern 0 (UR_Type nat nat) => exact FP_nat : typeclass_instances. *)

Section TestCase.

  Parameter nat' : Set.

  #[universes(collapse_sort_variables=no)]
  Definition pr_nat : nat ≈u nat'.
  Admitted.

  Hint Extern 0 (PR univalent nat nat') => 
    unshelve notypeclasses refine (PR_Type_univ_univ _) : typeclass_instances.

  Hint Extern 0 (nat ≈u nat') => exact pr_nat : typeclass_instances.
  Hint Extern 0 (UR_Type nat nat') => exact pr_nat : typeclass_instances.

  Parameter plus' : nat' -> nat' -> nat'.

  #[universes(collapse_sort_variables=no)]
  Definition pr_plus : plus ≈u plus'.
  cbn.
  Admitted.

  Hint Extern 0 (plus _ _ ≈u plus' _ _) => unshelve eapply pr_plus :  typeclass_instances.

  Lemma plus0 : forall m, eq (m + 0) m.
  induction m; cbn. 
  - reflexivity.
  - f_equal ;tc.
  Qed.

  Lemma plusS : forall m n, eq (S (m + n)) (m + S n).
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
    unshelve eapply (fst (equiv_P _)); [| | exact comm_plus]; tc. 
  Qed. 

End TestCase.

(* Definition FP_eq_rect : @path_Has_Leibniz_J_@{Type Prop| _ _ _} ≈ @path_Has_Leibniz_J_@{Type SProp| _ _ _}.
Proof.
  cbn; intros. destruct H4. assumption.
Defined. *)

Axiom SPropProp : Prop = SProp.

Section SoftwareFoundations.

  Axiom state: Type.

  Axiom state': Type. 

  #[universes(collapse_sort_variables=no)]
  Definition stateϵ : state ≈u state'.
  Admitted.

  Hint Extern 0 (state ≈u state') => exact stateϵ :  typeclass_instances.
  Hint Extern 0 (UR_Type state state') => exact stateϵ :  typeclass_instances.
  Hint Extern 0 (PR univalent state state') => 
    unshelve notypeclasses refine (PR_Type_univ_univ _) :  typeclass_instances.

  Axiom dcom: Type.

  Axiom dcom': Type. 

  #[universes(collapse_sort_variables=no)]
  Definition dcomϵ : dcom ≈u dcom'.
  Admitted.

  Hint Extern 0 (UR_Type dcom dcom') => exact dcomϵ :  typeclass_instances.
  Hint Extern 0 (dcom ≈u dcom') => exact dcomϵ :  typeclass_instances.
  Hint Extern 0 (PR univalent dcom dcom') => 
    unshelve notypeclasses refine (PR_Type_univ_univ _):  typeclass_instances.

  Definition Assertion := state -> Prop.

  Definition Assertion' := state' -> SProp.

  Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

  (* Axiom decorated' : Type. *)
  (* Axiom Decorated' : Assertion' -> dcom' -> decorated'.  *)

  Inductive decorated' : Type :=
  | Decorated' : Assertion' -> dcom' -> decorated'.

  Hint Extern 0 (PR _ Assertion Assertion') => unfold Assertion, Assertion' : typeclass_instances.

  Inductive decoratedϵ : decorated -> decorated' -> SProp :=
  | Decoratedϵ : forall (a:Assertion) (a':Assertion') (aϵ : a ≈u a') 
      (d : dcom) (d':dcom') (dϵ : d ≈u d'),
     decoratedϵ (Decorated a d) (Decorated' a' d').

  Definition dec_fun : decorated -> decorated'.
  Proof. 
    induction 1. refine (Decorated' (fun s => _) (↑ d)).
    rewrite <- SPropProp. pose (UR_Type_Inverse _ _ stateϵ). exact (a (↑ s)).
  Defined.

  Definition dec_fun' : decorated' -> decorated.
  Proof. 
    induction 1. pose (UR_Type_Inverse _ _ dcomϵ). refine (Decorated (fun s => _) (↑ d)).
    rewrite SPropProp. exact (a (↑ s)).
  Defined.

  Instance dec_eq : decorated ≃ decorated'.
  unshelve econstructor.
    + apply dec_fun. 
    + unshelve eapply isequiv_adjointify.
     * apply dec_fun'.
     * apply todo.
     * apply todo.
  Defined.

  #[universes(collapse_sort_variables=no)]
  Goal decorated ≈p decorated'.
  cbn. 
  unshelve econstructor. exact decoratedϵ.
  Defined.

Parameter imported_Corelib__Init__Datatypes__bool : Set.
Parameter Corelib__Init__Datatypes__bool_iso : bool ≈u imported_Corelib__Init__Datatypes__bool.
Hint Extern 0 (UR_Type bool _) => exact Corelib__Init__Datatypes__bool_iso : typeclass_instances. 
Hint Extern 0 (bool ≈u _) => exact Corelib__Init__Datatypes__bool_iso : typeclass_instances. 
Hint Extern 0 (PR univalent bool _) => 
  unshelve notypeclasses refine (PR_Type_univ_univ _) : typeclass_instances. 

Goal forall b, @Corelib.Init.Datatypes.true ≈u b.
Abort.

Parameter imported_Corelib__Init__Datatypes__list : Type -> Type.
Parameter Corelib__Init__Datatypes__list_iso : Datatypes.list ≈u imported_Corelib__Init__Datatypes__list.
Hint Extern 0 (UR_Type (Datatypes.list _) _) => unshelve refine (Corelib__Init__Datatypes__list_iso _ _ _) : typeclass_instances.
Hint Extern 0 (Datatypes.list _ ≈u _) => unshelve refine (Corelib__Init__Datatypes__list_iso _ _ _) : typeclass_instances.
Hint Extern 0 (PR univalent (Datatypes.list _) _) => 
  unshelve notypeclasses refine (PR_Type_univ_univ _) : typeclass_instances. 

Parameter imported_Corelib__Init__Datatypes__app: forall [A : Type],
       imported_Corelib__Init__Datatypes__list A -> imported_Corelib__Init__Datatypes__list A -> imported_Corelib__Init__Datatypes__list A.

Goal @Datatypes.app ≈u @imported_Corelib__Init__Datatypes__app.
Abort. 


  Goal decorated ≈u decorated'.
  unshelve econstructor.
  - econstructor. exact decoratedϵ.
  - econstructor; intros.
    split.
    + destruct 1. cbn. induction a. econstructor. 
      cbn. intros. pose proof ((snd (alt_ur_coh _ _ _) H)). unfold univalent_transport in H0. cbn in H0.
      destruct H0. 
      apply todo.
      eapply (fst (ur_coh _ _ )). reflexivity.
    + cbn. set (dec_fun a'). assert (dec_fun' d = a'). unfold d. exact (e_sect' dec_eq a').
      rewrite <- H. clearbody d. clear H. destruct 1.
      cbn. apply ap2. apply funext. intros s. cbn in aϵ.         

  Goal forall d d', decoratedϵ d d' -> d = d.
  Proof.
   intros d d'. destruct 1.
   cbn in aϵ.
  Abort.

End SoftwareFoundations.

(*! nat !*)

(*! FP for nat_rect !*)

Definition FP_nat_rect : nat_rect ≈p nat_rect : SProp.
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

Instance Equiv_List A B (e:A ≃ B) : list A ≃ list B.
Proof.
    equiv_pind2 (@list_rect _) (@nil _) (@cons _).
Defined.

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
 
Definition FP_list : list ≈u list.
  unshelve econstructor.
  - econstructor. intros l l'; split.
    + destruct 1. induction l; intros; econstructor; eauto. eapply (fst (ur_coh _ _) idpath). 
    + apply todo. 
Defined.

#[export] Hint Extern 0 (UR_Type (list ?A) (list ?B)) => unshelve notypeclasses refine (@FP_list _ _ _): typeclass_instances. 

Definition FP_cons : @cons ≈u @cons. 
Proof. 
  typeclasses eauto. 
Defined.

Definition FP_nil : @nil ≈u @nil.
Proof. 
  typeclasses eauto.  
Defined.

(* 
Definition FP_List_rect : @list_rect ≈p @list_rect.
Proof.
  cbn. intros A B e X X' eX P P' P_nil Q Q' Q_cons l l' el. 
  induction el; typeclasses eauto with typeclass_instances. 
Defined.

#[export] Hint Extern 0 (list_rect _ ?X ?P ?Q ?l ≈ list_rect _ ?X' ?P' ?Q' ?l') =>
unshelve notypeclasses refine (FP_List_rect _ _ _ X X' _ P P' _ Q Q' _ l l' _); intros
:  typeclass_instances.

Instance Equiv_List_instance : forall x y : Type, x ⋈ y -> (list x) ⋈ (list y) := ur_type FP_List.
*)

#[universes(collapse_sort_variables=no)]
Goal list Type ≈p list Type.
tc.
Defined.

#[universes(collapse_sort_variables=no)]
Goal list Type ≈u list Type.
eapply FP_list; cbn.
(* woudl require univalence *)  
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
  - exact (nil _).
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
  intros; induction l; inversion X; simpl; reflexivity.
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
      apply (ap2 vcons). exact (e_sect e h). specialize (X t). destruct (vector_to_list _ _ _ n _ _ t), e0. exact X. 
  - (* Sect (nlist_to_nvector a) (nvector_to_nlist a) *)
    destruct en. induction n.
    + intro rl. simpl. destruct rl as [l Hl].
      destruct l; try inversion Hl. 
      apply path_sigma_uncurried. unshelve eexists. apply is_hset. 
    + intro rl. destruct rl as [l Hl].
      destruct l. inversion Hl.  
      apply path_sigma_uncurried. unshelve eexists. 
      simpl. simpl in Hl.
      assert (length l = n). inversion Hl. reflexivity. 
      assert (Hl = ap S X). apply is_hset.
      rewrite X0. unfold list_to_vector; simpl. apply ap2.
      exact (e_retr e b). 
      specialize (IHn (l;X)).
      destruct X. simpl. cbn. exact (IHn..1). apply is_hset.
Defined.

Typeclasses Opaque vector_to_list list_to_vector.

#[export] Hint Extern 0 => progress (unfold length) :  typeclass_instances.


Instance Equiv_vector_list (A B:Type) {H: A ≃ B} (n n':nat) (en : n ≈ n')
  : Vector.t A n ≃ {l : list B & length l = n'}
    := BuildEquiv _ _ _ (IsEquiv_vector_list A B H n n' en).

Definition Equiv_Vector_id A n :Equiv_Vector A A (Equiv_id A) n n  idpath = Equiv_id (t A n).
apply path_Equiv, funext. intro v.
induction v. reflexivity. cbn. apply ap. exact IHv. 
Defined. 

Instance Transportable_vector A : Transportable (t A).
unshelve econstructor. intros. 
apply Equiv_Vector. apply Equiv_id. auto.
apply Equiv_Vector_id. 
Defined.

Definition Equiv_vector_list_
  : Vector.t ≈ (fun A n => {l : list A & length l = n}).
  intros A B e. econstructor. tc. intros n n' en. unshelve econstructor. 
  - econstructor.
    intros v l. exact ((vector_to_list A B (equiv e) n n' en v) = l).
  - econstructor. intros v v'. cbn.
    apply (@isequiv_ap _ _ (Equiv_vector_list _ _ _ _ _)). 
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined. 

Instance FP_sized_list_ {A B : Type} `{A ≈ B} (n n':nat) (en : n = n') : 
   {l : list A & length l = n} ⋈ {l : list B & length l = n'}.
Proof.
  unshelve eapply FP_Sigma. tc. cbn. econstructor. tc. intros.
  unshelve eapply FP_eq; try tc. 
  exact (FP_List_rect A B (ltac:(tc))  (fun _:list A => nat) (fun _:list B => nat)
                      (ltac:(econstructor; tc)) O O (ltac:(tc)) (fun _ _ (n0 : nat) => S n0) (fun _ _ (n0 : nat) => S n0) (ltac:(tc)) x y H0). 
Defined.

#[export] Hint Extern 0 (t ?A ?n ≃ _) =>
erefine (ur_type (Equiv_vector_list A _ n)) : typeclass_instances.

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


#[export] Hint Extern 0 (Vector.t _ _ ⋈ _) => apply Equiv_vector_list_; simpl : typeclass_instances. 



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
  erefine (FP_ap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) : typeclass_instances.

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

#[export] Hint Extern 0 (IsEquiv _ ⋈ IsEquiv _) => refine (ur_type (FP_IsEquiv _ _ _ _ _ _) _ _ _) : typeclass_instances. 

Definition FP_Equiv : @Equiv ≈ @Equiv.
Proof.
  cbn;   split ; [typeclasses eauto | ]; intros.
  unshelve refine (UR_Type_Equiv _ _ _). cbn. 
  unshelve refine (UR_Type_Equiv' _ _ _).
  erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn ; intros. tc.
  split; tc. 
Defined. 

#[export] Hint Extern 0 (UR (_ ≃ _) (_ ≃ _)) => refine (Ur (ur_type (FP_Equiv _ _ _) _ _ _)) : typeclass_instances.

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

#[export] Hint Extern 0 (eq_to_equiv _ _ ≈ eq_to_equiv _ _) => refine (FP_eq_to_equiv _ _ _ _ _ _ _ _ _) : typeclass_instances.



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

#[export] Hint Extern 0 => progress (unfold Canonical_eq_sig) :  typeclass_instances.

Definition FP_Canonical_eq : Canonical_eq ≈ Canonical_eq.
  univ_param_record.
Defined.

#[export] Hint Extern 0 (Canonical_eq _ ⋈ Canonical_eq _) => erefine (ur_type FP_Canonical_eq _ _ _); simpl
:  typeclass_instances.

#[export] Hint Extern 0 (Canonical_eq _ ≃ Canonical_eq _) => erefine (ur_type FP_Canonical_eq _ _ _).(equiv); simpl
:  typeclass_instances.

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

#[export] Hint Extern 0 (UR_list_vect ?R [] Snil) => exact (UR_list_vect_nil R)  : typeclass_instances.

#[export] Hint Extern 0 (UR_list_vect ?R (_::_) (Svcons _ _)) => unshelve refine (UR_list_vect_cons R _ _) : typeclass_instances.

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

#[export] Hint Extern 0 (list _ ⋈ Svector _) => apply FP_list_Svector : typeclass_instances. 

Definition FP_Svector_list
  : Svector ≈ list.
  econstructor. tc. intros A B e.
  pose (UR_Type_Inverse _ _ e).
  eapply UR_Type_Inverse. tc.
Defined. 

#[export] Hint Extern 0 (Svector _ ⋈ list _) => apply FP_Svector_list : typeclass_instances. 

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


