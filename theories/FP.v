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

(* Axiom SPropProp : path@{_ Type; _} Type Prop SProp.

Definition SPropProp_equiv : Prop ≃ SProp.
  unshelve econstructor.
  - intro P. refine (transport_eq (fun X => X) SPropProp P).
  - unshelve refine (isequiv_adjointify _ _ _ _).
    + intro P. refine (transport_eq (fun X => X) (eq_sym SPropProp) P).
    + intro x; cbn. rewrite transport_Vp. reflexivity.   
    + intro x; cbn. rewrite transport_pV. reflexivity.
Defined.

Axiom SPropProp_iff : forall P : Prop, P ↔ transport_eq id SPropProp P. *)


(* Instance UrProp_IsEq : URIsEq Prop SProp SPropProp_equiv _ _.
Proof.
  intros A B.
  simpl.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply univalence_P. typeclasses eauto.
  - intros e; cbn.
    destruct e. simpl.
    exact (@e_sect _ _ _ (univalence_P _ _) idpath).
  - intro e; cbn.
    destruct e as [e eur ecoh].
    revert eur ecoh. rewrite <- (@e_retr _ _ _ (univalence_P _ _) _).
    set (eeq := (e_inv _ e)).
    clearbody eeq;clear e.
    destruct eeq. intros eur ecoh.
    simpl.
    destruct eur as [eur].
    destruct ecoh as [ecoh].
    simpl in *.
    change (Equiv_id_P A) with (eq_to_equiv_P A A idpath).
    rewrite (@e_sect _ _ _ (univalence_P _ _) _). simpl.
    unfold UR_gen.
    rewrite <- (@e_retr _ _ (e_fun (equiv_relation_equiv_fun _ _ _ _)) _ ecoh).
    set (p := (e_inv _ ecoh)).
    clearbody p. clear ecoh.
    destruct p.
    assert (Ur_Can_A = Canonical_eq_gen A) by apply Canonical_contr.
    assert (Ur_Can_B = Canonical_eq_gen A) by apply Canonical_contr.
    destruct X, X0. reflexivity. 
Defined. *)
(* Instance Canonical_eq_Prop : Canonical_eq Prop := Canonical_eq_gen _. *)


(* Instance FP_Prop : Prop ⋈ SProp.
Proof.
  unshelve econstructor.
  - exact SPropProp_equiv.
  - econstructor. intros; cbn.  exact UR_Prop.
  - exact None.
  - intro P; cbn. exact (fun p p' => True).
    (* eapply SPropProp_iff. *)
Defined. *)

#[export] Hint Extern 0 (sigT _) => unshelve refine (existT _ _ _): typeclass_instances.

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
  (e' :  forall x y (H:x ≈ y), Q x ≈u P y) 
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

(* 
Instance Transportable_Forall_nondep A B (P: B -> A -> Type)
         (Hb : forall b, Transportable (P b)) : Transportable (fun a => forall b, P b a).
Proof.
  unshelve econstructor.
  - intros x y e.
    unshelve refine (BuildEquiv _ _ _ _).
    unshelve eapply functor_forall. exact id.
    intros b. exact (transportable _ _ e).
    typeclasses eauto. 
  - intro a. cbn. 
    unshelve refine (path_Equiv _).
    apply funext; intro f. apply funext; intro b. cbn. 
    exact (apD10 (ap e_fun (@transportable_refl _ _ (Hb b) a)) (f b)).  
Defined.
 
Instance Transportable_Forall A (B:A -> Type) (P: forall a, B a -> Type)
         (HB : Transportable B) (HA_can : Canonical_eq A)
         (HB_can : forall x, Canonical_eq (B x))
         (HP : Transportable (fun x => P x.1 x.2)):
  Transportable (fun a => forall b, P a b).
Proof.
  eapply Transportable_default.
  (* unshelve econstructor.
  - intros x y e.
    destruct HP as [HP HP'].
    pose e^.
    unshelve refine (BuildEquiv _ _ (functor_forall _ _) (isequiv_functor_forall _ _ _ )).
    intro X. apply (transportable _ _ (HA_can.(can_eq) _ _ p) X); auto. intro b. cbn.
  assert ((x;transportable y x (can_eq HA_can y x p) b) = (y;b)).
  apply path_sigma_uncurried. unshelve esplit. cbn. exact e.
  cbn. 
  exact (apD10 (ap e_fun (ap (transportable x x) (HA_can.(can_idpath) x) @ (@transportable_refl _ _ _ x))) b).
  apply (HP _ _ X);  typeclasses eauto.
  
  unshelve econstructor. intros.
  assert ((x;x0) = (x;y0)). 
  apply path_sigma_uncurried. unshelve esplit. exact X.
  exact (HP _ _ X0).  
  intros; cbn. apply (HP' (x;x0)).   
  apply (transportable y x (can_eq HA_can y x e0)). typeclasses eauto. 
  - destruct HP as [HP1 HP2]. cbn. 
    intro a. cbn.
    unshelve refine (path_Equiv _).
    apply funext; intro f. apply funext; intro b. cbn. unfold functor_forall.
    pose (fun (e : {e : B a ≃ B a & e = Equiv_id (B a)}) =>
            (HP1 (a; e.1 b) (a; b)
                           match apD10 (ap e_fun e.2) b in (_ = y) return ((a; e.1 b) = (a; y)) with
                            | idpath => idpath
                            end) (f (e.1 b)) = f b). 
    change (T (transportable a a (can_eq HA_can a a idpath);
               (ap (transportable a a) (HA_can.(can_idpath) a) @ (transportable_refl a)))).
  assert ((transportable a a (can_eq HA_can a a idpath);
               (ap (transportable a a) (HA_can.(can_idpath) a) @ (transportable_refl a)))= ((Equiv_id (B a); idpath): {e : B a ≃ B a & e = Equiv_id (B a)})).
  apply path_sigma_uncurried. unshelve esplit. cbn. 
  apply (ap (transportable a a) (HA_can.(can_idpath) a) @ (transportable_refl a)). 
  cbn. rewrite transport_paths_l. rewrite inv2. rewrite concat_refl. reflexivity.  
  apply (transport_eq T X^). unfold T. cbn.
  exact (apD10 (ap e_fun (HP2 (a;b))) _).  *)
Defined.
*)

(* this instance of transportable is for the equality type, we can use the default one*)

(* 
#[export] Hint Extern 0 (Transportable (fun _ : _ => _ = _))
=> apply Transportable_default : typeclass_instances.

#[export] Hint Extern 0 (Transportable (eq _ _))
=> apply Transportable_default : typeclass_instances.

#[export] Hint Extern 0 (Canonical_eq (_ = _))
=> apply Canonical_eq_gen : typeclass_instances.
*)

(* Definition option_map2 : forall [A B C : Type], (A -> B -> C) -> option A -> option B -> option C.
Proof.
  intros A B C f. destruct 1.
  - eapply option_map. exact (f a).
  - intros _; exact None.
Qed.  *)

(* Definition option_forall : forall A (B:A -> Type), (forall a, option (B a)) -> option (forall a, B a).
Proof.
  intros A B r.  *)
 
(*
Definition FP_forall_UR_Coh (A A' : Type) (eA : A ≈u A') (B : A -> Type) (B' : A' -> Type)  
     (eB : B ≈u B') :
  UR_Coh (forall x : A, B x) (forall x : A', B' x) 
    (Equiv_forall A A' eA B B' eB) (@URForall _ A A' B B' _ (fun x y e => Ur (eB x y e))).
Proof.
   
  econstructor. intros f g. 

  eapply equiv_compose. 
  eapply (BuildEquiv _ _ (@apD10_gen _ _ f g) _).
  
  unshelve eapply Equiv_forall.
  apply UR_gen. 2: apply URType_Refl_can.
  (* econstructor.  
  intros a a' e. cbn in e. cbn. eapply 
  apply Canonical_PR. 
  unshelve eapply Equiv_forall. auto. 
  split; [typeclasses eauto | ]. 
  intros a'' b e'. 
  apply Canonical_UR.  
  unshelve eapply Equiv_forall.
  apply Canonical_UR. 
  pose (e_fun (alt_ur_coh (equiv eA) _ _ _ _) e').
  apply Equiv_inverse. eapply equiv_compose. apply alt_ur_coh. apply eA. 
  eapply equiv_compose. apply isequiv_sym. destruct e.
  exact (transport_eq (fun X => (X = _) ≃ _) e0 (Equiv_id _)).
  cbn. split; [typeclasses eauto | ].
  intros X X' X''. destruct X. destruct e. 
  apply Canonical_UR.
  clear e' X''. 
  pose (e_fun (alt_ur_coh _ _ _ _ _) X').
  eapply equiv_compose. apply ur_coh. cbn. 
  unfold univalent_transport. cbn. 
  cbn in e. rewrite can_eq_eq. 
  set (T := fun (XX : {XX : _ & b = univalent_transport XX}) =>
               (f a'' ≈ e_fun (equiv (ur_type eB a'' b X')) (g a''))
  ≃ (f a'' ≈ e_fun (equiv (ur_type eB XX.1 b (e_fun (transport_eq (fun X : A' => (XX.1 ≈ X) ≃ (XX.1 ≈ b))
    XX.2 (Equiv_id (XX.1 ≈ b))) (e_fun (ur_coh XX.1 XX.1) idpath)))) (g XX.1))).
  change (T (_;(e_retr (e_fun (equiv eA)) b)^)).
  unshelve refine (@transport_eq _ T (_ ; (Move_equiv _ _ _ e)^) _ _ _).
  apply path_sigma_uncurried. unshelve eexists. 
  cbn. unfold univalent_transport.
  rewrite transport_paths_Fr. rewrite ap_V.
  rewrite <- concat_inv. reflexivity. 
  unfold T; cbn. clear T.
  rename a'' into a'. 
  pose (T := fun (XX : {XX : A' & a' ≈ XX}) => let foo := ur_type eB _ _ XX.2 in 
               (f a' ≈ e_fun (equiv (ur_type eB a' b X')) (g a'))
  ≃ (f a'  ≈ e_fun (equiv (ur_type eB a' b
               (e_fun (transport_eq (fun X : A' => (a' ≈ X) ≃ (a' ≈ b)) (Move_equiv (equiv eA) a' b e)^
               (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') idpath)))) (g a'))).
  change (T (_; ur_refl a')).
  assert (X' =
  transport_eq (fun XX : A' => a' ≈ XX)
               (Move_equiv (equiv eA) a' b e) (ur_refl a')).
  pose (e_sect' (alt_ur_coh _ _ _ _ _) X').
  apply inverse. etransitivity; try exact e0. 
  cbn. unfold Move_equiv, e, ur_refl, alt_ur_coh.
  rewrite e_sect.
  rewrite transport_pp. rewrite transport_ap.
  pose (Equiv_inverse (equiv eA)).
  pose (e_retr' (ur_coh a' (univalent_transport b))
                (transport_eq (fun XX => a' ≈ XX) (e_sect _ b)^ X')).
   cbn in e2.
  apply transport_switch. etransitivity ; try exact e2.
  clear e2.
  rewrite <- transport_e_fun. cbn.
  rewrite e_retr.
  set (h := (transport_eq (fun XX : A' => a' ≈ XX) (e_retr (e_fun (equiv eA)) b)^ X')).
  change (transport_eq (fun x0 : A => a' ≈ e_fun (equiv eA) x0)
    (e_inv (e_fun (ur_coh a' (e_inv (e_fun (equiv eA)) b)))
       h)
    (e_fun (ur_coh a' a') idpath) = h). cbn in h. 
  pose (e_retr' (ur_coh a' _) h). cbn in e2.
  rewrite transport_e_fun'. etransitivity ; try exact e2.
  set (e_inv (e_fun (ur_coh a' (e_inv (e_fun (equiv eA)) b))) h).
  destruct e3. reflexivity. 

  unshelve refine (@transport_eq _ T (_ ; X') _ _ _).
  apply path_sigma_uncurried. unshelve eexists. cbn.
  unfold univalent_transport. apply inverse. apply Move_equiv. exact e.
  rewrite inv2. exact X. 
  unfold T. cbn. clear T. 
  assert (X' = (e_fun (transport_eq (fun X : A' => (a' ≈ X) ≃ (a' ≈ b)) (Move_equiv (equiv eA) a' b e)^
                       (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') idpath))).
  unfold e. cbn.
  etransitivity; try apply transport_e_fun. 
  cbn. unfold Move_equiv, e, ur_refl, alt_ur_coh. cbn.  
  rewrite inv2. exact X. 
  destruct X0. apply Equiv_id. *)
Admitted. 
*)
#[export] Hint Extern 1 (PR (forall x:?A, _) (forall x:?A', _)) =>
  erefine (@URForall A A' _ _ _ _); cbn in *; intros : typeclass_instances.

Definition FP_forall_ur_type (A A' : Type) (eA : A ≈u A') (B : A -> Type) (B' : A' -> Type) 
     (eB : B ≈u B') :
  (forall x : A, B x) ≈u (forall x : A', B' x).
  unshelve econstructor.
  - tc.
  - econstructor. intros f g. split; cbn. 
    + intros efg x y e. destruct efg. 
      destruct (Ur_Coh (eB _ y (ur_refl (UR_Type_Inverse A A' eA) y))) as [ur_coh].
      cbn in ur_coh.
      pose proof (fst (ur_coh (f _) (f _)) idpath).
      unfold univalent_transport in H.
      pose proof (snd (alt_ur_coh (equiv eA) (Ur eA) _ _ _) e).
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
Proof. tc. Defined.

#[universes(collapse_sort_variables=no)]
Definition FP_forall_plain :
          (fun A B => forall x:A , B x) ≈p (fun A' B' => forall x:A', B' x).
Proof.
  tc.
Defined.

#[universes(collapse_sort_variables=no)]
Definition FP_forall_ur :
            (fun A B => forall x:A , B x) ≈u (fun A' B' => forall x:A', B' x).
Proof.
  intros A A' eA B B' eB. eapply FP_forall_ur_type; eauto.
Defined. 

#[export] Hint Extern 100 (PR _ _ _) => 
  unshelve notypeclasses refine (PR_Type_gen _ _ _ _); assumption: typeclass_instances.

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
  tc.
Defined. 

#[universes(collapse_sort_variables=no)]
Definition FP_forall_univ_Prop :
            (fun A (B:A->Prop) => forall x:A , B x) ≈u (fun A' (B':A'->SProp) => forall x:A', B' x).
Proof.
  intros A A' eA B B' eB.
  unshelve econstructor.
  - tc.
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

Hint Extern 0 (UR_Prop (forall x:_ , _) (forall y:_, _)) => unshelve eapply FP_forall_univ_Prop; cbn in *; intros : typeclass_instances.

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
