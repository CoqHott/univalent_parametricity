(************************************************************************)
(* This file proves the fundamental property for the main constructors of CIC *)
(************************************************************************)

Set Polymorphic Inductive Cumulativity. 

Set Universe Polymorphism.

Require Import HoTT CanonicalEq URTactics ADT UnivalentParametricity.theories.UR UnivalentParametricity.theories.Transportable.


(* Lemmas about canonical equality *)

Definition can_eq_eq {A} (e :Canonical_eq A) : e.(can_eq) = fun x y e => e.
Proof.
  apply funext; intros x. apply funext; intros y. apply funext; intro E.
  destruct E. apply can_eq_refl. 
Defined. 


Definition Canonical_eq_eq A (e e':Canonical_eq A)
           (H : e.(can_eq) = e'.(can_eq)) :
  (transport_eq (fun X => X = _) H  (can_eq_eq e) = (can_eq_eq e')) ->
  e = e'.
Proof.
  destruct e, e'. cbn in *. destruct H. cbn.
  unfold can_eq_eq.
  intros H. apply ap_inv_equiv' in H. cbn in H. 
  assert (can_eq_refl = can_eq_refl0).
  apply funext. intro x. 
  pose (H' := apD10 H x). apply ap_inv_equiv' in H'.
  pose (H'' := apD10 H' x). apply ap_inv_equiv' in H''.
  exact (apD10 H'' eq_refl). 
  destruct X. reflexivity.
Defined. 

Definition Canonical_contr A (e :Canonical_eq A) : e = Canonical_eq_gen A.
Proof.
  unshelve eapply Canonical_eq_eq.
  apply can_eq_eq.
  cbn. rewrite transport_paths_l. rewrite inv_inv.
  unfold can_eq_eq. cbn. apply inverse. 
  pose (@e_sect _ _ _ (funext _ _  (fun (x y : A) (e0 : eq A x y) => e0) (fun (x y : A) (e0 : eq A x y) => e0)) eq_refl).
  etransitivity; try exact e0. clear e0. apply ap. apply funext. intros. cbn.
  pose (@e_sect _ _ _ (funext _ _  (fun (y : A) (e0 : eq A x y) => e0) (fun (y : A) (e0 : eq A x y) => e0)) eq_refl).
  etransitivity ; try apply e0. clear e0. apply ap. apply funext. intros y. cbn.
  pose (@e_sect _ _ _ (funext _ _  (fun (e0 : eq A x y) => e0) (fun (e0 : eq A x y) => e0)) eq_refl). 
  etransitivity; try apply e0. clear e0. apply ap. apply funext. intros e0. cbn.
  destruct e0. reflexivity.                  
Defined.


(*! Establishing FP for Type !*)

Definition transport_UR_Type A B C (e: B = C) e1 e2 e3 e4 e5 :
  transport_eq (fun X : Type => A ⋈ X)
               e (Build_UR_Type A B e1 e2 e3 e4 e5) =
  Build_UR_Type A C (e # e1) (e#e2)
                (transportD2 _ _ (@UR_Coh A) e _ _ e3)
                e4 (e # e5)
  :=
  match e with eq_refl => eq_refl end.

Definition transport_UR_Type' A B C (e: A = C) e1 e2 e3 e4 e5:
  transport_eq (fun X : Type => X ⋈ B)
               e (Build_UR_Type A B e1 e2 e3 e4 e5) =
  Build_UR_Type C B (e # e1) (e#e2)
                (transportD2 _ _ (fun X => @UR_Coh X B) e _ _ e3)
                (e # e4) e5
  :=
  match e with eq_refl => eq_refl end.


Definition path_Equiv {A B} {f g: A ≃  B} : e_fun f = e_fun g -> f = g.
  destruct f, g. cbn. intro e. destruct e.
  assert (e_isequiv = e_isequiv0). apply hprop_isequiv.
  destruct X; reflexivity.
Defined.

Definition Equiv_inverse_inverse A B (e : A ≃ B) : Equiv_inverse (Equiv_inverse e) = e.
  intros. apply path_Equiv. reflexivity.
Defined. 

Instance is_equiv_alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:UR A B) : IsEquiv (alt_ur_coh e H). 
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

Definition ur_coh_equiv {A B:Type} (e:A ≃ B) (H:UR A B) (einv := Equiv_inverse e):
  UR_Coh A B e H ≃ forall (a:A) (b:B), (a ≈ b) ≃ (a = ↑ b)
  := BuildEquiv _ _ (alt_ur_coh e H) _.

Definition path_UR_Type A B (X Y:UR_Type A B) (e1:X.(equiv) = Y.(equiv))
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
  destruct Ur_Coh, Ur_Coh0. 
  assert (ur_coh = ur_coh0).
  apply funext. intro a.
  apply funext. intro a'.
  apply path_Equiv. apply e3. destruct X. reflexivity. 
Defined. 

Definition transport_UR A B C (e: B = C) e1 :
  transport_eq (fun X : Type => UR A X)
               e (Build_UR A B e1) =
  Build_UR A C (fun a x => e1 a ((eq_to_equiv _ _ e^).(e_fun) x))
  :=  match e with eq_refl => eq_refl end.

Definition transport_UR' A B C (e: A = C) e1 :
  transport_eq (fun X : Type => UR X B)
               e (Build_UR A B e1) =
  Build_UR C B (fun x b => e1 ((eq_to_equiv _ _ e^).(e_fun) x) b)
  :=  match e with eq_refl => eq_refl end.

Definition path_UR A B (X Y: UR A B) : (forall a b, @ur _ _ X a b = @ur _ _ Y a b) -> X = Y.
  intros e. pose ((funext _ _ _ _).(@e_inv _ _ _) (fun a => (funext _ _ _ _).(@e_inv _ _ _) (e a))).
  destruct X, Y. cbn in *. 
  destruct e0. reflexivity. 
Defined.

Definition UR_is_eq_equiv (A B:Type) (e:A ⋈ B) (a:A) (b:B) : (a = e_inv (e_fun (equiv e)) b) ≃ (a ≈ b).
Proof.
  eapply equiv_compose; try refine (ur_coh a _).
  refine (transport_eq (fun X =>  (a ≈ X) ≃ _) (e_retr _ b)^ (Equiv_id _)). 
Defined. 

Definition equiv_ind {A B} {f : A ≃  B} (P : B -> Type)
  : (forall x:A, P (e_fun f x)) -> forall y:B, P y
  := fun g y => transport_eq P (e_retr' f y) (g (e_inv' f y)).

Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_ind E Q _); intros x
  end.

Definition equiv_path (A B : Type) : (A = B) ≃ (A ≃ B) 
  := BuildEquiv _ _ (eq_to_equiv A B) _.

Definition equiv_path_V (A B : Type) (p : A = B) :
  eq_to_equiv  B A (p^) = Equiv_inverse (eq_to_equiv  A B p).
Proof.
  destruct p. simpl. simpl.
  apply path_Equiv. reflexivity. 
Defined.

Definition UR_Equiv (A B C:Type) `{C ≃ B} `{UR A B} : UR A C :=
  {| ur := fun a b => a ≈ ↑ b |}.

Definition UR_Equiv' (A B C:Type) `{C ≃ A} `{UR A B} : UR C B :=
  {| ur := fun c b => ↑ c ≈  b |}.

Definition UR_Type_Equiv (A B C:Type) `{C ≃ B} `{A ≈ B} : A ≈ C.
Proof.
  cbn in *. unshelve econstructor.
  - apply (equiv_compose (equiv H0)). apply Equiv_inverse. exact H.    
  - eapply UR_Equiv; typeclasses eauto.
  - econstructor.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq (fun X => _ ≃ (a ≈ X)) (e_retr' H _)^ _). apply ur_coh. 
  - apply H0.(Ur_Can_A).
  - pose H0.(Ur_Can_B). destruct c.
    unshelve refine (let x : forall (x y:C) , x=y -> x = y := _ in _).
    intros x y e. pose (can_eq _ _ (ap H e)).
    apply (Equiv_inverse (@isequiv_ap _ _ H _ _) e0). 
    apply (Build_Canonical_eq _ x).
    cbn. clear x; intro x. rewrite can_eq_refl. cbn. rewrite concat_refl.
    apply inv_inv.
Defined.     

Definition UR_Type_Equiv' (A B C:Type) `{C ≃ A} `{A ≈ B} : C ≈ B.
Proof.
    unshelve econstructor.
  - apply (equiv_compose H (equiv H0)).
  - cbn in *. eapply UR_Equiv'; typeclasses eauto.
  - econstructor. intros. cbn.
    unfold univalent_transport.
    pose (X:= isequiv_ap C A a a'). 
    eapply equiv_compose. apply X.
    apply ur_coh.
  - pose H0.(Ur_Can_A). destruct c.
    unshelve refine (let x : forall (x y:C) , x=y -> x = y := _ in _).
    intros x y e. pose (can_eq _ _ (ap H e)).
    apply (Equiv_inverse (@isequiv_ap _ _ H _ _) e0). 
    apply (Build_Canonical_eq _ x).
    cbn. clear x; intro x. rewrite can_eq_refl. cbn. rewrite concat_refl.
    apply inv_inv.
  - apply H0.(Ur_Can_B).
Defined. 

Definition UR_Type_Equiv_gen (X:Type) (eX : X ⋈ X) (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈ y) `{A x ≈ A y}
  : B x ≈ B y.
Proof.
  unshelve refine (UR_Type_Equiv _ _ _).
  unshelve refine (UR_Type_Equiv' _ _ _).
  auto. 
Defined.

Instance isequiv_forall_cod A B C (f : forall a : A, B a -> C a) `{!forall a, IsEquiv (f a)}
  : IsEquiv (fun (g : forall a, B a) a => f a (g a)).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - intros h a;exact (e_inv (f a) (h a)).
  - simpl. intros g;apply funext;intros a.
    apply e_sect.
  - simpl;intros h; apply funext; intros a.
    apply e_retr.
Defined.

Definition equiv_forall_cod A B C (e : forall a : A, B a ≃ C a) : (forall a, B a) ≃ (forall a, C a).
Proof.
  eexists;apply isequiv_forall_cod,_.
Defined.

Instance equiv_relation_equiv_fun A B (R1 R2 : A -> B -> Type)
  : (R1 = R2) ≃ (forall a b, R1 a b ≃ R2 a b).
Proof.
  eapply equiv_compose;[|apply equiv_forall_cod].
  eexists. apply funext.
  intros a. simpl.
  eapply equiv_compose;[|apply equiv_forall_cod].
  eexists. apply funext.
  intros b. simpl.
  eexists. apply univalence.
Defined.

Definition URType_Refl_can A (HA : Canonical_eq A) : A ⋈ A.
Proof.
  unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
  - apply HA.
  - apply HA.    
Defined.

Definition URType_Refl : URRefl Type Type (Equiv_id _) _.
Proof.
  constructor; intro A.
  apply URType_Refl_can. apply Canonical_eq_gen.
Defined.

(* this requires univalence *)
Instance URType_IsEq : URIsEq Type Type (Equiv_id _) _ URType_Refl.
Proof.
  intros A B. 
  simpl.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply univalence. typeclasses eauto.
  - intros e; cbn.
    destruct e. simpl.
    exact (@e_sect _ _ _ (univalence _ _) eq_refl).
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
    change (Equiv_id A) with (eq_to_equiv A A eq_refl).
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
Defined.

Instance Canonical_eq_Type : Canonical_eq Type := Canonical_eq_gen _.

Instance FP_Type : Type ⋈ Type.
Proof. 
  econstructor; try typeclasses eauto.
Defined.

Hint Extern 0 (UR_Type Set Set) => exact FP_Type : typeclass_instances. 

(*! Establishing FP for Prop !*)

Instance UR_Prop : UR Prop Prop :=
  {| ur := fun (A B :Prop) => A ⋈ B |}.

Instance URProp_Refl : URRefl Prop Prop (Equiv_id _) _.
Proof. refine {| ur_refl_ := _ |}. intro A. cbn. unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen. 
Defined.

Instance UrProp_IsEq : URIsEq Prop Prop (Equiv_id _) _ _.
Proof.
  intros A B.
  simpl.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply univalence_P. typeclasses eauto.
  - intros e; cbn.
    destruct e. simpl.
    exact (@e_sect _ _ _ (univalence_P _ _) eq_refl).
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
    change (Equiv_id_P A) with (eq_to_equiv_P A A eq_refl).
    rewrite (@e_sect _ _ _ (univalence_P _ _) _). simpl.
    unfold UR_gen.
    rewrite <- (@e_retr _ _ (e_fun (equiv_relation_equiv_fun _ _ _ _)) _ ecoh).
    set (p := (e_inv _ ecoh)).
    clearbody p. clear ecoh.
    destruct p.
    assert (Ur_Can_A = Canonical_eq_gen A) by apply Canonical_contr.
    assert (Ur_Can_B = Canonical_eq_gen A) by apply Canonical_contr.
    destruct X, X0. reflexivity. 
Defined.

Instance Canonical_eq_Prop : Canonical_eq Prop := Canonical_eq_gen _.

Instance FP_Prop : Prop ⋈ Prop.
Proof.
  econstructor; typeclasses eauto. 
Defined.


(*! UR is symmetric on types !*)

Definition UR_Type_Inverse (A B : Type) : A ≈ B -> B ≈ A.
Proof.
  intro e.
  unshelve eexists; cbn in *. 
  - apply Equiv_inverse.  typeclasses eauto. 
  - econstructor. exact (fun b a => ur a b).
  - econstructor. intros b b'. cbn. 
    eapply equiv_compose. apply isequiv_sym.
    eapply equiv_compose. apply (@isequiv_ap _ _ ( Equiv_inverse (equiv e))).
    eapply equiv_compose. apply ur_coh.
    cbn. unfold univalent_transport.
    refine (transport_eq (fun X => (_ ≈ X) ≃ _) (can_eq _ _ _ (e_retr _ _))^ (Equiv_id _)).
  - exact (e.(Ur_Can_B)).
  - exact (e.(Ur_Can_A)).
Defined.

(*! Canonical UR from a type equivalence !*)


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

Definition transport_univalence A B C (e: A ≃ B) (e': C ≃ A)  :
  transport_eq (Equiv C) (e_inv (eq_to_equiv A B) e) e'
  = e ∘∘ e'.
Proof.
  pose (@e_retr _ _ (eq_to_equiv A B) _ e). 
  set (e_inv (eq_to_equiv A B) e) in *.  rewrite <- e0.
  clear e0. destruct e1. cbn. apply path_Equiv. apply funext; reflexivity. 
Defined. 




Definition Canonical_UR (A B:Type) `{A ≃ B} : A ≈ B.
Proof.
  pose (einv := Equiv_inverse H).
  cbn in *. unshelve econstructor.
  - exact ({| ur := fun a b => a = ↑ b |}). 
  - econstructor.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq (fun X => _ ≃ (a = X)) (e_sect' H _)^ _). apply Equiv_id. 
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen. 
Defined.     


Definition UR_Type_canonical_eq (A A' : Type) (eA : A ⋈ A') :
  eA = @Canonical_UR A A' (equiv eA).
  unshelve eapply UR_Type_eq. 
  destruct eA, Ur, Ur_Coh. cbn; apply ap.
  apply funext; intro a. 
  apply funext; intro a'.
  specialize (ur_coh a (e_inv equiv a')).
  apply univalence.
  exact (transport_eq (fun X => ur a X ≃ _) (e_retr equiv _)
                      (Equiv_inverse ur_coh)).

  destruct eA, Ur, Ur_Coh. cbn.
  rewrite transport_ap. rewrite transport_Ur_Coh. apply ap.
  apply funext; intro a; apply funext; intro a'.
  apply path_Equiv. apply funext. intro e. 
  unfold univalent_transport in ur_coh.
  pose (@transport_funext _ _ ur (fun a a' => a = e_inv equiv a') (fun _ (X : A' -> Type) => (a = a') ≃ X (equiv a')) a (ur_coh a a')). 
  cbn in e0.
  rewrite e0. clear e0. 
  pose (@transport_funext _ _ (ur a) (fun a' => a = e_inv equiv a')
                          (fun _ X => (a = a') ≃ X) (equiv a') (ur_coh a a')). 
  rewrite e0. clear e0.
  rewrite transport_univalence. cbn.
  rewrite (e_adj equiv a'). rewrite transport_ap. 
  unfold e_sect'.
  pose (T := fun (X:{a'' : A & a'' = a'}) => (transport_eq (fun x : A => ur a (equiv x) ≃ (a = X.1))
     X.2 (Equiv_inverse (ur_coh a X.1)))
    ((ur_coh a a') e) =
  (transport_eq (fun X : A => (a = a') ≃ (a = X)) X.2^
     (Equiv_id (a = a'))) e).
  change (T (_ ; e_sect equiv a')).
  assert ((e_inv equiv (equiv a'); e_sect equiv a') =
          ((_;eq_refl):{a'' : A & a'' = a'})).
  apply path_sigma_uncurried. unshelve eexists. exact (e_sect equiv a').
  cbn. rewrite transport_paths_l. rewrite inv2. apply eq_sym, concat_refl.
  rewrite X. unfold T; clear T. cbn. apply e_sect.
  - apply Canonical_contr.
  - apply Canonical_contr.    
Defined. 





(*! FP for Product !*)

Definition Equiv_prod (A B A' B' : Type) (e:A ≃ B) (e':A' ≃ B') : (A * A') ≃ (B * B').
Proof.
  equiv_adt (@prod_rect _ _) (@pair _ _).
Defined.

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z') | 0.
Proof.
  unshelve refine (BuildIsEquiv _ _ _
                                (fun r => (ap fst r, ap snd r)) _ _ _).
  - intro e. destruct e. cbn. destruct z, z'.
    cbn in *. destruct e, e0. reflexivity.
  - intro e. destruct e. destruct z.  reflexivity.
  - destruct z, z'. intros [e e']. cbn in *. destruct e, e'. reflexivity. 
Defined.

Definition equiv_path_prod {A B : Type} (u v : A * B): ((fst u = fst v) * (snd u = snd v)) ≃ (u = v)
  := BuildEquiv _ _ (path_prod_uncurried u v) _. 

Instance UR_Prod (x y : Type) (H : x ⋈ y) (x0 y0 : Type) (H0 : x0 ⋈ y0) : UR (x * x0) (y * y0).
econstructor. exact (fun e e' => prod (fst e ≈ fst e') (snd e ≈ snd e')).
Defined. 

Definition FP_prod : prod ≈ prod.
  cbn in *. intros.
  (* this instance of transportable is on Type, we can only use the default one *)
  split; [typeclasses eauto | ].
  intros. 
  unshelve refine (Build_UR_Type _ _ _ _ _ _ _).
  unshelve refine (Equiv_prod _ _ _ _ _ _); typeclasses eauto. 
  econstructor. exact (fun e e' => prod (fst e ≈ fst e') (snd e ≈ snd e')). 
  econstructor. intros [X Y] [X' Y']. cbn.
  assert ( ((X, Y) = (X', Y')) ≃ ((X=X') * (Y=Y'))).
  apply Equiv_inverse. apply (equiv_path_prod (X, Y) (X', Y')).
  eapply equiv_compose. exact X0.
  eapply equiv_compose. apply Equiv_prod.
  apply ur_coh. apply ur_coh. apply Equiv_id.
  unshelve refine (let X : forall (a b:x*x0) , a=b -> a = b := _ in _).
  intros. apply path_prod_uncurried. apply (Equiv_inverse (BuildEquiv _ _ (path_prod_uncurried a b) _)) in X.
  split. apply can_eq. apply H. exact (fst X). 
  apply can_eq. apply H0. exact (snd X).
  apply (Build_Canonical_eq _ X). cbn; clear X. intros [a b].
  cbn. repeat rewrite can_eq_refl. reflexivity.
  unshelve refine (let X : forall (a b:y*y0) , a=b -> a = b := _ in _).
  intros. apply path_prod_uncurried. apply (Equiv_inverse (BuildEquiv _ _ (path_prod_uncurried a b) _)) in X.
  split. apply can_eq. apply H. exact (fst X). 
  apply can_eq. apply H0. exact (snd X).
  apply (Build_Canonical_eq _ X). cbn; clear X. intros [a b].
  cbn. repeat rewrite can_eq_refl. reflexivity.
Defined.

Hint Extern 0 ((_ * _) ≃ (_ * _)) => erefine (@Equiv_prod _ _ _ _ _ _)
:  typeclass_instances.

Hint Extern 0 (UR_Type (_ * _) (_ * _)) => erefine (ur_type (@FP_prod _ _ _) _ _ _)
:  typeclass_instances.


(*! FP for Dependent product !*)

(* isequiv_functor_forall can be found in
[https://github.com/HoTT/HoTT] *)

Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (g : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun H b => g b (H (f b)).
  
Instance isequiv_functor_forall {A B} {P : A -> Type} {Q : B -> Type}
         (eA : Canonical_eq A)
         (eP : Transportable P)
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - refine (functor_forall (e_inv f) _).
    intros a y.
    generalize (e_inv (g _) y). clear y.
    exact (transportable _ _ (eA.(can_eq) _ _ (e_retr f a))).
  - intros h. apply funext. intro a. unfold functor_forall.
    destruct (e_retr f a). rewrite can_eq_refl, transportable_refl. apply e_sect. 
  - intros h;apply funext. unfold functor_forall. intros b.
    rewrite e_adj. destruct (e_sect f b).
    cbn. rewrite can_eq_refl, transportable_refl. apply e_retr.
Defined.

Instance isequiv_functor_forall_ur {A B} `{P : A -> Type} `{Q : B -> Type} (e : B ≈ A) (e' : Q ≈ P) (eA : Canonical_eq A) (eP : Transportable P)
  : IsEquiv (functor_forall (e_fun (equiv e))
                            (fun x => (e_inv' ((equiv (ur_type e' x (e_fun (equiv e) x) (ur_refl x))))))).
Proof.
  apply isequiv_functor_forall.
  assumption. assumption. apply (equiv e).
  intros b. unfold e_inv'.
  apply isequiv_inverse.
Defined.

Instance Equiv_forall (A A' : Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') 
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  pose (e := UR_Type_Inverse _ _ eA).
  pose (e' := fun x y E => UR_Type_Inverse _ _ (ur_type eB y x E)).
  
   unshelve refine
           (BuildEquiv _ _ (functor_forall (e_fun (equiv e))
                                           (fun x => (e_inv' ((equiv (e' x (e_fun (equiv e) x) (ur_refl (e:=e) x)))))))
                       _). 
Defined.

Definition transport_e_fun' A B (P : A -> Type) a a' (e : a = a') (e' : B ≃ P a) x
    :
      transport_eq (fun X => P X) e (e_fun e' x) =
      e_fun (transport_eq (fun X => _ ≃ P X) e e') x.
Proof.
  destruct e. reflexivity.
Defined.

Definition apD10_gen (A : Type) (B : A -> Type) (f g : forall x : A, B x) :
  f = g -> forall x y (e:y = x), f x = e # g y.
  intros H x y e. destruct e. cbn. apply apD10. auto.  
Defined. 

Instance funextGen (A : Type) (P : A -> Type) f g: IsEquiv (@apD10_gen A P f g).
Proof.
  unshelve eapply isequiv_adjointify.
  intros. apply funext. intros x. exact (X _ _ eq_refl).
  cbn. intros e. cbn.
  exact (e_sect (@apD10 _ _ f g) e).
  cbn; intro e.
  apply funext. intro x.
  apply funext. intro y.
  apply funext. intro E.
  destruct E. cbn.
  pose (funext _ _ f g).
  pose (e_retr (@apD10 _ _ f g) (fun x => e x x eq_refl)).
  exact (apD10 e0 y).
Defined.

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
  unshelve econstructor.
  - intros x y e.
    destruct HP as [HP HP'].
    pose e^.
    unshelve refine (BuildEquiv _ _ (functor_forall _ _) (isequiv_functor_forall _ _ _ _ )).
    intro X. apply (transportable _ _ (HA_can.(can_eq) _ _ e0) X); auto. intro b. cbn.
  assert ((x;transportable y x (can_eq HA_can y x e0) b) = (y;b)).
  apply path_sigma_uncurried. unshelve esplit. cbn. destruct e.
  cbn. 
  exact (apD10 (ap e_fun (ap (transportable x x) (HA_can.(can_eq_refl) x) @ (@transportable_refl _ _ _ x))) b).
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
                            | eq_refl => eq_refl
                            end) (f (e.1 b)) = f b). 
    change (T (transportable a a (can_eq HA_can a a eq_refl);
               (ap (transportable a a) (HA_can.(can_eq_refl) a) @ (transportable_refl a)))).
  assert ((transportable a a (can_eq HA_can a a eq_refl);
               (ap (transportable a a) (HA_can.(can_eq_refl) a) @ (transportable_refl a)))= ((Equiv_id (B a); eq_refl): {e : B a ≃ B a & e = Equiv_id (B a)})).
  apply path_sigma_uncurried. unshelve esplit. cbn. 
  apply (ap (transportable a a) (HA_can.(can_eq_refl) a) @ (transportable_refl a)). 
  cbn. rewrite transport_paths_l. rewrite inv2. rewrite concat_refl. reflexivity.  
  apply (transport_eq T X^). unfold T. cbn.
  exact (apD10 (ap e_fun (HP2 (a;b))) _). 
Defined.


(* this instance of transportable is for the equality type, we can use the default one*)

Hint Extern 0 (Transportable (fun _ : _ => _ = _))
=> apply Transportable_default : typeclass_instances.

Hint Extern 0 (Transportable (eq _ _))
=> apply Transportable_default : typeclass_instances.

Hint Extern 0 (Canonical_eq (_ = _))
=> apply Canonical_eq_gen : typeclass_instances.

Definition FP_forall_UR_Coh (A A' : Type) (eA : A ⋈ A')
           (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') : 
  UR_Coh (forall x : A, B x) (forall x : A', B' x) (Equiv_forall A A' eA B B' eB) (URForall A A' B B').
Proof.

  econstructor. intros f g. 

  eapply equiv_compose. 
  eapply (BuildEquiv _ _ (@apD10_gen _ _ f g) _).
  
  unshelve eapply Equiv_forall.
  apply URType_Refl_can. apply eA. 
  split; [typeclasses eauto | ].
  intros a a' e. cbn in e. 
  apply Canonical_UR. 
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
    XX.2 (Equiv_id (XX.1 ≈ b))) (e_fun (ur_coh XX.1 XX.1) eq_refl)))) (g XX.1))).
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
               (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') eq_refl)))) (g a'))).
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
    (e_fun (ur_coh a' a') eq_refl) = h). cbn in h. 
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
                       (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') eq_refl))).
  unfold e. cbn.
  etransitivity; try apply transport_e_fun. 
  cbn. unfold Move_equiv, e, ur_refl, alt_ur_coh. cbn.  
  rewrite inv2. exact X. 
  destruct X0. apply Equiv_id.
Defined. 

Definition FP_forall_ur_type (A A' : Type) (eA : A ⋈ A')
           (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B') :
  (forall x : A, B x) ⋈ (forall x : A', B' x).
  unshelve econstructor.
  - apply FP_forall_UR_Coh.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined.

Definition FP_forall :
            (fun A B => forall x:A , B x) ≈ (fun A' B' => forall x:A', B' x).
Proof.
  cbn. intros A A' eA. split ; [typeclasses eauto | ]. 
  intros B B' eB. eapply FP_forall_ur_type; eauto. 
Defined. 

Hint Extern 0 (UR_Type (forall x:_ , _) (forall y:_, _)) => erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros : typeclass_instances.

Hint Extern 100 ((forall x:_ , _) ≃ (forall y:_, _)) => erefine (Equiv_forall _ _ _ _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros : typeclass_instances.

Hint Unfold ur. 
Typeclasses Transparent ur.
Hint Transparent ur. 
 
Instance Transportable_cst A B : Transportable (fun _ : A => B) :=
  {|
    transportable := fun (x y : A) _ => Equiv_id B;
    transportable_refl := fun x : A => eq_refl
  |}.

Definition Equiv_Arrow (A A' B B': Type)
           (eA: A ≈ A') (e' : B ≈ B') :
  (A -> B) ≃ (A' -> B') := Equiv_forall _ _ eA _ _ {| transport_ := _ ; ur_type:= fun _ _ _ => e' |}.

Hint Extern 0 ((_ -> _) ≃ (_ -> _)) =>
  erefine (Equiv_Arrow _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Hint Extern 0 (UR_Type (_ -> _) (_ -> _)) =>
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := Transportable_cst _ _; ur_type := _|} ); cbn in *; intros : typeclass_instances.
