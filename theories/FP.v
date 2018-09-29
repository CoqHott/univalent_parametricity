(************************************************************************)
(* This file proves the fundamental property for the main constructors of CIC *)
(************************************************************************)

Set Universe Polymorphism.

Require Import HoTT HoTT_axioms URTactics ADT String UR.

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

Ltac etransitivity := refine (_ @_).

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

(* this requires univalence *)
Instance URType_IsEq : URIsEq Type Type (Equiv_id _) _ _.
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

(*! Establishing FP for Type !*)

Instance UR_Prop : UR Prop Prop :=
  {| ur := fun (A B :Prop) => A ⋈ B |}.

Instance URProp_Refl : URRefl Prop Prop (Equiv_id _) _ :=
  {| ur_refl_ := _ |}.
Proof.
  intro A. cbn. unshelve eexists.
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
    destruct X, X0. 
    reflexivity.
Defined.

Instance Canonical_eq_Prop : Canonical_eq Prop := Canonical_eq_gen _.

Instance FP_Prop : Prop ⋈ Prop.
Proof.
  econstructor; typeclasses eauto. 
Defined.

(*! Establishing FP for Prop !*)


(*! ur is symmetric on types !*)

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


Definition URType_Refl_can A (HA : Canonical_eq A) : A ⋈ A.
Proof.
  unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
  - apply HA.
  - apply HA.    
Defined.

Definition URType_Refl_decidable A (Hdec:forall x y : A, (x=y) + ((x = y) -> False))
  : A ⋈ A :=
  URType_Refl_can A (Canonical_eq_decidable  _ Hdec).

(* Definition UR_Type_gen (A:Type) : ur A A := @Canonical_UR _ _ (Equiv_id A).  *)

(*! FP for nat, canonical !*)

Instance FP_nat : nat ⋈ nat := URType_Refl_decidable nat Decidable_eq_nat.

(*! FP for bool, canonical !*)

Instance FP_bool : bool ⋈ bool := URType_Refl_decidable bool Decidable_eq_bool.

(*! FP for Product !*)

(* IoE has been automated *)

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
  (* this instance of transportable is on Type, we can only use the default one*)
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
 
(*! FL for List !*)

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (compat "8.6").

Infix "::" := cons (at level 60, right associativity). 

(* IoE has been automated *)

Instance Equiv_List A B (e:A ≃ B) : list A ≃ list B.
Proof.
    equiv_adt2 (@list_rect _) (@nil _) (@cons _).
Defined.

Inductive UR_list {A B} (R : A -> B -> Type) : list A -> list B -> Type :=
  UR_list_nil : UR_list R nil nil
| UR_list_cons : forall {a b l l'},
    (R a b) -> (UR_list R l l') ->
    UR_list R (a::l) (b::l').

Instance UR_list_ A B `{UR A B} : UR (list A) (list B) :=
  {| ur := UR_list ur |}.

Hint Extern 0 (UR (list ?A) (list ?B)) => unshelve notypeclasses refine (@UR_list _ _ _): typeclass_instances. 

Hint Extern 0 (UR_list ?R [] []) => exact (UR_list_nil R)  : typeclass_instances.

Hint Extern 0 (UR_list ?R (_::_) (_::_)) => unshelve refine (UR_list_cons R _ _) : typeclass_instances.

Instance Equiv_UR_list A B (R R' : A -> B -> Type)
         (e:forall a b, R a b ≃ R' a b) : forall l l' , UR_list R l l' ≃ UR_list R' l l'.
Proof.
  intros. 
  equiv_adt2 (@UR_list_rect _ _ _) (@UR_list_nil _ _ _) (@UR_list_cons _ _ _).
Defined.

Definition inversion_cons {A a a'} {l l':list A} (X: a::l = a'::l') :
  {p : (a = a') * (l = l') & X = ap2 cons (fst p) (snd p)}
  := match X with
       | eq_refl => ((eq_refl ,eq_refl) ; eq_refl) end.

Definition eq_nil_refl {A} {l:list A} (e : [] = l) :
  match l return [] = l -> Type with [] => fun e => e = eq_refl | _ => fun _ => False end e.
Proof.
  destruct e. reflexivity. 
Defined.

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
  cbn. pose (X0 := eq_nil_refl X). cbn in X0. rewrite X0. reflexivity. 
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

Definition FP_List : list ≈ list.
  (* this instance of transportable is on Type, we can only use the default one*)
  split ; [typeclasses eauto | ]. 
  intros A B e. 
  econstructor; try typeclasses eauto. econstructor.
  intros a b. apply URIsUR_list.
  (* to be improved *)
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.    
Defined.

Definition FP_List_rect : @list_rect ≈ @list_rect.
Proof.
  cbn. intros A B e X X' eX P P' P_nil Q Q' Q_cons l l' el. 
  induction el; typeclasses eauto with typeclass_instances. 
Defined.

Hint Extern 0 (list_rect _ ?X ?P ?Q ?l ≈ list_rect _ ?X' ?P' ?Q' ?l') =>
unshelve notypeclasses refine (FP_List_rect _ _ _ X X' _ P P' _ Q Q' _ l l' _); intros
:  typeclass_instances.

Definition FP_cons : @cons ≈ @cons. 
Proof. 
  typeclasses eauto. 
Defined.

Definition FP_nil : @nil ≈ @nil.
Proof. 
  typeclasses eauto.  
Defined.

Instance Equiv_List_instance : forall x y : Type, x ⋈ y -> (list x) ⋈ (list y) := ur_type FP_List.

(*! FL for Dependent product !*)

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
    apply (transportable _ _ (eA.(can_eq) _ _ (e_retr f a))).
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
           (fun x => (e_inv' ((equiv (e' x (e_fun (equiv e) x) (ur_refl (e:=e) x)))))))_). 
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
  - intro a. cbn.
    unshelve refine (path_Equiv _).
    apply funext; intro f. apply funext; intro b. cbn. unfold functor_forall.
    pose (fun (e : {e : B a ≃ B a & e = Equiv_id (B a)}) =>
            (transportable (a; e.1 b) (a; b)
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
  exact (apD10 (ap e_fun (transportable_refl (a;b))) _). 
Defined.


(* this instance of transportable is for the equality type, we can use the default one*)

Hint Extern 0 (Transportable (fun _ : _ => _ = _))
=> apply Transportable_default : typeclass_instances.

Hint Extern 0 (Transportable (eq _ _))
=> apply Transportable_default : typeclass_instances.

Hint Extern 0 (Canonical_eq (_ = _))
=> apply Canonical_eq_gen : typeclass_instances.

Definition FP_forall :
            (fun A B => forall x:A , B x) ≈ (fun A' B' => forall x:A', B' x).
Proof.
  cbn. intros A A' eA. split ; [typeclasses eauto | ]. 
  intros B B' eB.
  
  unshelve econstructor.
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

  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
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

(* Fl for sigmas *)

Definition exist_eq {A P} (a a': A) (l : P a) (l' : P a') (e : a = a') :
  e # l = l' -> existT _ a l = (a'; l').
Proof. intros e'; destruct e, e'; reflexivity. Defined.

Fixpoint sigma_map {A B P Q} (f: A -> B) (g : forall a, P a -> Q (f a)) (l : sigT P) : sigT Q :=
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
  induction l; unshelve refine (exist_eq _ _ _ _ _ _). 
Defined.

(* Equiv_Sigma is similar to equiv_functor_sigma *)
(* in the [https://github.com/HoTT] *)

Definition Equiv_Sigma (A A':Type) (e: A ≈ A')
           (B: A -> Type) (B': A' -> Type)
           (e' : B ≈ B') : (sigT B) ≃ (sigT B').
  destruct e' as [eB_refl e'].
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - unshelve refine (sigma_map univalent_transport (fun a => univalent_transport)).
  - unshelve refine (sigma_map univalent_transport (fun a => univalent_transport)).
    apply Equiv_inverse; typeclasses eauto.
    pose (einv := UR_Type_Inverse _ _ e).
    pose (einv' := fun x y E => UR_Type_Inverse _ _ (e' y x E)).
    unshelve refine (equiv (einv' a (e_fun (equiv einv) a) (ur_refl (e:=einv) a))). 
  - intro E. rewrite sigma_map_compose.
     unfold univalent_transport. simpl. 
    unshelve refine (sigma_map_eq _ _ _ _ _).
    apply e_sect. 
    intros a l. clear E. apply transport_switch. cbn. 
    rewrite e_adj. cbn. 
    pose (equiv0 := fun a b c => equiv (e' a b c)).
    pose (equiv1 := equiv e).
    pose ((e_sect (e_fun (equiv e)) a)^ # l).
    pose (X0 := (e_fun
                (transport_eq
                   (fun X : A' =>
                    (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ X)
                    ≃ (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ e_fun (equiv e) a))
                   (ap (e_fun (equiv e)) (e_sect (e_fun (equiv e)) a))^
                   (Equiv_id (e_inv (e_fun (equiv e)) (e_fun (equiv e) a) ≈ e_fun (equiv e) a)))
                (e_fun
                   (ur_coh (e_inv (e_fun (equiv e)) (e_fun (equiv e) a))
                      (e_inv (e_fun (equiv e)) (e_fun (equiv e) a))) eq_refl))).
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
    etransitivity; try exact (X (e_sect (e_fun (equiv e)) a)).
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
    rewrite <- transport_e_fun. cbn. rewrite inv2. reflexivity. 
Defined. 

Hint Extern 0 (sigT _ ≃ sigT _) => erefine (@Equiv_Sigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v) : u.1 = v.1 := ap projT1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.2 = p..1^ # v.2.
  destruct p. reflexivity. 
Defined.
    
Notation "p ..2" := (pr2_path p) (at level 50). 


Instance isequiv_path_sigma {A : Type} {B:A-> Type} {z z' : sigT B}
: IsEquiv (path_sigma_uncurried B z z') | 0.
Proof.
  unshelve eexists. 
  - exact (fun r => (r..1 ; r..2)). 
  - intro e. destruct e. cbn. destruct z, z'.
    cbn in *. destruct x. cbn in *. destruct e. reflexivity.
  - intro e. destruct e. destruct z.  reflexivity.
  - destruct z, z'. intros [e e']. cbn in *. destruct e. cbn in *. destruct e'. reflexivity. 
Defined.

Definition equiv_path_sigma {A : Type} {P : A -> Type} (u v : {x : A & P x}) :
       {p : u .1 = v .1 & u .2 = transport_eq P p^ v .2} ≃ (u = v)
  := BuildEquiv _ _ (path_sigma_uncurried P u v) _. 

Definition FP_Sigma : @sigT ≈ @sigT.
  cbn in *; intros.
  split ; [typeclasses eauto | ].
  intros. unshelve eexists. 
  - eapply URSigma. typeclasses eauto.
  - econstructor. intros a a'.
    assert ((a = a') ≃ {p : a.1 = a'.1 & a.2 = p^# a'.2}).
    apply Equiv_inverse. eapply equiv_path_sigma.
    eapply equiv_compose. exact X.
    unshelve eapply Equiv_Sigma.
    apply Canonical_UR. 
    destruct a, a'. apply ur_coh.
    cbn. split ; [typeclasses eauto | ].
    intros e e' E.
    apply Canonical_UR. 
    destruct a, a'. cbn in *. unfold univalent_transport. 
    destruct e.
    apply  Move_equiv in E. rewrite <- E. 
    apply ur_coh.
  - unshelve refine (let X : forall (a b: {x : x & x0 x}) , a=b -> a = b := _ in _).
    intros. apply path_sigma_uncurried. apply (Equiv_inverse (BuildEquiv _ _ (path_sigma_uncurried _ a b) _)) in X. exact X.
    apply (Build_Canonical_eq _ X). cbn; clear X. intros [a b].
    reflexivity.
  - unshelve refine (let X : forall (a b: {x : y & y0 x}) , a=b -> a = b := _ in _).
    intros. apply path_sigma_uncurried. apply (Equiv_inverse (BuildEquiv _ _ (path_sigma_uncurried _ a b) _)) in X. exact X.
    apply (Build_Canonical_eq _ X). cbn; clear X. intros [a b].
    reflexivity.
Defined.

Hint Extern 0 (UR_Type (sigT _) (sigT _)) => erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn in *; intros : typeclass_instances.

Transparent functor_forall sigma_map. 
Hint Transparent functor_forall sigma_map. 
Hint Unfold functor_forall sigma_map. 

Definition FP_existT : @existT ≈ @existT.
  intros A B H P Q H' x y e X Y E. 
  exact (existT _ e E).
Defined. 

Hint Extern 0 ({e0 : ?x ≈ ?y & ?X ≈ ?Y}) => unshelve refine (FP_existT _ _ _ _ _ _ _ _ _ _ _ _ ): typeclass_instances.

Definition FP_sigT_rect : @sigT_rect ≈ @sigT_rect.
Proof.
  cbn. intros A B H P Q [H' H'']. cbn. intros P' Q' [H1 H2]. cbn. intros. 
  destruct x0, y0, H3. apply H0. 
Defined. 

Hint Extern 0 (sigT_rect ?A ?P ?Q ?f ?s ≈ sigT_rect ?A' ?P' ?Q' ?f' ?s')
               => unshelve refine (FP_sigT_rect A A' _ P P' _ Q Q'
                     {| transport_ := _; ur_type := _ |} f f' _ s s' _): typeclass_instances.

Hint Extern 0 (sigT_rect ?A ?P ?Q ?f ?s ≈ _)
               => unshelve refine (FP_sigT_rect A _ _ P _ _ Q _
                     {| transport_ := _; ur_type := _ |} f _ _ s _ _) ; try eassumption : typeclass_instances.

Hint Extern 0 (_ ≈ sigT_rect ?A ?P ?Q ?f ?s)
               => unshelve refine (FP_sigT_rect _ A _ _ P _ _ Q
                     {| transport_ := _; ur_type := _ |} _ f _ _ s _ ) ; try eassumption : typeclass_instances.

(*! FP for the identity types !*)

Definition eq_map (A B:Type) (e: A ≈ B) (HB : Canonical_eq B)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (x = x') -> (y = y').
Proof.
  pose (e_i := Equiv_inverse (equiv e)).
  pose (e_fun (alt_ur_coh _ _ _ _ _) e1).
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

(* another potential definition of univalent parametricity on eq, not use here *)

Inductive UR_eq (A_1 A_2 : Type) (A_R : A_1 -> A_2 -> Type) (x_1 : A_1) (x_2 : A_2) (x_R : A_R x_1 x_2):
   forall (y_1 : A_1) (y_2 : A_2), A_R y_1 y_2 -> x_1 = y_1 -> x_2 = y_2 -> Type :=
   UR_eq_refl : UR_eq A_1 A_2 A_R x_1 x_2 x_R x_1 x_2 x_R eq_refl eq_refl.
 
Hint Extern 0 ((_ = _) ≃ (_ = _)) => erefine (Equiv_eq _ _ _ _ _ _ _ _ _) : typeclass_instances.



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
    destruct X, Y, eH. apply UR_eq_refl. 
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

Definition FP_eq : @eq ≈ @eq.
  cbn. intros.
  split ; [typeclasses eauto| ]. 
  unshelve eexists. 
  - econstructor. exact (UR_eq x y _ x0 y0 H0 x1 y1 H1).
  - econstructor. intros e e'. cbn. 
    eapply equiv_compose. Focus 2. apply Equiv_inverse.
    apply UR_eq_equiv.
    eapply Equiv_inverse,  equiv_compose.
    apply (@isequiv_ap _ _ (alt_ur_coh _ _ _ x1 y1) (transport_eq (ur x1) (eq_map x y H _ x0 y0 H0 x1 y1 H1 e')
     (transport_eq (fun X : x => X ≈ y0) e H0)) H1).
    rewrite alt_ur_coh_transport_l.
    rewrite alt_ur_coh_transport_r. cbn. 
    unfold eq_map. repeat rewrite can_eq_eq. repeat rewrite ap_pp. 
    set ((alt_ur_coh _ _ _ x0 y0) H0).
    set ((alt_ur_coh _ _ _ x1 y1) H1).
    change ( ((e^ @ e0) @
   ((ap (e_inv (equiv H)) (e_retr (equiv H) y0)^ @
     ((ap (e_inv (equiv H)) (ap (equiv H) e0^) @
       ap (e_inv (equiv H)) (ap (equiv H) e')) @
      ap (e_inv (equiv H)) (ap (equiv H) e1))) @
    ap (e_inv (equiv H)) (e_retr (equiv H) y1)) = e1) ≃ 
                                                      (e = e')).
    assert (forall y0,  ap (e_inv (equiv H)) (e_retr (equiv H) y0) = (e_sect _ _)).
    intro.
    apply (@isequiv_ap _ _ (@isequiv_ap _ _ (equiv H) _ _)). cbn.
    rewrite <- e_adj. rewrite <- ap_compose. apply moveR_M1.
    rewrite <- (ap_inv (fun x2 : y => (equiv H) (e_inv (equiv H) x2))).
    rewrite <- (transport_paths_naturality' _ (e_retr (equiv H))).
    apply inverse, inv_inv'.
    rewrite ap_inv. 
    repeat rewrite X. 
    assert (e0 @ (e_sect (equiv H) (e_inv (equiv H) y0))^  @
                                                               ((ap (e_inv (equiv H)) (ap (equiv H) e0^))) = (e_sect (equiv H) x0)^).
    rewrite <- concat_p_pp.
    rewrite <- ap_compose.
    repeat rewrite ap_inv.
    rewrite <- concat_inv. 
    rewrite <- (transport_paths_naturality' _ (e_sect (equiv H))).
    rewrite concat_inv. rewrite concat_p_pp. rewrite inv_inv'. reflexivity.
    repeat rewrite <- concat_p_pp.
    rewrite (concat_p_pp e0).
    rewrite (concat_p_pp (e0 @ (e_sect (equiv H) (e_inv (equiv H) y0))^)).
    rewrite X0. rewrite <- ap_compose. 
    rewrite (concat_p_pp (e_sect (equiv H) x0)^).
    rewrite <- (transport_paths_naturality _ (fun x => (e_sect (equiv H) x)^)).
    rewrite <- ap_compose. 
    repeat rewrite <- concat_p_pp.
    rewrite (concat_p_pp (e_sect (equiv H) x1)^).
    rewrite <- (transport_paths_naturality _ (fun x => (e_sect (equiv H) x)^)).
    repeat rewrite <- concat_p_pp.
    rewrite inv_inv. rewrite concat_refl.

    eapply equiv_compose. apply (Equiv_inverse (BuildEquiv _ _ _ (isequiv_moveL_M1 (e^ @ (e' @ e1)) e1))). 
    repeat rewrite concat_inv.     repeat rewrite <- concat_p_pp.
    rewrite (concat_p_pp e1). rewrite inv_inv'. cbn. rewrite inv2. 
    eapply equiv_compose. apply (BuildEquiv _ _ _ (isequiv_moveR_M1 _ _)). 

    clear.
    unshelve econstructor.
    intro X; destruct X. reflexivity. 
    unshelve refine (isequiv_adjointify _ _ _ _);
      intro X; destruct X; reflexivity.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.    
Defined. 

Hint Extern 0 (UR_Type (_ = _) (_ = _)) => erefine (ur_type (FP_eq _ _ _ _ _ _) _ _ _) :  typeclass_instances.
 
Hint Extern 0 (UR_Type (_ = _) (_ = _)) => unshelve notypeclasses refine (ur_type (FP_eq _ _ _ _ _ _) _ _ _) :  typeclass_instances.

Opaque alt_ur_coh.

Definition FP_eq_refl : @eq_refl ≈ @eq_refl.
Proof.
  cbn; intros. unfold eq_map_inv. cbn.
  apply UR_eq_refl.
Defined.

Hint Extern 0 ( UR_eq _ _ _ _ _ _ _ _ _ eq_refl eq_refl) =>
erefine (FP_eq_refl _ _ _ _ _ _):  typeclass_instances.

Definition FP_eq_rect : @eq_rect ≈ @eq_rect.
Proof.
  cbn; intros.
  induction H4. cbn. auto.
Defined. 
