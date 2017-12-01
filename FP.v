(************************************************************************)
(* This file proves the fundamental property for the main constructors of CIC *)
(************************************************************************)

Set Universe Polymorphism.

Require Import HoTT URTactics String UR.

Instance Equiv_eff_id A : Equiv_eff A A (Equiv_id A).
Instance Equiv_eff_inv_id A : Equiv_eff_inv A A (Equiv_id A).
Instance Equiv_eff_retraction_id A : Equiv_eff_retraction A A (Equiv_id A). 
Instance Equiv_eff_section_id A : Equiv_eff_section A A (Equiv_id A). 
Instance Equiv_eff_full_id A : Equiv_eff_full A A (Equiv_id A) := {}.

(*! Establishing FP for Type !*)

Instance URType_Refl : URRefl Type Type (Equiv_id _) _ :=
  {| ur_refl_ := _ |}.
Proof.
  intro A. cbn. unshelve eexists.
  - apply Equiv_id.
  - apply UR_gen.
  - constructor. intros;apply Equiv_id.
Defined.

Definition transport_UR_Type A B C (e: B = C) e1 e2 e3 :
  transport_eq (fun X : Type => A ⋈ X)
               e (Build_UR_Type A B e1 e2 e3) =
  Build_UR_Type A C (e # e1) (e#e2)
                        (transportD2 _ _ (@UR_Coh A) e _ _ e3)
  :=
  match e with eq_refl => eq_refl end.

Definition transport_UR_Type' A B C (e: A = C) e1 e2 e3 :
  transport_eq (fun X : Type => X ⋈ B)
               e (Build_UR_Type A B e1 e2 e3) =
  Build_UR_Type C B (e # e1) (e#e2)
                        (transportD2 _ _ (fun X => @UR_Coh X B) e _ _ e3)
  :=
  match e with eq_refl => eq_refl end.

Definition path_UR_Type A B (X Y:UR_Type A B) (e1:X.(equiv) = Y.(equiv))
           (e2 : X.(Ur) = Y.(Ur))
           (e3 : forall a a',
               e_fun (@ur_coh _ _ _ _ (transport_eq (fun X => UR_Coh A B X _ ) e1
                                   (transport_eq (fun X => UR_Coh A B _ X ) e2 X.(Ur_Coh))) a a') =
               e_fun (@ur_coh _ _ _ _ Y.(Ur_Coh) a a'))
                               : X = Y. 
Proof.
  destruct X, Y. cbn in *. 
  destruct e1, e2. cbn.
  destruct Ur_Coh, Ur_Coh0. 
  assert (ur_coh = ur_coh0).
  apply funext. intro a.
  apply funext. intro a'.
  apply path_Equiv. apply e3. destruct X; reflexivity. 
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
Defined. 


Definition UR_Type_Equiv_gen (X:Type) (eX : X ⋈ X) (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈ y) `{A x ≈ A y}
  : B x ≈ B y.
Proof.
  unshelve refine (UR_Type_Equiv _ _ _).
  unshelve refine (UR_Type_Equiv' _ _ _).
  auto. 
Defined.

Ltac etransitivity := refine (_ @_).

Instance funext_isequiv A P (f g : forall x : A, P x) : IsEquiv (@apD10 _ _ f g) := funext _ _ _ _.

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
    destruct e as [e eur ecoh].
    revert eur ecoh. rewrite <- (@e_retr _ _ _ (univalence _ _) _).
    set (eeq := (e_inv _ e)).
    clearbody eeq;clear e.
    destruct eeq. intros eur ecoh.
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
    destruct p. reflexivity.
Defined.

Instance FP_Type : Type ⋈ Type.
Proof. 
  econstructor; try typeclasses eauto.
Defined.

(* This one is not effective due to the use of univalence *)
(* Instance UR_coh_eff_Type : Equiv_eff Type Type.  *)

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
    destruct p. reflexivity.
Defined.

Instance FP_Prop : Prop ⋈ Prop.
Proof.
  econstructor; typeclasses eauto. 
Defined.

(* This one is not effective due to the use of univalence *)
(* Instance UR_coh_eff_Prop : Equiv_eff Prop Prop.  *)

(*! Establishing FP for Prop !*)


(*! ur is symmetric on types !*)

Definition UR_Type_Inverse (A B : Type) : A ≈ B -> B ≈ A.
Proof.
  intro e.
  unshelve eexists; cbn in *. 
  - apply Equiv_inverse; typeclasses eauto. 
  - econstructor. exact (fun b a => ur a b).
  - econstructor. intros b b'. cbn. 
    eapply equiv_compose. apply isequiv_sym.
    eapply equiv_compose. apply (@isequiv_ap _ _ ( Equiv_inverse (equiv e))).
    eapply equiv_compose. apply ur_coh.
    cbn. unfold univalent_transport.
    refine (transport_eq (fun X => (_ ≈ X) ≃ _) (e_retr _ _)^ (Equiv_id _)). 
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
Defined.     

Instance Ur_Coh_eff_gen (A B:Type) e (H:Equiv_eff_full A B e) : Ur_Coh_eff A B (@Canonical_UR A B e).

Instance UR_eff_gen (A B:Type) e (H:Equiv_eff_full A B e) : UR_eff A B (@Canonical_UR A B e) := {}.


Definition UR_Type_gen (A:Type) : ur A A := @Canonical_UR _ _ (Equiv_id A). 

(*! FP for nat, canonical !*)

Instance FP_nat : nat ⋈ nat := UR_Type_gen _.

(*! FP for bool, canonical !*)

Instance FP_bool : bool ⋈ bool := UR_Type_gen _.

(*! FP for Product !*)

(* IoE has been automated *)

Definition Equiv_prod (A B A' B' : Type) (e:A ≃ B) (e':A' ≃ B') : (A * A') ≃ (B * B').
Proof.
  equiv_adt (@prod_rect _ _) (@pair _ _).
Defined.

Instance Equiv_eff_prod (A A' B B':Type) (e_A : A ≃ A') (e_B : B ≃ B')
         `{@Equiv_eff A A' e_A} `{@Equiv_eff B B' e_B}
  : Equiv_eff (A*B) (A'*B') (Equiv_prod _ _ _ _ e_A e_B).

Instance Equiv_eff_inv_prod (A A' B B':Type) (e_A : A ≃ A') (e_B : B ≃ B')
         `{@Equiv_eff_inv A A' e_A} `{@Equiv_eff_inv B B' e_B}
  : Equiv_eff_inv (A*B) (A'*B') (Equiv_prod _ _ _ _ e_A e_B) := { }.

Instance Equiv_eff_section_prod (A A' B B':Type) (e_A : A ≃ A') (e_B : B ≃ B')
         `{@Equiv_eff_section A A' e_A} `{@Equiv_eff_section B B' e_B}
  : Equiv_eff_section (A*B) (A'*B') (Equiv_prod _ _ _ _ e_A e_B).

Instance Equiv_eff_retraction_prod (A A' B B':Type) (e_A : A ≃ A') (e_B : B ≃ B')
         `{@Equiv_eff_retraction A A' e_A} `{@Equiv_eff_retraction B B' e_B}
  : Equiv_eff_retraction (A*B) (A'*B') (Equiv_prod _ _ _ _ e_A e_B) := { }.

Instance Equiv_eff_full_prod (A A' B B':Type) (e_A : A ≃ A') (e_B : B ≃ B')
         `{@Equiv_eff_full A A' e_A} `{@Equiv_eff_full B B' e_B}
  : Equiv_eff_full (A*B) (A'*B') (Equiv_prod _ _ _ _ e_A e_B) := { }.

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
  := BuildEquiv _ _ _ _. 

Definition FP_prod : prod ≈ prod.
  cbn in *; intros.
  unshelve refine (Build_UR_Type _ _ _ _ _).
  unshelve refine (Equiv_prod _ _ _ _ _ _); typeclasses eauto. 
  econstructor. exact (fun e e' => prod (fst e ≈ fst e') (snd e ≈ snd e')). 
  econstructor. intros [X Y] [X' Y']. cbn.
  assert ( ((X, Y) = (X', Y')) ≃ ((X=X') * (Y=Y'))).
  apply Equiv_inverse. apply (equiv_path_prod (X, Y) (X', Y')).
  eapply equiv_compose. exact X0.
  eapply equiv_compose. apply Equiv_prod.
  apply ur_coh. apply ur_coh. apply Equiv_id. 
Defined.

Instance Ur_Coh_eff_prod (A A' B B':Type) (UR_A : A ⋈ A') (UR_B : B ⋈ B')
         `{@Ur_Coh_eff A A' UR_A} `{@Ur_Coh_eff B B' UR_B}
  : Ur_Coh_eff (A*B) (A'*B') (FP_prod _ _ UR_A _ _ UR_B).

Instance UR_eff_prod (A A' B B':Type) (UR_A : A ⋈ A') (UR_B : B ⋈ B')
         `{@UR_eff A A' UR_A} `{@UR_eff B B' UR_B}
  : UR_eff (A*B) (A'*B') (FP_prod _ _ UR_A _ _ UR_B) := { }.

Hint Extern 0 ((_ * _) ≃ (_ * _)) => erefine (@Equiv_prod _ _ _ _ _ _)
:  typeclass_instances.

Hint Extern 0 (UR_Type (_ * _) (_ * _)) => erefine (@FP_prod _ _ _ _ _ _)
:  typeclass_instances.
 
(*! FL for List !*)

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (compat "8.4").

Infix "::" := cons (at level 60, right associativity). 

(* IoE has been automated *)

Instance Equiv_List A B (e:A ≃ B) : list A ≃ list B.
Proof.
    equiv_adt2 (@list_rect _) (@nil _) (@cons _).
Defined.

Instance Equiv_eff_list (A A':Type) (e_A : A ≃ A')
         `{@Equiv_eff A A' e_A} : Equiv_eff (list A) (list A') (Equiv_List _ _ e_A).

Instance Equiv_eff_inv_list (A A':Type) (e_A : A ≃ A')
         `{@Equiv_eff_inv A A' e_A} : Equiv_eff_inv (list A) (list A') (Equiv_List _ _ e_A).

Instance Equiv_eff_section_list (A A':Type) (e_A : A ≃ A')
         `{@Equiv_eff_section A A' e_A} : Equiv_eff_section (list A) (list A') (Equiv_List _ _ e_A).

Instance Equiv_eff_retraction_list (A A':Type) (e_A : A ≃ A')
         `{@Equiv_eff_retraction A A' e_A} : Equiv_eff_retraction (list A) (list A') (Equiv_List _ _ e_A).

Instance Equiv_eff_full_list (A A':Type) (e_A : A ≃ A')
         `{@Equiv_eff_full A A' e_A} : Equiv_eff_full (list A) (list A') (Equiv_List _ _ e_A) := { }.

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
  intros. cbn. apply alt_ur_coh. 
  eapply equiv_compose. eapply UR_List_is_eq.
  refine (transport_eq (fun X => (l = X) ≃ _) (e_sect _ l')^ _). refine (Equiv_id _).
Defined. 

Definition FP_List : list ≈ list.
  intros A B e. 
  econstructor; try typeclasses eauto. econstructor.
  intros a b. apply URIsUR_list. 
Defined.

Instance Ur_Coh_eff_list (A A':Type) (UR_A : A ⋈ A') 
         `{@Ur_Coh_eff A A' UR_A} : Ur_Coh_eff (list A) (list A') (FP_List _ _ UR_A).

Instance UR_eff_list (A A':Type) (UR_A : A ⋈ A') 
         `{@UR_eff A A' UR_A} : UR_eff (list A) (list A') (FP_List _ _ UR_A) := {}.

Definition FP_List_rect : @list_rect ≈ @list_rect.
Proof.
  intros A B e X X' eX P P' P_nil Q Q' Q_cons l l' el. 
  induction el; typeclasses eauto with typeclass_instances. 
Defined.

Hint Extern 0 (list_rect _ ?X ?P ?Q ?l ≈ list_rect _ ?X' ?P' ?Q' ?l') =>
unshelve notypeclasses refine (FP_List_rect _ _ _ X X' _ P P' _ Q Q' _ l l' _); intros
:  typeclass_instances.

Definition FP_cons : @cons ≈ @cons.
Proof. 
  cbn; intros. typeclasses eauto. 
Defined.

Definition FP_nil : @nil ≈ @nil.
Proof. 
  cbn; intros. typeclasses eauto.  
Defined.

Instance Equiv_List_instance : forall x y : Type, x ⋈ y -> (list x) ⋈ (list y) := FP_List.

(*! FL for Dependent product !*)

(* isequiv_functor_forall can be found in
[https://github.com/HoTT/HoTT] *)

Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (g : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun H b => g b (H (f b)).

Instance isequiv_functor_forall {A B} {P : A -> Type} {Q : B -> Type}
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - refine (functor_forall (e_inv f) _).
    intros a y.
    generalize (e_inv (g _) y). clear y.
    exact (transport_eq _ (e_retr f a)).
  - intros h;apply funext. intros a.
    unfold functor_forall.
    destruct (e_retr f a). apply e_sect.
  - intros h;apply funext.
    unfold functor_forall.
    intros b.
    rewrite e_adj. destruct (e_sect f b). apply e_retr.
Defined.

Instance isequiv_functor_forall_ur {A B} `{P : A -> Type} `{Q : B -> Type} (e : B ≈ A) (e' : Q ≈ P)
  : IsEquiv (functor_forall (e_fun (equiv e))
                            (fun x => (e_inv' ((equiv (e' x (e_fun (equiv e) x) (ur_refl x))))))).
Proof.
  apply isequiv_functor_forall;[exact _|].
  intros b. unfold e_inv'.
  apply isequiv_inverse.
Defined.

Instance Equiv_forall (A A' : Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  pose (e := UR_Type_Inverse _ _ eA).
  pose (e' := fun x y E => UR_Type_Inverse _ _ (eB y x E)).
  unshelve refine
           (BuildEquiv _ _ (functor_forall (e_fun (equiv e))
           (fun x => (e_inv' ((equiv (e' x (e_fun (equiv e) x) (ur_refl (e:=e) x))))))) _).
Defined.

Instance Equiv_eff_forall (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@Equiv_eff_inv A A' (equiv eA)} `{forall x y e, @Equiv_eff (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff (forall x:A, B x) (forall x: A', B' x) (Equiv_forall _ _ eA _ _ eB).

Instance Equiv_eff_forall_inv (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@Equiv_eff A A' (equiv eA)} `{forall x y e, @Equiv_eff_inv (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff_inv (forall x:A, B x) (forall x: A', B' x) (Equiv_forall _ _ eA _ _ eB).

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

Definition FP_forall :
            (fun A B => (forall x:A , B x)) ≈ (fun A' B' => (forall x:A', B' x)).
Proof.
  intros A A' eA x y H. cbn in H.
  cbn. unshelve econstructor.
  econstructor. intros f g.

  eapply equiv_compose. 
  eapply (BuildEquiv _ _ (@apD10_gen _ _ f g) _).

  unshelve eapply Equiv_forall. apply (@ur_refl_ _ _ _ _ URType_Refl A). 
  intros a a' e. cbn in e. destruct e.
  apply Canonical_UR. 
  unshelve eapply Equiv_forall. typeclasses eauto.
  intros a' b e'. 
  apply Canonical_UR. 
  unshelve eapply Equiv_forall.
  apply Canonical_UR.
  pose (e_fun (alt_ur_coh eA _ _) e').
  apply Equiv_inverse. eapply equiv_compose. apply alt_ur_coh.
  eapply equiv_compose. apply isequiv_sym.
  exact (transport_eq (fun X => (X = _) ≃ _) e (Equiv_id _)).
  intros X X' X''. destruct X. 
  apply Canonical_UR.
  clear e' X''. 
  pose (e_fun (alt_ur_coh eA _ _) X').
  eapply equiv_compose. apply ur_coh. cbn. 
  unfold univalent_transport. cbn. 
  cbn in e.
  set (T := fun (XX : {XX : _ & b = univalent_transport XX}) =>
               (f a' ≈ e_fun (equiv (H a' b X')) (g a'))
  ≃ (f a' ≈ e_fun (equiv (H XX.1 b (e_fun (transport_eq (fun X : A' => (XX.1 ≈ X) ≃ (XX.1 ≈ b))
    XX.2 (Equiv_id (XX.1 ≈ b))) (e_fun (ur_coh XX.1 XX.1) eq_refl)))) (g XX.1))).
  change (T (_;(e_retr (e_fun (equiv eA)) b)^)).
  unshelve refine (transport_eq T _ _).
  exact (_ ; (Move_equiv _ _ _ e)^).
  apply path_sigma_uncurried. unshelve eexists. exact e.
  cbn. unfold univalent_transport.
  rewrite transport_paths_Fr. rewrite ap_V.
  rewrite <- concat_inv. reflexivity. 
  unfold T; cbn. clear T. 
  pose (T := fun (XX : {XX : A' & a' ≈ XX}) => let foo := H _ _ XX.2 in 
               (f a' ≈ e_fun (equiv (H a' b X')) (g a'))
  ≃ (f a'  ≈ e_fun (equiv (H a' b
               (e_fun (transport_eq (fun X : A' => (a' ≈ X) ≃ (a' ≈ b)) (Move_equiv (equiv eA) a' b e)^
               (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') eq_refl)))) (g a'))).
  change (T (_; ur_refl a')).
  assert (X' =
  transport_eq (fun XX : A' => a' ≈ XX)
               (Move_equiv (equiv eA) a' b e) (ur_refl a')).
  pose (e_sect' (alt_ur_coh _ _ _) X').
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

  unshelve refine (transport_eq T _ _).
  exact (_ ; X'). 
  apply path_sigma_uncurried. unshelve eexists. cbn.
  unfold univalent_transport. apply inverse. apply Move_equiv. exact e.
  rewrite inv2. exact X. 
  unfold T. cbn. clear T. 
  assert (X' = (e_fun (transport_eq (fun X : A' => (a' ≈ X) ≃ (a' ≈ b)) (Move_equiv (equiv eA) a' b e)^
                       (Equiv_id (a' ≈ b))) (e_fun (ur_coh a' a') eq_refl))).
  unfold e. cbn.
  etransitivity; try apply transport_e_fun. 
  cbn. unfold Move_equiv, e, ur_refl, alt_ur_coh.
  cbn.  
  rewrite inv2. exact X. 
  destruct X0. apply Equiv_id. 
Defined. 

Hint Extern 0 (UR_Type (forall x:_ , _) (forall y:_, _)) => erefine (FP_forall _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Hint Extern 100 ((forall x:_ , _) ≃ (forall y:_, _)) => erefine (Equiv_forall _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Hint Unfold ur. 
Typeclasses Transparent ur.
Hint Transparent ur. 

Definition Equiv_Arrow (A A' B B': Type)
           (eA: A ≈ A') (e' : B ≈ B') :
  (A -> B) ≃ (A' -> B') := Equiv_forall _ _ eA _ _ (fun _ _ _ => e').

Hint Extern 0 ((_ -> _) ≃ (_ -> _)) =>
  erefine (Equiv_Arrow _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

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
  induction l.
  - unshelve refine (exist_eq _ _ _ _ _ _). apply H. apply H'. 
Defined.


(* Equiv_Sigma is similar to equiv_functor_sigma *)
(* in the [https://github.com/HoTT] *)

Definition Equiv_Sigma (A A':Type) (e: A ≈ A')
           (B: A -> Type) (B': A' -> Type)
           (e' : B ≈ B') : (sigT B) ≃ (sigT B').
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
    apply ap. 
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
    apply (ap (fun x => e_fun x _)).
    apply ap. unfold ur_refl.
    rewrite <- transport_e_fun. cbn. rewrite inv2. reflexivity. 
Defined. 

Instance Equiv_eff_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@Equiv_eff A A' (equiv eA)} `{forall x y e, @Equiv_eff (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff (sigT B) (sigT B') (Equiv_Sigma _ _ eA _ _ eB).

Instance Equiv_eff_inv_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@UR_eff A A' eA} `{forall x y e, @Equiv_eff_inv (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff_inv (sigT B) (sigT B') (Equiv_Sigma _ _ eA _ _ eB).

Instance Equiv_eff_section_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@UR_eff A A' eA} `{forall x y e, @Equiv_eff_full (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff_section (sigT B) (sigT B') (Equiv_Sigma _ _ eA _ _ eB).

Instance Equiv_eff_retraction_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@UR_eff A A' eA} `{forall x y e, @Equiv_eff_full (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff_retraction (sigT B) (sigT B') (Equiv_Sigma _ _ eA _ _ eB).

Instance Equiv_eff_full_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@UR_eff A A' eA} `{forall x y e, @Equiv_eff_full (B x) (B' y) (equiv (eB _ _ e))} :
  Equiv_eff_full (sigT B) (sigT B') (Equiv_Sigma _ _ eA _ _ eB) := {}.

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
  := BuildEquiv _ _ _ _. 

Definition FP_Sigma : @sigT ≈ @sigT.
  cbn in *; intros. unshelve eexists.
  - eapply URSigma. typeclasses eauto.
  - econstructor. intros a a'.
    assert ((a = a') ≃ {p : a.1 = a'.1 & a.2 = p^# a'.2}).
    apply Equiv_inverse. eapply equiv_path_sigma.
    eapply equiv_compose. exact X.
    unshelve eapply Equiv_Sigma.
    apply Canonical_UR. 
    destruct a, a'. apply ur_coh.
    intros e e' E.
    apply Canonical_UR. 
    destruct a, a'. cbn in *. unfold univalent_transport. 
    destruct e.
    apply  Move_equiv in E. rewrite <- E. 
    apply ur_coh.
Defined.

Hint Extern 0 (UR_Type (sigT _) (sigT _)) => erefine (@FP_Sigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Instance Ur_Coh_eff_section_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@UR_eff A A' eA} `{forall x y e, @Ur_Coh_eff (B x) (B' y) (eB _ _ e)} :
  Ur_Coh_eff (sigT B) (sigT B') (FP_Sigma _ _ eA _ _ eB).

Instance UR_eff_section_Sigma (A A':Type) (eA : A ≈ A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈ B')
         `{@UR_eff A A' eA} `{forall x y e, @UR_eff (B x) (B' y) (eB _ _ e)} :
  UR_eff (sigT B) (sigT B') (FP_Sigma _ _ eA _ _ eB) := {}.

Transparent functor_forall sigma_map. 
Hint Transparent functor_forall sigma_map. 
Hint Unfold functor_forall sigma_map. 

Definition FP_existT : @existT ≈ @existT :=
  fun A B H P Q H' x y e X Y E =>
      existT _ e E.

Hint Extern 0 ({e0 : ?x ≈ ?y & ?X ≈ ?Y}) => unshelve refine (FP_existT _ _ _ _ _ _ _ _ _ _ _ _ ): typeclass_instances. 

Definition FP_sigT_rect : @sigT_rect ≈ @sigT_rect.
Proof.
  cbn. intros. 
  destruct x3, y3, H3. apply H2. 
Defined. 

(*! FP for the identity types !*)

Definition eq_map (A B:Type) (e: A ≈ B)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (x = x') -> (y = y').
Proof.
  pose (e_i := Equiv_inverse (equiv e)).
  pose (e_fun (alt_ur_coh e _ _) e1).
  pose (e_fun (alt_ur_coh e _ _) e2).
  - intro ex. 
    exact ((e_retr _ y)^ @ ap _ (e0^ @ ex  @ e3) @ e_retr _ y').
Defined.

Definition eq_map_inv (A B:Type) (e: A ≈ B)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (y = y') -> (x = x').
Proof.
  unfold univalent_transport in *.
  pose (e_i := Equiv_inverse (equiv e)).
  pose (e_fun (alt_ur_coh e _ _) e1).
  pose (e_fun (alt_ur_coh e _ _) e2).
  - intro ey. 
    exact (e0 @ ap _ ey @ e3^). 
Defined.

Definition Equiv_eq (A B:Type) (e: A ≈ B)
           (x :A) (y : B) (e1 : x ≈ y)
           (x' : A) (y' : B) (e2 : x' ≈ y'): (x = x') ≃ (y = y').
Proof.
  unfold univalent_transport in *.
  pose (e_i := Equiv_inverse (equiv e)).
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - eapply eq_map; eauto. 
  - eapply eq_map_inv; eauto. 
  - intro E. unfold eq_map_inv, eq_map.
    unfold univalent_transport. cbn. 
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
  - intro E. cbn. unfold eq_map_inv, eq_map.
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

Definition FP_eq : @eq ≈ @eq.
  cbn. unshelve eexists. 
  - econstructor. intros e e'.
    assert ((y0 = y1) ≃ (x0 = x1)). eapply Equiv_inverse. typeclasses eauto with typeclass_instances.
    exact (e = ↑ e').
  - econstructor. intros e e'.
    Opaque Equiv_eq. 
    unfold univalent_transport. cbn. 
    Transparent Equiv_eq. rewrite e_sect. 
    apply Equiv_id. 
Defined. 

Hint Extern 0 (UR_Type (_ = _) (_ = _)) => erefine (FP_eq _ _ _ _ _ _ _ _ _) :  typeclass_instances.
 
Hint Extern 0 (UR_Type (_ = _) (_ = _)) => unshelve notypeclasses refine (FP_eq _ _ _ _ _ _ _ _ _) :  typeclass_instances.

Opaque alt_ur_coh.

Definition FP_eq_refl : @eq_refl ≈ @eq_refl.
Proof.
  cbn; intros. unfold eq_map_inv. cbn.
  apply inverse.
  exact ((ap2 _ (concat_refl _ _ _ _) eq_refl) @ inv_inv' _ _ _ _).
Defined.

Hint Extern 0 (eq_refl = eq_map_inv _ _ _ _ _ _ _ _ _  eq_refl) =>
erefine (FP_eq_refl _ _ _ _ _ _):  typeclass_instances.

Definition FP_eq_rect : @eq_rect ≈ @eq_rect.
Proof.
  simpl. intros. destruct x4 , y4. cbn.
  revert H2.  
  assert (H1 x0 y0 H0 (@eq_refl x x0)
                (@eq_refl y y0)
                (FP_eq_refl x y H x0 y0 H0) = H1 x0 y0 H3 (@eq_refl x x0) (@eq_refl y y0) H4).
  pose (T := fun (X:{X : x0 ≈ y0 & eq_refl =
  eq_map_inv x y H x0 y0 H0 x0 y0 
              X eq_refl}) => H1 x0 y0 X.1 eq_refl eq_refl X.2).
  change (T (H0 ; FP_eq_refl x y H x0 y0 H0) =
          T (H3; H4)).
  refine (transport_eq (fun X => T X = _) _ eq_refl).
  clear T. 
  cbn. rename H4 into X. 
  unfold eq_map_inv in X.
  set (eq := alt_ur_coh H x0 y0) in *. 
  apply path_sigma_uncurried. unshelve eexists. cbn in *. 
  apply (ap_inv_equiv (e_fun eq)).
  cbn. apply moveL_M1 in X. exact (X @ concat_refl _ _ _ _).
  cbn.
  rewrite transport_paths_Fr.
  apply moveR_pV.
  unfold FP_eq_refl, ap_inv_equiv, ap_inv_equiv',  eq_map_inv.
  fold eq. unfold univalent_transport; cbn.
  rewrite inv2.
  set (moveL_M1 (e_fun eq H3) (e_fun eq H0 @ eq_refl) X @
         concat_refl x x0 (e_inv (e_fun (equiv H)) y0) (e_fun eq H0)) in *.
  cbn in *. 
  rewrite (ap_compose (fun x => (e_fun eq x)^)).
  rewrite (ap_compose (fun x => (e_fun eq x))).
  assert (forall X , ap (fun x3 : x0 ≈ y0 => e_fun eq x3)
          (((e_sect (e_fun eq) H3)^ @ ap (e_inv (e_fun eq)) X) @
            e_sect (e_fun eq) H0)^ = X^).
  clear. intro X. rewrite ap_V. apply ap. repeat rewrite ap_pp.
  rewrite <- ap_compose. rewrite <- e_adj.
  rewrite <- concat_p_pp. rewrite (concat_A1p (f:=(fun x1 : x0 = e_inv (e_fun (equiv H)) y0 => e_fun eq (e_inv (e_fun eq) x1)))).
  rewrite ap_V. rewrite e_adj. rewrite concat_p_pp, inv_inv. reflexivity. 
  rewrite X0. clear X0.
  rewrite concat_inv. 
  repeat rewrite ap_pp. 
  rewrite moveL_M1_eq.
  rewrite concat_p_pp. apply whiskerR.
  clear e X.
  set (e_fun eq H0). 
  destruct e. cbn in *. reflexivity.
  rewrite X. exact id. 
Defined.

