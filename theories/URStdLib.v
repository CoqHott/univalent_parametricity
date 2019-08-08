(************************************************************************)
(* This file contains basic definitions of UR that are helpful for many examples  *)
(************************************************************************)

Require Import HoTT HoTT_axioms UR URTactics DecidableEq FP ADT.

(*! nat !*)

Instance DecidableEq_eq_nat : DecidableEq nat.
constructor. intros x y; revert y. 
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (ap S H).
    intro H; right. intro e. inversion e. apply (H (logic_eq_is_eq H1)).
Defined.

Instance UR_nat : UR nat nat := UR_gen nat. 
Instance FP_nat : nat ⋈ nat := _ URType_Refl_decidable nat DecidableEq_eq_nat.
Canonical Structure Dnat : DType := Build_DType nat _.

(*! FP for nat_rect !*)

Definition nat_rect : forall P : nat -> Type,
    P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
  := 
    fun (P : nat -> Type) (f : P 0)
        (f0 : forall n : nat, P n -> P (S n)) =>
      fix F (n : nat) : P n :=
      match n as n0 return (P n0) with
      | 0 => f
      | S n0 => f0 n0 (F n0)
      end.

Definition FP_nat_rect : nat_rect ≈ nat_rect.
  intros X X' [H H'] P P' e0 Q Q' e_S n n' en.    
  equiv_elim. exact (e_S n n eq_refl _ _ IHn).
Defined.

Definition FP_nat_rect_cst (P Q:Type) (e : P ≈ Q) :
  nat_rect (fun _ => P) ≈ nat_rect (fun _ => Q) :=
  FP_nat_rect (fun _ => P) (fun _ => Q)
              {| transport_ := Transportable_cst nat P ; ur_type := fun _ _ _ => e |}.


(*! bool !*)

Instance DecidableEq_eq_bool : DecidableEq bool.
constructor. intros x y; revert y. induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- destruct y.
 + right; intro H; inversion H.
 + left ;reflexivity.
Defined.

Instance UR_bool : UR bool bool := UR_gen bool. 
Instance FP_bool : bool ⋈ bool := URType_Refl_decidable bool DecidableEq_eq_bool.
Canonical Structure Dbool : DType := Build_DType bool _.


(*! List !*)

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Infix "::" := cons (at level 60, right associativity). 

Definition inversion_cons {A} {l l':list A} {a a'} : a :: l = a' :: l' -> (a = a') * (l = l').
  inversion 1. split; reflexivity.
Defined. 

Instance Transportable_list A (P: list A -> Type)
         (HP : forall (P:A->Type), Transportable P) : Transportable P.
Proof.
  unshelve econstructor.
  - intros n m. revert P; revert m.
    induction n; intro m; destruct m; intros P e. 
    + apply Equiv_id.
    + inversion e.
    + inversion e.
    + pose (inversion_cons e). specialize (IHn _ (fun n => P (a :: n)) (snd p)).
      cbn in IHn. eapply equiv_compose; try exact IHn. apply (HP (fun x => P (x :: m))).
      exact (fst p). 
  - cbn. intro n; revert P; induction n; cbn; intro P. 
    + reflexivity.
    + rewrite transportable_refl. rewrite (IHn (fun n => P (a :: n))).
      apply path_Equiv. reflexivity.
Defined. 

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

(* ET: renamed that one since inversion_cons already exists, in a different form, above *)
Definition inversion_cons' {A a a'} {l l':list A} (X: a::l = a'::l') :
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
  cbn in *. pose (inversion_cons' X). destruct s as [s s']. 
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
  split ; [typeclasses eauto | ]. 
  intros A B e. 
  econstructor; try typeclasses eauto. econstructor.
  intros a b. apply URIsUR_list.
  (* to be improved *)
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.    
Defined.

(* ET: why do we keep this one? *)
(* non-effective FP for list *)
Definition FP_List' : list ≈ list.
  cbn. split; [apply Transportable_default | ].
  intros A B e.
  destruct (e_inv (eq_to_equiv _ _) (equiv e)).
  apply Canonical_UR.
  apply Equiv_id.
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


