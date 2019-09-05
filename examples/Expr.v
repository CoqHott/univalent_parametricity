Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Set Universe Polymorphism.

Inductive Expr@{i} : Set -> Type@{i} :=
  I : nat -> Expr nat
| B : bool -> Expr bool
| Add : Expr nat -> Expr nat -> Expr nat
| Mul : Expr nat -> Expr nat -> Expr nat
| Eq  : Expr nat -> Expr nat -> Expr bool.

(* directly using univalence *)

Definition FP_Expr : Expr ≈ Expr.
Proof.
  cbn.
  (* this instance of transportable is on Type, we can only use the default one*)
  split; [apply Transportable_default | ].
  intros A B e. 
  rewrite (@e_inv _ _ _ (univalence _ _) (equiv e)).
  apply (@ur_refl_ _ _ _ _ URType_Refl).
Defined.

(* using the decomposition of a parametrized inductive type 
plus a fipoint *)

Inductive Expr_p : Set :=
  I_p : nat -> Expr_p 
| B_p : bool -> Expr_p 
| Add_p : Expr_p -> Expr_p -> Expr_p
| Mul_p : Expr_p -> Expr_p -> Expr_p
| Eq_p  : Expr_p -> Expr_p -> Expr_p.

Definition index_Expr@{i j} (E : Expr_p) (EType : Set) : Type@{i} :=
  Expr_p_rect@{j}
    (fun _ => Set -> Type@{i})
    (fun _ EType => @eq@{i} Set nat EType)
    (fun _ EType => @eq@{i} Set bool EType)
    (fun E X E' X' EType => ((X nat) * (X' nat) * (@eq@{i} Set nat EType))%type)
    (fun E X E' X' EType => ((X nat) * (X' nat) * (@eq@{i} Set nat EType))%type)
    (fun E X E' X' EType => ((X nat) * (X' nat) * (@eq@{i} Set bool EType))%type)
    E EType.

Definition Expr' A := { E : Expr_p@{} & index_Expr E A}.

Definition I' : nat -> Expr' nat := fun n => (I_p n ; eq_refl). 
Definition B' : bool -> Expr' bool := fun b => (B_p b ; eq_refl). 
Definition Add' : Expr' nat -> Expr' nat  -> Expr' nat
  := fun e e0 => (Add_p e.1 e0.1; ((e.2,e0.2,eq_refl))).
Definition Mul' : Expr' nat -> Expr' nat  -> Expr' nat
  := fun e e0 => (Mul_p e.1 e0.1; ((e.2,e0.2,eq_refl))).
Definition Eq' : Expr' nat -> Expr' nat  -> Expr' bool
  := fun e e0 => (Eq_p e.1 e0.1; ((e.2,e0.2,eq_refl))).

Section Expr'.

Variable (P : forall P : Set, Expr' P -> Type)
   (PI: forall n : nat, P nat (I' n))
   (PB : forall b : bool, P bool (B' b)) 
   (PAdd : forall e : Expr' nat,
           P nat e -> forall e0 : Expr' nat, P nat e0 ->
                                      P nat (Add' e e0))
   (PMul : forall e : Expr' nat,
       P nat e -> forall e0 : Expr' nat, P nat e0 -> P nat (Mul' e e0))
   (PEq : forall e : Expr' nat,
        P nat e -> forall e0 : Expr' nat, P nat e0 -> P bool (Eq' e e0)) .
  
Definition Expr'_rect :
       forall (P0: Set) (e : Expr' P0), P P0 e.
Proof.
  intros. destruct e as [x e].
  revert e. revert P0. induction x; cbn; intros P0 e.
  destruct e. exact (PI n).
  destruct e. exact (PB b).
  destruct e as ((e1,e2),e). destruct e.
  refine (PAdd (_;_) _ (_;_) _).
  apply IHx1. apply IHx2. 
  destruct e as ((e1,e2),e). destruct e.
  refine (PMul (_;_) _ (_;_) _).
  apply IHx1. apply IHx2. 
  destruct e as ((e1,e2),e). destruct e.
  refine (PEq (_;_) _ (_;_) _).
  apply IHx1. apply IHx2. 
Defined. 

Definition Expr'_rect_Add : forall e1 e2,
                Expr'_rect _ (Add' e1 e2) = PAdd _ (Expr'_rect _ e1) _ (Expr'_rect _ e2).
Proof.
  destruct e1, e2. reflexivity.
Defined. 

Definition Expr'_rect_Mul : forall e1 e2,
                Expr'_rect _ (Mul' e1 e2) = PMul _ (Expr'_rect _ e1) _ (Expr'_rect _ e2).
Proof.
  destruct e1, e2. reflexivity.
Defined. 

Definition Expr'_rect_Eq : forall e1 e2,
                Expr'_rect _ (Eq' e1 e2) = PEq _ (Expr'_rect _ e1) _ (Expr'_rect _ e2).
Proof.
  destruct e1, e2. reflexivity.
Defined. 
End Expr'. 
