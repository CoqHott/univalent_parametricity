(*
As discussed in the paper, for a GADT like Expr, univalence is required to establish FP.
*)

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
  rewrite (@e_inv _ _ _ (univalence _ _) (equiv e)). (* and use univalence *)
  apply (@ur_refl_ _ _ _ _ URType_Refl).
Defined.
