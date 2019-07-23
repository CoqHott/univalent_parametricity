Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable Conversion_table.
Require Import BinInt BinNat Nnat. 

Require Import Utf8.
Require Export Zdiv. 

(* axiomatization of int63 and its operations *)

Axiom int63 : Type.

Delimit Scope int63_scope with int63.

Axiom zero : int63. 
Axiom one : int63. 
Axiom lsl : int63 -> int63 -> int63. 
Axiom lsr : int63 -> int63 -> int63. 
Axiom land : int63 -> int63 -> int63. 
Axiom lor : int63 -> int63 -> int63. 
Axiom add : int63 -> int63 -> int63. 
Axiom sub : int63 -> int63 -> int63. 
Axiom mul : int63 -> int63 -> int63. 
Axiom div : int63 -> int63 -> int63. 
Axiom eqb : int63 -> int63 -> bool. 
Axiom is_even : int63 -> bool. 

Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Infix ">>" := lsr (at level 30, no associativity) : int63_scope.

Infix "land" := land (at level 40, left associativity) : int63_scope.

Infix "lor" := lor (at level 40, left associativity) : int63_scope.

Notation "n + m" := (add n m) : int63_scope.

Notation "n - m" := (sub n m) : int63_scope.

Notation "n * m" := (mul n m) : int63_scope.

Notation "0" := zero : int63_scope.
Notation "1" := one : int63_scope.

Notation "n / m" := (div n m) : int63_scope.

Notation "m '==' n" := (eqb m n) (at level 3, no associativity) : int63_scope.

Local Open Scope int63_scope.

Local Open Scope Z_scope.

(* Axiomatization of the equivalence with Z modulo 2^62*)

Definition size : nat  := 63.

Definition wB := (Z.pow 2 (Z_of_nat size)).

Definition ZwB := { n : Z & n < wB }.

Delimit Scope zwB_scope with ZwB.

Fixpoint to_Z_rec (n:nat) (i:int63) :=
  match n with 
  | O => 0%Z 
  | S n => 
    (if is_even i then Zdouble else Zdouble_plus_one) (to_Z_rec n (i >> 1%int63))
  end.

Definition to_Z := to_Z_rec size.

Axiom _to_Z_modulo : forall (x:int63), to_Z x < wB.

Definition to_Z_modulo : int63 -> ZwB := fun x => (to_Z x; _to_Z_modulo x).

Notation "[| x |]" := (to_Z_modulo x)  (at level 0, x at level 99) : int63_scope.

Axiom IsEquiv_to_Z_ : IsEquiv to_Z_modulo.

(* now instrumenting type class resolution *)

Instance IsEquiv_to_Z : IsEquiv to_Z_modulo := IsEquiv_to_Z_.

Notation "|] x [|" := (e_inv to_Z_modulo x)  (at level 0, x at level 99) : int63_scope.

Instance equiv_int63_ZwB : int63 ≃ ZwB := BuildEquiv _ _ to_Z_modulo _.

Instance equiv_ZwB_int63 : ZwB ≃ int63 := Equiv_inverse _.

Instance compat_int63_ZwB : int63 ⋈ ZwB := @Canonical_UR _ _ _.

Instance compat_ZwB_int63 : ZwB ⋈ int63 := UR_Type_Inverse _ _ compat_int63_ZwB.

(* addition on Z modulo 2^63 *)

Program Definition ZwB_add : ZwB -> ZwB -> ZwB :=
  fun n m => ((n.1 + m.1) mod wB ; _).
Next Obligation.
  now apply Z.mod_pos_bound. 
Defined. 

Notation "n + m" := (ZwB_add n m) : ZwB_scope.

Local Open Scope ZwB_scope.

Definition ZwB_comm (n m: ZwB) : n + m = m + n.
Proof.
  unfold ZwB_add, ZwB_add_obligation_1. simpl.
  rewrite (Z.add_comm n.1 m.1). reflexivity. 
Defined.

(* Axiomatization of compatibility with add *)

Axiom compat_add : add ≈ ZwB_add.
Definition compat_add' : ZwB_add ≈ add := compat_inverse2 compat_add. 
  
Hint Extern 0 (add _ _ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (ZwB_add _ _ = _) => eapply compat_add' : typeclass_instances.

(* now property on 2wB_add can be lifted to add on int63 *)

Definition int63_comm : forall (n m: int63), (n + m = m + n)%int63 := ↑ ZwB_comm. 


