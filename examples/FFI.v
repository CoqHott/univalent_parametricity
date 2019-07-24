Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable Conversion_table.
Require Import BinInt BinNat Nnat. 

Require Import Utf8.
Require Export Zdiv.

Require Export DoubleType.

(* axiomatization of int63 and its operations *)

Definition size : nat  := 63.

Require Import Int63.

Definition int63 : Type := int. 

Local Open Scope Z_scope.

(* Axiomatization of the equivalence with Z modulo 2^62*)

Require Import BinInt Zpow_facts.

Definition wB := (Z.pow 2 (Z_of_nat size)).

Definition ZwB := { n : Z & 0 <= n < wB }.

Delimit Scope zwB_scope with ZwB.

Local Open Scope int63_scope.

Fixpoint to_Z_rec (n:nat) (i:int63) :=
  match n with 
  | O => 0%Z
  | S n => 
    (if is_even i then Z.double else Zdouble_plus_one) (to_Z_rec n (i >> 1))
  end.

Definition to_Z := to_Z_rec size.

Lemma to_Z_bounded : forall x, 0 <= to_Z x < wB.
Proof.
 unfold to_Z, wB;induction size;intros.
 simpl;auto with zarith.
 rewrite inj_S;simpl;assert (W:= IHn (x >> 1)).
 rewrite Zpower_Zsucc;auto with zarith.
 destruct (is_even x).
 rewrite Zdouble_mult;auto with zarith.
 rewrite Zdouble_plus_one_mult;auto with zarith.
Qed.

Definition to_Z_modulo : int63 -> ZwB := fun x => (to_Z x; to_Z_bounded x).

Notation "[| x |]" := (to_Z_modulo x)  (at level 0, x at level 99) : int63_scope.

Fixpoint of_pos_rec (n:nat) (p:positive) : int63 :=
  match n, p with 
  | O, _ => 0
  | S n, xH => 1
  | S n, xO p => (of_pos_rec n p) << 1
  | S n, xI p => (of_pos_rec n p) << 1 lor 1
  end.

Definition of_pos := of_pos_rec size.

Definition of_Z (z:ZwB) : int63 := 
  match z.1 with
  | Zpos p => of_pos p
  | Z0 => 0
  | Zneg p => (0 - (of_pos p))
  end.

Notation "|] x [|" := (of_Z x)  (at level 0, x at level 99) : int63_scope.

Axiom to_Z_section : forall x, of_Z (to_Z_modulo x) = x.
Axiom to_Z_retraction : forall x, to_Z_modulo (of_Z x) = x.

Program Definition mod_inj : Z -> ZwB := fun z => (z mod wB; _).
Next Obligation.
  apply Z.mod_pos_bound. compute. reflexivity.
Defined. 

Definition isHProp_leq_Z : forall (n m p : Z) (e e': n <= m < p), e = e'. 
(* to be done *)
Admitted. 

Definition eqZ_ZwB (x y:ZwB) : x.1 = y.1 -> x = y.
Proof.
  intro e. apply path_sigma_uncurried. unshelve eexists.
  apply isHProp_leq_Z. 
Defined. 
  
Definition IsEquiv_to_Z_ : IsEquiv to_Z_modulo := isequiv_adjointify _ of_Z to_Z_section to_Z_retraction.
  
(* now instrumenting type class resolution *)

Instance IsEquiv_to_Z : IsEquiv to_Z_modulo := IsEquiv_to_Z_.

Instance equiv_int_ZwB : int63 ≃ ZwB := BuildEquiv _ _ to_Z_modulo _.

Instance equiv_ZwB_int : ZwB ≃ int63 := Equiv_inverse _.

Instance compat_ZwB_int : ZwB ⋈ int := @Canonical_UR _ _ _.

Instance compat_int_ZwB : int ⋈ ZwB := UR_Type_Inverse _ _ compat_ZwB_int.

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
  rewrite Z.add_comm; reflexivity. 
Defined.

Local Open Scope int63_scope.

(* Axiomatization of compatibility with add *)

Axiom compat_add : add ≈ ZwB_add.
Definition compat_add' : ZwB_add ≈ add := compat_inverse2 compat_add. 

Hint Extern 0 (add _ _ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (ZwB_add _ _ = _) => eapply compat_add' : typeclass_instances.
Hint Extern 0 (_ = to_Z_modulo (add _ _)) => eapply compat_add' : typeclass_instances.

(* now property on 2wB_add can be lifted to add on int *)

Definition add_comm : forall (n m: int), n + m = m + n := ↑ ZwB_comm. 

(* multiplication on Z modulo 2^63 *)

Program Definition ZwB_mul : ZwB -> ZwB -> ZwB :=
  fun n m => ((n.1 * m.1) mod wB ; _).
Next Obligation.
  now apply Z.mod_pos_bound. 
Defined. 

Notation "n * m" := (ZwB_mul n m) : ZwB_scope.

(* Axiomatization of compatibility with mul *)

Axiom compat_mul : mul ≈ ZwB_mul.
Definition compat_mul' : ZwB_mul ≈ mul := compat_inverse2 compat_mul. 
  
Hint Extern 0 (mul _ _ = _) => eapply compat_mul : typeclass_instances.
Hint Extern 0 (ZwB_mul _ _ = _) => eapply compat_mul' : typeclass_instances.

(* substraction on Z modulo 2^63 *)

Program Definition ZwB_sub : ZwB -> ZwB -> ZwB :=
  fun n m => ((n.1 - m.1) mod wB ; _).
Next Obligation.
  now apply Z.mod_pos_bound. 
Defined. 

Notation "n - m" := (ZwB_sub n m) : ZwB_scope.

(* Axiomatization of compatibility with sub *)

Axiom compat_sub : sub ≈ ZwB_sub.
Definition compat_sub' : ZwB_sub ≈ sub := compat_inverse2 compat_sub. 
  
Hint Extern 0 (sub _ _ = _) => eapply compat_sub : typeclass_instances.
Hint Extern 0 (ZwB_sub _ _ = _) => eapply compat_sub' : typeclass_instances.

(* lsl on Z modulo 2^63 *)

Program Definition ZwB_lsl : ZwB -> ZwB -> ZwB :=
  fun n m => ((n.1 * Z.pow 2 m.1) mod wB ; _).
Next Obligation.
  now apply Z.mod_pos_bound. 
Defined. 

Notation "n << m" := (ZwB_lsl n m) : ZwB_scope.

Arguments ZwB_lsl : simpl never.

(* Axiomatization of compatibility with mul *)

Axiom compat_lsl : lsl ≈ ZwB_lsl.
Definition compat_lsl' : ZwB_lsl ≈ lsl := compat_inverse2 compat_lsl. 
  
Hint Extern 0 (lsl _ _ = _) => eapply compat_lsl : typeclass_instances.
Hint Extern 0 (ZwB_lsl _ _ = _) => eapply compat_lsl' : typeclass_instances.
Hint Extern 0 (_ = to_Z_modulo (lsl _ _)) => eapply compat_lsl : typeclass_instances.
Hint Extern 0 (ZwB_lsl _ _ = _) => eapply compat_lsl' : typeclass_instances.



(* Test with polynomials *)

Local Open Scope Z_scope.
Local Open Scope ZwB_scope.

Coercion mod_inj : Z >-> ZwB.

Definition poly : ZwB -> ZwB :=
  fun n => 12 * n + 51 * n * n * n * n - (n * n * n * n * n).

Arguments poly : simpl never.

(* Fail Eval compute in poly 50. *)

(* comparison on Z modulo 2^63 *)

Definition compat_eq_int : @eq int63 ≈ @eq ZwB := ltac:(tc). 
Definition compat_eq_ZwB : @eq ZwB ≈ @eq int63 := ltac:(tc). 

Hint Extern 0 (eq ZwB _ _ ≃ _) => eapply compat_eq_ZwB : typeclass_instances.
Hint Extern 0 (eq int _ _ ≃ _) => eapply compat_eq_int : typeclass_instances.
Hint Extern 0 (eq int63 _ _ ≃ _) => eapply compat_eq_int : typeclass_instances.
Hint Extern 0 (eq ZwB _ _ ⋈ _) => eapply compat_eq_ZwB : typeclass_instances.
Hint Extern 0 (eq int _ _ ⋈ _) => eapply compat_eq_int : typeclass_instances.
Hint Extern 0 (eq int63 _ _ ⋈ _) => eapply compat_eq_int : typeclass_instances.

Goal eq ZwB 6250600 (poly 50).
  unfold poly. replace_goal. compute. reflexivity. 
Defined.

Local Open Scope int63_scope.

Ltac change_eq_to_eq := let e := fresh "e" in
                       match goal with | |- ?X = ?Y => assert (e : Logic.eq X Y) ; [idtac | now destruct e] end.

Definition ZwB_lsr_add_distr x y n :
  ZwB_lsl (ZwB_add x y) n = ZwB_add (ZwB_lsl x n) (ZwB_lsl y n).
apply eqZ_ZwB. unfold ZwB_lsl. simpl. 
rewrite -> Zmult_mod_idemp_l. rewrite <-Zplus_mod.
eapply ap2; try reflexivity. change_eq_to_eq. 
auto with zarith. 
Defined. 
  
Definition lsr_add_distr : forall x y n, eq int63 ((x + y) << n) ((x << n) + (y << n)) :=
  ↑ ZwB_lsr_add_distr.
