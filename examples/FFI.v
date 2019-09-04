Require Import HoTT Tactics UnivalentParametricity.theories.UR UnivalentParametricity.theories.StdLib.UR URTactics UnivalentParametricity.theories.FP Record UnivalentParametricity.theories.StdLib.FP UnivalentParametricity.theories.Transportable CanonicalEq DecidableEq NatBinDefs Conversion_table ALCTactics.

Require Import BinInt BinNat Nnat. 

Require Import Utf8.
Require Export Zdiv.

Require Export DoubleType.

Definition nat := Datatypes.nat.
Definition S := Datatypes.S.

(* axiomatization of int63 and its operations *)

Require Import Int63.

Definition int63 : Type := int. 

Local Open Scope Z_scope.

(* Axiomatization of the equivalence with Z modulo 2^62*)

Require Import BinInt Zpow_facts.

Definition ZwB := { n : Z & 0 <= n < wB }.

Delimit Scope zwB_scope with ZwB.

Local Open Scope int63_scope.

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

Definition to_ZwB : int63 -> ZwB := fun x => (to_Z x; to_Z_bounded x).

Definition of_ZwB (z:ZwB) : int63 := of_Z z.1.

Lemma to_ZwB_section : forall x, of_ZwB (to_ZwB x) = x.
  unfold of_ZwB, to_ZwB; simpl. intro. rewrite of_to_Z. reflexivity.
Defined.

Definition IsIrr_le_Z (n m : Z) : IsIrr (n <= m)%Z.
Proof.
  apply IsIrr_forall. intro. exact IsIrr_False.
Defined.

Definition IsIrr_lt_Z (n m : Z) : IsIrr (n < m)%Z.
Proof.
  intros x y. unfold Z.lt in *.
  pose (is_hset (n ?= m)%Z Lt (logic_eq_is_eq x) (logic_eq_is_eq y)).
  refine (logic_eq_is_eq_inj x y e). 
Defined.

Definition isHProp_leq_Z (n m p : Z): IsIrr (n <= m < p).
Proof.
  apply IsIrr_conj. apply IsIrr_le_Z. apply IsIrr_lt_Z. 
Defined.

Definition eqZ_ZwB (x y:ZwB) : x.1 = y.1 -> x = y.
Proof.
  intro e. apply path_sigma_uncurried. unshelve eexists.
  apply isHProp_leq_Z. 
Defined.

Definition to_ZwB_retraction : forall x, to_ZwB (of_ZwB x) = x.
  unfold of_ZwB, to_ZwB; destruct x; apply eqZ_ZwB; simpl.
  rewrite of_Z_spec. now rewrite Z.mod_small.
Defined. 
  
Program Definition mod_inj : Z -> ZwB := fun z => (z mod wB; _).
Next Obligation.
  apply Z.mod_pos_bound. compute. reflexivity.
Defined. 
  
Definition IsEquiv_to_Z_ : IsEquiv to_ZwB := isequiv_adjointify _ of_ZwB to_ZwB_section to_ZwB_retraction.
  
(* now instrumenting type class resolution *)

Instance IsEquiv_to_Z : IsEquiv to_ZwB := IsEquiv_to_Z_.

Instance equiv_int_ZwB : int63 ≃ ZwB := BuildEquiv _ _ to_ZwB _.

Instance equiv_ZwB_int : ZwB ≃ int63 := Equiv_inverse _.

Instance compat_ZwB_int : ZwB ⋈ int := @Canonical_UR _ _ _.

Instance compat_int_ZwB : int ⋈ ZwB := UR_Type_Inverse _ _ compat_ZwB_int.

Definition compat_eq_int : @eq int63 ≈ @eq ZwB := ltac:(tc). 
Definition compat_eq_ZwB : @eq ZwB ≈ @eq int63 := ltac:(tc). 

Hint Extern 0 (eq ZwB _ _ ≃ _) => eapply compat_eq_ZwB : typeclass_instances.
Hint Extern 0 (eq int _ _ ≃ _) => eapply compat_eq_int : typeclass_instances.
Hint Extern 0 (eq int63 _ _ ≃ _) => eapply compat_eq_int : typeclass_instances.
Hint Extern 0 (eq ZwB _ _ ⋈ _) => eapply compat_eq_ZwB : typeclass_instances.
Hint Extern 0 (eq int _ _ ⋈ _) => eapply compat_eq_int : typeclass_instances.
Hint Extern 0 (eq int63 _ _ ⋈ _) => eapply compat_eq_int : typeclass_instances.

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

(* ompatibility with add *)

Definition compat_add : add ≈ ZwB_add.
  simpl; intros. apply eqZ_ZwB. simpl. 
  now rewrite add_spec, H, H0. 
Defined.

Definition compat_add' : ZwB_add ≈ add := compat_inverse2 compat_add. 

Hint Extern 0 (add _ _ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (ZwB_add _ _ = _) => eapply compat_add' : typeclass_instances.
Hint Extern 0 (_ = to_ZwB (add _ _)) => eapply compat_add' : typeclass_instances.

(* now property on 2wB_add can be lifted to add on int *)

Definition add_comm : forall (n m: int), n + m = m + n := ↑ ZwB_comm. 

(* multiplication on Z modulo 2^63 *)

Program Definition ZwB_mul : ZwB -> ZwB -> ZwB :=
  fun n m => ((n.1 * m.1) mod wB ; _).
Next Obligation.
  now apply Z.mod_pos_bound. 
Defined. 

Notation "n * m" := (ZwB_mul n m) : ZwB_scope.

(* compatibility with mul *)

Definition compat_mul : mul ≈ ZwB_mul.
  simpl; intros. apply eqZ_ZwB. simpl. 
  now rewrite mul_spec, H, H0. 
Defined.

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

(* compatibility with sub *)

Definition compat_sub : sub ≈ ZwB_sub.
  simpl; intros. apply eqZ_ZwB. simpl. 
  now rewrite sub_spec, H, H0. 
Defined.

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

(* compatibility with mul *)

Definition compat_lsl : lsl ≈ ZwB_lsl.
  simpl; intros. apply eqZ_ZwB. simpl. 
  now rewrite lsl_spec, H, H0. 
Defined.

Definition compat_lsl' : ZwB_lsl ≈ lsl := compat_inverse2 compat_lsl. 
  
Hint Extern 0 (lsl _ _ = _) => eapply compat_lsl : typeclass_instances.
Hint Extern 0 (ZwB_lsl _ _ = _) => eapply compat_lsl' : typeclass_instances.
Hint Extern 0 (_ = to_ZwB (lsl _ _)) => eapply compat_lsl : typeclass_instances.
Hint Extern 0 (ZwB_lsl _ _ = _) => eapply compat_lsl' : typeclass_instances.

Local Open Scope Z_scope.
Local Open Scope ZwB_scope.

Coercion mod_inj : Z >-> ZwB.


Definition ZwB_lsl_add_distr x y n : (x + y) << n = (x << n) + (y << n).
apply eqZ_ZwB. unfold ZwB_lsl. simpl. 
rewrite -> Zmult_mod_idemp_l. rewrite <-Zplus_mod.
eapply ap2; try reflexivity. change_eq_to_Logic_eq; auto with zarith. 
Defined. 

Local Open Scope int63_scope.

Definition lsl_add_distr : forall x y n, (x + y) << n = (x << n) + (y << n) :=
  ↑ ZwB_lsl_add_distr.

(* Test with polynomials *)

Local Open Scope Z_scope.

Definition poly : Z -> Z :=
  fun n =>  45 + Z.pow n 100 - Z.pow n 99 * 16550. 

Goal poly 16550 = 45.
  Time compute. reflexivity.  
Defined.

Local Open Scope ZwB_scope.

Fixpoint ZwB_pow z (n:nat) : ZwB := match n with 0%nat => 1 | Datatypes.S n => z * ZwB_pow z n end.  

Local Open Scope Z_scope.

Local Open Scope ZwB_scope.

Definition poly_ZwB : ZwB -> ZwB :=
  fun n => 45 + ZwB_pow n 100%nat - ZwB_pow n 99%nat * 16550.

Goal poly_ZwB 16550 = 45.
  Time reflexivity. 
Defined.

Fixpoint pow z (n:nat) : int := match n with 0%nat => 1 | Datatypes.S n => z * pow z n end.  

Lemma succ_spec x : Z.succ (Z.of_nat x) = Z.pos (Pos.of_succ_nat x).
  destruct x. easy. cbn. apply ap.
  now rewrite Pos.add_1_r.
Defined. 

Definition compat_pow : pow ≈ ZwB_pow.
  simpl; intros. destruct H0. apply eqZ_ZwB. induction x0.
  - easy.
  - simpl. rewrite IHx0. simpl. rewrite mul_spec. now rewrite H.
Defined.

Definition compat_pow' : ZwB_pow ≈ pow.
  simpl; intros. destruct H0. apply eqZ_ZwB. induction x0.
  - easy.
  - simpl. rewrite IHx0. simpl. rewrite mul_spec. now rewrite H.
Defined.

Hint Extern 0 (pow _ _ = _) => eapply compat_pow : typeclass_instances.
Hint Extern 0 (ZwB_pow _ _ = _) => eapply compat_pow' : typeclass_instances.
Hint Extern 0 (_ = to_ZwB (pow _ _)) => eapply compat_pow : typeclass_instances.
Hint Extern 0 (ZwB_pow _ _ = _) => eapply compat_pow' : typeclass_instances.

Opaque pow ZwB_pow. 

Goal poly_ZwB 16550 = 45.
  unfold poly_ZwB. Opaque mod_inj. replace_goal. Transparent mod_inj. Time reflexivity. 
Defined.
