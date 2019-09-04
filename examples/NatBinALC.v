Require Import HoTT Tactics UnivalentParametricity.theories.UR UnivalentParametricity.theories.StdLib.UR URTactics UnivalentParametricity.theories.FP UnivalentParametricity.theories.StdLib.FP Record UnivalentParametricity.theories.Transportable  DecidableEq CanonicalEq Conversion_table ALCTactics NatBinDefs.

Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.


(* TRANSPORT A LA CARTE *)


(* axiomatizing correspondance between nat and N functions *)
Definition compat_add : plus ≈ N.add. Admitted. 
Definition compat_mul : mult ≈ N.mul. Admitted. 
Definition compat_div : Nat.div ≈ N.div. Admitted.
Definition compat_pow : Nat.pow ≈ N.pow. Admitted.
Definition compat_sub : Nat.sub ≈ N.sub. Admitted.
Definition compat_le : Peano.le ≈ N.le. Admitted.

Hint Extern 0 (plus _ _ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (mult _ _ = _) => eapply compat_mul : typeclass_instances.
Hint Extern 0 (Nat.div _ _ = _) => eapply compat_div : typeclass_instances.
Hint Extern 0 (Nat.pow _ _ = _) => eapply compat_pow : typeclass_instances.
Hint Extern 0 (Nat.sub _ _ = _) => eapply compat_sub : typeclass_instances.
Hint Extern 0 (Peano.le _ _ ≃ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (Peano.le _ _ ⋈ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (Nat.le _ _ ≃ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (Nat.le _ _ ⋈ _) => eapply compat_le : typeclass_instances. 

Definition compat_add' : N.add ≈ plus. Admitted.
Definition compat_mul' : N.mul ≈ mult. Admitted. 
Definition compat_div' : N.div ≈ Nat.div. Admitted.
Definition compat_pow' : N.pow ≈ Nat.pow. Admitted.
Definition compat_sub' : N.sub ≈ Nat.sub. Admitted.
Definition compat_le' : N.le ≈ Peano.le. Admitted.

Hint Extern 0 (N.add _ _ = _) => eapply compat_add' : typeclass_instances.
Hint Extern 0 (N.mul _ _ = _) => eapply compat_mul' : typeclass_instances.
Hint Extern 0 (N.div _ _ = _) => eapply compat_div' : typeclass_instances.
Hint Extern 0 (N.pow _ _ = _) => eapply compat_pow' : typeclass_instances.
Hint Extern 0 (N.sub _ _ = _) => eapply compat_sub' : typeclass_instances.
Hint Extern 0 (N.le _ _ ≃ _) => eapply compat_le' : typeclass_instances.
Hint Extern 0 (N.le _ _ ⋈ _) => eapply compat_le' : typeclass_instances.

Arguments N.mul : simpl never.
Arguments N.pow : simpl never.
Arguments N.sub : simpl never.
Arguments N.add : simpl never.
Arguments mult  : simpl never.
Arguments Nat.pow : simpl never.
Arguments Nat.sub  : simpl never.
Arguments Nat.div : simpl never.



Lemma nat_distrib : forall (c a b: nat), c * (a + b) = c * a + c * b.
Proof.
  induction c; intros; cbn.
  - reflexivity.
  - apply can_eq. tc.
    unfold mult; cbn. rewrite IHc. repeat rewrite <- plus_assoc.
    rewrite (plus_assoc b). rewrite (plus_comm b).
    repeat rewrite <- plus_assoc. reflexivity.
Defined.

Lemma nat_distrib' : forall (c a b: nat), (a + b) * c = a * c + b * c.
Proof.
  intros. rewrite mult_comm. rewrite nat_distrib.
  rewrite mult_comm. rewrite (mult_comm c b). reflexivity. 
Defined.


(* we can also convert functions from one setting to another *)

Definition cube := fun n => n * n * n.  

(* not that a direct lifting does not using the conversion table *)

Fail Check eq_refl : (↑ cube : N -> N) = (fun x:N => (x * x * x)%N).

Check eq_refl : (↑ cube : N -> N) = (fun x:N => ↑ (cube (↑ x))).


(* the convert tactic uses the conversion table *)

Definition N_cube_def := ltac: (convert cube : (N -> N)).

Check (N_cube_def :{opt : N -> N & cube ≈ opt}). 

Definition N_cube := N_cube_def.1.

Check eq_refl : N_cube = (fun x => (x * x * x)%N).

(* add cube and N_cube in the conversion table *)

Hint Extern 0 (cube _ = _) => eapply N_cube_def.2 : typeclass_instances.

Arguments cube : simpl never.



(* we can lift properties up to the conversion table *)

Lemma cube_prop : forall n, cube (3 * n) = 27 * cube n.
  intro n. unfold cube, mult; cbn; fold mult.  
  repeat rewrite plus_0_r. repeat rewrite nat_distrib.
  repeat rewrite nat_distrib'. repeat rewrite plus_assoc. reflexivity. 
Qed. 

Lemma N_cube_prop : forall n, (N_cube (3 * n) = 27 * N_cube n)%N.
  exact (↑ cube_prop). 
Qed.

Lemma nat_comm : forall n m, n + m = m + n.
  intros. rewrite plus_comm. reflexivity.
Defined. 

Lemma bin_comm : forall n m : N, (n + m = m + n)%N.
  exact (↑ nat_comm).
Defined.

Lemma pow_prop : forall n, Nat.pow 3 (n + 1)  = 3 * Nat.pow 3 n.
  intro n; rewrite nat_comm; reflexivity. 
Qed.
  
Lemma N_pow_prop : forall n, (N.pow 3 (n + 1) = 3 * N.pow 3 n)%N.
  exact (↑ pow_prop). 
Qed.

(* Test with polynomials *)

Definition poly := fun n => 12 * n + 51 * (Nat.pow n 4) - (Nat.pow n 5).

Arguments poly : simpl never.

Fail Eval compute in poly 50.

Hint Extern 0 => progress (unfold ge) : typeclass_instances.

Goal poly 50 >= 1000.
  unfold poly. replace_goal; now compute. 
Defined.

(* Test for sequences *)

Definition g x := fun (n:nat) X => Nat.pow X x.

Hint Extern 0 => progress (unfold g) : typeclass_instances. 

Section sequence.
  
Variable acc : Datatypes.nat.

Fixpoint test_sequence n :=
  match n with
    0 => acc
  | 1 => 2 * acc
  | 2 => 3 * acc
  | Datatypes.S n => g acc (↑n) (test_sequence n)
    (* Nat.pow (f n) acc would be better ... *)
  end.

End sequence. 

Goal test_sequence 2 5 >= 1000.
  Fail compute.
Abort. 

(* Definition test_sequence_conv := ltac: (convert test_sequence : (N -> nat -> N)). *)

Goal test_sequence 2 5 >= 1000.
  replace_goal. now compute.
Defined.



(* we can even convert dependent functions *)

Notation "n <= m" := (Nat.le n m) : nat_scope.

Definition lt (n m : nat) := (S n <= m)%nat. 
Notation "n < m" := (lt n m) : nat_scope.
Hint Extern 0 => progress (unfold lt) :  typeclass_instances.

Hint Extern 0 => progress (unfold projT1) :  typeclass_instances.

(* the original definition of N.lt is using compare and is more complicated to deal with *)

Definition lt_N (n m : N) := (N.succ n <= m)%N. 
Notation "n < m" := (lt_N n m) : N_scope.
Hint Extern 0 => progress (unfold lt_N) :  typeclass_instances.

Instance Decidable_leq_N (n m:N) : DecidableEq (n <= m)%N.
apply (DecidableEq_equiv (Peano.le (↑n) (↑m)) (n <= m)%N); tc.
Defined.



(** OLD: SEE what to recover 

Definition lt (n m : nat) := (S n <= m)%nat. 
Notation "n < m" := (lt n m) : nat_scope.
Hint Extern 0 => progress (unfold lt) :  typeclass_instances.

Definition divide n (m : {m : nat & 0 < m }) : nat := n / m.1.

Hint Extern 0 => progress (unfold projT1) :  typeclass_instances.

(* the original definition of N.lt is using compare and is more compicated to deal with *)

Definition lt_N (n m : N) := (N.succ n <= m)%N. 
Notation "n < m" := (lt_N n m) : N_scope.
Hint Extern 0 => progress (unfold lt_N) :  typeclass_instances.

Instance Decidable_leq_N n m : DecidableEq (n <= m)%N.
apply (DecidableEq_equiv (Peano.le (↑n) (↑m)) (n <= m)%N); tc. 
Defined.

Definition N_divide_conv :=
  ltac: (convert divide : (forall (n:N) (m : {m : N & (0 < m)%N}), N)).
Arguments divide : simpl never.
Hint Extern 0 => eapply N_divide_conv.2 : typeclass_instances.

Definition N_divide := N_divide_conv.1.

(* N_divide is really the division on N *)
Check eq_refl : N_divide = (fun x y => (x / y.1)%N).

(* more dependent version of divide (on Nat)*)

Definition divide_dep_p n (m : {m : nat & 0 < m }) : (divide n m <= n)%nat.
  destruct m as [m Hm]. destruct m.
  - inversion Hm.
  - apply Nat.div_le_upper_bound.
    + apply Nat.neq_succ_0.
    + rewrite <- Nat.mul_1_l at 1.
      apply Nat.mul_le_mono_r. apply le_n_S. apply Nat.le_0_l.
Qed.

Definition divide_dep n (m : {m : nat & 0 < m }) : {res: nat & (res <= n)%nat} :=
  (divide n m ; divide_dep_p n m).

(* divide_dep_p is a proof with no computational meaning, so we want to lift it globally *)

Hint Extern 0 (divide_dep_p _ _ ≈ ?g _ _) => direct_lifting divide_dep_p g : typeclass_instances.

(* Approach 1: start from divide, N_divide and divide_dep, convert first proj, lift second proj... *)

Definition N_divide_dep_p_conv := ltac: (convert divide_dep_p : (forall (n:N) (m : {m : N & (0 < m)%N}), (N_divide n m <= n)%N)).

Definition N_divide_dep_p := N_divide_dep_p_conv.1.

(* ... and put the pieces together *)
Definition N_divide_dep_comp : forall (n:N) (m : {m : N & (0 < m)%N}),
    {res:N & (res <= n)%N} :=
  fun n m => (N_divide n m; N_divide_dep_p n m).

Definition N_two : {m : N & (0 < m)%N}.
  apply (existT _) with (x:=N.succ (N.succ 0)). unfold lt_N.
  apply -> N.succ_le_mono. apply N.le_succ_diag_r.
Defined.

Eval lazy in (N_divide_dep_comp 10%N N_two).1.

(* Approach 2: more automatic *)
(* ... it's direct! *)

Definition N_divide_dep_auto_conv :=
  ltac: (convert divide_dep : (forall (n:N) (m : {m : N & (0 < m)%N}), {res:N & (res <= n)%N})). 

Definition N_divide_dep_auto := N_divide_dep_auto_conv.1.

Eval lazy in (N_divide_dep_auto 10%N N_two).1.

(* the two versions we derive are indeed equal *)

Goal N_divide_dep_comp = N_divide_dep_auto.
  reflexivity.
Defined. 


(* Now, we can exploit the new divide - N_divide correspondance 
to efficiently convert nat functions that use divide, such as avg below *)

Definition two_zero : 0 < 2.
  apply -> Nat.succ_le_mono. apply Nat.le_succ_diag_r.
Qed.

Definition two : {n:nat & 0 < n} := (2 ; two_zero).

Definition avg (x y: nat) := divide (x + y) two.

(* first, make sure that TC resolution exploits the correspondance *)

Definition N_two_lift := ltac: (convert two : {n:N & (0 < n)%N}).

Eval compute in N_two_lift.1.

(* here also, feed the TC resolution *)
Hint Extern 0  => eapply N_two_lift.2 : typeclass_instances.

(* instruct resolution to dive into avg if helpful *)
Hint Extern 0 => progress (unfold avg) :  typeclass_instances.

(* now convert  *)

Definition N_avg_conv := ltac: (convert avg : (N -> N -> N)).

Definition N_avg := N_avg_conv.1.

(* it works... *)
Eval lazy in N_avg 10%N 30%N.

(* and is needed the same as the hand-written N-based version *)
Check eq_refl : N_avg = (fun x y => N_divide (x + y) N_two).


**)
