Require Import HoTT Tactics UnivalentParametricity.theories.UR UnivalentParametricity.theories.StdLib.UR URTactics UnivalentParametricity.theories.FP Record UnivalentParametricity.theories.StdLib.FP UnivalentParametricity.theories.Transportable UnivalentParametricity.theories.StdLib.Transportable CanonicalEq DecidableEq Nat_binnat Conversion_table.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

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



(* we can lift properties up to the correspondance table *)

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

 

(* with eliminator instead of pattern matching *)

(*
Definition test_sequence_ : nat -> nat -> nat := fun acc =>
  nat_rect (fun _ => nat) acc
           (fun n res => nat_rect (fun _ => nat) (2 * acc)
                                  (fun m res' =>
                                     nat_rect (fun _ => nat) (3 * acc)
                                              (fun _ res'' => Nat.pow res acc) m) n).

Definition test_sequence__conv := ltac: (convert test_sequence_ : (N -> nat -> N)).

Hint Extern 0 (test_sequence_ _ _ = _ )  => eapply test_sequence__conv.2 : typeclass_instances.
Arguments test_sequence_ : simpl never.

Goal test_sequence_ 2 5 >= 1000.
  replace_goal; inversion 1. 
Defined. 

*)