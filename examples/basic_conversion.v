Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable Conversion_table.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

(* we can also convert functions from one setting to another *)

Definition cube : nat -> nat := fun n => n * n * n.  

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
  unfold cube. intro n. unfold mult.
  cbn. repeat rewrite plus_0_r. repeat rewrite nat_distrib.
  repeat rewrite nat_distrib'. repeat rewrite plus_assoc.
  reflexivity. 
Qed. 

Lemma N_cube_prop : forall n, (N_cube (3 * n) = 27 * N_cube n)%N.
  exact (↑ cube_prop). 
Qed.

(* Test with polynomials *)

Definition poly : nat -> nat := fun n => 4 * n + 12 * (Nat.pow n 4) - 11 * (Nat.pow n 4).
Arguments poly : simpl never.

Fail Eval compute in poly 50.

(* Set Printing Universes.  *)

Definition poly_conv := ltac: (convert poly : (N -> N)).

Hint Extern 0 (poly _ = _) => eapply poly_conv.2 : typeclass_instances.

Lemma poly_50_abstract : { n : N & poly 50 = ↑ n}.
  eexists.
  eapply concat.
  - tc.
  - reflexivity.
Defined.

Eval lazy in poly_50_abstract.1.

Fail Eval lazy in (↑ poly_50_abstract.1 : nat).

Goal poly 50 >= 1000.
  Fail compute.
  replace_goal; compute -[N.le]. inversion 1.
Defined.












(* Test for sequences *)

Definition g x := fun (n:nat) X => Nat.pow X x.

Hint Extern 0 => progress (unfold g) : typeclass_instances. 

Definition test_sequence acc := fix f (n : nat) :=
  match n with
    0 => acc
  | 1 => 2 * acc
  | 2 => 3 * acc
  | S n => g acc n (f n)
    (* Nat.pow (f n) acc would be better ... *)
  end.

Goal test_sequence 2 5 >= 1000.
  Fail compute. 
Abort. 

Definition test_sequence_conv := ltac: (convert test_sequence : (N -> nat -> N)).

Goal test_sequence 2 5 >= 1000.
  replace_goal; compute -[N.le]. inversion 1. 
Defined.

(* with eliminator instead of pattern matching *)

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
 