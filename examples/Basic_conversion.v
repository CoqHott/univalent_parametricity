Require Import HoTT Tactics UnivalentParametricity.theories.UR UnivalentParametricity.theories.StdLib.UR URTactics UnivalentParametricity.theories.FP Record UnivalentParametricity.theories.StdLib.FP UnivalentParametricity.theories.Transportable CanonicalEq DecidableEq Nat_binnat Conversion_table.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

 

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
