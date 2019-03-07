Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable Conversion_table.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.




(*****************************)

(* As mentioned in Sections 1 and 6, we can lift functions on 
   binary nats to operate on normal nats, sometimes considerably
   improving performance. *)

Definition nat_pow_ : nat -> nat -> nat := ↑ N.pow.

Print Assumptions nat_pow_.

(* (the use of [Eval compute] in the definition above is to 
   force reduction of some noise produced by the lifting.) *)

Definition nat_pow : nat -> nat -> nat := Eval compute in ↑ N.pow.

Print Assumptions nat_pow.


Definition const0 {A} : A -> nat := fun _ => 0. 

(* with the standard nat function: *)
Time Eval vm_compute in let x := Nat.pow 3 15 in const0 x.

(* with the lifted function *)
Time Eval vm_compute in let x := nat_pow 3 15 in const0 x.



Goal forall n m, nat_pow n (S m) = n * nat_pow n m.
  intros. simpl. unfold nat_pow at 1. 
Abort. 
  