(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Definitions of Vectors and functions to use them

   Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

(**
Names should be "caml name in list.ml" if exists and order of arguments
have to be the same. complain if you see mistakes ... *)

Require Import Arith_base HoTT.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

(************************************************************************)
(* We need to copy this file in order to benefit from universe polymorphism *)
(* The only change is the line below  *)
(************************************************************************)

Set Universe Polymorphism.
Unset Universe Minimization ToSet.


(**
A vector is a list of size n whose elements belong to a set A. *)

Inductive t A : nat -> Type :=
  |nil : t A O
  |cons : forall (h:A) (n:nat), t A n -> t A (S n).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.

(** An induction scheme for non-empty vectors *)

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v :=
 match v with
 |@cons _ a O v =>
   match v with
     |nil _ => bas a
     |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
   end
 |@cons _ a (S nn') v => rect a v (rectS_fix v)
 |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
 end.

(** A vector of length [0] is [nil] *)
Definition case0 {A} (P:t A O -> Type) (H:P (nil A)) v:P v :=
match v with
  |[] => H
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

(** A vector of length [ S _] is [cons] *)
Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

(** An induction scheme for 2 vectors of same length *)
Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match v1 with
  | [] => fun v2 => case0 _ bas v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
  end.

End SCHEMES.

Section BASES.
(** The first element of a non empty vector *)
Definition hd {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

(** The last element of an non empty vector *)
Definition last {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

(** Build a vector of n{^ th} [a] *)
Definition const {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

(** Remove the first element of a non empty vector *)
Definition tl {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl {A} {n} v.

Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
  fix map_fix {n} (v : t A n) : t B n := match v with
  | [] => []
  | a :: v' => (f a) :: (map_fix v')

                                       end.

(** Concatenation of two vectors *)
Fixpoint append {A}{n}{p} (v:t A n) (w:t A p):t A (add n p) :=
  match v with
  | [] => w
  | a :: v' => a :: (append v' w)
  end.

End BASES.
