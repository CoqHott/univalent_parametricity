Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.Basics.
Require Import NatBinDefs.
Require Import BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.


(*****************************)
(* A library on nats  *)

Record Lib (C : Type -> nat -> Type) :=
  { head : forall {A : Type} {n : nat}, C A (S n) -> A;
    map : forall {A B} (f:A -> B) {n}, C A n -> C B n;
    lib_prop : forall n A (B : DType) (f : A -> B) (v : C A (S n)), head (map f v) = f (head v) }.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.
Arguments lib_prop {_} _ {_ _} _ _ _.


(* the proof that Lib is a univalent type constructor requires to 
   use an equivalent representation with dependent sums *)

Definition Lib_sig C :=   {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A (B:DType) (f : A -> B) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}.

Instance issig_lib_hd_map C : Lib_sig C ≃ Lib C.
Proof.
  issig (Build_Lib C) (@head C) (@map C) (@lib_prop C).
Defined.

Instance issig_lib_hd_map_inv C : Lib C ≃ Lib_sig C :=
  Equiv_inverse _.

Hint Extern 0 => progress (unfold Lib_sig) :  typeclass_instances.



(* the proof is automatic using the univ_param_record tactic *)

Definition FP_Lib : Lib ≈ Lib.
  univ_param_record.
Defined.

Hint Extern 0 (Lib _ ≃ Lib _) => erefine (ur_type FP_Lib _ _ _).(equiv); simpl
:  typeclass_instances.



(* we now define an instance of Lib for vectors *)

Definition lib_vector_prop : forall n A (B:DType) (f : A -> B) (v : t A (S n)),
  Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  intros.
  apply (Vector.caseS (fun _ v => Vector.hd (Vector.map f v) = f (Vector.hd v))).
  intros. reflexivity.
Defined.


Definition libvec : Lib Vector.t :=
  {| head := fun A n x => @Vector.hd A n x;
     map := fun A B f n => Vector.map f;
     lib_prop := lib_vector_prop |}.

(* using the equivalence between vectors and sized lists
   we can automatically infer the Lib structure on sized lists. 
*)

Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑ libvec.

Notation vect_to_list := (vector_to_list _ _ (Equiv_id _) _ _ _).
Notation list_to_vect := (list_to_vector _ _ (Equiv_id _) _ _ _).

Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((UR.cons x (UR.cons y .. (UR.cons z UR.nil) ..)) ;eq_refl).


(* the lib_prop theorem has been lifted as expected. *)

Check lib_list.(lib_prop).

(* and can be effectively used *)

Time Eval lazy in (lib_list.(lib_prop) Dnat S [[S O; S (S O)]]).

(* the induced lib_list.(map) function behaves as map on sized lists. *)

Time Eval lazy in lib_list.(map) Datatypes.S [[1;2;3;4;5;6;7;8]].




Definition libvec_
  : {hd : forall {A : Type} {n : nat}, Vector.t A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  Vector.t A n -> Vector.t B n &
                  forall n A (B:DType) (f : A -> B) (v : Vector.t A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}
  :=
  ( fun A n x => @Vector.hd A n x;
     ( fun A B f n => Vector.map f;
                        lib_vector_prop)).

Definition sizedList A n := {l: list A & length l = n}.

Opaque vector_to_list.

Definition foo : ({hd : forall (A : Type) (n : nat), t A (S n) -> A &
                {map : forall A B : Type, (A -> B) -> forall n : nat, t A n -> t B n
                &
                forall (n : nat) (A : Type) (B : DType) (f : A -> B) (v : t A (S n)),
                hd B n (map A B f (S n) v) = f (hd A n v) : Type}}
                ≃ {hd : forall (A : Type) (n : nat), sizedList A (S n) -> A &
                  {map
                  : forall A B : Type,
                    (A -> B) -> forall n : nat, sizedList A n -> sizedList B n &
                  forall (n : nat) (A : Type) (B : DType) 
                    (f : A -> B) (v : sizedList A (S n)),
                    hd B n (map A B f (S n) v) = f (hd A n v) : Type}}).
  tc. Defined. 

Hint Extern 0 => apply foo :  typeclass_instances.


Definition liblist : {hd :forall {A : Type} {n : nat}, sizedList A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  sizedList A n -> sizedList B n &
                   forall n A (B:DType) (f : A -> B) (v : sizedList A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}
  := ↑ libvec_.
  

(* Some more tests using the append function *)

Definition app {A} : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | UR.nil => m
   | a :: l1 => a :: app l1 m
  end.

Lemma app_length {A} : forall l l' : list A, length (app l l') = length l + length l'.
Proof.
  induction l; simpl; intros. reflexivity. apply ap. auto.
Defined.

Definition app_list {A:Type} {n n'} `{A ⋈ A} :
  {l: list A & length l = n} -> {l: list A & length l = n'}
  -> {l: list A & length l = n + n'} := ↑ Vector.append.

Definition app_list' {A:Type} {n n'} `{A ⋈ A} :
  {l: list A & length l = n} -> {l: list A & length l = n'}
  -> {l: list A & length l = n + n'}.
   intros l l'. exists (app l.1 l'.1). eapply concat. apply app_length. apply ap2; [exact l.2 | exact l'.2].
Defined.

Eval compute in (app_list [[1;2]] [[1;2]]).

Eval compute in (app_list' [[1;2]] [[1;2]]).

Eval compute in (lib_list.(map) Datatypes.S (app_list [[1;2]] [[5;6]])).

Definition neg : bool -> bool := fun b => match b with
                                          | true => false
                                          | false => true
                                                       end. 

Eval compute in (lib_list.(map) neg (app_list [[true;false]] [[true;false]])).
