Require Import UnivalentParametricity.theories.Basics.
Require Import UnivalentParametricity.theories.StdLib.Basics.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(*****************************)
(* A library parametrized by the underlying size-aware container type *)
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

#[export] Hint Extern 0 => progress (unfold Lib_sig) :  typeclass_instances.



(* the proof is automatic using the univ_param_record tactic *)

Definition FP_Lib : Lib ≈ Lib.
  univ_param_record.
Defined.

#[export] Hint Extern 0 (Lib _ ≃ Lib _) => erefine (ur_type FP_Lib _ _ _).(equiv); simpl
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
  tc. 
Defined. 
#[export] Hint Extern 0 => apply foo :  typeclass_instances.

Transparent vector_to_list.

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

(* Example of lifting structurally a fixpoint on lists to a fixpoint on vectors. *)
(* This example would need some more automation to be nicer *)

Definition fold_left (A B : Type) (f : A -> B -> A) 
  := list_rect B (fun _ => A -> A) id (fun x xs IH => fun init => IH (f init x)).

Definition Svect_fold_left_ : forall A B : Type, (A -> B -> A) -> forall l : Svector B, (fun _ : _ => A -> A) l.
  pose fold_left. unfold fold_left in p. 
  let X := fresh "X" in
  assert (X : { opt :forall A B : Type, (A -> B -> A) -> forall l : Svector B, (fun _ : _ => A -> A) l  & fold_left ≈ opt}).
  unfold fold_left. cbn.
  eexists (fun A B f v a => Svect_rect B (fun _ => A -> A) _ _ _ _).
  intros. pose (FP_List_vect_rect _ _ H0 (fun _ => x -> x) (fun _ => y -> y) (ltac:(tc))).
  cbn in u; eapply u; tc. 
  exact X.1.
Defined.

Definition Svect_fold_left := Eval compute in Svect_fold_left_. 

