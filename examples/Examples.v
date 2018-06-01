Require Import HoTT Tactics UR URTactics FP Record MoreInductive Transportable.
Require Import BinInt BinNat Nnat Vector.

Set Universe Polymorphism.

Definition append_list {A:Type} {n p} {H : A ⋈ A} :
  {l : list A & length l = n} ->
  {l : list A & length l = p} ->
  {l : list A & length l = n+p}   := ↑ Vector.append.

Eval compute in ((append_list ([1;2];eq_refl) ([4;5;6];eq_refl)).1).

Definition map_list {A B} (e : A ≃ B)
           {HA : ur A A} {HB : ur B B}
           (f:A -> B) {n} :
  {l : list A & length l = n} ->
  {l : list B & length l = n}
  := ↑ (Vector.map f).

Typeclasses Transparent map_list.

Typeclasses Opaque vector_to_list list_to_vector.

Opaque vector_to_list list_to_vector.

Record Lib (C : Type -> nat -> Type) :=
  { head : forall {A : Type} {n : nat}, C A (S n) -> A;
    map : forall {A B} (f:A -> B) {n}, C A n -> C B n;
    lib_prop : forall n A (f : A -> nat) (v : C A (S n)), head (map f v) = f (head v)}.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.
Arguments lib_prop {_} _ {_ _} _ _.

Definition Lib_sig C :=   {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A (f : A -> (nat:Type)) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}.

Instance issig_lib_hd_map C : Lib_sig C ≃ Lib C.
Proof.
  issig (Build_Lib C) (@head C) (@map C) (@lib_prop C).
Defined.

Instance issig_lib_hd_map_inv C : Lib C ≃ Lib_sig C :=
  Equiv_inverse _.

Hint Extern 0 => progress (unfold Lib_sig) :  typeclass_instances.

Definition FP_Lib : Lib ≈ Lib.
 univ_param_record.
Defined.

Hint Extern 0 (Lib _ ≃ Lib _) => erefine (ur_type FP_Lib _ _ _).(equiv); simpl
:  typeclass_instances.

Definition lib_vector_prop : forall (n : nat) (A : Type) (f : A -> nat) (v : t A (S n)),
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

Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑ libvec.

Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((FP.cons x (FP.cons y .. (FP.cons z FP.nil) ..)) ;eq_refl).

Time Eval compute in lib_list.(map) S [[1;2]].

Definition app {A} : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | FP.nil => m
   | a :: l1 => a :: app l1 m
  end.

Lemma app_length {A} : forall l l' : list A, length (app l l') = length l + length l'.
Proof.
  induction l; simpl; intros. reflexivity. apply ap. auto.
Defined.

Definition app_list {A:Type} {n n'} `{A ⋈ A} :
  {l: list A & length l = n} -> {l: list A & length l = n'}
  -> {l: list A & length l = n+n'} := ↑ Vector.append.

Definition app_list' {A:Type} {n n'} `{A ⋈ A} :
  {l: list A & length l = n} -> {l: list A & length l = n'}
  -> {l: list A & length l = n+n'}.
   intros l l'. exists (app l.1 l'.1). etransitivity. apply app_length. apply ap2; [exact l.2 | exact l'.2].
Defined.

Eval compute in (app_list [[1;2]] [[1;2]]).

Eval compute in (app_list' [[1;2]] [[1;2]]).

Eval compute in (lib_list.(map) S (app_list [[1;2]] [[5;6]])).

Eval compute in (lib_list.(lib_prop) S (app_list [[1;2]] [[5;6]])).


Record Monoid A :=
  Build_Monoid {
      mon_e : A;
      mon_m : A -> A -> A;
      mon_unitL : forall x, mon_m x mon_e = x;
      mon_unitR : forall x, mon_m mon_e x = x;
      mon_assoc : forall x y z, mon_m x (mon_m y z) = mon_m (mon_m x y) z
    }.

Instance issig_monoid {A : Type} :
  { e:A & {m:A -> A -> A & {uL : forall x, m x e = x & { uR : forall x, m e x = x &
                                            forall x y z, m x (m y z) = m (m x y) z}}}}
  ≃ Monoid A.
Proof.
  issig (Build_Monoid A) (@mon_e A) (@mon_m A) (@mon_unitL A) (@mon_unitR A) (@mon_assoc A).
Defined.

Instance issig_monoid_inv {A : Type} :
  Monoid A ≃
         { e:A & {m:A -> A -> A & {uL : forall x, m x e = x & { uR : forall x, m e x = x &
                                                                               forall x y z, m x (m y z) = m (m x y) z}}}}
         := Equiv_inverse _.


Definition FP_Monoid : Monoid ≈ Monoid.
Proof.
  univ_param_record.
Defined. 

Hint Extern 0 (Monoid ≈ Monoid) => exact (ur_type FP_Monoid) : typeclass_instances. 

Hint Extern 0 (Monoid _ ≃ Monoid _) => unshelve refine (equiv (ur_type FP_Monoid _ _ _)) : typeclass_instances. 

Definition N_mon : Monoid N.
Proof.
  unshelve refine (Build_Monoid _ _ _ _ _ _).
  - exact N0.
  - exact N.add.
  - intro x. destruct x; reflexivity. 
  - intro x. destruct x; reflexivity.
  - intros. cbn. apply logic_eq_is_eq. exact (N.add_assoc x y z).  
Defined.

Definition n_mon : Monoid nat := ↑ N_mon.

Notation "a ++ b" := (n_mon.(mult) a b).

Fixpoint even (n:nat) := match n with
                             0 => true
                           | 1 => false
                           | S (S n) => even n
                           end. 

Definition nat_pow : nat -> nat -> nat := ↑ N.pow.


(* Observe the evolution of time as the exponent increases, 
   in first the standard nat version, and in the lifted N version. 
   (all Time Eval commands are commented in order to not affect
   compilation time - just uncomment and eval to test.)
*)

(* Time Eval vm_compute in let x := Nat.pow 2 26 in 0. *)
(* 26: 8.221u *)
(* 27: 28.715u *)
(* 28: 83.669u *)


(* Time Eval vm_compute in let x := nat_pow 2 26 in 0. *)
(* 26: 13.994u *)
(* 27: 24.465u *)
(* 28: 60.975u *)

(* a non-neglibible part of the cost here is the conversion of 
   the result binary number to a nat. *)

(* Consider another function that also uses pow, but does 
   not always such big numbers: *)

(* a- the N version *)
Definition diffN x y n := N.sub (N.pow x n) (N.pow y n).

(* b- the nat version *)
Definition diff x y n := (Nat.pow x n) - (Nat.pow y n).

(* c- the nat version obtained by lifting the N version *)
Definition diff' : nat -> nat -> nat -> nat := Eval compute in ↑ diffN.

(* In the following, the computed value is 0 (so converting back 
   in the lifted version costs nothing). *)

Definition const0 {A} : A -> nat := fun _ => 0. 

(* Time Eval vm_compute in let x := diff 2 2 25 in const0 x. *)
(* 8.322u *)

(* Time Eval vm_compute in let x := diff' 2 2 25 in const0 x. *)
(* 0u *)

(* In the following the computed value is still large, but not as large
   as in the first example, so the difference in favor 
   of the lifted version is quite clear *)

(* Time Eval vm_compute in let x := diff 3 2 17 in 0. *)
(* 22.591u *)

(* Time Eval vm_compute in let x := diff' 3 2 17 in 0. *)
(* 8.478u *)


(* Time Eval vm_compute in let x := nat_pow 2 26 in (const0 x). *)
(* 18.725u *)

(* Time Eval vm_compute in let x := Nat.pow 2 26 in (const0 x). *)
(* 36.493u *)

(* Time Eval vm_compute in let x := N.pow 2 26 in (const0 x). *)
(* 0.1u *)

