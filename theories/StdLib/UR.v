(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)

Require Import HoTT CanonicalEq UnivalentParametricity.theories.Transportable URTactics
        UnivalentParametricity.theories.UR.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

(*! Sigma !*)

Definition URSigma A A' (B : A -> Type)(B' : A' -> Type) `{UR A A'}
           `{forall x y (H: x ≈ y), UR (B x) (B' y)} : UR (sigT B) (sigT B')
  :=
  {| ur := fun x y => sigT (fun (_ : x.1 ≈ y.1) => x.2 ≈ y.2) |}.

Hint Extern 0 (UR ({x:_ & _}) ({x:_ & _})) =>
  erefine (@URSigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

Definition UREq A (x x' y y' : A) (H:x=x') (H':y=y') : UR (x = y) (x' = y') :=
  {| ur := fun e e' => H^ @ e @ H' = e' |}.

Hint Extern 0 (UR (_ = _)(_ = _)) => erefine (@UREq _ _ _ _ _ _ _) : typeclass_instances.

(* eq *)

Inductive UR_eq (A_1 A_2 : Type) (A_R : A_1 -> A_2 -> Type) (x_1 : A_1) (x_2 : A_2) (x_R : A_R x_1 x_2):
   forall (y_1 : A_1) (y_2 : A_2), A_R y_1 y_2 -> x_1 = y_1 -> x_2 = y_2 -> Type :=
   UR_eq_refl : UR_eq A_1 A_2 A_R x_1 x_2 x_R x_1 x_2 x_R eq_refl eq_refl.

(* lists *)

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Infix "::" := cons (at level 60, right associativity). 

Inductive UR_list {A B} (R : A -> B -> Type) : list A -> list B -> Type :=
  UR_list_nil : UR_list R nil nil
| UR_list_cons : forall {a b l l'},
    (R a b) -> (UR_list R l l') ->
    UR_list R (a::l) (b::l').

Instance UR_list_ A B `{UR A B} : UR (list A) (list B) :=
  {| ur := UR_list ur |}.

Hint Extern 0 (UR (list ?A) (list ?B)) => unshelve notypeclasses refine (@UR_list _ _ _): typeclass_instances. 

Hint Extern 0 (UR_list ?R [] []) => exact (UR_list_nil R)  : typeclass_instances.

Hint Extern 0 (UR_list ?R (_::_) (_::_)) => unshelve refine (UR_list_cons R _ _) : typeclass_instances.

(* nat *)

Instance UR_nat : UR nat nat := UR_gen nat. 

(* bool *)

Instance UR_bool : UR bool bool := UR_gen bool. 

(* vectors *)

Require Import Vector.

Definition vector A (n:nat) := Vector.t A n.
Definition vnil {A} := Vector.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := Vector.cons A val _ v.

Inductive UR_vector {A B} (R : A -> B -> Type) : forall (n n':nat) (en : n ≈ n'),
  Vector.t A n -> Vector.t B n' -> Type :=
  UR_vector_nil : UR_vector R O O eq_refl (nil A) (nil B) 
| UR_vector_cons : forall {a b n n' v v'} (en : n ≈ n'),
    (R a b) -> (UR_vector R n n' en v v') ->
    UR_vector R (S n) (S n') (ap S en) (vcons a v) (vcons b v').



