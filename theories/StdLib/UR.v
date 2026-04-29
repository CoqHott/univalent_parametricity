(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)

Require Import UnivalentParametricity.theories.Basics.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.

(*! Sigma !*)

#[universes(collapse_sort_variables=no)]
Definition PRSigma (A A':Type) (B : A -> Type)(B' : A' -> Type) `{PR plain A A'}
           `{forall x y (H: x ≈p y), PR plain (B x) (B' y)} : PR plain (sigT B) (sigT B')
  :=
  {| pr := fun x y => sigT (fun (_ : x.1 ≈ y.1) => x.2 ≈ y.2) |}.

#[export] Hint Extern 0 (PR plain ({x:_ & _}) ({x:_ & _})) =>
  erefine (@PRSigma _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition PRProd (A A' B B' : Type) `{PR plain A A'}
           `{PR plain B B'} : PR plain (A * B) (A' * B')
  :=
  {| pr := fun x y => prod (fst x ≈p fst y) (snd x ≈p snd y) |}.

#[export] Hint Extern 0 (PR plain (_ * _) (_ * _)) =>
  erefine (@PRProd _ _ _ _ _ _); cbn in *; intros : typeclass_instances.

(* eq *)

(* generalize on the right hand side *)

#[universes(collapse_sort_variables=no)]
Inductive PR_eq (A_1 A_2 : Type) (A_R : A_1 -> A_2 -> Type) (x_1 : A_1) (x_2 : A_2) (x_R : A_R x_1 x_2):
   forall (y_1 : A_1) (y_2 : A_2), A_R y_1 y_2 -> 
   eq x_1 y_1 -> x_2 = y_2 -> SProp :=
   PR_idpath : PR_eq A_1 A_2 A_R x_1 x_2 x_R x_1 x_2 x_R eq_refl idpath.

(* Definition PREq A (x x' y y' : A) (H:x=x') (H':y=y') : PR (x = y) (x' = y') :=
  {| pr := fun e e' => H^ @ e @ H' = e' |}.

#[export] Hint Extern 0 (PR (_ = _)(_ = _)) => erefine (@PREq _ _ _ _ _ _ _) : typeclass_instances. *)

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

Inductive PR_list {A B} (R : A -> B -> Type) : list A -> list B -> Type :=
  PR_list_nil : PR_list R nil nil
| PR_list_cons : forall {a b l l'},
    (R a b) -> (PR_list R l l') ->
    PR_list R (a::l) (b::l').

Instance PR_list_ (A B:Type) `{A ≈p B} : PR plain (list A) (list B) :=
  {| pr := PR_list (pr plain) |}.

#[export] Hint Extern 0 (PR plain (list ?A) (list ?B)) => unshelve notypeclasses refine (@PR_list _ _ _): typeclass_instances. 

#[export] Hint Extern 0 (PR_list ?R [] []) => exact (PR_list_nil R)  : typeclass_instances.

#[export] Hint Extern 0 (PR_list ?R (_::_) (_::_)) => unshelve refine (PR_list_cons R _ _) : typeclass_instances.

(* nat *)

Instance PR_nat : PR plain nat nat := UR_gen nat. 

(* bool *)

Instance PR_bool : PR plain bool bool := UR_gen bool. 

(* vectors *)

Require Import Vector.

Definition vector A (n:nat) := Vector.t A n.
Definition vnil {A} := Vector.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := Vector.cons A val _ v.

Inductive PR_vector {A B} (R : A -> B -> Type) : forall (n n':nat) (en : n ≈ n'),
  Vector.t A n -> Vector.t B n' -> Type :=
  PR_vector_nil : PR_vector R O O idpath (nil A) (nil B) 
| PR_vector_cons : forall {a b n n' v v'} (en : n ≈ n'),
    (R a b) -> (PR_vector R n n' en v v') ->
    PR_vector R (S n) (S n') (ap S en) (vcons a v) (vcons b v').



