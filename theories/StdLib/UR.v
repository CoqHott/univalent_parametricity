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
Definition PRSigma k (A A':Type) (B : A -> Type)(B' : A' -> Type) `{PR k A A'}
           {HB : forall x y (H: x ≈[k] y), PR k (B x) (B' y)} : PR k (sigT B) (sigT B')
  :=
  {| pr := fun x y => sigT (fun (p : x.1 ≈[k] y.1) => @pr k _ _ (HB x.1 y.1 p) x.2 y.2) |}.

#[export] Hint Extern 0 (PR ?k (@sigT _  _) (@sigT _ _)) =>
  unshelve erefine (@PRSigma _ _ _ _ _ _ _); intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition PRProd k (A A' B B' : Type) `{PR k A A'}
           `{PR k B B'} : PR k (A * B) (A' * B')
  :=
  {| pr := fun x y => prod (fst x ≈[k] fst y) (snd x ≈[k] snd y) |}.

#[export] Hint Extern 0 (PR _ (prod _ _) (prod _ _)) =>
  unshelve erefine (@PRProd _ _ _ _ _ _ _); intros; shelve_non_PR  : typeclass_instances ur_typeclass_instances.

(* eq *)

(* generalize on the right hand side *)

#[universes(collapse_sort_variables=no)]
Inductive PR_eq (A_1 A_2 : Type) (A_R : A_1 -> A_2 -> Type) (x_1 : A_1) (x_2 : A_2) (x_R : A_R x_1 x_2):
   forall (y_1 : A_1) (y_2 : A_2), A_R y_1 y_2 -> 
   eq x_1 y_1 -> x_2 = y_2 -> SProp :=
   PR_idpath : PR_eq A_1 A_2 A_R x_1 x_2 x_R x_1 x_2 x_R eq_refl idpath.

#[universes(collapse_sort_variables=no)]
Instance PREq k (A_1 A_2 : Type) (A_R : A_1 ≈[k] A_2) (x_1 : A_1) (x_2 : A_2) (x_R : x_1 ≈[k] x_2)
   (y_1 : A_1) (y_2 : A_2) (y_R : y_1 ≈[k] y_2) : PR k (eq x_1 y_1) (x_2 = y_2)  :=
  {| pr := fun e e' => PR_eq _ _ _ _ _ x_R _ _ y_R e e' |}.

#[universes(collapse_sort_variables=no)]
Instance PREq_Prop k (A_1 : Prop) (A_2 : Type) (A_R : A_1 ≈[k] A_2) (x_1 : A_1) (x_2 : A_2) (x_R : x_1 ≈[k] x_2)
   (y_1 : A_1) (y_2 : A_2) (y_R : y_1 ≈[k] y_2) : PR k (eq x_1 y_1) (x_2 = y_2)  :=
  {| pr := fun e e' => PR_eq _ _ _ _ _ x_R _ _ y_R e e' |}.
  
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

#[universes(collapse_sort_variables=no)]
Inductive PR_list {A B} (R : A -> B -> Type) : list A -> list B -> SProp :=
  PR_list_nil : PR_list R nil nil
| PR_list_cons : forall {a b l l'},
    (R a b) -> (PR_list R l l') ->
    PR_list R (a::l) (b::l').

#[universes(collapse_sort_variables=no)]
Instance PR_list_ (A B:Type) `{A ≈p B} : PR plain (list A) (list B) :=
  {| pr := PR_list (pr plain) |}.

#[export] Hint Extern 0 (PR plain (list ?A) (list ?B)) => unshelve notypeclasses refine (@PR_list_ _ _ _); intros; shelve_non_PR : typeclass_instances ur_typeclass_instances. 

#[export] Hint Extern 0 (PR_list ?R [] []) => exact (PR_list_nil R)  : typeclass_instances ur_typeclass_instances.

#[export] Hint Extern 0 (PR_list ?R (_::_) (_::_)) => unshelve refine (PR_list_cons R _ _); intros; shelve_non_PR : typeclass_instances ur_typeclass_instances.

(* nat *)

Inductive natϵ : nat -> nat -> SProp :=
| Oϵ : natϵ O O 
| Sϵ : forall {n m}, natϵ n m -> natϵ (S n) (S m).

Instance PR_nat : PR plain nat nat := {pr := natϵ}. 

(* bool *)

Inductive boolϵ : bool -> bool -> SProp :=
| trueϵ : boolϵ true true 
| falseϵ : boolϵ false false.

Instance PR_bool : PR plain bool bool := {pr := boolϵ}.

(* empty *)

Inductive Emptyϵ : Empty -> Empty -> SProp :=.

Instance PR_empty : PR plain (Empty:Type) (Empty:Type) := {pr := Emptyϵ}.

(* vectors *)

Require Import Vector.

Definition vector A (n:nat) := Vector.t A n.
Definition vnil {A} := Vector.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := Vector.cons A val _ v.

Inductive PR_vector {A B} (R : A -> B -> Type) : forall (n n':nat) (en : n ≈p n'),
  Vector.t A n -> Vector.t B n' -> Type :=
  PR_vector_nil : PR_vector R O O Oϵ (nil A) (nil B) 
| PR_vector_cons : forall {a b n n' v v'} (en : n ≈p n'),
    (R a b) -> (PR_vector R n n' en v v') ->
    PR_vector R (S n) (S n') (Sϵ en) (vcons a v) (vcons b v').



