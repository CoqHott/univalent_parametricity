(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)

Require Import HoTT CanonicalEq.
Require Import UnivalentParametricity.theories.Transportable.
Require Import URTactics.

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity. 
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

#[universes(collapse_sort_variables=no)]
Definition iff P Q : Type := (prod (P -> Q) (Q -> P)).

Notation "P ↔ Q" := (iff P Q) (at level 50).

(* basic class for parametric relations *)

Variant parametricity_kind : Set := 
  | plain 
  | univalent.

#[universes(collapse_sort_variables=no)]
Class PR (k : parametricity_kind) A B : Type := {
  pr : A -> B -> Type 
}.

(* #[universes(collapse_sort_variables=no)]
Class UR A B : Type := {
  ur : A -> B -> Type 
}. *)

Arguments pr k {_ _ _} a b.

Notation "x ≈[ k ] y" := (pr k x y) (at level 20).

Notation "x ≈p y" := (x ≈[plain] y) (at level 20).

Notation "x ≈u y" := (x ≈[univalent] y) (at level 20).

Instance PR_Type_plain@{s;i j} : PR@{Type Type Type Type | j j j} plain Type@{i} Type@{i} :=
  Build_PR@{Type Type Type Type | j j j} _ _ _ (PR@{Type Type Type s; i i i} plain).

#[universes(collapse_sort_variables=no)]
Class UR_Coh A B (e : A ≃ B) (H: PR@{Type _ _ SProp | _ _ _} plain A B) : Type := {
  ur_coh : forall (a a':A), (a = a') ↔ (a ≈p ↑ a')}.

Inductive UR_Type A B :=
  { 
    Ur :: PR plain A B;
    equiv : A ≃ B;
    Ur_Coh :: UR_Coh A B equiv Ur
  }.

Ltac shelve_non_PR :=
  lazymatch goal with
  | [ |- PR _ _ _ ] => idtac
  | [ |- UR_Type _ _ ] => idtac
  | [ |- pr _ _ _ ] => idtac
  | [ |- _ ] => shelve
  end.

Instance PR_Type_univ@{i j} : PR@{Type Type Type Type | j j j} univalent Type@{i} Type@{i} :=
  Build_PR@{Type Type Type Type | j j j} _ _ _ UR_Type@{i i i i i i}.

Instance PR_Type@{s;i j} k : PR@{Type Type Type Type | j j j} k Type@{i} Type@{i} :=
  match k with 
  | plain => PR_Type_plain@{s; i j}
  | univalent => PR_Type_univ@{i j}
  end.  

Arguments Ur {_ _} _.
Arguments equiv {_ _} _.
Arguments Ur_Coh {_ _} _.
Arguments ur_coh {_ _ _ _ _} _ _.

#[universes(collapse_sort_variables=no)]
Definition PR_Type_plain_univ {A B : Type} (H: A ≈u B) : PR plain A B := Ur H. 

#[universes(collapse_sort_variables=no)]
Definition PR_Type_univ_univ {A B : Type} (H: A ≈u B) : PR univalent A B :=
  {|pr := @pr plain _ _ (Ur H) |}.

#[universes(collapse_sort_variables=no)]
Definition PR_Type_gen k (A B:Type) (H:@pr _ _ _ (PR_Type k) A B) : PR k A B :=
  match k return pr k A B -> PR k A B with 
  | plain => fun H => H
  | univalent => fun H => PR_Type_univ_univ H
  end H.

Ltac head_is_var term :=
  lazymatch term with
  | ?head _ => head_is_var head
  | _ => is_var term
  end.

Ltac check_blacklist_PR_Sort_univ_univ lhs :=
  lazymatch lhs with
  | Type => fail
  | Prop => fail
  | SProp => fail
  | forall _, _ => fail
  | _ => tryif head_is_var lhs then fail else idtac
  end.

Ltac check_blacklist_PR_Type_univ_univ lhs :=
  check_blacklist_PR_Sort_univ_univ lhs;
  lazymatch type of lhs with
  | Prop => fail
  | SProp => fail
  | _ => idtac
  end.

#[export] Hint Extern 2 (PR univalent ?lhs _) =>
  check_blacklist_PR_Type_univ_univ lhs;
  unshelve notypeclasses refine (PR_Type_univ_univ _); intros; shelve_non_PR: typeclass_instances.

#[export] Hint Extern 100 (PR univalent _ _) => 
  unshelve notypeclasses refine (PR_Type_univ_univ _); solve [eassumption]: typeclass_instances.

  #[export] Hint Extern 100 (PR plain _ _) => 
  unshelve notypeclasses refine (PR_Type_plain_univ _); solve [eassumption]: typeclass_instances.

#[export] Hint Extern 100 (PR _ _ _) => 
  unshelve notypeclasses refine (PR_Type_gen _ _ _ _); solve [eassumption]: typeclass_instances.

#[export] Hint Extern 100 (PR univalent (?P ?x) _) => 
  unshelve notypeclasses refine (PR_Type_univ_univ _);
  match goal with | H : P ≈[_] _ |- _ => eapply H end
  : typeclass_instances.

#[export] Hint Extern 100 (PR univalent _ (?P ?x)) => 
  unshelve notypeclasses refine (PR_Type_univ_univ _);
  match goal with | H : _ ≈[_] P |- _ => eapply H end
  : typeclass_instances.

#[export] Hint Extern 100 (PR _ (?P ?x) _) => 
  unshelve notypeclasses refine (PR_Type_gen _ _ _ _);
  match goal with | H : P ≈[_] _ |- _ => eapply H end
  : typeclass_instances.

#[export] Hint Extern 100 (PR _ _ (?P ?x)) => 
  unshelve notypeclasses refine (PR_Type_gen _ _ _ _);
  match goal with | H : _ ≈[_] P |- _ => eapply H end
  : typeclass_instances.

#[export] Hint Extern 100 (_ ≃ _) => unshelve notypeclasses refine (equiv _): typeclass_instances. 
#[export] Hint Extern 100 (UR_Coh _ _ _ _) => unshelve notypeclasses refine (Ur_Coh _): typeclass_instances. 

Definition PR_Prop_plain : PR plain Prop SProp := 
  {| pr := PR@{Type _ _ SProp; _ _ _} plain |}.

#[export] Hint Extern 100 (PR plain Prop _) =>
  exact PR_Prop_plain : typeclass_instances.

Record UR_Prop (P:Prop) (Q:SProp) :=
  { 
    Ur_P :: PR@{Type Prop SProp SProp | _ _ _} plain P Q;
    equiv_P: iff@{Prop SProp Prop; _ _ _ _} P Q; (* P ↔ Q *)
    pr_Coh : forall (p:P) (q:Q), p ≈p q
  }.

Arguments Ur_P {_ _} _.
Arguments equiv_P {_ _} _.
Arguments pr_Coh {_ _} _.

Definition PR_Prop_univalent : PR univalent Prop SProp := 
  {| pr := UR_Prop |}.

#[export] Hint Extern 100 (PR univalent Prop _) =>
  exact PR_Prop_univalent : typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition PR_Prop_univ_univ {A : Prop} {B : SProp} (H: A ≈u B) : PR univalent A B :=
  {| pr := @pr plain _ _ (Ur_P H) |}.

Ltac check_blacklist_PR_Prop_univ_univ lhs :=
  check_blacklist_PR_Sort_univ_univ lhs;
  lazymatch type of lhs with
  | Prop => idtac
  | Type => fail
  | SProp => fail
  | _ => idtac
  end.

#[export] Hint Extern 2 (PR univalent ?lhs _) =>
  check_blacklist_PR_Prop_univ_univ lhs;
  unshelve notypeclasses refine (PR_Prop_univ_univ _); intros; shelve_non_PR: typeclass_instances.

#[export] Hint Extern 100 (PR univalent _ _) =>
  unshelve notypeclasses refine (PR_Prop_univ_univ _); solve [eassumption]: typeclass_instances.

#[export] Hint Extern 100 (PR univalent (?P ?x) _) => 
  unshelve notypeclasses refine (PR_Prop_univ_univ _);
  match goal with | H : P ≈[_] _ |- _ => eapply H end
  : typeclass_instances.

#[export] Hint Extern 100 (PR univalent _ (?P ?x)) => 
  unshelve notypeclasses refine (PR_Prop_univ_univ _);
  match goal with | H : _ ≈[_] ?P |- _ => eapply H end
  : typeclass_instances.

(* some facilities to create an instance of UR_Type *)

#[universes(collapse_sort_variables=no)]
Definition UR_gen A : PR plain A A := {| pr := (path A) |}.

#[universes(collapse_sort_variables=no)]
Definition PR_inverse k {A B : Type} (ur: PR k A B) : PR k B A := 
  {| pr := fun b a => pr k a b |}.

(* This is the Black Box Property *)

#[universes(collapse_sort_variables=no)]
Definition ur_refl {A B: Type} (e : A ≈u B) :
  forall a : A, a ≈u ↑ a.
Proof.
  destruct (Ur_Coh e) as [ur_coh]. 
  exact (fun a => fst (ur_coh a a) idpath).
Defined.  

#[export] Hint Extern 100 (_ ≈[ _ ] _) => unshelve notypeclasses refine  (ur_refl _ _): typeclass_instances.

(* The definition of Ur_coh given in the paper is equivalent to *)
(* the definition given here, but technically, this one is more convenient to use *)

Definition alt_ur_coh {A B:Type} (H:A ≈u B) 
  (einv := Equiv_inverse (equiv H))
  :
  forall (a:A) (b:B), (a = ↑ b) ↔ (a ≈p b).
Proof.
  intros a b. cbn. 
  refine (transport_eq_gen (fun X => (a = univalent_transport b) ↔ (a ≈p X))
                       (e_sect _ b) _). 
  unshelve refine (ur_coh _ _). 
Defined.

Definition alt_ur_coh_inv {A B:Type}  (e:A ≃ B) (H:A ≈p B) (einv := Equiv_inverse e)
           (HCoh : forall (a:A) (b:B), (a = ↑ b) ↔ (a ≈p b)):
  UR_Coh A B e H.
Proof.
  refine (Build_UR_Coh _ _ _ _ _). intros a a'.
  refine (transport_eq_gen (fun X => (a = X) ↔ (a ≈p univalent_transport a'))
                       (e_sect _ a') _). 
  unshelve refine (HCoh _ _). 
Defined.

(* Definition of univalent relation for basic type constructors *)

(*! Forall !*)

#[export] Hint Extern 0 (?x ≈[ _ ] ?y) => eassumption : typeclass_instances.

#[universes(collapse_sort_variables=no)]
Definition URForall_Type k A A' {HA : PR k A A'} :
   PR k (A -> Type) (A' -> Type)
  :=
    {| pr := fun P Q => forall x y (H:@pr k _ _ HA x y), pr k (P x) (Q y) |}.

#[universes(collapse_sort_variables=no)]
Definition URForall k A A' (B : A -> Type) (B' : A' -> Type) {HA : PR k A A'} 
           {HB: forall x y (H: x ≈[ k ] y), PR k (B x) (B' y)} : PR k (forall x, B x) (forall y, B' y)
  :=
  {| pr := fun f g => forall x y (H:x ≈[ k ] y), f x ≈[ k ] g y |}.

#[export] Hint Extern 0 (PR ?k (forall x:?A, _) _) =>
  unshelve erefine (@URForall_Type k A _ _); intros; shelve_non_PR : typeclass_instances.

#[export] Hint Extern 0 (PR ?k _ (forall x:?A, _)) =>
  unshelve erefine (@URForall_Type k A _ _); intros; shelve_non_PR : typeclass_instances.

#[export] Hint Extern 1 (PR ?k (forall x:?A, _) _) =>
  unshelve erefine (@URForall k A _ _ _ _ _); intros; shelve_non_PR : typeclass_instances.

#[export] Hint Extern 1 (PR ?k _ (forall x:?A, _)) =>
  unshelve erefine (@URForall k A _ _ _ _ _); intros; shelve_non_PR : typeclass_instances.

#[export] Hint Extern 0 =>
  match goal with H : @pr _ _ _
    (@URForall _ _ _ _ _ _ _) _ _ |- _ => cbn in H end : typeclass_instances. 

#[export] Hint Extern 0 =>
  match goal with H : @pr _ _ _
    (@URForall_Type _ _ _ _) _ _ |- _ => cbn in H end : typeclass_instances. 

Definition UR_Equiv_refl k (A B:Type) (e:A ≃ B) (e_inv := Equiv_inverse e) `{PR k A B} : PR k B B :=
  {| pr := fun b b' => ↑ b ≈[k] b' |}.

(*! UR is symmetric on types !*)

Definition UR_Type_Inverse (A B : Type) : A ≈u B -> B ≈u A.
intro e. unshelve econstructor.
- eapply PR_inverse. eapply Ur. tc. 
- apply Equiv_inverse; tc.
- apply alt_ur_coh_inv. 
  intros b a. cbn.
  destruct (alt_ur_coh e a b) as [l r].  
  split; intro.
  + eapply l. rewrite H. eapply inverse, e_sect.
  + eapply r in H. rewrite H. eapply inverse, e_retr.
Defined.

Definition compat_inverse k (A A' B B':Type) (pA: PR k A A') (pB: PR k B B')
           (pA' := PR_inverse k pA)
           (pB' := PR_inverse k pB) (f : A -> B) (g : A' -> B') :
  f ≈[k] g -> g ≈[k] f.
  cbn. tc. 
Defined.

Definition compat_inverse2 k {A A' B B' C C' :Type} {eA: PR k A A'} (eA' := PR_inverse k eA)
           {eB: PR k B B'} (eB' := PR_inverse k eB)
           {eC: PR k C C'} (eC' := PR_inverse k eC)
           {f : A -> B -> C} {g : A' -> B' -> C'} :
  f ≈[k] g -> g ≈[k] f.
  cbn. tc. 
Defined. 

(*! Canonical UR from a type equivalence !*)

Definition Canonical_PR k (A B:Type) `{e : A ≃ B} (einv := Equiv_inverse e) : PR k A B := 
    ({| pr := fun a b => a = ↑ b |}).

Definition Canonical_UR (A B:Type) `{A ≃ B} : A ≈u B.
Proof.
  unshelve econstructor.
  - eapply Canonical_PR. 
  - refine {| ur_coh := _ |}.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq_gen (fun X => _ ↔ (a = X)) (e_sect' H _)^ _). 
    split; intro; eauto. 
Defined.      

Definition transport_UR k A B C (e: B = C) e1 :
  transport_eq_gen (fun X : Type => PR k A X)
               e (Build_PR k A B e1) =
  Build_PR k A C (fun a x => e1 a ((eq_to_equiv _ _ e^).(e_fun) x))
  :=  match e with idpath => idpath end.

Definition transport_UR' k A B C (e: A = C) e1 :
  transport_eq (fun X : Type => PR k X B)
               e (Build_PR k A B e1) =
  Build_PR k C B (fun x b => e1 ((eq_to_equiv _ _ e^).(e_fun) x) b)
  :=  match e with idpath => idpath end.

(* some generic ways of getting UR instances *)

#[universes(collapse_sort_variables=no)]
Definition UR_Equiv (A B C:Type) `{C ≃ B} (eAB:A ≈p B) : A ≈p C :=
  {| pr := fun a b => a ≈p ↑ b |}.

#[universes(collapse_sort_variables=no)]
Definition UR_Equiv' (A B C:Type) `{C ≃ A} (eAB :A ≈p B) : C ≈p B :=
  {| pr := fun c b => ↑ c ≈p b |}.

Definition UR_Type_Equiv (A B C:Type) `{C ≃ B} `{A ≈u B} : A ≈u C.
Proof.
  unshelve econstructor.
  - eapply UR_Equiv; eauto. eapply H0.   
  - apply (equiv_compose (equiv H0)). apply Equiv_inverse. exact H.
  - econstructor.
    intros a a'. cbn. unfold univalent_transport. 
    refine (transport_eq_gen (fun X => _ ↔ (a ≈u X)) (e_retr' H _)^ _). apply ur_coh; tc.
Defined.     

Definition UR_Type_Equiv' (A B C:Type) `{C ≃ A} `{A ≈u B} : C ≈u B.
Proof.
    unshelve econstructor.
  - eapply UR_Equiv'; try eapply Ur; tc. 
  - apply (equiv_compose H (equiv H0)).
  - econstructor. intros. cbn.
    unfold univalent_transport. 
    pose proof (ucoh := ur_coh (H a) (H a')).
    split; intros.
    + exact (fst ucoh (ap H H1)).
    + eapply isequiv_ap. apply (snd ucoh); tc.
Defined. 

Definition UR_Equiv_gen (X:Type) (eX : X ≈p X) (A B: X -> Type)
  (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈p y) (H:A x ≈p A y)
  : B x ≈p B y.
Proof.
  unshelve refine (UR_Equiv _ _ _ _).
  unshelve refine (UR_Equiv' _ _ _ _).
  auto. 
Defined.

Definition UR_Type_Equiv_gen (X:Type) (eX : X ≈u X)
  (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈u y) (H:A x ≈u A y)
  (H':A x ≈u A y)
  : B x ≈u B y.
Proof.
  unshelve refine (UR_Type_Equiv _ _ _).
  unshelve refine (UR_Type_Equiv' _ _ _); tc. 
Defined.  

