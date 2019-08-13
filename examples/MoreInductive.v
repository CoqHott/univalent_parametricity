Require Import HoTT HoTT_axioms UR URTactics ADT FP Record DecidableEq FPStdLib.

Set Universe Polymorphism.
Unset Universe Minimization ToSet. 


(* moved and BROKEN *)

Instance issig_isequiv {A B : Type} (f : A -> B):
{ e_inv : B -> A & {
    e_sect : forall x : A, e_inv (f x) = x & {
    e_retr : forall y : B, f (e_inv y) = y &
    forall x : A, e_retr (f x) = ap f (e_sect x) }}} ≃ IsEquiv f.
issig (BuildIsEquiv A B f) (@e_inv A B f) (@e_sect A B f) (@e_retr A B f) (@e_adj A B f).
Defined. 

Instance issig_isequiv_inv {A B : Type} (f : A -> B):
  IsEquiv f ≃
{ e_inv : B -> A & {
    e_sect : forall x : A, e_inv (f x) = x & {
    e_retr : forall y : B, f (e_inv y) = y &
    forall x : A, e_retr (f x) = ap f (e_sect x) }}} := Equiv_inverse _.

Hint Extern 0 (UR (_ = _) (_ = _)) => unshelve notypeclasses refine (Ur (ur_type (FP_eq _ _ _ _ _ _) _ _ _)) :  typeclass_instances.

Instance foo: UR (forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y)(forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y).
    typeclasses eauto with typeclass_instances. 
Defined. 
  
Definition equivalence_hprop (P Q: Type) (eP:forall p p':P, p = p')
           (eQ: forall q q':Q, q = q')
           (f : P -> Q) (g : Q -> P)
  : P ≃ Q := BuildEquiv _ _ f (isequiv_adjointify _ g _ _).


(*! FP Equiv !*)

(* ET: repeated - should be in Record? *)
Instance issig_equiv A B : { e_fun : A -> B &  IsEquiv e_fun }
                               ≃ (A ≃ B).
  issig (BuildEquiv A B) (@e_fun A B) (@e_isequiv A B).
Defined.

Instance issig_equiv' A B :  (A ≃ B) ≃ { e_fun : A -> B &  IsEquiv e_fun } :=
  Equiv_inverse _.


(* ET: should be in FP *)
Definition FP_ap:  @ap ≈ @ap.
  intros A A' eA B B' eB f f' ef x x' ex y y' ey p p' ep. 
  cbn in *.
  induction ep. apply UR_eq_refl. 
Defined.

Hint Extern 0 (UR_eq _ _ _ _ _ _ _ _ _ _ _ ) => 
  erefine (FP_ap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) : typeclass_instances.


(* ET: should be in FP *)
Definition FP_IsEquiv : @IsEquiv ≈ @IsEquiv.
Proof.
  cbn. split ; [typeclasses eauto | ]; intros.
  unshelve refine (UR_Type_Equiv _ _ _). cbn.
  unshelve refine (UR_Type_Equiv' _ _ _).
  erefine ((ur_type (@FP_Sigma _ _ _) _ _ _)); cbn ; intros .
  typeclasses eauto with typeclass_instances.
  split.
  typeclasses eauto with typeclass_instances.
  intros. erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn; intros.
  typeclasses eauto with typeclass_instances.
  split.
  typeclasses eauto with typeclass_instances.
  intros. erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn; intros.
  typeclasses eauto with typeclass_instances.
  split.
  typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
Defined. 

Hint Extern 0 (IsEquiv _ ⋈ IsEquiv _) => refine (ur_type (FP_IsEquiv _ _ _ _ _ _) _ _ _) : typeclass_instances. 

(* ET: should be in FP *)
(* ET: BROKEN, sorry... *)
Definition FP_Equiv : @Equiv ≈ @Equiv.
Proof.
  cbn;   split ; [typeclasses eauto | ]; intros.
  unshelve refine (UR_Type_Equiv _ _ _). cbn. 
  unshelve refine (UR_Type_Equiv' _ _ _).
  erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn ; intros. tc.
  split; tc. 
Defined. 

Hint Extern 0 (UR (_ ≃ _) (_ ≃ _)) => refine (Ur (ur_type (FP_Equiv _ _ _) _ _ _)) : typeclass_instances.


(* ET: should be in UR? *)
Definition Isequiv_ur_hprop A A' B B' (H : A ⋈ A')(H' : B ⋈ B') (f:A->B) (g:A'->B')
           (e : IsEquiv f) (e' : IsEquiv g)
           (efg:f ≈ g) : e ≈ e'. 
  intros; apply ur_hprop. apply hprop_isequiv. 
Defined.   


Definition FP_Equiv_id : @Equiv_id ≈ @Equiv_id.
  intros A A' eA. unshelve eexists. cbn. auto.
  apply Isequiv_ur_hprop.
Defined. 

Definition FP_eq_to_equiv : @eq_to_equiv ≈ @eq_to_equiv.
  intros A A' eA B B' eB f f' ef. destruct ef. 
  apply FP_Equiv_id. 
Defined. 

Opaque eq_to_equiv. 

Hint Extern 0 (eq_to_equiv _ _ ≈ eq_to_equiv _ _) => refine (FP_eq_to_equiv _ _ _ _ _ _ _ _ _) : typeclass_instances.



(* ET: should be in FP? *)
Instance bar : UR (forall A B, IsEquiv (eq_to_equiv A B))
     (forall A B, IsEquiv (eq_to_equiv A B)).
unshelve erefine (@URForall _ _ _ _ _ _); cbn in *; intros .
tc. 
unshelve erefine (@URForall _ _ _ _ _ _); cbn in *; intros .
tc.
unshelve refine (Ur (ur_type (FP_IsEquiv _ _ _ _ _ _) _ _ _)).
tc. cbn; intros. refine (ur_type (FP_Equiv _ _ _) _ _ _); tc.
apply FP_eq_to_equiv.
Defined.



(* ET: should be in FP *)
Definition FP_univalence : univalence ≈ univalence.
  intros A A' eA B B' eB. 
  apply Isequiv_ur_hprop.
Defined. 

(****)

(* ET: what is this neg stuff for? *)

Definition neg : bool -> bool := fun b => match b with
                                          | true => false
                                          | false => true
                                                       end. 

Instance neg_isequiv : IsEquiv neg.
refine (isequiv_adjointify _ neg _ _).
- destruct x; reflexivity.  
- destruct x; reflexivity. 
Defined.

Definition neg_ur : bool ≈ bool.
  unshelve refine (Build_UR_Type _ _ (BuildEquiv _ _ neg neg_isequiv) _ _ _ _).
  econstructor. exact (fun b b' => b = neg b').
  unshelve econstructor. intros. destruct a, a'; apply Equiv_id.  
Defined. 


Definition absurd : neg = id -> False.
  intro e. pose (apD10 e true). inversion e0.
Defined.

(*! Establishing FP for Vector !*)

(* We go through the equivalence Vector.t A n ≃ {l : list B & length l ≈ n} *)

