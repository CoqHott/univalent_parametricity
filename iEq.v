Require Import HoTT Tactics UR URTactics FP Record MoreInductive Transportable.
Require Import BinInt BinNat Nnat Vector.



Definition iEq A x y := forall (P : A -> Type), P x -> P y.

Definition iEq_refl A x : iEq A x x := fun P X => X.
  
Definition fun_forall_iEq (A A' : Type) (eA : A ⋈ A')
           (x : A) (y : A') (H : x ≈ y) (x0 : A) (y0 : A')
           (H0 : x0 ≈ y0) :
    (forall P : A -> Type, P x -> P x0) -> (forall P : A' -> Type, P y -> P y0).
Proof.
  intros.
  pose (alt_ur_coh' eA _ _ H).
  pose (alt_ur_coh' eA _ _ H0).
  exact (e0 # (X (fun x => P (↑ x)) (e^ # X0))).
Defined.


Axiom cheat : forall X, X. 

Definition Equiv_forall_iEq (A A' : Type) (eA : A ⋈ A')
           (x : A) (y : A') (H : x ≈ y) (x0 : A) (y0 : A')
           (H0 : x0 ≈ y0) :
    (forall P : A -> Type, P x -> P x0) ≃ (forall P : A' -> Type, P y -> P y0).
Proof.
  unshelve refine (BuildEquiv _ _ (fun_forall_iEq _ _ _ _ _ _ _ _ _) _); auto. 
  unshelve eapply isequiv_adjointify. 
  unshelve eapply (fun_forall_iEq _ _ _ _ _ _ _ _ _); auto. 
  apply UR_Type_Inverse; auto. exact H. exact H0. 
  - intros. apply funext. intro P. apply funext. intro X.
    unfold fun_forall_iEq. cbn.
    apply cheat. 
  - intros. apply funext. intro P. apply funext. intro X.
    unfold fun_forall_iEq. cbn. apply cheat. 
Defined.

Definition FP_forall_iEq :
  (fun A (x y : A) => forall P : A -> Type , P x -> P y) ≈
  (fun A (x y : A) => forall P : A -> Type , P x -> P y).
Proof.
  cbn. intros A A' eA. split.
  apply Transportable_default.
  intros. 
  unshelve eapply (Build_UR_Type _ _ ( Equiv_forall_iEq _ _ _ _ _ _ _ _ _)); auto. 
  apply cheat. 
  apply Canonical_eq_gen. 
  apply Canonical_eq_gen. 
Defined. 

Definition foo_iEq : forall n:N, iEq _ n n :=
  fun n => iEq_refl _ _.

Hint Extern 0 => progress (unfold iEq) :  typeclass_instances.

Eval compute in foo_iEq 0.

(* If you comment this line, then bar_iEq below does not compute *)
(* because the canonical instance of FP_Forall does not exploit *)
(* the fact that the type family P is always applied *)

Hint Extern 0 (UR_Type (forall P:_ , P _ -> P _) (forall P:_, P _ -> P _)) =>
erefine (ur_type (FP_forall_iEq N nat _ _ _ _) _ _ _); cbn in *; intros : typeclass_instances.

Definition bar_iEq := ↑ foo_iEq : forall n,  iEq _ n n.

Eval compute in bar_iEq 0.