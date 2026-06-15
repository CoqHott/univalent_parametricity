(************************************************************************)
(* This file proves the fundamental property for the main constructors of CIC *)
(************************************************************************)
Set Polymorphic Inductive Cumulativity.
Set Universe Polymorphism.
Require Import HoTT CanonicalEq URTactics.
Require Export UnivalentParametricity.theories.UR.
Require Import UnivalentParametricity.theories.Transportable.
(*! Establishing FP for Type !*)
Unset Collapse Sorts ToType.

Definition URType_Refl_can (A:Type) : A ≈u A.
Proof.
  unshelve eexists.
  - apply UR_gen.
  - apply Equiv_id.
  - intros ? ?; split; eauto.
  - intros ? ?; split; eauto.
Defined.

Instance Canonical_eq_Type : Canonical_eq Type := Canonical_eq_gen _.
(* We avoid the use of univalence and use `None` for the coherence condition *)

Definition FP_Type : Type ≈p Type := {| pr := UR_Type |}.

Inductive Squash (P:Prop) : SProp := sq : P -> Squash P.
Arguments sq {P} _.
Axiom unsquash : forall {P}, Squash P -> P.
Axiom unsquash_eq : forall (P:Prop) (p:P), path@{Prop;_} _ (unsquash (sq p)) p.

Lemma pi_Prop : forall (P:Prop) (p q : P), path@{Prop;_} _ p q.
Proof.
  intros P p q.
  eapply concat. eapply inverse. exact (unsquash_eq _ p).
  eapply concat. 2: eapply unsquash_eq. reflexivity.
Qed.

Definition UR_Type_Prop_SProp (P : Prop) (Q :SProp) : P ≈u Q -> (Squash P ↔ Q : SProp).
Proof.
  intros e. destruct e as [e H coh]. cbn. 
  split.
  - intros p. eapply H. now eapply unsquash.
  - intros q. econstructor. now eapply H.
Qed.

Definition UR_Type_Prop_SProp_inv (P : Prop) (Q :SProp) : (Squash P ↔ Q : SProp) -> P ≈u Q.
Proof.
  intro e. unshelve econstructor.
  - exact  {|pr := fun _ _  => Squash True |}.
  - unshelve econstructor.
    + intro p. eapply (fst e). now econstructor.
    + unshelve econstructor.
      * intro q. eapply unsquash. now eapply (snd e).
      * intro p; cbn. eapply pi_Prop.
      * intro; reflexivity.
      * intro; reflexivity.
  - unfold univalent_transport; cbn. intros; split; eauto.
    + destruct 1. repeat econstructor.
    + intros _. eapply pi_Prop.
  - econstructor; reflexivity.
Defined.

Axiom sprop_ext : forall (P Q : SProp), (P ↔ Q:SProp) -> P = Q.
Axiom prop_ext : forall (P Q : Prop), (P ↔ Q:Prop) -> P = Q.

Inductive Box (P:SProp) : Prop := box : P -> Box P.

Definition path_UR_Type_uncurried {P : Prop} {Q: SProp} (u v : P ≈u Q)
           (pq : (Ur u = Ur v) * (equiv u = equiv v))
  : u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p, q. cbn in *.
  reflexivity. 
Defined.

Lemma Ur_Irr_Prop_SProp : 
  UR_Irr Prop SProp {| pr := fun (P : Prop) (Q : SProp) => P ≈u Q |}.
Proof.
  intros P Q e e'.
  unshelve eapply path_UR_Type_uncurried. repeat unshelve eexists.
  - destruct e, e'. cbn. destruct Ur, Ur0.
    eapply ap. repeat (apply funext; intro).
    eapply sprop_ext. rewrite <- (e_retr _ x0).
    split; intros.
    + apply (fst (Ur_Coh0 x ((e_inv equiv0 x0)))).
      now apply (snd (Ur_Coh x ((e_inv equiv0 x0)))) in H.
    + apply (fst (Ur_Coh x ((e_inv equiv0 x0)))).
      now apply (snd (Ur_Coh0 x ((e_inv equiv0 x0)))) in H.
  - destruct e, e'. cbn. destruct equiv, equiv0.
    unshelve eapply ap. 
    destruct e_isequiv, e_isequiv0. 
    assert (e_inv = e_inv0).
    { apply funext. intro. eapply pi_Prop. }
    now destruct H. 
Qed. 

Definition FP_Prop_Ext: Prop ≈u SProp.
Proof. cbn. 
  unshelve refine {| Ur := {| pr := fun P Q => UR_Type P Q|} |}.
  - repeat unshelve econstructor.
    + exact Squash.
    + exact Box.
    + intros. eapply prop_ext. split; intros. destruct H.
      now eapply unsquash in H. now repeat econstructor.
    + intros. eapply sprop_ext. split; intros.
      now destruct H as [[]]. now repeat econstructor.
    + reflexivity.
  - unfold univalent_transport; cbn. intros; split; eauto.
    + destruct 1. eapply UR_Type_Prop_SProp_inv. split; eauto.
    + intro e. eapply UR_Type_Prop_SProp in e.  eapply prop_ext. split ; intro.
      pose proof (fst e (sq H)). now eapply unsquash in H0.
      pose proof (snd e (sq H)). now eapply unsquash in H0.
  - apply Ur_Irr_Prop_SProp@{SProp;_ _ _ _ _}.
Defined.

Hint Extern 0 (Prop ≈u _) => exact FP_Prop_Ext: typeclass_instances ur_typeclass_instances.

Definition PR_Prop_univ_univ {k} {A :Prop} {B : SProp} (H: A ≈u B) : PR k A B := 
  {|pr := fun _ _  => Squash True |}.
 
(* Hint Extern 0 (_ ≈[ _ ] _) => 
  ltac2: ( match! goal with
  | [ |- ?p ≈[ _ ] _ ] => if Constr.is_prop (Constr.type p) then eapply UR_Type_Prop_SProp_inv else () end) : typeclass_instances ur_typeclass_instances. *)

(*! FP for Dependent product !*)
(* isequiv_functor_forall can be found in
[https://github.com/HoTT/HoTT] *)

Definition functor_forall {A B} `{P : A -> Type} `{Q : B -> Type}
    (f : B -> A) (g : forall b:B, P (f b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b) := fun H b => g b (H (f b)).

Instance isequiv_functor_forall {A B} {P : A -> Type} {Q : B -> Type} (* (eP : Transportable P) *)
         (f : B -> A) `{!IsEquiv f} (g : forall b, P (f b) -> Q b) `{!forall b, IsEquiv (g b)}
  : IsEquiv (functor_forall f g).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - refine (functor_forall (e_inv f) _).
    intros a y.
    generalize (e_inv (g _) y). clear y.
    (* exact (transportable _ _ ((e_retr f a))). *)
    exact (fun t => transport_eq_gen P (e_retr f a) t).
  - intros h. apply funext. intro a. unfold functor_forall.
    destruct (@e_retr _ _ f IsEquiv0 a). apply e_sect.
  - intros h;apply funext. unfold functor_forall. intros b.
    rewrite e_adj. rewrite (transport_ap P f (e_sect f b)).
    rewrite <- (@e_retr _ _ (g b) (H b) (h b)).
    apply ap. set (e_sect f b).
    set (e_inv f (f b)) in *. destruct p. cbn. reflexivity.
Defined.

Instance isequiv_functor_forall_ur {A B : Type} `{P : A -> Type} `{Q : B -> Type} (e : B ≈u A)
  (e' :  forall x y (H:x ≈u y), Q x ≈u P y)
: IsEquiv (functor_forall (equiv e)
                          (fun x =>
                    (e_inv' ((equiv (e' x (equiv e x) (ur_refl e x))))))).
Proof.
  apply isequiv_functor_forall.
  - apply (equiv e).
  - intros b. unfold e_inv'. apply isequiv_inverse.
Defined.

Instance Equiv_forall (A A' : Type) (eA : A ≈u A') (B : A -> Type) (B' : A' -> Type) (eB : B ≈u B')
         : (forall x:A , B x) ≃ (forall x:A', B' x).
Proof.
  pose (e := UR_Type_Inverse _ _ eA).
  pose (e' := fun x y E => UR_Type_Inverse _ _ (eB x y E)).
  assert (eB' : forall (x:A') (y:A) (H:@pr _ _ _ (Ur e) x y) , B' x ≈u B y).
  { intros. exact (e' y x H). }
  unshelve refine
           (BuildEquiv _ _ (functor_forall (e_fun (equiv e))
                                           (fun x => (e_inv' ((equiv (eB' x (e_fun (equiv e) x) (ur_refl e x)))))))
                       _).
  apply isequiv_functor_forall_ur.
Defined.

Definition FP_forall_ur_type (A A' : Type) (eA : A ≈u A') (B : A -> Type) (B' : A' -> Type)
     (eB : B ≈u B') :
  (forall x : A, B x) ≈u (forall x : A', B' x).
Proof.
  unshelve econstructor.
  - intros f g. split; cbn.
    + intros efg x y e.
      destruct efg.
      pose (ur_coh := Ur_Coh (eB _ y (ur_refl (UR_Type_Inverse A A' eA) y))).
      cbn in ur_coh.
      pose proof (fst (ur_coh (f _) (f _)) idpath).
      unfold univalent_transport in X.
      pose proof (H := alt_UR_Coh eA x y).
      destruct H as [_ H].
      specialize (H e).
      cbn in H.
      generalize e; clear e. rewrite H. intro e. 
      rewrite (Ur_Irr _ _ eA _ _ e (ur_refl (UR_Type_Inverse A A' eA) y)).
      exact X.
    + intros e. apply funext. intros x.
      pose proof (fst (Ur_Coh eA x _) idpath).
      specialize (e _ _ X). unfold univalent_transport in *.
      pose (ur_cohB := Ur_Coh (eB _ _ X)).
      destruct (ur_cohB (f x) (g x)) as [_ X']. apply X'. 
      clear ur_cohB. unfold univalent_transport.
      pose proof (e_sect (equiv eA) x).
      set (ur_refl (UR_Type_Inverse A A' eA)
            (equiv eA x)) in *. cbn in p. clearbody p.
      set (e_inv (equiv eA) (equiv eA x)) in *.
      clearbody a. revert e. generalize p; clear p. rewrite H.
      pose (Ur_Irr _ _ eA). intro p. 
      now rewrite (u _ _ X p).
  - intros f g e e'. 
    repeat (eapply funext; intro). eapply (Ur_Irr _ _ (eB _ _ x1)).
Defined.

Definition FP_forall_pr_type (A A' : Type) (eA : A ≈p A') (B : A -> Type) (B' : A' -> Type)
     (eB : B ≈p B') :
  (forall x : A, B x) ≈p (forall x : A', B' x).
Proof. cbn. tc. Defined.

Definition FP_forall_plain :
          (fun A B => forall x:A , B x) ≈p (fun A' B' => forall x:A', B' x).
Proof.
  cbn. tc.
Defined.

Definition FP_forall_ur :
            (fun A B => forall x:A , B x) ≈u (fun A' B' => forall x:A', B' x).
Proof.
  intros A A' eA B B' eB. eapply FP_forall_ur_type; eauto.
Defined.

Definition FP_forall k :
          pr k (fun A B => forall x:A , B x) (fun A' B' => forall x:A', B' x).
Proof.
  destruct k.
  - eapply FP_forall_plain.
  - eapply FP_forall_ur.
Defined.

Ltac apply_forall :=
  first [unshelve eapply FP_forall_ur | unshelve eapply FP_forall];
    intros; shelve_non_PR.

Hint Extern 0 =>
  lazymatch goal with |
    [ |- UR_Type (forall x:_ , _) _ ] => apply_forall |
    [ |- UR_Type _ (forall x:_ , _) ] => apply_forall |
    [ |- (forall x : _, _) ≈[ _] _  ] => apply_forall |
    [ |- _ ≈[ _] (forall x : _, _)  ] => apply_forall
  end
    : typeclass_instances ur_typeclass_instances.

Goal forall k (A A':Type) (Aϵ: A ≈[k] A') (t t':Type) (tϵ : t ≈[k] t'),
          (fun x:A => t) ≈[k] (fun x:A' => t').
Proof.
  Fail tc.
Abort.

Goal forall k (A A':Type) (Aϵ: A ≈[k] A') (t t':Type) (tϵ : t ≈[k] t'),
          (fun x:A => t) ≈[k] (fun x:A' => t').
Proof.
  Fail tc. cbn. tc.
Defined.

Hint Extern 0 ((fun x : _ => _) ≈[ _] _) => intros ? ? ? : typeclass_instances ur_typeclass_instances.
Hint Extern 0 (_ ≈[ _] (fun x : _ => _)) => intros ? ? ? : typeclass_instances ur_typeclass_instances.

Goal forall k (A A':Type) (Aϵ: A ≈[k] A') (t t':Type) (tϵ : t ≈[k] t'),
          (fun x:A => t) ≈[k] (fun x:A' => t').
Proof.
  tc.
Abort.


