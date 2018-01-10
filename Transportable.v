Require Import HoTT Tactics UR URTactics FP Record MoreInductive.
Require Import BinInt BinNat Nnat Vector.

Set Universe Polymorphism.

Instance Transportable_Sigma (A:Type) B (P : A -> B -> Type) (HP: forall a, Transportable (P a))
  (HP': forall x, Transportable (fun a => P a x)):
  Transportable (fun x => {a: A & P a x}).
Proof.
  unshelve econstructor.
  intros. erefine (@Equiv_Sigma _ _ (@ur_refl_ _ _ _ _ URType_Refl A) _ _ _). 
  cbn. split. typeclasses eauto.
  intros.
  { unshelve eexists.
    - destruct H. typeclasses eauto. 
    - destruct X, H. apply UR_gen.
    - constructor. destruct X, H. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
  }
  intros. unshelve refine (path_Equiv _). cbn.
  apply funext. intros. eapply path_sigma_uncurried.
  destruct x0. unshelve esplit.  reflexivity. cbn.
  unfold univalent_transport. exact (apD10 (ap e_fun (transportable_refl x)) p). 
Defined.


Definition Transportable_compose_ A B C (g : B -> C) (P : C -> Type) `{Transportable C P} x:
  forall f f': A -> B, f = f' -> P (g (f x)) ≃ P (g (f' x)). 
  intros. assert (g (f x) = g (f' x)). destruct X; reflexivity.
  apply H. typeclasses eauto.
Defined.

Instance Transportable_compose A B C (g : B -> C) (P : C -> Type) `{Transportable C P} x:
  Transportable (fun (f:A -> B) => P (g (f x))). 
Proof.
  refine (Build_Transportable _ _ (Transportable_compose_ A B C g P x) _). 
  intros. apply H. 
Defined. 

Instance Transportable_apply B C (g : B -> C) (P : C -> Type) `{Transportable C P}:
  Transportable (fun (f:B) => P (g f)).
Proof.
  unshelve econstructor. intros. apply H. 
Defined. 

Instance Transportable_Arrow A (P Q: A -> Type)
         (HP : Transportable P) (HQ : Transportable Q) : Transportable (fun a => P a -> Q a).
Proof.
  unshelve econstructor. intros x y e. pose (inverse e). 
  unshelve refine (BuildEquiv _ _ _ _).
  { unshelve eexists.
    - destruct e. apply UR_gen.
    - constructor. destruct e. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
  }
  cbn. split. typeclasses eauto. intros. 
  { unshelve eexists.
    - destruct e. apply UR_gen.
    - constructor. destruct e. cbn. unfold univalent_transport.
      rewrite transportable_refl. cbn. intros;apply Equiv_id.
  }
  intro a; cbn. 
  unshelve refine (path_Equiv _).
  apply funext; intro f. apply funext; intro b. cbn.
  rewrite (@transportable_refl _ _ HQ a). cbn. apply ap. 
  exact (apD10 (ap e_fun (@transportable_refl _ _ HP a)) b).
Defined.

Hint Extern 0 (URForall_Type_class ?A ?B ?F ?G) => is_ground A; is_ground B; is_ground F; is_ground G;
                                                     econstructor : typeclass_instances.

