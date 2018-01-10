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

Hint Extern 0 (Transportable (fun a : _ => _ = _))
=> apply Transportable_default : typeclass_instances.

Instance Transportable_Forall A (B:A -> Type) (P: forall a, B a -> Type)
         (HB : Transportable B)
         (HP : Transportable (fun x => P x.1 x.2)):
  Transportable (fun a => forall b, P a b).
Proof.
  unshelve econstructor. intros x y e.
  destruct HP as [HP HP'].
  pose e^.
  unshelve refine (BuildEquiv _ _ (functor_forall _ _) (isequiv_functor_forall _ _ _ )).
  apply transportable; auto. intro b. cbn.
  assert ((x;transportable y x e0 b) = (y;b)).
  apply path_sigma_uncurried. unshelve esplit.  exact e. cbn. destruct e.
  cbn. exact (apD10 (ap e_fun (@transportable_refl _ _ _ x)) b).
  apply (HP _ _ X);  typeclasses eauto.
  unshelve econstructor. intros.
  assert ((x;x0) = (x;y0)). 
  apply path_sigma_uncurried. unshelve esplit. reflexivity. exact X.
  exact (HP _ _ X0).  
  intros; cbn. apply (HP' (x;x0)).   
  typeclasses eauto. 
  typeclasses eauto. 
  intro a. cbn.
  unshelve refine (path_Equiv _).
  apply funext; intro f. apply funext; intro b. cbn. unfold functor_forall.
  pose (fun (e : {e : B a ≃ B a & e = Equiv_id (B a)}) =>
               (transportable (a; e.1 b) (a; b)
                            match apD10 (ap e_fun e.2) b in (_ = y) return ((a; e.1 b) = (a; y)) with
                            | eq_refl => eq_refl
                            end) (f (e.1 b)) = f b).
  change (T (transportable a a eq_refl; transportable_refl a)).
  assert ((transportable a a eq_refl; transportable_refl a) = ((Equiv_id (B a); eq_refl): {e : B a ≃ B a & e = Equiv_id (B a)})).
  apply path_sigma_uncurried. unshelve esplit. apply (transportable_refl a).
  cbn. rewrite transport_paths_l. rewrite inv2. rewrite concat_refl. reflexivity.  
  apply (transport_eq T X^). unfold T. cbn.
  exact (apD10 (ap e_fun (transportable_refl (a;b))) _). 
Defined.


Definition Transportable_lift_ A B C (g : B -> C) (P : C -> Type) `{Transportable C P} x:
  forall f f': A -> B, f = f' -> P (g (f x)) ≃ P (g (f' x)). 
  intros. assert (g (f x) = g (f' x)). destruct X; reflexivity.
  apply H. typeclasses eauto.
Defined.

Instance Transportable_compose A B C (g : B -> C) (P : C -> Type) `{Transportable C P} x:
  Transportable (fun (f:A -> B) => P (g (f x))). 
Proof.
  refine (Build_Transportable _ _ (Transportable_lift_ A B C g P x) _). 
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

