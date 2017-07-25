Require Import HoTT.Basics HoTT.Types HoTT.Tactics.

Set Universe Polymorphism.
Set Primitive Projections.

Context {ua : Univalence} {fe : Funext}.


Record Pack (A₀ A₁ : Type) (Aᴿ : A₀ -> A₁ -> Type) := mkPack {
  el₀ : A₀;
  el₁ : A₁;
  prp : Aᴿ el₀ el₁;
}.

Arguments el₀ {_ _ _} _.
Arguments el₁ {_ _ _} _.
Arguments prp {_ _ _} _.


Definition Rel A B := A -> B -> Type.

Definition HEqRefl {A B} (R : Rel A B) (e : A <~> B)
  := forall x, R x (e x).

Definition HEqIsEq {A B} (R : Rel A B) (e : A <~> B) (r : HEqRefl R e)
  := forall x x', @IsEquiv (x = x') (R x (e x'))
                      (fun p => transport (fun y => R x (e y)) p (r x)).

(* Definition of univalent relation for the universe *)
(* Note that this definiiton slighty differs from the papier *)
(* As we ask for a functior from forall x, R x (e x) that leads to an *)
(* equivalence x = y <~> R x (e y), instead of asking directly *)
(* for the equivalence *)


Definition univalent {A B} (R : Rel A B)
  := exists (e : A <~> B) (r : HEqRefl R e), HEqIsEq R e r.

Definition univalentRel A B := {R : Rel A B & univalent R}.


Definition TYPE :=
  Pack Type Type (fun A₀ A₁ => {R : A₀ -> A₁ -> Type & univalent R}).

Definition El (A : TYPE) : Type := Pack A.(el₀) A.(el₁) (A.(prp).1).


(* Auxiliary lemma *)
Definition transportD3 {A : Type} (B : A -> Type) (B' : A -> Type) B''
           (C : forall (a:A) (x: B a) (y: B' a), B'' a x y -> Type)
  {x1 x2 : A} (p : x1 = x2) y y' y'' (z : C x1 y y' y'')
  : C x2 (p # y) (p # y') (transportD2 _ _ _ p _ _ y'')
  :=
  match p with idpath => z end.

Definition transport_univalentRel {A B B'} (e: B = B') R e' r H
  : transport (univalentRel A) e (R; (e'; (r; H)))
    = (e # R ; (e # e' ; (transportD2 _ _ (fun B e' (R : Rel A B) => HEqRefl R e') e _ _ r ; transportD3 _ _ _ (fun B e' (R : Rel A B) (r : HEqRefl R e') => HEqIsEq R e' r) e _ _ _ H))).
  destruct e; reflexivity.
Defined.

Definition path_univalentRel {A B} (X Y : univalentRel A B)
           (eR : X.1 = Y.1) (ee : X.2.1 = Y.2.1)
           (eH : transport (fun Z => HEqRefl Y.1 Z) ee (transport (fun Z => HEqRefl Z X.2.1) eR X.2.2.1) = Y.2.2.1)
  : X = Y.
  destruct X as [R [e [r H]]].
  destruct Y as [R' [e' [r' H']]].
  cbn in *. destruct ee, eR. cbn in *. destruct eH.
  assert (H  = H').
  apply path_forall; intro. apply path_forall; intro. apply hprop_isequiv.
  destruct X. reflexivity. 
Defined. 


Definition HEqGen A : univalentRel A A.
  exists paths. exists equiv_idmap.
  unshelve econstructor.
  - intro; reflexivity.
  - intros x y; cbn.
    eapply isequiv_homotopic.
    eapply isequiv_idmap. intros []; reflexivity.
Defined.

(** Type *)

Notation "A ⋈ B" := {R : A -> B -> Type & univalent R} (at level 50).

Definition UR_Equiv (A B C:Type) {e : B <~> C} {R : A -> B -> Type} : A -> C -> Type :=
  fun a b => R a (e^-1 b).

Definition UR_Type_Struct_Equiv {A B C} (e' : B <~> C) (H: A ⋈ B) : A ⋈ C.
Proof.
  destruct H as [R e r H].
  unshelve econstructor.
  - eapply UR_Equiv; eassumption.
  - unshelve econstructor.
    + eapply equiv_compose'. eassumption. destruct e as [e _]. auto. 
    +  unshelve eexists.
       intro x. cbn. unfold UR_Equiv. cbn. destruct e as [e [ur_refl _]]. cbn. 
       refine ((eissect e' (e x))^ # _). eapply ur_refl.
       intros a b. serapply isequiv_adjointify; cbn.
       *  intro p. destruct e as [e [ur_refl ur_is_eq]].
          cbn in *. apply ur_is_eq. refine (eissect e' (e b) # p).
       * intro p; cbn. destruct e as [e [ur_refl ur_is_eq]].
         match goal with
         | |- transport _ (@equiv_inv _ _ ?gg ?ff ?pp) ?qq = _ =>
           set pp; set ff; set gg in *
         end.
         match goal with
         | |- transport _ ?ff _ = _ => set ff
         end.
         transitivity (transport (R a) (eissect e' (e b))^
                    (transport (fun x => R a (e x)) p0 (ur_refl a))).
         destruct p0. reflexivity.
         cbn. eapply (moveR_transport_V (R a)).
         exact (eisretr r0 r). 
       * intros []; cbn. rewrite <- transport_pp.
         rewrite concat_Vp. cbn.
         apply equiv_moveR_equiv_V. reflexivity.
Defined.


Definition transport_equiv `{Fs: Funext} {A B} P {e e' : A <~> B} (H : e = e' :> (A -> B))
  : transport (fun e : A <~> B => P (equiv_fun e)) (path_equiv H)
    = transport (fun f => P f) H.
  eapply path_forall; intro a.
  (* Set Printing Coercions. *)
  rewrite (transport_compose P).
  eapply ap10, ap. destruct e as [f Hf], e' as [f' Hf']; cbn in *.
  rewrite concat_1p, concat_p1. cbn.
  destruct H. assert (Hf = Hf'). apply path_ishprop.
  destruct X.
  assert (path_sigma_hprop (f; Hf) (f; Hf) 1 = 1)%path. {
    unfold path_sigma_hprop.
    unshelve eapply path_path_sigma.
    rewrite pr1_path_sigma_uncurried.
    reflexivity. eapply path_ishprop. }
  rewrite X. reflexivity.
Defined.



Definition path_UR_Type_Struct {A B} {e e' : A <~> B} {R R' : A -> B -> Type}
           {r : forall a, R a (e a)}
           {r' : forall a, R' a (e' a)} {H H'}
           (e1: e == e')
           (e2: forall x y, R x y = R' x y)
           (e3 : (forall a, (transport (fun b => R' a b) (e1 a)
                                  (transport idmap (e2 _ _) (r a))) = r' a))
  : (R ; (e; (r ; H))) = (R' ; (e'; (r' ; H'))) :> A ⋈ B.
Proof.
  transparent assert (e1' : (e = e')). {
    eapply path_equiv, path_forall, e1. }
  transparent assert (e2' : (R = R')). {
    eapply path_forall; intro; eapply path_forall; intro.
    apply e2. }
  assert (e3' : transport (fun e : A <~> B => forall a, R' a (e a)) e1'
                          (transport (fun R => forall a, R a (e a)) e2' r) = r'). {
    etransitivity. eapply path_forall.
    simple refine (transport_forall_constant _ _).
    eapply path_forall; intro a.
    subst e1'. rewrite (transport_equiv (fun f => R' a (f a))).
    rewrite transport_compose. rewrite ap_apply_l.
    rewrite ap10_path_forall. rewrite transport_forall_constant.
    refine (_ @ e3 a). apply ap.
    subst e2'. by transport_path_forall_hammer. }
  destruct e1', e2', e3'. cbn.
  assert (H = H'). apply path_ishprop.
    by destruct X.
Defined.

Definition UR_Type_Struct_transport_equiv {A B C} {e' : B <~> C} {H: A ⋈ B}
  : transport (fun X => A ⋈ X) (path_universe_uncurried e') H
    = UR_Type_Struct_Equiv e' H.
  rewrite <- (equiv_path_path_universe_uncurried e').
  set (path_universe_uncurried e'). 
  destruct p. clear e'.
  rewrite eta_path_universe_uncurried; cbn.
  destruct H as [R [e [u u']]]. 
  unshelve eapply path_UR_Type_Struct.
  intro; reflexivity.
  intros; cbn. reflexivity.
  intro; reflexivity.
Defined.

Definition UR_is_eq_equiv {A B} (e : A ⋈ B) (a : A) (b : B)
  : (a = (e.2.1)^-1 b) <~> (e.1 a b).
Proof.
  etransitivity. econstructor.
  exact (e.2.2.2 a _).
  refine (transport (fun X =>  (e.1 a X) <~> _) (eisretr _ b)^ (equiv_idmap _)). 
Defined. 

Definition UR_is_eq_equiv' {A B} (e : A ⋈ B) (a : A) (b : B)
  : (a = (e.2.1)^-1 b) <~> (e.1 a b).
Proof.
  refine (transport (fun X =>  a = (e.2.1)^-1 b <~> (e.1 a  X))
                    (eisretr (e.2.1) b) _).
  econstructor.
  exact (e.2.2.2 a ((e.2.1)^-1 b)).
Defined. 

Definition Typeᶠ : TYPE.
  refine (mkPack Type Type (fun A₀ A₁ => {R : A₀ -> A₁ -> Type & univalent R})
                 Type Type (fun A₀ A₁ => {R : A₀ -> A₁ -> Type & univalent R} ; _)).
  exists equiv_idmap. cbn.
  unshelve econstructor.
  - exact HEqGen.
  - intros A B; cbn. unshelve eapply isequiv_adjointify.
    + intro e. apply path_universe_uncurried. destruct e as [_ [e _]]. exact e. 
    + intros [R [e [r H]]].
      rewrite UR_Type_Struct_transport_equiv.
      serapply path_UR_Type_Struct; cbn.
      intro; reflexivity.
      intros. apply path_universe_uncurried.
      apply (UR_is_eq_equiv (R;(e;(r;H)))).
      intro; cbn.
      rewrite transport_idmap_path_universe_uncurried. cbn.
      rewrite transport_paths_r.
      rewrite concat_1p.
      match goal with
      | |- ?f ?g = _ => set f; set g
      end.
      transitivity (transport (fun x => R a (e x)) (eissect e a) r1).
      apply ap10. subst r1 r0. clear.
      rewrite <- (equiv_path_path_universe_uncurried e).
      destruct (path_universe_uncurried e). reflexivity.
      subst r0.
      refine (transport_pV (fun x : A => R a (e x)) (eissect e a) (r a)).
    + intro e; cbn. destruct e. cbn.
      exact (eta_path_universe_uncurried idpath).
Defined.


Check Typeᶠ : El Typeᶠ.

Definition mkTYPE (A₀ A₁ : Type) (Aᴿ : A₀ -> A₁ -> Type) (Aᴿs : univalent Aᴿ)
  : El Typeᶠ :=
  mkPack Type Type (fun A₀ A₁ => univalentRel A₀ A₁) A₀ A₁ (Aᴿ ; Aᴿs).



(** Dependent products *)

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : El Typeᶠ.
  refine (mkTYPE
            (forall x : El A, (B x).(el₀))
            (forall x : El A, (B x).(el₁))
            (fun f₀ f₁ => forall x : El A, (B x).(prp).1 (f₀ x) (f₁ x))
            _).
  simple refine (_; (_; _)).
  - eapply equiv_functor_forall_id.
    intro ; exact ((B a).(prp).2.1).
  - intros f a. cbn; unfold functor_forall.
    exact ((B a).(prp).2.2.1 (f a)).
  - intros f g; cbn; unfold functor_forall.
    unshelve eapply isequiv_adjointify.
    + intro H. eapply path_forall; intro a.
      refine (@equiv_inv _ _ _ ((B a).(prp).2.2.2 (f a) (g a)) _).
      exact (H a).
    + intro H. eapply path_forall; intro a.
      rewrite transport_forall_constant.
      rewrite (transport_compose
                 (fun y => (prp (B a)).1 (f a) (((prp (B a)).2).1 y))).
      match goal with
      | |- transport ?PP (ap _ ?ee) ?uu = ?vv
        => change (transport PP (apD10 ee a) uu = vv)
      end.
      rewrite apD10_path_forall.
      exact (@eisretr _ _ _ ((B a).(prp).2.2.2 (f a) (g a)) (H a)).
    + intro e.
      pose proof (fun a => @eissect _ _ _ ((B a).(prp).2.2.2 (f a) (g a))
                                 (apD10 e a)).
      cbn in *.
      match goal with
      | |- path_forall f g ?ee = e
        => assert (XX: ee = apD10 e); [|rewrite XX; apply eta_path_forall]
      end.
      eapply path_forall; intro a; cbn.
      etransitivity. 2: exact (X a).
      eapply ap. rewrite transport_forall_constant.
      rewrite (transport_compose
                 (fun y => (prp (B a)).1 (f a) (((prp (B a)).2).1 y))).
      reflexivity.
Defined.
      

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
  unshelve econstructor.
  + refine (fun x => (f x).(el₀)).
  + refine (fun x => (f x).(el₁)).
  + refine (fun x => (f x).(prp)).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
  unshelve econstructor.
  + refine (f.(el₀) x).
  + refine (f.(el₁) x).
  + refine (f.(prp) x).
Defined.

Notation "t · u" := (Appᶠ t u) (at level 64, left associativity).

Eval compute in idpath : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in idpath : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).


(** Prop *)
Axiom Prop_irrelevance :
  forall (P Q : Prop), IsEquiv (fun p : P = Q
                        => transport (fun Q : Prop => P <-> Q) p (iff_reflexive P)).

Definition Propᶠ : El Typeᶠ.
  refine (mkTYPE Prop Prop (fun P Q => P <-> Q) _).
  exists equiv_idmap.
  unshelve econstructor.
  - intro P; cbn. reflexivity.
  - intros P Q; cbn. exact (Prop_irrelevance P Q).
Defined.

Definition ElProp : El Propᶠ -> Type.
  intro P. refine (Pack P.(el₀) P.(el₁) (fun _ _ => True)).
Defined.

Definition ProdPropᶠ (A : TYPE) (B : El A -> El Propᶠ) : El Propᶠ.
  unshelve eapply mkPack.
  - cbn. exact (forall x : El A, (B x).(el₀)).
  - cbn. exact (forall x : El A, (B x).(el₁)).
  - cbn. split; intros f x.
    + apply (B x).(prp). exact (f x).
    + apply (B x).(prp). exact (f x).
Defined.


Definition LamPropᶠ {A : TYPE} {B : El A -> El Propᶠ}
           (f : forall x : El A, ElProp (B x))
  : ElProp (ProdPropᶠ A B).
Proof.
  unshelve econstructor.
  + refine (fun x => (f x).(el₀)).
  + refine (fun x => (f x).(el₁)).
  + refine I.
Defined.




(** Bool *)

Definition Boolᶠ : El Typeᶠ.
  refine (mkTYPE Bool Bool (fun b₀ b₁ => b₀ = b₁) _).
  exists equiv_idmap. unshelve econstructor.
  - intros []; reflexivity. 
  - intros b b'; cbn. 
    unshelve eapply isequiv_adjointify.
    + exact (fun p => p).
    + intros []; cbn. destruct b; reflexivity.
    + intro p. destruct b, b', p; reflexivity.
Defined.

Definition trueᶠ : El Boolᶠ := {| prp := idpath true |}.
Definition falseᶠ : El Boolᶠ := {| prp := idpath false |}.

Definition Bool_rectᶠ : El
  (Πᶠ (P : El (Boolᶠ →ᶠ Typeᶠ)), P · trueᶠ →ᶠ P · falseᶠ →ᶠ
  Πᶠ (b : El Boolᶠ), P · b).
Proof.
  refine (λᶠ P Pt Pf b, _).
  destruct P as [P0 P1 PP]. destruct b as [b b' e], e, b.
  cbn in *. exact Pt. exact Pf.
Defined.

Eval compute in idpath :
  (fun P Pt Pf => Bool_rectᶠ · P · Pt · Pf · trueᶠ) = (fun P Pt Pf => Pt).

Eval compute in idpath :
  (fun P Pt Pf => Bool_rectᶠ · P · Pt · Pf · falseᶠ) = (fun P Pt Pf => Pf).
