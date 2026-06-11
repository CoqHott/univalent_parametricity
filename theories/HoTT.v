(************************************************************************)
(* This file defines basic ingredients of HoTT, most of them already *)
(* present in https://github.com/HoTT. We have created our own library *)
(* to be independent from the HoTT framework, which requires a tailored version of Coq  *)
(************************************************************************)

(*
Sort Fib.

Abbreviation Fib := Type@{Fib;_}.
*)

Set Universe Polymorphism.
Set Definitional UIP.
Set Polymorphic Inductive Cumulativity.

(* Basic notations *)
#[universes(collapse_sort_variables=no)]
Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

#[universes(collapse_sort_variables=no)]
Definition sigT_rect
	 : forall (A : Type)
         (P : forall _ : A, Type)
         (P0 : forall _ : @sigT A P, Type)
         (_ : forall (x : A) (p : P x), P0 (@existT A P x p))
         (s : @sigT A P),
       P0 s.
Proof.
  intros ? ? ? ? []; eauto.
Defined.

Register Scheme sigT_rect as rect_dep for sigT.
Register Scheme sigT_rect as rect_nodep for sigT.

#[universes(collapse_sort_variables=no)]
Inductive prod (A B : Type) : Type :=  pair : A -> B -> prod A B.

#[universes(collapse_sort_variables=no)]
Definition prod_rect :
forall (A B : Type) (P : forall _ : prod A B, Type)
         (_ : forall (a : A) (b : B), P (pair A B a b))
         (p : prod A B),
       P p.
Proof.
  intros ? ? ? ? []; eauto.
Defined.

Register Scheme prod_rect as rect_dep for prod.
Register Scheme prod_rect as rect_nodep for prod.

Arguments pair {_ _} _ _.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z): type_scope.

#[universes(collapse_sort_variables=no)]
Definition fst {A B} (p:prod A B) := prod_rect _ _ (fun _ => A) (fun x y => x) p.

#[universes(collapse_sort_variables=no)]
Definition snd {A B} (p:prod A B) := prod_rect _ _ (fun _ => B) (fun x y => y) p.

#[universes(cumulative)]
Inductive path@{s;i} (A:Type@{s;i}) (x:A) : A -> SProp :=
  idpath : path A x x.

Arguments idpath {_ _}.

Definition path_Has_Leibniz_elim_@{s s';l l' l''} : Has_Leibniz@{s _ s';l l' l''} (@path).
intros  A x P t y e . now destruct e.
Defined.

Instance path_Has_Leibniz_elim@{s s';l l' l''} : Has_Leibniz@{s _ s';l l' l''} (@path)
:= path_Has_Leibniz_elim_.

Hint Resolve path_Has_Leibniz_elim : rewrite_instances.

Definition path_Has_Leibniz_r_elim_@{s s'; l l' l''} : Has_Leibniz_r@{s _ s';l l' l''} (@path).
intros A x P t y e . now destruct e.
Defined.

Instance path_Has_Leibniz_r_elim@{s s'; l l' l''} : Has_Leibniz_r@{s _ s';l l' l''} (@path) :=
 path_Has_Leibniz_r_elim_.

Hint Resolve path_Has_Leibniz_r_elim : rewrite_instances.

Instance path_Has_refl@{s;l} : Has_refl@{s _;l l} (@path) :=
  fun A x => idpath.

Definition path_Has_Leibniz_J_@{s s'; l l' l''} : Has_J@{s _ s';l l' l''} (@path) _.
intros A x P t y e. now destruct e.
Defined.

Instance path_Has_Leibniz_J@{s s'; l l' l''} : Has_J@{s _ s';l l' l''} (@path) _ :=
  path_Has_Leibniz_J_.

Hint Resolve path_Has_Leibniz_J : rewrite_instances.

Definition path_Has_Leibniz_J_r_@{s s'; l l' l''} : Has_J_r@{s _ s';l l' l''} (@path) _.
intros  A x P t y e . now destruct e.
Defined.

Instance path_Has_Leibniz_J_r@{s s'; l l' l''} : Has_J_r@{s _ s';l l' l''} (@path) _ :=
  path_Has_Leibniz_J_r_.

Hint Resolve path_Has_Leibniz_J_r : rewrite_instances.

Notation "x = y :> A" := (@path A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

#[universes(collapse_sort_variables=no)]
Definition projT1 {A} {P:A -> Type} (p:sigT P) : A :=
  sigT_rect _ _ (fun _ => A) (fun x y => x) p.

#[universes(collapse_sort_variables=no)]
Definition projT2  {A} {P:A -> Type} (p:sigT P) : P (projT1 p) :=
  sigT_rect _ _ (fun x => P (projT1 x)) (fun x y => y) p.

Notation id := (fun x => x).

Notation compose := (fun g f x => g (f x)).

Notation "g ∘ f" := (compose g%function f%function) (at level 1): function_scope.

Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "x .1" := (projT1 x).
Notation "x .2" := (projT2 x).
Notation " ( x ; p ) " := (existT _ x p).

Notation "f == g" := (forall x, f x = g x) (at level 70).


(* Equality-related definitions *)

#[universes(collapse_sort_variables=no)]
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

#[universes(collapse_sort_variables=no)]
Definition ap2 {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : f x x' = f y y'
  := match p with idpath => match q with idpath => idpath end end.

#[universes(collapse_sort_variables=no)]
Definition ap3 {A A' A'' B:Type} (f:A -> A' -> A'' -> B) {x y:A} (p:x = y)
  {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'') : f x x' x''= f y y' y''
  := match p with idpath => match p' with idpath => match p'' with idpath => idpath end end end.

#[universes(collapse_sort_variables=no)]
Definition ap4 {A A' A'' A''' B:Type} (f:A -> A' -> A'' -> A''' -> B) {x y:A} (p:x = y)
           {x' y':A'} (p':x' = y') {x'' y'':A''} (p'':x'' = y'')
           {x''' y''':A'''} (p''':x''' = y''') : f x x' x'' x'''= f y y' y'' y'''
  := match p with idpath =>
     match p' with idpath =>
     match p'' with idpath =>
     match p''' with idpath => idpath end end end end.

(* HSet *)

Class HSet A := {is_hset : forall (x y : A) (e e' : x = y), e = e'}.

(* From HoTT/Coq *)

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g.
destruct h ; reflexivity.
Qed.

#[universes(collapse_sort_variables=no)]
Definition transport_eq_gen {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

#[universes(collapse_sort_variables=no)]
Definition transport_eq_gen_refl {A : Type} (P : A -> Type) {x : A} (u : P x) :
  transport_eq_gen P idpath u = u.
Proof. cbn. reflexivity. Qed.

Definition transport_eq {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Notation "p ## x" := (transport_eq_gen _ p x) (right associativity, at level 65, only parsing).
Notation "p # x" := (transport_eq _ p x) (right associativity, at level 65, only parsing).

#[universes(collapse_sort_variables=no)]
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  destruct p; exact q.
Qed.

Notation "p @ q" := (concat p q) (at level 20).

#[universes(collapse_sort_variables=no)]
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x.
destruct p; exact idpath.
Qed.

Notation "p ^" := (inverse p) (at level 3, format "p '^'").

#[universes(collapse_sort_variables=no)]
Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with idpath => z end.

#[universes(collapse_sort_variables=no)]
Definition transportD2 {A : Type} (B : A -> Type) (B' : A -> Type) (C : forall a:A, B a -> B' a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)  (y' : B' x1) (z : C x1 y y')
  : C x2 (p # y) (p # y')
  :=
  match p with idpath => z end.

#[universes(collapse_sort_variables=no)]
Definition transportD3 {A : Type} (B : A -> Type) (B' : A -> Type) B''
           (C : forall (a:A) (x: B a) (y: B' a), B'' a x y -> Type)
  {x1 x2 : A} (p : x1 = x2) y y' y'' (z : C x1 y y' y'')
  : C x2 (p # y) (p # y') (transportD2 _ _ _ p _ _ y'')
  :=
    match p with idpath => z end.

#[universes(collapse_sort_variables=no)]
Definition transport_double A (P : A -> A -> Type) x y (e : x = y) (f : forall a, P a a) :
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e (f x)) = f y.
  destruct e. reflexivity.
Qed.

#[universes(collapse_sort_variables=no)]
Definition transport_forall A B (f : forall x : A , B x)  y z (e : z = y) :
  e # (f z) = f y.
Proof.
  destruct e. reflexivity.
Qed.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u.
exact (match q with idpath =>
    match p with idpath => idpath end
  end).
Qed.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z.
Proof.
  destruct p; reflexivity.
Qed.

Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y)
  : p^ # p # z = z.
Proof.
  destruct p; reflexivity.
Qed.

Definition inv_inv A (x y :A) (e: x = y) : e^ @ e = idpath.
Proof.
  destruct e; reflexivity.
Qed.

#[universes(collapse_sort_variables=no)]
Definition transport_ap {A B : Type} (P : B -> Type) (f : A -> B) {x y : A}
           (p : x = y) (z : P (f x)) : transport_eq_gen P (ap f p) z =
                                       transport_eq_gen (fun x => P (f x)) p z.
Proof.
  destruct p. repeat rewrite transport_eq_gen_refl. reflexivity.
Qed.

Definition concat_inv {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
             Proof.
  destruct p, q; reflexivity.
Defined.

Definition ap_inv {A B:Type} (f:A -> B) {x y:A} (p:x = y) : ap f p^ = (ap f p)^.
Proof.
  destruct p; reflexivity.
Defined.

Definition transport_inv {A : Type} (P : A -> Type) {x y : A} (p : x = y) u v :
  p # u = v -> u = transport_eq P p^ v.
Proof.
  destruct p;cbn. exact id.
Defined.


Definition transport_commute A B (P : A -> B -> Type) x y (e : x = y) x' y' (e' : x' = y') u:
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ X) e' u) =
  transport_eq (fun X => P _ X ) e' (transport_eq (fun X => P X _) e u).
  destruct e, e'. reflexivity.
Defined.

Definition transport_double' A B (P : A -> B -> Type) x y (e : x = y) g (f : forall a, P a (g a)) :
  transport_eq (fun X => P X _ ) e (transport_eq (fun X => P _ (g X)) e (f x)) = f y.
  destruct e. reflexivity.
Defined.

#[universes(collapse_sort_variables=no)]
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 & u.2 = p^ ## v.2})
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q. rewrite q. rewrite transport_eq_gen_refl. reflexivity.
Defined.

Definition path_sigma_SProp {A : Type} (P : A -> SProp) (u v : sigT P)
           (pq : u.1 = v.1)
: u = v.
Proof.
  eapply path_sigma_uncurried. now unshelve econstructor.
Defined.

#[universes(collapse_sort_variables=no)]
Definition pr1_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v) : u.1 = v.1 := ap projT1 p.

Notation "p ..1" := (pr1_path p) (at level 50).

#[universes(collapse_sort_variables=no)]
Definition pr2_path {A} `{P : A -> Type} {u v : sigT P} (p : u = v)
  : u.2 = p..1^ ## v.2.
  destruct p. now rewrite transport_eq_gen_refl.
Defined.

Notation "p ..2" := (pr2_path p) (at level 50).

#[universes(collapse_sort_variables=no)]
Definition path_prod_uncurried {A B : Type} (u v : A * B)
           (pq : (fst u = fst v) * (snd u = snd v))
: u = v.
Proof.
  destruct pq as [p q]. destruct u, v. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

#[universes(collapse_sort_variables=no)]
Definition path_prod_eta {A B : Type} (u : A * B):
           u = (fst u , snd u).
Proof.
  destruct u; reflexivity.
Defined.

Definition ap_id A (x y:A) (e:x = y) : ap id e = e.
Proof.
  destruct e; reflexivity.
Defined.

Definition refl_V {A : Type} {x : A} (p : x = x) :
  p^ = idpath -> p = idpath.
Proof.
  pose (ep := inv_inv _ _ _ p).
  intro e. rewrite e in ep. exact ep.
Defined.

Definition unpack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u.
  destruct u. exact id.
Defined.

Definition pack_prod {A B} `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u).
  destruct u; exact id.
Defined.

Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: transport_eq P (path_prod_uncurried _ _ H) Px
  = unpack_prod _ (transport_eq (fun x => P (x, snd y))
              (fst H)
              (transport_eq (fun y => P (fst x, y))
                         (snd H)
                         (pack_prod _ Px))).
Proof.
  destruct x, y, H; simpl in *.
  destruct p, p0.
  reflexivity.
Defined.

Lemma path_prod_uncurried_inv {A B} {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
  : (path_prod_uncurried _ _ H)^
    = path_prod_uncurried _ _ ((fst H)^, (snd H)^).
Proof.
  destruct H, x ,y. cbn in *. destruct p, p0. reflexivity.
Defined.

Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport_eq (fun a => prod (P a) (Q a)) p z  =  (p # (fst z), p # (snd z)).
  destruct p, z. reflexivity.
Defined.

Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport_eq (fun x => B) p y = y.
Proof.
  destruct p.  exact idpath.
Defined.

Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r.
  destruct p, q; reflexivity.
Defined.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p).
  destruct p. reflexivity. Defined.


Definition inv_inv' A (x y :A) (e: x = y) : e @ e^ = idpath.
Proof.
  destruct e; reflexivity.
Defined.

Definition transport_switch {A : Type} (P : A -> Type) {x y : A} (p : y = x) (z : P y) z'
  : z = p^ # z' -> p # z = z'.
Proof.
  destruct p; cbn; exact id.
Qed.



(* Equivalences *)

#[universes(collapse_sort_variables=no)]
Class IsEquiv {A : Type} {B : Type} (f : A -> B) : Type := BuildIsEquiv {
  e_inv : B -> A ;
  e_sect : forall x, e_inv (f x) = x;
  e_retr : forall y, f (e_inv y) = y;
  e_adj : forall x : A, e_retr (f x) = ap f (e_sect x);
}.

(** A class that includes all the data of an adjoint equivalence. *)
#[universes(collapse_sort_variables=no)]
Class Equiv A B : Type := BuildEquiv {
  e_fun : A -> B ;
  e_isequiv : IsEquiv e_fun
}.

Hint Resolve e_isequiv : typeclass_instances.

Notation "A ≃ B" := (Equiv A B) (at level 20).

Arguments e_fun {_ _} _ _.
Arguments e_inv {_ _} _ {_} _.
Arguments e_sect {_ _} _ {_} _.
Arguments e_retr {_ _} _ {_} _.
Arguments e_adj {_ _} _ {_} _.
Arguments e_isequiv {_ _ _}.

Typeclasses Transparent e_fun e_inv.

Coercion e_fun : Equiv >-> Funclass.

#[universes(collapse_sort_variables=no)]
Definition univalent_transport {A B : Type} {e: A ≃ B} : A -> B := e_fun e.

Notation "↑" := univalent_transport (only parsing).

#[universes(collapse_sort_variables=no)]
Definition e_inv' {A B : Type} (e : A ≃ B) : B -> A := e_inv (e_fun e).
#[universes(collapse_sort_variables=no)]
Definition e_sect' {A B : Type} (e : A ≃ B) := e_sect (e_fun e).
#[universes(collapse_sort_variables=no)]
Definition e_retr' {A B : Type} (e : A ≃ B) := e_retr (e_fun e).
#[universes(collapse_sort_variables=no)]
Definition e_adj' {A B : Type} (e : A ≃ B) := e_adj (e_fun e).

#[universes(collapse_sort_variables=no)]
Definition iff P Q : Type := (prod (P -> Q) (Q -> P)).

Notation "P ↔ Q" := (iff P Q) (at level 50).

#[universes(collapse_sort_variables=no)]
Definition Equiv_iff_SProp {A B : SProp} (e : A ↔ B) : A ≃ B.
Proof.
  unshelve eapply BuildEquiv.
  - exact (fun a => match e with (a2b, _) => a2b a end).
  - unshelve eapply BuildIsEquiv.
    + exact (fun b => match e with (_, b2a) => b2a b end).
    + reflexivity.
    + reflexivity.
    + reflexivity.
Defined.

Axiom PI : forall (P : Prop) (p q : P), path@{Prop;_} _ p q.

#[universes(collapse_sort_variables=no)]
Definition Equiv_iff_Prop {A: Prop} {B: SProp} (e : A ↔ B) : Equiv@{_ _ Prop SProp;_ _ _} A B.
Proof.
  unshelve eapply BuildEquiv.
  - exact (fun a => match e with (a2b, _) => a2b a end).
  - unshelve eapply BuildIsEquiv.
    + exact (fun b => match e with (_, b2a) => b2a b end).
    + intros; cbn. eapply PI.
    + reflexivity.
    + reflexivity.
Defined.

Definition issect'  {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g ∘ f == id) (isretr : f  ∘ g == id) :=
  fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.


#[universes(collapse_sort_variables=no)]
Definition isequiv_adjointify {A B : Type} (f : A -> B) (g : B -> A)
           (issect : g∘ f == id) (isretr : f  ∘ g == id)  : IsEquiv f
  := BuildIsEquiv A B f g issect isretr
                  (fun x => idpath).

#[universes(collapse_sort_variables=no)]
Definition Equiv_id A : A ≃ A :=
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => idpath) (fun _ => idpath) (fun _ => idpath)).

#[universes(collapse_sort_variables=no)]
Definition isequiv_compose A B C f g `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (g ∘ f).
Proof.
  unshelve eapply isequiv_adjointify.
  - exact ((e_inv f) ∘ (e_inv g)).
  - exact (fun a => ap (e_inv f) (e_sect g (f a)) @ e_sect f a).
  - exact (fun c => ap g (e_retr f (e_inv g c)) @ e_retr g c).
Defined.

#[universes(collapse_sort_variables=no)]
Definition equiv_compose {A B C : Type} (f: A ≃ B) (g : B ≃ C)
  : A ≃ C
  := BuildEquiv A C ((e_fun g) ∘ (e_fun f)) (isequiv_compose _ _ _ _ _).

Notation "g ∘∘ f" := (equiv_compose f g) (at level 50).

Definition concat_Vp {A : Type} {x y : A} (p : x = y) := inv_inv A x y p.

#[universes(collapse_sort_variables=no)]
Definition isequiv_inverse {A B : Type} (f : A -> B) {feq : IsEquiv f} : IsEquiv (e_inv f)
    := BuildIsEquiv _ _ (e_inv f) f (e_retr f) (e_sect f) (fun x => idpath).

#[universes(collapse_sort_variables=no)]
Definition Equiv_inverse {A B : Type} (e: A ≃ B) : B ≃ A := BuildEquiv _ _ (e_inv (e_fun e)) (isequiv_inverse _).

Definition Move_equiv {A B} (e : A ≃ B) x y : x = e_inv' e y -> e_fun e x = y.
Proof.
  intro X. apply (ap (e_fun e)) in X. exact (X @ e_retr' e _).
Qed.

Definition Move_equiv' {A B} (e : A ≃ B) x y : e_fun e x = y -> x = e_inv' e y.
Proof.
  intro X. apply (ap (e_inv' e)) in X. exact ((e_sect' e _)^ @ X).
Qed.

Definition transport_e_fun A B (P : A -> Type) a a' (e : a = a') (e' : P a ≃ B) x
    :
      e_fun e' (transport_eq P e^ x) =
      e_fun (transport_eq (fun X => P X ≃ _) e e') x.
Proof.
  destruct e; cbn. reflexivity.
Qed.

Definition transport_e_fun' A B (P : A -> Type) a a' (e : a = a') (e' : B ≃ P a) x
    :
      transport_eq P e (e_fun e' x) =
      e_fun (transport_eq (fun X => _ ≃ P X) e e') x.
Proof.
  destruct e. reflexivity.
Qed.

Definition ap_inv_equiv {A B} (f : A -> B) `{IsEquiv _ _ f} x y : f x = f y -> x = y.
Proof.
  intro X. exact ((e_sect f x)^@ ap (e_inv f) X @ e_sect f y).
Qed.

Definition ap_inv_equiv' {A B} (f : A -> B) `{IsEquiv _ _ f} x y : e_inv f x = e_inv f y -> x = y.
Proof.
  intro X. exact ((e_retr f x)^@ ap f X @ e_retr f y).
Qed.

Definition eq_is_path {A} {x y:A} : eq x y -> x = y.
Proof.
  destruct 1. reflexivity.
Qed.

#[universes(collapse_sort_variables=no)]
Definition isequiv_ap (A B:Type) {H : A ≃ B} a a' :
  (e_fun H a = e_fun H a') -> (a = a').
Proof.
  intro X. apply (ap (e_inv' H)) in X. exact ((e_sect' H a)^ @ X @ e_sect' H _).
Qed.

Definition transport_equiv A X (a b:A) Q (e : a = b) (x : Q a) (e' : Q b ≃ X):
  e_fun e' (transport_eq Q e x) =
  e_fun
    (transport_eq (fun X : A => Q X ≃ _) e^
       e') x.
Proof.
  destruct e;cbn. reflexivity.
Qed.

Definition inversionS n m : S n = S m -> n = m.
  inversion 1; reflexivity.
Defined.

Inductive Empty@{s;} : Type@{s;0} := .

Definition zeroS n : O = S n -> Empty.
  inversion 1.
Defined.

Inductive le (n : nat) : nat -> Prop :=
    le_n : le n n | le_S : forall m : nat, le n m -> le n (S m).

Infix "<=" := le.

Definition le_rect : forall (n : nat) (P : forall n0 : nat, le n n0 -> Prop),
       P n (le_n n) ->
       (forall (m : nat) (l : le n m), P m l -> P (S m) (le_S n m l)) -> forall (n0 : nat) (l : le n n0), P n0 l :=
fun (n : nat) (P : forall n0 : nat, le n n0 -> Prop) (f : P n (le_n n))
  (f0 : forall (m : nat) (l : le n m), P m l -> P (S m) (le_S n m l)) =>
fix F (n0 : nat) (l : le n n0) {struct l} : P n0 l :=
  match l as l0 in (le _ n1) return (P n1 l0) with
  | le_n _ => f
  | le_S _ m l0 => f0 m l0 (F m l0)
  end.

Definition inv_eq m : eq (S m) m -> False.
  induction m.
  - inversion 1.
  - intro e. assert (eq (S m) m). inversion e. exact e. auto.
Defined.

Fixpoint apply_S_n (n:nat) m : nat :=
  match n with O => S m
          | S n => S (apply_S_n n m)
  end.

Definition apply_prop n m : eq (apply_S_n n (S m)) (S (apply_S_n n m)).
Proof.
  induction n. reflexivity. cbn. f_equal; auto.
Defined.

Definition inv_eq_gen m : forall n, eq (apply_S_n n m) m -> False.
Proof.
  induction m. destruct n; cbn; intro; inversion H.
  - intros. rewrite apply_prop in H. inversion H. apply (IHm _ H1).
Defined.

Definition inv_leq m : forall n, apply_S_n n m <= m -> False.
  induction m.
  - destruct n; cbn; intro; inversion H.
  - intros n e. rewrite apply_prop in e. inversion e.
    + apply (inv_eq_gen _ _ H0).
    + apply (IHm (S n) H0).
Defined.

Definition ap2_inv {A A' B:Type} (f:A -> A' -> B) {x y:A} (p:x = y)
  {x' y':A'} (q:x' = y') : (ap2 f p q)^ = ap2 f p^ q^.
  destruct p, q. reflexivity.
Defined.

Definition ap2_pp {A A' B:Type} (f:A -> A' -> B) {x y z:A} (p:x = y) (p':y = z)
           {x' y' z' :A'} (q:x' = y') (q':y' = z') :
  ap2 f p q @ ap2 f p' q' =  ap2 f (p @ p') (q @ q').
  destruct p, q. reflexivity.
Defined.

Ltac etransitivity := refine (_ @_).


#[universes(collapse_sort_variables=no)]
Definition Funext := forall (A : Type) (P : A -> Type) (f g : forall a:A, P a), (forall x, f x = g x) -> f = g.
(* IsEquiv (@apD10 A P f g). *)

(* The frawework relies on the univalence axiom and functional extensionality *)

(* Axiom univalence : forall A B, IsEquiv (eq_to_equiv A B). *)
#[universes(collapse_sort_variables=no)]
Axiom funext : Funext.

Definition transport_apD10 A B (f g : forall x:A, B x)
           (P : forall x:A, B x -> Type)
           (e : f = g) x v: transport_eq (fun X => P x (X x))
                                                       e v
                                          = transport_eq (fun X => P x X)
                                                (apD10 e x) v.
  destruct e. reflexivity.
Qed.

(* Definition transport_funext {A B} {f g : forall x:A, B x}
           (P : forall x:A, B x -> Type) x
           (v : P x (f x)) (e : forall x, f x = g x)
            : transport_eq (fun X => P x (X x))
                                                       (e_inv apD10 e) v
                                          = transport_eq (fun X => P x X)
                                                (e x) v.
Proof.
  rewrite transport_apD10. rewrite e_retr. reflexivity.
Defined. *)

(* for minor differences between Prop and Type (coming from impredicativity)  *)
(* we need to state again univalence for Prop, even if in principle Prop is  *)
(* a subtype of Type *)

Definition Equiv_id_P (A:Prop) : A ≃ A :=
  BuildEquiv _ _ id (BuildIsEquiv _ _ _ id (fun _ => idpath) (fun _ => idpath) (fun _ => idpath)).

Definition eq_to_equiv_P (A B:Prop) : A = B -> A ≃ B :=
  fun e => @transport_eq Prop (fun X => A ≃ X) A B e (Equiv_id_P A).

Definition UIP (A:SProp) (x y : A) : x = y := idpath.

(* This property has been proven in https://github.com/HoTT/HoTT/blob/86c3bc0edb5c0dc2be76b47e4bbe0b348929a856/theories/EquivalenceVarieties.v#L86 *)


Definition IsContr (A:Type) := { x : A & forall y, x = y}.
Existing Class IsContr.

Definition isequiv_hprop {A B : Type} {f: A -> B} : forall (e e' : IsEquiv f), e = e'.
Admitted.

Definition path_Equiv {A B} {f g: A ≃  B} : e_fun f = e_fun g -> f = g.
  destruct f, g. cbn. intro e. destruct e.
  destruct (isequiv_hprop e_isequiv0 e_isequiv1). reflexivity.
Qed.

Definition Equiv_inverse_inverse A B (e : A ≃ B) : Equiv_inverse (Equiv_inverse e) = e.
  intros. apply path_Equiv. reflexivity.
Defined.

Definition equiv_ind {A B} {f : A ≃  B} (P : B -> Type)
  : (forall x:A, P (e_fun f x)) -> forall y:B, P y
  := fun g y => transport_eq P (e_retr' f y) (g (e_inv' f y)).

Definition apD10_gen (A : Type) (B : A -> Type) (f g : forall x : A, B x) :
  f = g -> forall x y (e:y = x), f x = e # g y.
  intros H x y e. destruct e. cbn. apply apD10. auto.
Qed.