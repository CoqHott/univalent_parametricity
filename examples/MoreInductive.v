Require Import HoTT HoTT_axioms UR URTactics ADT FP Record DecidableEq URStdLib.

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
(* ET: BROKEN, sorry... *)
Definition FP_Equiv : @Equiv ≈ @Equiv.
Proof.
  cbn;   split ; [typeclasses eauto | ]; intros.
  unshelve refine (UR_Type_Equiv _ _ _). cbn. 
  unshelve refine (UR_Type_Equiv' _ _ _).
  erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn ; intros .
  typeclasses eauto with typeclass_instances. 
  split; tc.
Defined. 

Hint Extern 0 (UR (_ ≃ _) (_ ≃ _)) => refine (Ur (ur_type (FP_Equiv _ _ _) _ _ _)) : typeclass_instances.


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


(* ET: should be in UR? *)
Definition Isequiv_ur_hprop A A' B B' (H : A ⋈ A')(H' : B ⋈ B') (f:A->B) (g:A'->B')
           (e : IsEquiv f) (e' : IsEquiv g)
           (efg:f ≈ g) : e ≈ e'. 
  intros; apply ur_hprop. apply hprop_isequiv. 
Defined.   

(* ET: should be in FP *)
Definition FP_ap:  @ap ≈ @ap.
  intros A A' eA B B' eB f f' ef x x' ex y y' ey p p' ep. 
  cbn in *.
  induction ep. apply UR_eq_refl. 
Defined.

Hint Extern 0 (UR_eq _ _ _ _ _ _ _ _ _ _ _ ) => 
  erefine (FP_ap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) : typeclass_instances.


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


(* ET: move all stuff related to Vector in a separate file *)
(* could have Vector.v in theories (the universe polymorphic version of Vector),
   and Vector.v in examples (this development)? or StdLib? ... *)

(*! Establishing FP for Vector !*)

(* We go through the equivalence Vector.t A n ≃ {l : list B & length l ≈ n} *)

Require Import Vector.

Definition vector A (n:nat) := Vector.t A n.
Definition vnil {A} := Vector.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := Vector.cons A val _ v.


Definition inversionS n m : S n = S m -> n = m.
  inversion 1. reflexivity.
Defined. 

Definition zeroS n : 0 = S n -> False.
  inversion 1.
Defined.


Definition Equiv_Vector_not_eff A B (e:A ≃ B) n n' (en :n = n') : Vector.t A n ≃ Vector.t B n'.
Proof.
  equiv_adt2 (@Vector.t_rect _) (@Vector.nil _) (@Vector.cons _).
Defined.

Definition Equiv_Vector_fun A B (e:A ≃ B) n n' (en : n = n') : Vector.t A n -> Vector.t B n'.
Proof.
  intros v; generalize dependent n'. 
  induction v; destruct n'; intros. 
  apply_cons (@Vector.nil _).
  destruct (zeroS _ en).
  destruct (zeroS _ en^).
  apply univalent_transport in h. 
  unshelve eapply (@Vector.cons _ h _ _).
  apply IHv. 
  exact  (inversionS _ _ en).
Defined.   

Instance Equiv_Vector A B (e:A ≃ B) n n' (en :n = n') : Vector.t A n ≃ Vector.t B n'.
Proof.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  apply  Equiv_Vector_fun; auto.
  pose (Equiv_inverse e); pose en^. apply  Equiv_Vector_fun; auto.
  intro v. destruct en. induction v; intros; cbn.  reflexivity.
  apply (ap2 (fun a => @Vector.cons _ a _)). 
  typeclasses eauto with equiv typeclass_instances. auto. 
  intro v. destruct en. induction v; intros; cbn.  reflexivity.
  apply (ap2 (fun a => @Vector.cons _ a _)). 
  typeclasses eauto with equiv typeclass_instances. auto. 
Defined.


Definition length {A} (l:list A) : nat := list_rect _ (fun _ => (nat:Type)) 0 (fun _ _ n => S n) l.

Fixpoint vector_to_list A B (e: A ≃ B) (n m:nat) (en : n = m) :
  vector A n -> {l : list B & length l ≈ m}.
   refine (
  match n, m return n = m -> vector A n -> {l : list B & length l = m} with
  | O,O => fun en _ => ([]; _)
  | S n, S m => fun en v => let IHn :=  vector_to_list A B e n m _ (Vector.tl v) in
           (e (Vector.hd v) :: IHn.1 ; ap S (IHn.2))
  |  _ , _ => _ end en).
   - destruct en. reflexivity.
   - inversion 1.
   - inversion 1.
   - apply inversionS; auto.
Defined. 

Fixpoint list_to_vector_ A B (e: A ≃ B) (n m:nat) (en : n = m) (l:list A) (H : length l ≈ n) {struct n}: Vector.t B m.
  destruct n, m.
  - exact (nil _).
  - inversion en. 
  - inversion en. 
  - destruct l.
    + destruct (zeroS _ H).
    + exact (vcons (e a) (list_to_vector_ _ _ e _ _ (inversionS _ _ en) l (inversionS _ _ H))).
Defined. 

Definition list_to_vector A B (e: A ≃ B) (n m:nat) (en: n = m) : {l : list A & length l ≈ n} -> Vector.t B m
  := fun x => list_to_vector_ A B e n m en x.1 x.2.
                                                                                 
Definition transport_vector A n a (s:vector A n) k (e : n = k):
  ap S e # vcons a s  = vcons a (e # s).
  destruct e. reflexivity.
Defined.

Definition tl {A} (l:list A) : list A:=
    match l with
      | [] => []
      | a :: m => m
    end.

Definition S_length :
  forall (A : Type) (l : list A) (n: nat),
    length l = S n -> length (tl l) = n.
  intros; induction l; inversion X; simpl; reflexivity.
Defined.

Instance IsEquiv_vector_list A B e n m en  : IsEquiv (vector_to_list A B e n m en).
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - exact (list_to_vector B A (Equiv_inverse e) m n en^). 
  - (* Sect (nvector_to_nlist a) (nlist_to_nvector a) *)
    destruct en. induction n.
    + intro v. apply Vector.case0. reflexivity.
    + intro v. revert IHn. 
      refine (Vector.caseS (fun n v => (forall x : vector A n,
                                      list_to_vector _ _ _ n _ _ (vector_to_list _ _ _ n _ _ x) = x)
                                    -> list_to_vector _ _ _ (S n) _ _ (vector_to_list _ _ _ (S n) _ _ v) = v) _ _).
      clear. intros. simpl. unfold list_to_vector. cbn. 
      apply (ap2 vcons). exact (e_sect e h). specialize (X t). destruct (vector_to_list _ _ _ n _ _ t), u. exact X. 
  - (* Sect (nlist_to_nvector a) (nvector_to_nlist a) *)
    destruct en. induction n.
    + intro rl. simpl. destruct rl as [l Hl].
      destruct l; try inversion Hl. 
      apply path_sigma_uncurried. unshelve eexists. apply is_hset. 
    + intro rl. destruct rl as [l Hl].
      destruct l. inversion Hl.  
      apply path_sigma_uncurried. unshelve eexists. 
      simpl. simpl in Hl.
      assert (length l = n). inversion Hl. reflexivity. 
      assert (Hl = ap S X). apply is_hset.
      rewrite X0. unfold list_to_vector; simpl. apply ap2.
      exact (e_retr e b). 
      specialize (IHn (l;X)).
      destruct X. simpl. cbn. exact (IHn..1). apply is_hset.
Defined.

Set Printing Universes. 

Typeclasses Opaque vector_to_list list_to_vector.

Hint Extern 0 => progress (unfold length) :  typeclass_instances.


Instance Equiv_vector_list (A B:Type) {H: A ≃ B} (n n':nat) (en : n ≈ n')
  : Vector.t A n ≃ {l : list B & length l ≈ n'}
    := BuildEquiv _ _ _ (IsEquiv_vector_list A B H n n' en).

Definition Equiv_Vector_id A n :Equiv_Vector A A (Equiv_id A) n n  eq_refl = Equiv_id (t A n).
apply path_Equiv, funext. intro v.
induction v. reflexivity. cbn. apply ap. exact IHv. 
Defined. 

Instance Transportable_vector A : Transportable (t A).
unshelve econstructor. intros. 
apply Equiv_Vector. apply Equiv_id. auto.
apply Equiv_Vector_id. 
Defined.

Definition Equiv_vector_list_
  : Vector.t ≈ (fun A n => {l : list A & length l ≈ n}).
  intros A B e. econstructor. tc. intros n n' en. unshelve econstructor. 
  - econstructor.
    intros v l. exact ((vector_to_list A B (equiv e) n n' en v) = l).
  - econstructor. intros v v'. cbn.
    apply (@isequiv_ap _ _ (Equiv_vector_list _ _ _ _ _)). 
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined. 

Hint Extern 0 (UR_Type (t ?A ?n) _) =>
erefine (ur_type (Equiv_vector_list_ _ _ _) _ _ _) : typeclass_instances.

Hint Extern 0 (UR_Type (vector ?A ?n) _) =>
erefine (ur_type (Equiv_vector_list_ _ _ _) _ _ _) : typeclass_instances.

Hint Extern 0 (t ?A ?n ≃ _) =>
erefine (ur_type (Equiv_vector_list A _ n)) : typeclass_instances.

Instance Equiv_list_vector (A B:Type) {H : ur B A} n : {l : list A & length l = n} ≃ Vector.t B n | 1 := Equiv_inverse _.

Definition Equiv_list_vector_ : (fun A n => {l : list A & length l ≈ n}) ≈ Vector.t.
Proof.
  cbn. intros A B e.
  split.
  unshelve econstructor. intros.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  intros [l Hl]; exists l. exact (Hl @ H). 
  intros [l Hl]; exists l. exact (Hl @ H^).
  intros; cbn. destruct x0. apply path_sigma_uncurried. exists eq_refl.
  cbn. apply is_hset.
  intros; cbn. destruct x0. apply path_sigma_uncurried. exists eq_refl.
  cbn. apply is_hset.
  cbn. intros ; cbn. apply path_Equiv. cbn. apply funext. intros [l Hl]. destruct Hl; reflexivity. 
  intros n n' en.
  apply UR_Type_Inverse. apply Equiv_vector_list_. apply UR_Type_Inverse. 
  typeclasses eauto. apply eq_sym. exact en. 
Defined. 

Hint Extern 0 (UR_Type _ (vector ?A ?n)) =>
erefine (ur_type (Equiv_list_vector_ _ _ _) _ _ _) : typeclass_instances.

Hint Extern 0 (UR_Type _ (t ?A ?n)) =>
erefine (ur_type (Equiv_list_vector_ _ _ _) _ _ _) : typeclass_instances.

Inductive UR_vector {A B} (R : A -> B -> Type) : forall (n n':nat) (en : n ≈ n'),
  Vector.t A n -> Vector.t B n' -> Type :=
  UR_vector_nil : UR_vector R 0 0 eq_refl (nil A) (nil B) 
| UR_vector_cons : forall {a b n n' v v'},
    (R a b) -> forall (en : n ≈ n'), (UR_vector R n n' en v v') ->
    UR_vector R (S n) (S n') (ap S en) (vcons a v) (vcons b v').


(* ET: admit here *)
Definition FP_Vector : Vector.t ≈ Vector.t.
  intros A B e. cbn in e. split.
  typeclasses eauto. 
  
  intros n n' en.
  unshelve eexists.
  - unshelve econstructor. refine (UR_vector ur n n' en).  
  - apply admit. 
    (* econstructor. intros v v'. *)
    (* cbn. unfold univalent_transport. *)
    (* assert (Equiv_vector_list A A (H:=Equiv_id A) n n' en v'= *)
    (*          (vector_to_list B A (Equiv_inverse (equiv e)) n' n' eq_refl *)
    (*                          ((Equiv_Vector A B (equiv e) n n' en) v'))). *)
    (* clear. destruct en. cbn. unfold univalent_transport. *)
    (* induction v'. reflexivity. cbn.  *)
    (* apply path_sigma_uncurried. unshelve eexists. *)
    (* cbn. apply ap2. apply eq_sym. apply e_sect. *)
    (* apply ap. exact IHv'. cbn. apply is_hset. cbn in X.  *)
    (* rewrite <- X.   *)
    (* pose (@Ur_Coh _ _ (@ur_type nat nat _ _ _ (Equiv_vector_list_ A A (ur_refl A)) _ _ en)). *)
    (* exact (@ur_coh _ _ _ _ u v v').  *)
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined.

Instance Equiv_Vector_instance : forall x y : Type, x ⋈ y -> forall n n' (e:n=n'), (Vector.t x n) ⋈ (Vector.t y n') :=
  fun x y e n n' en => ur_type (FP_Vector x y e) n n' en. 




(* should be somewhere else: tactics? *)
Hint Extern 0 (UR_Type Set Set) => exact FP_Type : typeclass_instances. 



(* Instance compat_nat_N : nat ⋈ N := UR_Type_Inverse _ _ compat_N_nat. *)

(* ET: where should the following be? *)

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

Definition inv_eq m : Logic.eq (S m) m -> False.
  induction m.
  - inversion 1.
  - intro e. assert (Logic.eq (S m) m). inversion e. exact e. auto.
Defined. 

Fixpoint apply_S_n (n:nat) m : nat :=
  match n with 0 => S m
          | S n => S (apply_S_n n m)
  end. 

Definition apply_prop n m : Logic.eq (apply_S_n n (S m)) (S (apply_S_n n m)).
Proof.
  induction n. reflexivity. cbn. f_equal; auto.
Defined. 

Definition inv_eq_gen m : forall n, Logic.eq (apply_S_n n m) m -> False.
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

Instance Decidable_leq n m : DecidableEq (n <= m).
constructor. revert m n. intros n m.  
assert (forall n n'
(e : n = n'), forall (le_mn1 : m <= n) (le_mn2 : m <= n'), Logic.eq (e # le_mn1) le_mn2).
clear.
intros. revert n' e le_mn2.
induction le_mn1 using le_rect; intros. 
- destruct le_mn2 using le_rect.
  + assert (e = eq_refl). apply is_hset. rewrite X. reflexivity.
  + assert False. clear - e le_mn2. rewrite e in le_mn2. apply (inv_leq _ 0 le_mn2). destruct H.
- destruct le_mn2 using le_rect; try clear IHle_mn2.
  + assert False. clear - e le_mn1. rewrite <- e in le_mn1. apply (inv_leq _ 0 le_mn1). destruct H. 
  + assert (m0 = m1). clear - e. inversion e. reflexivity.
    specialize (IHle_mn1 _ X le_mn2). rewrite <- IHle_mn1.
    assert (e = ap S X). apply is_hset. rewrite X0 in *. clear e X0.
    destruct X. reflexivity. 
- intros a b; apply inl. destruct (H _ _ eq_refl a b). reflexivity. 
Defined. 


