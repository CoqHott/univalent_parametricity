(************************************************************************)
(* This file contains basic definitions of UR that are helpful for many examples  *)
(************************************************************************)

Require Import HoTT UR URTactics DecidableEq FP ADT.

(*! nat !*)

Instance FP_nat : nat ⋈ nat := _ URType_Refl_decidable nat DecidableEq_eq_nat.

(*! FP for nat_rect !*)

Definition FP_nat_rect : nat_rect ≈ nat_rect.
  intros X X' [H H'] P P' e0 Q Q' e_S n n' en.    
  equiv_elim. exact (e_S n n eq_refl _ _ IHn).
Defined.

Definition FP_nat_rect_cst (P Q:Type) (e : P ≈ Q) :
  nat_rect (fun _ => P) ≈ nat_rect (fun _ => Q) :=
  FP_nat_rect (fun _ => P) (fun _ => Q)
              {| transport_ := Transportable_cst nat P ; ur_type := fun _ _ _ => e |}.

(*! bool !*)

Instance FP_bool : bool ⋈ bool := URType_Refl_decidable bool DecidableEq_eq_bool.

(*! List !*)

Definition inversion_cons {A} {l l':list A} {a a'} : a :: l = a' :: l' -> (a = a') * (l = l').
  inversion 1. split; reflexivity.
Defined. 

Instance Transportable_list A (P: list A -> Type)
         (HP : forall (P:A->Type), Transportable P) : Transportable P.
Proof.
  unshelve econstructor.
  - intros n m. revert P; revert m.
    induction n; intro m; destruct m; intros P e. 
    + apply Equiv_id.
    + inversion e.
    + inversion e.
    + pose (inversion_cons e). specialize (IHn _ (fun n => P (a :: n)) (snd p)).
      cbn in IHn. eapply equiv_compose; try exact IHn. apply (HP (fun x => P (x :: m))).
      exact (fst p). 
  - cbn. intro n; revert P; induction n; cbn; intro P. 
    + reflexivity.
    + rewrite transportable_refl. rewrite (IHn (fun n => P (a :: n))).
      apply path_Equiv. reflexivity.
Defined. 

Instance Equiv_List A B (e:A ≃ B) : list A ≃ list B.
Proof.
    equiv_adt2 (@list_rect _) (@nil _) (@cons _).
Defined.


Instance Equiv_UR_list A B (R R' : A -> B -> Type)
         (e:forall a b, R a b ≃ R' a b) : forall l l' , UR_list R l l' ≃ UR_list R' l l'.
Proof.
  intros. 
  equiv_adt2 (@UR_list_rect _ _ _) (@UR_list_nil _ _ _) (@UR_list_cons _ _ _).
Defined.

(* ET: renamed that one since inversion_cons already exists, in a different form, above *)
Definition inversion_cons' {A a a'} {l l':list A} (X: a::l = a'::l') :
  {p : (a = a') * (l = l') & X = ap2 cons (fst p) (snd p)}
  := match X with
       | eq_refl => ((eq_refl ,eq_refl) ; eq_refl) end.

Definition eq_nil_refl {A} {l:list A} (e : [] = l) :
  match l return [] = l -> Type with [] => fun e => e = eq_refl | _ => fun _ => False end e.
Proof.
  destruct e. reflexivity. 
Defined.

Definition transport_UR_list_cons A B {equ:A ≃ B} (einv := Equiv_inverse equ)
           (a :A) a' a'' (l l': list A ) (l'':list B) (h:a'=a) (e:l'=l)
  (E: a = ↑ a'') (E': UR_list (fun a b => a = ↑b) l l''):
   transport_eq
    (fun X => UR_list  (fun a b => a = ↑b) X (a''::l''))
    (ap2 cons h e)^ (UR_list_cons _ E E')  =
  UR_list_cons (fun a b => a = ↑b) (transport_eq (fun X => eq A X _) h^ E)
               (transport_eq (fun X : list A => UR_list _ X _) e^ E').
  destruct h, e. reflexivity.
Defined.

Definition UR_List_is_eq A B {e:A ≃ B} (e_inv := Equiv_inverse e) :
  forall l l' , UR_list (fun a b => a = ↑b) l l' ≃ (l = ↑ l').
Proof.
  intros l l'. 
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  induction 1; typeclasses eauto. 
  intro x. refine (transport_eq (fun X => UR_list _ X l') x^ _).
  clear x. induction l'; typeclasses eauto. 
  cbn. intro x. induction x; cbn.
  typeclasses eauto. etransitivity. apply transport_UR_list_cons.
  apply ap2. rewrite transport_paths_l. rewrite concat_refl. apply inv2.
  exact IHx.
  cbn. intro x. generalize dependent l'.  
  induction l; cbn; intro l'; destruct l'; intro X.
  cbn. pose (X0 := eq_nil_refl X). cbn in X0. rewrite X0. reflexivity. 
  inversion X. inversion X. 
  cbn in *. pose (inversion_cons' X). destruct s as [s s']. 
  rewrite s'. etransitivity. apply ap. apply transport_UR_list_cons.
  cbn. apply (ap2 (fun e e' => ap2 cons e e')).
  rewrite transport_paths_l. rewrite concat_refl. apply inv2.
  apply IHl. 
Defined. 

    
Definition URIsUR_list {A B : Type} {H : ur A B} (l l':list A) : (l = l') ≃ (l ≈ (↑ l')).
Proof.
  pose (einv := Equiv_inverse (equiv H)). 
  eapply Equiv_inverse. eapply equiv_compose. 
  unshelve apply Equiv_UR_list.
  exact (fun a b => a = ↑ b).
  intros. cbn. apply alt_ur_coh. apply H. 
  eapply equiv_compose. eapply UR_List_is_eq.
  refine (transport_eq (fun X => (l = X) ≃ _) (e_sect _ l')^ _). refine (Equiv_id _).
Defined. 

Definition FP_List : list ≈ list.
  split ; [typeclasses eauto | ]. 
  intros A B e. 
  econstructor; try typeclasses eauto. econstructor.
  intros a b. apply URIsUR_list.
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.    
Defined.


Definition FP_List_rect : @list_rect ≈ @list_rect.
Proof.
  cbn. intros A B e X X' eX P P' P_nil Q Q' Q_cons l l' el. 
  induction el; typeclasses eauto with typeclass_instances. 
Defined.

Hint Extern 0 (list_rect _ ?X ?P ?Q ?l ≈ list_rect _ ?X' ?P' ?Q' ?l') =>
unshelve notypeclasses refine (FP_List_rect _ _ _ X X' _ P P' _ Q Q' _ l l' _); intros
:  typeclass_instances.

Definition FP_cons : @cons ≈ @cons. 
Proof. 
  typeclasses eauto. 
Defined.

Definition FP_nil : @nil ≈ @nil.
Proof. 
  typeclasses eauto.  
Defined.

Instance Equiv_List_instance : forall x y : Type, x ⋈ y -> (list x) ⋈ (list y) := ur_type FP_List.



Require Import Vector.


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
  intros; induction l; inversion H; simpl; reflexivity.
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






