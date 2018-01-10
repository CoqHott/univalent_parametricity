Require Import HoTT Tactics UR URTactics FP Record.

Set Universe Polymorphism.


Definition inversionS n m : S n = S m -> n = m.
  inversion 1. reflexivity.
Defined. 

Definition zeroS n : 0 = S n -> False.
  inversion 1.
Defined. 

(*! Establishing FP for nat_rect !*)

Definition FP_nat_rect : nat_rect ≈ nat_rect.
  intros X X' [H H'] P P' e0 Q Q' e_S n n' en.   
  equiv_elim. exact (e_S n n eq_refl _ _ IHn).
Defined.

(*! non effective FP for list !*)
Definition FP_List' : list ≈ list.
  (* this instance of transportable is on Type, we can only use the default one*)
  cbn. split; [apply Transportable_default | ].
  intros A B e.
  destruct (e_inv (eq_to_equiv _ _) (equiv e)).
  apply Canonical_UR.
  apply Equiv_id.
Defined.

(*! Establishing FP for Vector !*)

(* We go through the equivalence Vector.t A n ≃ {l : list B & length l ≈ n} *)

Require Import Vector.

Definition vector A (n:nat) := Vector.t A n.
Definition vnil {A} := Vector.nil A.
Definition vcons {A n} (val:A) (v:vector A n) := Vector.cons A val _ v.

Definition Equiv_Vector_not_eff A B (e:A ≃ B) n n' (en :n = n') : Vector.t A n ≃ Vector.t B n'.
Proof.
  equiv_adt2 (@Vector.t_rect _) (@Vector.nil _) (@Vector.cons _).
Defined.

Definition Equiv_Vector_fun A B (e:A ≃ B) n n' (en :n = n') : Vector.t A n -> Vector.t B n'.
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
      apply path_sigma_uncurried. unshelve eexists. 
      reflexivity. simpl in *. apply nat_Hset. 
    + intro rl. destruct rl as [l Hl].
      destruct l. inversion Hl.  
      apply path_sigma_uncurried. unshelve eexists. 
      simpl. simpl in Hl.
      assert (length l = n). inversion Hl. reflexivity. 
      assert (Hl = ap S X). apply nat_Hset.
      rewrite X0. unfold list_to_vector; simpl. apply ap2.
      exact (e_retr e b). 
      specialize (IHn (l;X)).
      destruct X. simpl. cbn. exact (IHn..1). apply nat_Hset.
Defined.

Typeclasses Opaque vector_to_list list_to_vector.

Hint Extern 0 => progress (unfold length) :  typeclass_instances.

Definition UR_Equiv_refl (A B:Type) (e:A ≃ B) (e_inv := Equiv_inverse e) `{UR A B} : UR B B :=
  {| ur := fun b b' => ↑ b ≈  b' |}.

Instance Equiv_vector_list (A B:Type) {H: A ≃ B} (n n':nat) (en : n ≈ n')
  : Vector.t A n ≃ {l : list B & length l ≈ n'}
    := BuildEquiv _ _ _ (IsEquiv_vector_list A B H n n' en).

Axiom admit : forall A, A. 

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
  intros A B e. cbn in e. cbn. split. typeclasses eauto. 
  intros n n' en.
  unshelve eexists.
  - eapply UR_Equiv'. apply Equiv_vector_list; typeclasses eauto.
    unshelve eapply URSigma. apply UR_list_. apply UR_gen.
    intros. cbn.
    refine (Ur (ur_type (FP_eq nat nat FP_nat _ _ _) _ _ _ )).
    unfold length. refine (FP_List_rect B B (ur_refl B) _ _ {| transport_ := _; ur_type := _|} _ _ _ _ _ _ x y H); typeclasses eauto.
    typeclasses eauto.
  - econstructor. intros v v'.
    cbn. eapply equiv_compose. apply isequiv_ap.
    unfold univalent_transport.
    assert (forall (l l':{l : list B & length l ≈ n'}), (l = l')
  ≃ {H
    : UR_list (eq B) l .1
        l' .1 &
    (l.2 =
    eq_map_inv nat nat FP_nat (length l.1)
      (length l' .1)
      (FP_List_rect B B (ur_refl B) (fun _ : list B => nat)
                    (fun _ : list B => nat)
                    {| transport_ := _; ur_type := fun _ _ _ => FP_nat|}
                    0 0 eq_refl
         (fun (_ : B) (_ : list B) (n0 : nat) => S n0)
         (fun (_ : B) (_ : list B) (n0 : nat) => S n0)
         (fun (x0 y0 : B) (_ : x0 = y0) (x1 y1 : list B)
            (_ : UR_list (fun a b : B => a = b) x1 y1) (x2 y2 : nat) 
            (H2 : x2 = y2) => ap S H2) l.1
         l'.1 H) n' n' eq_refl
      l'.2)}).
    intros. 
    eapply equiv_compose. apply Equiv_inverse. apply equiv_path_sigma.
    unshelve eapply Equiv_Sigma.
    cbn. eapply UR_Type_Equiv'.
    unshelve refine (@ur_coh _ _ _ _ (@Ur_Coh _ _ (ur_type FP_List B B (@ur_refl_ _ _ _ _ URType_Refl  B))) _ _).
    cbn. assert (forall l, list_rect B (fun _ : list B => list B) []
       (fun (H0 : B) (_ H2 : list B) => H0 :: H2) l = l). clear. 
    induction l; cbn. reflexivity. apply ap. assumption.
    rewrite X. apply (@ur_refl_ _ _ _ _ URType_Refl).
    cbn. intros. destruct l, l'. cbn in *. destruct x.
    (* this instance of transportable is for the equality type, we can use the default one*)
    split ; [apply Transportable_default | ]. 
    cbn. intros. 
    match goal with | |- (u = ?u0) ⋈ (u = ?u1) => assert (u1 = u0) by apply is_hset end. 
    rewrite X. apply (@ur_refl_ _ _ _ _ URType_Refl).
    (* this instance of transportable is for the equality type, we can use the default one*)
    split ; [apply Transportable_default | ]. 
    cbn. intros.     match goal with | |- (u = ?u0) ⋈ (u = ?u1) => assert (u1 = u0) by apply is_hset end. 
    rewrite X. apply (@ur_refl_ _ _ _ _ URType_Refl).
    
    apply X. 
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

Definition FP_Vector : Vector.t ≈ Vector.t.
  intros A B e. cbn in e. split.
  typeclasses eauto. 
  
  intros n n' en.
  unshelve eexists.
  - pose (Equiv_inverse (equiv e)). eapply UR_Equiv. apply Equiv_vector_list; typeclasses eauto.
    apply Equiv_vector_list_. apply (@ur_refl_ _ _ _ _ URType_Refl). typeclasses eauto.
  - econstructor. intros v v'.
    cbn. unfold univalent_transport.
    assert (Equiv_vector_list A A (H:=Equiv_id A) n n' en v'=
             (vector_to_list B A (Equiv_inverse (equiv e)) n' n' eq_refl
                             ((Equiv_Vector A B (equiv e) n n' en) v'))).
    clear. destruct en. cbn. unfold univalent_transport.
    induction v'. reflexivity. cbn. 
    apply path_sigma_uncurried. unshelve eexists.
    cbn. apply ap2. apply eq_sym. apply e_sect.
    apply ap. exact IHv'. cbn. apply is_hset. cbn in X. 
    rewrite <- X.  
    pose (@Ur_Coh _ _ (@ur_type nat nat _ _ _ (Equiv_vector_list_ A A (ur_refl A)) _ _ en)).
    exact (@ur_coh _ _ _ _ u v v'). 
Defined.

Instance Equiv_Vector_instance : forall x y : Type, x ⋈ y -> forall n n' (e:n=n'), (Vector.t x n) ⋈ (Vector.t y n') :=
  fun x y e n n' en => ur_type (FP_Vector x y e) n n' en. 

Definition UREq A (x x' y y' : A) (H:x=x') (H':y=y') : UR (x = y) (x' = y') :=
  {| ur := fun e e' => H^ @ e @ H' = e' |}.

Hint Extern 0 (UR (_ = _)(_ = _)) => erefine (@UREq _ _ _ _ _ _ _) : typeclass_instances.

(*! Establishing FP for Expr !*)


Inductive Expr@{i} : Set -> Type@{i} :=
  I : nat -> Expr nat
| B : bool -> Expr bool
| Add : Expr nat -> Expr nat -> Expr nat
| Mul : Expr nat -> Expr nat -> Expr nat
| Eq  : Expr nat -> Expr nat -> Expr bool.

(* directly using univalence *)

Definition FP_Expr : Expr ≈ Expr.
Proof.
  cbn.
  (* this instance of transportable is on Type, we can only use the default one*)
  split; [apply Transportable_default | ].
  intros A B e. 
  rewrite (@e_inv _ _ _ (univalence _ _) (equiv e)).
  apply (@ur_refl_ _ _ _ _ URType_Refl).
Defined.

(* using the decomposition of a parametrized inductive type 
plus a fipoint *)

Inductive Expr_p : Set :=
  I_p : nat -> Expr_p 
| B_p : bool -> Expr_p 
| Add_p : Expr_p -> Expr_p -> Expr_p
| Mul_p : Expr_p -> Expr_p -> Expr_p
| Eq_p  : Expr_p -> Expr_p -> Expr_p.

Definition index_Expr@{i j} (E : Expr_p) (EType : Set) : Type@{i} :=
  Expr_p_rect@{j}
    (fun _ => Set -> Type@{i})
    (fun _ EType => @eq@{i} Set nat EType)
    (fun _ EType => @eq@{i} Set bool EType)
    (fun E X E' X' EType => ((X nat) * (X' nat) * (@eq@{i} Set nat EType))%type)
    (fun E X E' X' EType => ((X nat) * (X' nat) * (@eq@{i} Set nat EType))%type)
    (fun E X E' X' EType => ((X nat) * (X' nat) * (@eq@{i} Set bool EType))%type)
    E EType.

Definition Expr'@{i j} A := { E : Expr_p & index_Expr@{i j} E A}.

Definition I' : nat -> Expr' nat := fun n => (I_p n ; eq_refl). 
Definition B' : bool -> Expr' bool := fun b => (B_p b ; eq_refl). 
Definition Add' : Expr' nat -> Expr' nat  -> Expr' nat
  := fun e e0 => (Add_p e.1 e0.1; ((e.2,e0.2,eq_refl))).
Definition Mul' : Expr' nat -> Expr' nat  -> Expr' nat
  := fun e e0 => (Mul_p e.1 e0.1; ((e.2,e0.2,eq_refl))).
Definition Eq' : Expr' nat -> Expr' nat  -> Expr' bool
  := fun e e0 => (Eq_p e.1 e0.1; ((e.2,e0.2,eq_refl))).

Section Expr'.

Variable (P : forall P : Set, Expr' P -> Type)
   (PI: forall n : nat, P nat (I' n))
   (PB : forall b : bool, P bool (B' b)) 
   (PAdd : forall e : Expr' nat,
           P nat e -> forall e0 : Expr' nat, P nat e0 ->
                                      P nat (Add' e e0))
   (PMul : forall e : Expr' nat,
       P nat e -> forall e0 : Expr' nat, P nat e0 -> P nat (Mul' e e0))
   (PEq : forall e : Expr' nat,
        P nat e -> forall e0 : Expr' nat, P nat e0 -> P bool (Eq' e e0)) .
  
Definition Expr'_rect :
       forall (P0: Set) (e : Expr' P0), P P0 e.
Proof.
  intros. destruct e as [x e].
  revert e. revert P0. induction x; cbn; intros P0 e.
  destruct e. exact (PI n).
  destruct e. exact (PB b).
  destruct e as ((e1,e2),e). destruct e.
  refine (PAdd (_;_) _ (_;_) _).
  apply IHx1. apply IHx2. 
  destruct e as ((e1,e2),e). destruct e.
  refine (PMul (_;_) _ (_;_) _).
  apply IHx1. apply IHx2. 
  destruct e as ((e1,e2),e). destruct e.
  refine (PEq (_;_) _ (_;_) _).
  apply IHx1. apply IHx2. 
Defined. 

Definition Expr'_rect_Add : forall e1 e2,
                Expr'_rect _ (Add' e1 e2) = PAdd _ (Expr'_rect _ e1) _ (Expr'_rect _ e2).
Proof.
  destruct e1, e2. reflexivity.
Defined. 

Definition Expr'_rect_Mul : forall e1 e2,
                Expr'_rect _ (Mul' e1 e2) = PMul _ (Expr'_rect _ e1) _ (Expr'_rect _ e2).
Proof.
  destruct e1, e2. reflexivity.
Defined. 

Definition Expr'_rect_Eq : forall e1 e2,
                Expr'_rect _ (Eq' e1 e2) = PEq _ (Expr'_rect _ e1) _ (Expr'_rect _ e2).
Proof.
  destruct e1, e2. reflexivity.
Defined. 
End Expr'. 

Definition Expr_Expr_p_fun@{i j} (A:Set) (E:Expr@{i} A) :
  Expr'@{i j} A :=
  Expr_rect (fun A _ => Expr'@{i j} A)
            (fun n => I' n)
            (fun b => B' b)
            (fun _ e _ e' => Add' e e')
            (fun _ e _ e' => Mul' e e')
            (fun _ e _ e' => Eq' e e') _ E.

Definition Expr_Expr_p_inv@{i j} (A:Set) (E:Expr'@{i j} A) :
  Expr@{i} A :=
  Expr'_rect (fun A _ => Expr@{i} A)
            (fun n => I n)
            (fun b => B b)
            (fun _ e _ e' => Add e e')
            (fun _ e _ e' => Mul e e')
            (fun _ e _ e' => Eq e e') _ E.

Definition Expr_Expr_p@{i j} (A:Set) : Expr@{i} A ≃ { E : Expr_p & index_Expr@{i j} E A}. 
Proof. 
  unshelve econstructor.
  apply Expr_Expr_p_fun. 
  unshelve eapply isequiv_adjointify.
  - apply Expr_Expr_p_inv.
    Opaque Expr'_rect. 
  - intro E. induction E; try reflexivity.
    unfold Expr_Expr_p_inv. cbn.
    rewrite Expr'_rect_Add. 
    refine (transport_eq (fun X => _ = Add X _) IHE1 _).
    refine (transport_eq (fun X => _ = Add _ X) IHE2 _).
    reflexivity. 
    unfold Expr_Expr_p_inv. cbn.
    rewrite Expr'_rect_Mul. 
    refine (transport_eq (fun X => _ = Mul X _) IHE1 _).
    refine (transport_eq (fun X => _ = Mul _ X) IHE2 _).
    reflexivity. 
    unfold Expr_Expr_p_inv. cbn.
    rewrite Expr'_rect_Eq. 
    refine (transport_eq (fun X => _ = Eq X _) IHE1 _).
    refine (transport_eq (fun X => _ = Eq _ X) IHE2 _).
    reflexivity. 
  - Transparent Expr'_rect.
    revert A. apply Expr'_rect; intros; try reflexivity. 
    unfold Expr_Expr_p_inv. 
    rewrite Expr'_rect_Add. cbn. apply ap2. exact X. exact X0. 
    unfold Expr_Expr_p_inv. 
    rewrite Expr'_rect_Mul. cbn. apply ap2. exact X. exact X0. 
    unfold Expr_Expr_p_inv. 
    rewrite Expr'_rect_Eq. cbn. apply ap2. exact X. exact X0. 
Defined. 

Instance FP_Expr_p : Expr_p ⋈ Expr_p :=
  @Canonical_UR _ _ (Equiv_id _).

Definition FP_Expr_p_rect : @Expr_p_rect ≈ @Expr_p_rect.
  cbn. intros. destruct H. cbn. intros. destruct H5. induction x5; cbn.
   refine (H0 _ _ eq_refl).
   refine (H1 _ _ eq_refl).
   refine (H2 _ _ eq_refl _ _ IHx5_1 _ _ eq_refl _ _ IHx5_2).
   refine (H3 _ _ eq_refl _ _ IHx5_1 _ _ eq_refl _ _ IHx5_2).
   refine (H4 _ _ eq_refl _ _ IHx5_1 _ _ eq_refl _ _ IHx5_2).
Defined.

Hint Extern 0 (Expr_p_rect ?P ?x1 ?x2 ?x3 ?x4 ?x5 ?X ≈ Expr_p_rect ?P' ?x1' ?x2' ?x3' ?x4' ?x5' ?X') =>
erefine (FP_Expr_p_rect P P' _ x1 x1' _ x2 x2' _ x3 x3' _ x4 x4' _ x5 x5' _ X X' _); intros
:  typeclass_instances.

Hint Extern 0 => progress (unfold index_Expr) : typeclass_instances.

Hint Extern 0 (UR_Type Set Set) => exact FP_Type : typeclass_instances. 

Definition FP_Expr_sigma (A B:Set) (e:A ≈ B): {E : Expr_p & index_Expr E A} ≈ {E : Expr_p & index_Expr E B}.
  erefine (ur_type (@FP_Sigma _ _ _) _ _ _).
  exact FP_Expr_p. cbn; intros.
  (* this instance of transportable is on Type, we can only use the default one*)
  cbn. split; [apply Transportable_default | ].
  unfold index_Expr. intros. 
  destruct H.
  (* match goal with | |- (Expr_p_rect ?P ?x1 ?x2 ?x3 ?x4 ?x5 ?X _ ⋈ Expr_p_rect ?P' ?x1' ?x2' ?x3' ?x4' ?x5' ?X' _) =>   *)
  (*                   apply (fun E1 E2 E3 E4 E5 => FP_Expr_p_rect P P' *)
  (*                                        (_, fun _ _ _ =>  ( snd (FP_forall _ _ FP_Type) _ _ (_,fun _ _ _ => FP_Type))) _ *)
  (*                                                               x1 x1' E1 x2 x2' E2 x3 x3' E3 x4 x4' E4 x5 x5' E5 X X' eq_refl A B e) end; typeclasses eauto. *)
  apply admit. 
Defined.

Definition FP_Expr'@{i j' k k'} :
  forall x y : Set,
  UR_Type@{Set Set Set} x y ->
  UR_Type@{i i i} (Expr@{i} x) (Expr@{i} y).
Proof.
  intros A B e. cbn in *.
  refine (@UR_Type_Equiv'@{i i i k} _ _ _ (Expr_Expr_p@{i j'} A) _).
  refine (@UR_Type_Equiv@{i i i k} _ _ _ (Expr_Expr_p@{i j'} B) _)
  .
  (* exact (FP_Expr_sigma@{k i i k i k' k' j'} _ _ e). *)
  apply admit. 
Defined.

(* nat ⋈ N *)

Require Import BinInt BinNat Nnat.

Lemma iter_op_succ : forall A (op:A->A->A),
 (forall x y z, op x (op y z) = op (op x y) z) ->
 forall p a,
 Pos.iter_op op (Pos.succ p) a = op a (Pos.iter_op op p a).
Proof.
 induction p; simpl; intros; try reflexivity.
 rewrite X. apply IHp.
Defined.

Fixpoint plus_assoc (n m p : nat) : n + (m + p) = n + m + p.
 induction n. cbn. reflexivity.
 cbn. apply ap. apply plus_assoc.
Defined. 
 
Lemma inj_succ p : Pos.to_nat (Pos.succ p) = S (Pos.to_nat p).
Proof.
 unfold Pos.to_nat. rewrite iter_op_succ. reflexivity. 
 apply plus_assoc.
Defined.

Definition is_succ : forall p, {n:nat & Pos.to_nat p = S n}.
Proof.
 induction p using Pos.peano_rect.
 now exists 0.
 destruct IHp as (n,Hn). exists (S n). now rewrite inj_succ, Hn.
Defined. 

Theorem Pos_id (n:nat) : n<>0 -> Pos.to_nat (Pos.of_nat n) = n.
Proof.
 induction n as [|n H]; trivial. now destruct 1.
 intros _. simpl Pos.of_nat. destruct n. reflexivity.
 rewrite inj_succ. f_equal. apply ap. now apply H.
Defined.

Lemma of_nat_succ (n:nat) : Pos.of_succ_nat n = Pos.of_nat (S n).
Proof.
 induction n. reflexivity. simpl. apply ap. now rewrite IHn.
Defined. 

Theorem id_succ (n:nat) : Pos.to_nat (Pos.of_succ_nat n) = S n.
Proof.
rewrite of_nat_succ. now apply Pos_id.
Defined.

Lemma inj (n m : nat) : Pos.of_succ_nat n = Pos.of_succ_nat m -> n = m.
Proof.
 intro H. apply (ap Pos.to_nat) in H. rewrite !id_succ in H.
 inversion H. reflexivity. 
Defined.

Theorem Pos2Nat_id p : Pos.of_nat (Pos.to_nat p) = p.
Proof.
 induction p using Pos.peano_rect. reflexivity. 
 rewrite inj_succ. rewrite <- (ap Pos.succ IHp).
 now destruct (is_succ p) as (n,->).
Defined.

Lemma Pos2Nat_inj p q : Pos.to_nat p = Pos.to_nat q -> p = q.
Proof.
 intros H. now rewrite <- (Pos2Nat_id p), <- (Pos2Nat_id q), H.
Defined.

Lemma N2Nat_id a : N.of_nat (N.to_nat a) = a.
Proof.
  destruct a as [| p]; simpl. reflexivity.
  destruct (is_succ p) as [n H]. rewrite H. simpl. apply ap. 
  apply Pos2Nat_inj. rewrite H. apply id_succ.
Defined.

Theorem Pos_id_succ p : Pos.of_succ_nat (Pos.to_nat p) = Pos.succ p.
Proof.
rewrite of_nat_succ, <- inj_succ. apply Pos2Nat_id.
Defined.

Theorem id_succ' (n:nat) : Pos.to_nat (Pos.of_succ_nat n) = S n.
Proof.
rewrite of_nat_succ. apply Pos_id. intro H. inversion H.
Defined.

Lemma Nat2N_id n : N.to_nat (N.of_nat n) = n.
Proof.
 induction n; simpl; try reflexivity. apply id_succ'.
Defined. 

Instance Equiv_N_nat : Equiv nat N.
Proof.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - exact N.of_nat. 
  - exact N.to_nat. 
  - cbn; intro. exact (Nat2N_id _).
  - cbn; intro. exact (N2Nat_id _).
Defined. 

Instance Equiv_nat_N : Equiv N nat := Equiv_inverse _. 

Instance UR_nat_N : UR nat N | 0. 
eapply UR_Equiv.
typeclasses eauto.
typeclasses eauto.
Defined. 


Instance UR_N : UR N N := UR_gen N. 

Instance FP_N : N ⋈ N := @ur_refl_ _ _ _ _ URType_Refl _.

Hint Extern 0 (?f ?x = ?y ) => erefine (Move_equiv Equiv_nat_N x y _)
                               : typeclass_instances.

Hint Extern 0 (?f ?x = ?y ) => erefine (Move_equiv Equiv_N_nat x y _)
                               : typeclass_instances.

Instance UR_N_nat : UR N nat | 0. 
eapply UR_Equiv.
typeclasses eauto.
typeclasses eauto.
Defined. 

Instance compat_N_nat : N ⋈ nat.
Proof.
  unshelve eexists. 
  econstructor. intros. cbn.
  rewrite (N2Nat_id _). apply Equiv_id. 
Defined. 

Instance compat_nat_N : nat ⋈ N.
  unshelve eexists. 
  econstructor. intros. cbn.
  rewrite (Nat2N_id _). apply Equiv_id.
Defined.
