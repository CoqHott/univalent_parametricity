Require Import HoTT HoTT_axioms UR URTactics ADT FP Record.

Set Universe Polymorphism.
  
Ltac tc := typeclasses eauto with typeclass_instances.

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
  
Definition FP_ap:  @ap ≈ @ap.
  intros A A' eA B B' eB f f' ef x x' ex y y' ey p p' ep. 
  cbn in *.
  induction ep. apply UR_eq_refl. 
Defined.

Hint Extern 0 (UR_eq _ _ _ _ _ _ _ _ _ _ _ ) => 
  erefine (FP_ap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) : typeclass_instances.

Definition equivalence_hprop (P Q: Type) (eP:forall p p':P, p = p')
           (eQ: forall q q':Q, q = q')
           (f : P -> Q) (g : Q -> P)
  : P ≃ Q := BuildEquiv _ _ f (isequiv_adjointify _ g _ _).

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

Definition ur_hprop A A' (H : A ⋈ A') (HA: forall x y:A, x = y) (x:A) (y:A')
  : x ≈ y. 
  intros. apply (alt_ur_coh _ _ _ _ ). apply HA. 
Defined.   

Definition Isequiv_ur_hprop A A' B B' (H : A ⋈ A')(H' : B ⋈ B') (f:A->B) (g:A'->B')
           (e : IsEquiv f) (e' : IsEquiv g)
           (efg:f ≈ g) : e ≈ e'. 
  intros; apply ur_hprop. apply hprop_isequiv. 
Defined.   

Instance issig_equiv A B : { e_fun : A -> B &  IsEquiv e_fun }
                               ≃ (A ≃ B).
  issig (BuildEquiv A B) (@e_fun A B) (@e_isequiv A B).
Defined.

Instance issig_equiv' A B :  (A ≃ B) ≃ { e_fun : A -> B &  IsEquiv e_fun } :=
  Equiv_inverse _.
  
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

Definition FP_transport_eq : @transport_eq ≈ @transport_eq.
  cbn; intros. induction H3. auto.
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

Definition UR_Type_equiv (A A' : Type) (eA : A ⋈ A') (eA': A ≃ A')
  (e  : equiv eA = eA') : 
  eA =
  Build_UR_Type _ _ eA' (Ur eA)
                (transport_eq (fun X => UR_Coh A A' X _) e (Ur_Coh eA)) _ _. 
  destruct e. reflexivity.
Defined. 

Definition UR_Type_eq (A A' : Type) (eA eA': A ⋈ A')
           (equiv_eq  : equiv eA = equiv eA')
           (ur_eq  : Ur eA = Ur eA')
           (coh_eq  : transport_eq (fun X => UR_Coh A A' _ X) ur_eq (transport_eq (fun X => UR_Coh A A' X _) equiv_eq (Ur_Coh eA))
                      = Ur_Coh eA')
           (canonA_eq  : eA.(Ur_Can_A) = eA'.(Ur_Can_A))
           (canonB_eq  : eA.(Ur_Can_B) = eA'.(Ur_Can_B))
  : eA = eA'. 
  destruct eA, eA'.
  cbn in *. rewrite <- coh_eq. destruct equiv_eq, ur_eq, canonA_eq, canonB_eq.
  reflexivity.
Defined.                  

Definition  transport_Ur_Coh (A A': Type)
            (equiv : A ≃ A')
            (_ur _ur' : A -> A' -> Type)
            (ur_coh : forall a a' : A, (a = a') ≃ (_ur a (equiv a')))
            (e : _ur = _ur')
  :   transport_eq (fun X => UR_Coh A A' equiv {| ur := X |}) e
                   (Build_UR_Coh _ _ equiv {| ur := _ur |} ur_coh)
      =
      Build_UR_Coh _ _ equiv {| ur := _ur' |} (fun a a' => transport_eq (fun X =>
                                               (a = a') ≃ (X a (equiv a'))) e (ur_coh a a')).
  destruct e. reflexivity.
Defined.

Definition transport_apD10 A B (f g : forall x:A, B x)
           (P : forall x:A, B x -> Type)
           (e : f = g) x v: transport_eq (fun X => P x (X x))
                                                       e v
                                          = transport_eq (fun X => P x X)
                                                (apD10 e x) v.
  destruct e. reflexivity.
Defined. 


Definition transport_funext {A B} {f g : forall x:A, B x}
           (P : forall x:A, B x -> Type) x 
           (v : P x (f x)) (e : forall x, f x = g x)
            : transport_eq (fun X => P x (X x))
                                                       (e_inv apD10 e) v
                                          = transport_eq (fun X => P x X)
                                                (e x) v.
Proof.
  rewrite transport_apD10. rewrite e_retr. reflexivity.
Defined.

Definition transport_univalence A B C (e: A ≃ B) (e': C ≃ A)  :
  transport_eq (Equiv C) (e_inv (eq_to_equiv A B) e) e'
  = e ∘∘ e'.
Proof.
  pose (@e_retr _ _ (eq_to_equiv A B) _ e). 
  set (e_inv (eq_to_equiv A B) e) in *.  rewrite <- e0.
  clear e0. destruct e1. cbn. apply path_Equiv. apply funext; reflexivity. 
Defined. 
  
Definition UR_Type_canonical_eq (A A' : Type) (eA : A ⋈ A') :
  eA = @Canonical_UR A A' (equiv eA).
  unshelve eapply UR_Type_eq.
  destruct eA, Ur, Ur_Coh. cbn; apply ap.
  apply funext; intro a. 
  apply funext; intro a'.
  specialize (ur_coh a (e_inv equiv a')).
  apply univalence.
  exact (transport_eq (fun X => ur a X ≃ _) (e_retr equiv _)
                      (Equiv_inverse ur_coh)).

  destruct eA, Ur, Ur_Coh. cbn.
  rewrite transport_ap. rewrite transport_Ur_Coh. apply ap.
  apply funext; intro a; apply funext; intro a'.
  apply path_Equiv. apply funext. intro e. 
  unfold univalent_transport in ur_coh.
  pose (@transport_funext _ _ ur (fun a a' => a = e_inv equiv a') (fun _ (X : A' -> Type) => (a = a') ≃ X (equiv a')) a (ur_coh a a')). 
  cbn in e0.
  rewrite e0. clear e0. 
  pose (@transport_funext _ _ (ur a) (fun a' => a = e_inv equiv a')
                          (fun _ X => (a = a') ≃ X) (equiv a') (ur_coh a a')). 
  rewrite e0. clear e0.
  rewrite transport_univalence. cbn.
  rewrite (e_adj equiv a'). rewrite transport_ap. 
  unfold e_sect'.
  pose (T := fun (X:{a'' : A & a'' = a'}) => (transport_eq (fun x : A => ur a (equiv x) ≃ (a = X.1))
     X.2 (Equiv_inverse (ur_coh a X.1)))
    ((ur_coh a a') e) =
  (transport_eq (fun X : A => (a = a') ≃ (a = X)) X.2^
     (Equiv_id (a = a'))) e).
  change (T (_ ; e_sect equiv a')).
  assert ((e_inv equiv (equiv a'); e_sect equiv a') =
          ((_;eq_refl):{a'' : A & a'' = a'})).
  apply path_sigma_uncurried. unshelve eexists. exact (e_sect equiv a').
  cbn. rewrite transport_paths_l. rewrite inv2. apply eq_sym, concat_refl.
  rewrite X. unfold T; clear T. cbn. apply e_sect.
  - apply Canonical_contr.
  - apply Canonical_contr.    
Defined. 


Definition FP_univalence : univalence ≈ univalence.
  intros A A' eA B B' eB. 
  apply Isequiv_ur_hprop.
Defined. 

Definition inversionS n m : S n = S m -> n = m.
  inversion 1. reflexivity.
Defined. 

Definition zeroS n : 0 = S n -> False.
  inversion 1.
Defined. 

(*! Establishing FP for nat_rect !*)

Definition nat_rect : forall P : nat -> Type,
    P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
  := 
    fun (P : nat -> Type) (f : P 0)
        (f0 : forall n : nat, P n -> P (S n)) =>
      fix F (n : nat) : P n :=
      match n as n0 return (P n0) with
      | 0 => f
      | S n0 => f0 n0 (F n0)
      end.

Definition FP_nat_rect : nat_rect ≈ nat_rect.
  intros X X' [H H'] P P' e0 Q Q' e_S n n' en.    
  equiv_elim. exact (e_S n n eq_refl _ _ IHn).
Defined.

Definition FP_nat_rect_cst (P Q:Type) (e : P ≈ Q) :
  nat_rect (fun _ => P) ≈ nat_rect (fun _ => Q) :=
  FP_nat_rect (fun _ => P) (fun _ => Q)
              {| transport_ := Transportable_cst nat P ; ur_type := fun _ _ _ => e |}.

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

Typeclasses Opaque vector_to_list list_to_vector.

Hint Extern 0 => progress (unfold length) :  typeclass_instances.

Definition UR_Equiv_refl (A B:Type) (e:A ≃ B) (e_inv := Equiv_inverse e) `{UR A B} : UR B B :=
  {| ur := fun b b' => ↑ b ≈  b' |}.

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
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
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

(*
Definition Expr_Expr_p_fun@{i j} (A:Set) (E:Expr@{i} A) :
  Expr'@{i j} A :=
  Expr_rect (fun A _ => Expr'@{i j} A)
            (fun n => I' n)
            (fun b => B' b)
            (fun _ e _ e' => Add' e e')
            (fun _ e _ e' => Mul' e e')
            (fun _ e _ e' => Eq' e e') A E.

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


*)

Hint Extern 0 (UR_Type Set Set) => exact FP_Type : typeclass_instances. 

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

Instance IsEquiv_N_nat : IsEquiv N.of_nat.
Proof.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - exact N.to_nat. 
  - cbn; intro. exact (Nat2N_id _).
  - cbn; intro. exact (N2Nat_id _).
Defined. 

Instance Equiv_N_nat : Equiv nat N := BuildEquiv _ _ N.of_nat _. 

Instance Equiv_nat_N : Equiv N nat := Equiv_inverse _.

Instance UR_N : UR N N := UR_gen N. 

Instance Decidable_eq_N : DecidableEq N := DecidableEq_equiv nat N _.

Hint Extern 0 (?f ?x = ?y ) => erefine (Move_equiv Equiv_nat_N x y _)
                               : typeclass_instances.

Hint Extern 0 (?f ?x = ?y ) => erefine (Move_equiv Equiv_N_nat x y _)
                               : typeclass_instances.

Instance UR_N_nat : UR N nat | 0.
eapply UR_Equiv; tc.
Defined.

Instance compat_N_nat : N ⋈ nat.
Proof.
  unshelve eexists; try tc.
  econstructor. intros. cbn.
  rewrite (N2Nat_id _). apply Equiv_id.
Defined. 

Instance UR_nat_N : UR nat N | 0.
eapply UR_Equiv; tc. 
Defined.

Instance compat_nat_N : nat ⋈ N.
Proof.
  unshelve eexists; try tc.
  econstructor. intros. cbn.
  rewrite (Nat2N_id _). apply Equiv_id.
Defined. 

Definition refl_nat_N (n:nat) : n ≈ (↑ n : N) := ur_refl (e:=compat_nat_N) n.
Hint Extern 0 (?n = _) => unshelve refine (refl_nat_N _) : typeclass_instances.

(* Instance compat_nat_N : nat ⋈ N := UR_Type_Inverse _ _ compat_N_nat. *)

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


