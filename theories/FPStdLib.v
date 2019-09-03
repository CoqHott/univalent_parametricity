(************************************************************************)
(* This file contains basic definitions of UR that are helpful for many examples  *)
(************************************************************************)

Unset Universe Minimization ToSet.

Require Import HoTT UR URTactics DecidableEq FP ADT.

(*! nat !*)

Instance FP_nat : nat ⋈ nat := URType_Refl_decidable nat DecidableEq_eq_nat.
  
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

Definition inversion_cons {A a a'} {l l':list A} (X: a::l = a'::l') :
  {p : (a = a') * (l = l') & X = ap2 cons (fst p) (snd p)}
  := match X with
       | eq_refl => ((eq_refl ,eq_refl) ; eq_refl) end.

Instance Transportable_list A (P: list A -> Type)
         (HP : forall (P:A->Type), Transportable P) : Transportable P.
Proof.
  unshelve econstructor.
  - intros n m. revert P; revert m.
    induction n; intro m; destruct m; intros P e. 
    + apply Equiv_id.
    + inversion e.
    + inversion e.
    + pose (inversion_cons e).1. specialize (IHn _ (fun n => P (a :: n)) (snd p)).
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
  cbn. pose (X0 := eq_nil_refl X). cbn in *. rewrite X0. reflexivity. 
  inversion X. inversion X. 
  cbn in *. pose (inversion_cons X). destruct s as [s s']. 
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


Definition length {A} (l:list A) : nat := list_rect _ (fun _ => nat) O (fun _ _ n => S n) l.

Fixpoint vector_to_list A B (e: A ≃ B) (n m:nat) (en : n = m) :
  vector A n -> {l : list B & length l = m}.
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

Fixpoint list_to_vector_ A B (e: A ≃ B) (n m:nat) (en : n = m) (l:list A) (H : length l = n) {struct n}: Vector.t B m.
  destruct n, m.
  - exact (nil _).
  - inversion en. 
  - inversion en. 
  - destruct l.
    + destruct (zeroS _ H).
    + exact (vcons (e a) (list_to_vector_ _ _ e _ _ (inversionS _ _ en) l (inversionS _ _ H))).
Defined. 

Definition list_to_vector A B (e: A ≃ B) (n m:nat) (en: n = m) : {l : list A & length l = n} -> Vector.t B m
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
      apply (ap2 vcons). exact (e_sect e h). specialize (X t). destruct (vector_to_list _ _ _ n _ _ t), e0. exact X. 
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


Instance Equiv_vector_list (A B:Type) {H: A ≃ B} (n n':nat) (en : n ≈ n')
  : Vector.t A n ≃ {l : list B & length l = n'}
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
  : Vector.t ≈ (fun A n => {l : list A & length l = n}).
  intros A B e. econstructor. tc. intros n n' en. unshelve econstructor. 
  - econstructor.
    intros v l. exact ((vector_to_list A B (equiv e) n n' en v) = l).
  - econstructor. intros v v'. cbn.
    apply (@isequiv_ap _ _ (Equiv_vector_list _ _ _ _ _)). 
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined. 

(* Instance Equiv_UR_vector A B (R R' : A -> B -> Type) n n' en *)
(*          (e:forall a b, R a b ≃ R' a b) : forall l l' , UR_vector R n n' en l l' ≃ UR_vector R' n n' en l l'. *)
(* Proof. *)
(*   intros.  *)
(*   clear_eq.  *)
(*   let e' := fresh in set (e' := fun a b => Equiv_inverse (e a b)). *)
(*   unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)); try ( *)
(*   refine (@UR_vector_rect _ _ _ (fun n n' e l l' _ => UR_vector _ n n' e l l') _ _ _ _ _ _ _); *)
(*   repeat (let l := fresh in *)
(*           intros l; *)
(*           first [apply univalent_transport in l | *)
(*                  idtac]); *)
(*   econstructor; eassumption). *)
(*   let l := fresh "l" in intro l; induction l ; cbn in *. *)
(*   reflexivity. *)
(*   eapply (ap2 (UR_vector_cons _ _)); *)
(*   typeclasses eauto with equiv typeclass_instances. *)
(*   let l := fresh "l" in intro l; induction l ; cbn in *. *)
(*   reflexivity. *)
(*   eapply (ap2 (UR_vector_cons _ _)); *)
(*   typeclasses eauto with equiv typeclass_instances. *)
(* Defined. *)


Instance FP_sized_list_ {A B : Type} `{A ≈ B} (n n':nat) (en : n = n') : 
   {l : list A & length l = n} ⋈ {l : list B & length l = n'}.
Proof.
  unshelve eapply FP_Sigma. tc. cbn. econstructor. tc. intros.
  unshelve eapply FP_eq; try tc. 
  exact (FP_List_rect A B (ltac:(tc))  (fun _:list A => nat) (fun _:list B => nat)
                      (ltac:(econstructor; tc)) O O (ltac:(tc)) (fun _ _ (n0 : nat) => S n0) (fun _ _ (n0 : nat) => S n0) (ltac:(tc)) x y H0). 
Defined.

Hint Extern 0 (t ?A ?n ≃ _) =>
erefine (ur_type (Equiv_vector_list A _ n)) : typeclass_instances.

Instance Equiv_list_vector (A B:Type) {H : ur B A} n :
  {l : list A & length l = n} ≃ Vector.t B n | 1 := Equiv_inverse _.

Definition Equiv_list_vector_ : (fun A n => {l : list A & length l = n}) ≈ Vector.t.
  cbn. intros A B e.
  split. tc.  intros. apply UR_Type_Inverse. apply Equiv_vector_list_.
  apply UR_Type_Inverse. tc. symmetry. tc. 
Defined.

Definition UrEq_S n n' e m m' e' X Y : UR_eq nat nat (eq nat) n n' e m m' e' X Y ->
                                       UR_eq nat nat (eq nat) (S n) (S n') (ap S e)
                                             (S m) (S m') (ap S e') (ap S X) (ap S Y).
Proof.
  destruct 1. econstructor.
Defined.

Definition IsIrr_UrEq_nat n n' e m m' e' X Y :
  UR_eq nat nat (eq nat) n n' e m m' e' X Y.
  destruct e, e', X. assert (Y = eq_refl). apply is_hset. rewrite X. econstructor.
Defined. 

Definition IsHProp_UrEq_nat_B {n n' e m m' e' X Y p p' e'' X' Y'}
           (Hm:m = p) (Hm' : m' = p')
           (He : Hm # Hm' # e' = e'')
           (HX : Hm # X = X')
           (HY : Hm' # Y = Y')
           (B : UR_eq nat nat (eq nat) n n' e p p' e'' X' Y')
  : UR_eq nat nat (eq nat) n n' e m m' e' X Y.
  pose (transport_eq (fun XX => UR_eq nat nat (eq nat) n n' e p p' XX _ _) He^
        (transport_eq (fun XX => UR_eq nat nat (eq nat) n n' e p p' e'' XX _) HX^
         (transport_eq (fun XX => UR_eq nat nat (eq nat) n n' e p p' e'' X'  XX) HY^ B))).
  cbn in u. clearbody u. clear HX He HY B.
  destruct Hm, Hm'. 
  exact u.
Defined. 

Definition IsHProp_UrEq_nat_gen {n n' e m m' e' X Y p p' e'' X' Y'}
           (Hm:m = p) (Hm' : m' = p')
           (He : Hm # Hm' # e' = e'')
           (HX : Hm # X = X')
           (HY : Hm' # Y = Y')
           (A : UR_eq nat nat (eq nat) n n' e m m' e' X Y)
           (B : UR_eq nat nat (eq nat) n n' e p p' e'' X' Y')
  : A = IsHProp_UrEq_nat_B Hm Hm' He HX HY B. 
  destruct A, B. cbn in *. revert He HX HY. 
  assert (Hm = eq_refl). apply is_hset. rewrite X. clear X. 
  assert (Hm' = eq_refl). apply is_hset. rewrite X. clear X. cbn.
  intros.
  assert (He = eq_refl). apply IsIrr_IsHprop'. intros X Y. apply is_hset. rewrite X. clear X. 
  assert (HX = eq_refl). apply IsIrr_IsHprop'. intros X Y. apply is_hset. rewrite X. clear X. 
  assert (HY = eq_refl). apply IsIrr_IsHprop'. intros X Y. apply is_hset. rewrite X. clear X. 
  reflexivity. 
Defined.

Definition IsHProp_UrEq_nat n n' e m m' e' X Y (A B :
  UR_eq nat nat (eq nat) n n' e m m' e' X Y) : A = B :=
  IsHProp_UrEq_nat_gen eq_refl eq_refl eq_refl eq_refl eq_refl A B.

Definition UR_sized_list_irr A B {X:A ⋈ B}
           (n n':nat) (en : n = n')
           (s : {l : list A & length l = n})
           (s' : {l : list B & length l = n'})                  
  : 
   (s.1 ≈ s'.1) ≃ (s ≈ s').
Proof.
  cbn. set (Hl := s.2). set (Hl' := s'.2). set (l := s.1) in *. set (l' := s'.1) in *.
  clearbody Hl Hl' l l'. destruct en. clear s s'. cbn in Hl. destruct Hl.
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - intro urlist. unshelve eexists. induction urlist; try econstructor; auto.
    apply IsIrr_UrEq_nat.
  - apply projT1.
  - intro urlist; destruct urlist; reflexivity.
  - intros [urlist UR_eq_list]. apply path_sigma_uncurried.
    unshelve eexists. cbn. destruct urlist; reflexivity.
    cbn. apply IsHProp_UrEq_nat.
Defined.

Definition ap_S_section {n m} en : (en = ap S (inversionS n m en)).
  apply is_hset.
Defined.

Definition ap_S_retraction {n m} (en:n=m) : (en = inversionS _ _ (ap S en)).
  apply is_hset.
Defined. 

Definition transport_UR_vector_cons A B {X:A ⋈ B} (X_inv := UR_Type_Inverse _ _ X)
           n n' (en:n = n')
           (a :A) a' a'' (v v': Vector.t A n) (v'':Vector.t B n') (h:a'=a) (e:v'=v)
  (E: ur a a'') (E': UR_vector ur n n' en v v''):
   transport_eq
    (fun X => UR_vector ur (S n) (S n') (ap S en) X (vcons a'' v''))
    (ap2 vcons h e)^ (UR_vector_cons ur en E E')  =
  UR_vector_cons ur en (transport_eq (fun X => ur X _) h^ E)
               (transport_eq (fun X => UR_vector ur _ _ en X _) e^ E').
  destruct h, e. reflexivity.
Defined.

Definition transport_UR_vector_cons_eq (A B:Type) {X:A ⋈ B} (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en en':n = n') (a:A) (a':B) (e:en' = en)
           (v: Vector.t A n) (v':Vector.t B n')
  (E: ur a a') (E': UR_vector ur n n' en v v'):
   transport_eq
    (fun X => UR_vector ur (S n) (S n') X (vcons a v) (vcons a' v'))
    (ap (ap S) e)^ (UR_vector_cons ur en E E')  =
   UR_vector_cons ur _ E (transport_eq (fun X => UR_vector ur _ _ X _ _) e^ E').
  destruct e. reflexivity.
Defined.

Definition UR_vector_list_is_eq_fun A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en : n = n')
           (en_inv : n' = n := inverse en)
           (v : t A n)
           (v' : t B n') :
  UR_vector ur n n' en v v'
  -> UR_list ur (vector_to_list A A (Equiv_id A) n n eq_refl v) .1
      (vector_to_list B B (Equiv_id B) n' n' eq_refl v') .1.
  induction 1; cbn; econstructor; auto.
Defined.


Definition UR_list_decompose {A B} (R:A->B->Type) l l' (e : UR_list R l l') :
  match l,l' return UR_list R l l' -> Type
  with [],[] => fun e => e = UR_list_nil R
  | a::l,a'::l' => fun e => { X : (R a a') * UR_list R l l' & e = UR_list_cons R (fst X) (snd X)}
  | _,_ => fun _ => False end e.
Proof.
  destruct e. reflexivity. exists (r,e). reflexivity. 
Defined.

Definition UR_vector_list_is_eq_inv A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en : n = n')
           (en_inv : n' = n := inverse en)
           (v : t A n)
           (v' : t B n')
           (canA := ur_refl A)
           (canB := ur_refl B)
  :
UR_list ur (vector_to_list A A (Equiv_id A) n n eq_refl v) .1
        (vector_to_list B B (Equiv_id B) n' n' eq_refl v') .1 ->
UR_vector ur n n' en v v'.
intros Hlist. clear en_inv. generalize dependent n'.
    induction v; destruct v'; intros.
    + assert (en = eq_refl). apply is_hset.
      rewrite X0. econstructor.
    + destruct (zeroS _ en).
    + destruct (zeroS _ en^).
    + cbn in Hlist.
      pose (UR_list_decompose ur _ _ Hlist). cbn in y. destruct y as [(r,r') _].
      refine (transport_eq (fun X => UR_vector ur (S n) (S n0) X _ _) (ap_S_section en)^ _).
      econstructor; auto.
Defined.


Definition UR_vector_list_is_eq_inv_eq A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en en': n = n') (e : en' = en)
           (en_inv : n' = n := inverse en)
           (v : t A n)
           (v' : t B n') XX:
  transport_eq (fun X0 : n ≈ n' => UR_vector ur n n' X0 v v') e
  (UR_vector_list_is_eq_inv A B n n' _ v v' XX) =
  UR_vector_list_is_eq_inv A B n n' en v v' XX.
destruct e. reflexivity. 
Defined.

Definition UR_vector_list_is_eq A B {X:A ⋈ B}
           (X_inv := UR_Type_Inverse _ _ X)
           (n n':nat) (en : n = n')
           (en_inv : n' = n := inverse en)
           (canA := ur_refl A)
           (canB := ur_refl B)
  : 
  forall (v:t A n) (v' : t B n') ,
    let l := ↑ v : {l : list A & length l = n} in
    let l' := ↑ v' : {l : list B & length l = n'} in 
    (UR_vector ur n n' en v v') ≃ 
    (l ≈ l').
Proof.
  intros. cbn. eapply equiv_compose; try apply UR_sized_list_irr.
  cbn. 
  unshelve refine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - apply UR_vector_list_is_eq_fun.
  - apply UR_vector_list_is_eq_inv. 
  - intro Hv. simpl. induction Hv.
    + reflexivity.
    + simpl. assert (ap_S_section (ap S en) = ap (ap S) (ap_S_retraction en)). 
      apply IsIrr_IsHprop'. unfold IsIrr. intros. apply is_hset.
      rewrite X0. clear X0. eapply concat. 
      apply transport_UR_vector_cons_eq. apply ap.
      rewrite UR_vector_list_is_eq_inv_eq. auto.  
  - intro Hl. generalize dependent n'. induction v; destruct v'; intros; simpl. 
    + assert (en = eq_refl). apply is_hset. rewrite X0. cbn in *.
      symmetry. exact (UR_list_decompose _ _ _ Hl). 
    + destruct (zeroS _ en).
    + destruct (zeroS _ en^).
    + destruct (UR_list_decompose ur (h :: (vector_to_list A A (Equiv_id A) n n eq_refl v) .1)
                                  (h0 :: (vector_to_list B B (Equiv_id B) n0 n0 eq_refl v') .1) Hl).
      destruct x. rewrite e. clear e Hl.
      pose (ap_S_section en). rewrite e. set (inversionS n n0 en).
      clearbody e0. clear e en en_inv. rename e0 into en. 
      assert (ap_S_section (ap S en) = ap (ap S) (ap_S_retraction en)). 
       apply IsIrr_IsHprop'. unfold IsIrr. intros. apply is_hset.
       rewrite X0. eapply concat. apply ap. apply transport_UR_vector_cons_eq. 
       simpl. apply ap. simpl in IHv. specialize (IHv n0 en v' u0).
       rewrite UR_vector_list_is_eq_inv_eq. exact IHv. 
Defined.

Instance UR_vector_ A B `{UR A B} n n' en : UR (t A n) (t B n') :=
  {| ur := UR_vector ur _ _ en |}.

Definition URIsUR_vector {A B : Type} {H : ur A B}  (n n':nat) (en : n ≈ n')
           (v v':t A n) : (v = v') ≃ (v ≈ (↑ v')).
Proof.
  pose (einv := Equiv_inverse (equiv H)).
  eapply Equiv_inverse.
  eapply equiv_compose. eapply UR_vector_list_is_eq. 
  unfold univalent_transport. 
  pose (canA := ur_refl A). pose (canB := ur_refl B).
  refine (transport_eq (fun X => (Equiv_vector_list A A n n eq_refl v
   ≈ Equiv_vector_list B B n' n' eq_refl (Equiv_Vector A B (equiv H) n n' en v')) ≃ (X = _))
                       (e_sect (vector_to_list A A _ n n _) v) _).
  refine (transport_eq (fun X => (Equiv_vector_list A A n n eq_refl v
   ≈ Equiv_vector_list B B n' n' eq_refl (Equiv_Vector A B (equiv H) n n' en v')) ≃ (_ = X))
                       (e_sect (vector_to_list A A _ n n _) v') _).
  assert (vector_to_list B B (Equiv_id B) n' n' eq_refl
                         (Equiv_Vector_fun A B (equiv H) n n' en v')
          = ↑ (vector_to_list A A (Equiv_id A) n n eq_refl v')).
  { clear. destruct en. apply path_sigma_uncurried.
    unshelve eexists; [idtac | apply is_hset]. 
    destruct v'. reflexivity. cbn. apply ap. induction v'; cbn.
    - reflexivity.
    - apply ap. exact IHv'.   
  }
  cbn. rewrite X; clear X.
  set (vector_to_list A A (Equiv_id A) n n eq_refl v).
  set (vector_to_list A A (Equiv_id A) n n eq_refl v'). 
  clearbody s s0. clear v v'.
  eapply equiv_compose.
  apply Equiv_inverse. exact (@ur_coh _ _ _ _ (Ur_Coh (@FP_sized_list_ A B H n n' en)) s s0).
  apply (@isequiv_ap _ _ (@Equiv_list_vector A A canA n)). 
Defined.

Definition FP_Vector : Vector.t ≈ Vector.t.
  intros A B e. cbn in e. split. tc. 
  intros n n' en.
  unshelve eexists.
  - unshelve econstructor. refine (URIsUR_vector n n' en).  
  - apply Canonical_eq_gen.
  - apply Canonical_eq_gen.
Defined.

Instance Equiv_Vector_instance : forall x y : Type, x ⋈ y -> forall n n' (e:n=n'), (Vector.t x n) ⋈ (Vector.t y n') :=
  fun x y e n n' en => ur_type (FP_Vector x y e) n n' en. 

