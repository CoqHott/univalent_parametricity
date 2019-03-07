Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable .
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

Tactic Notation "convert" constr(function) ":" constr(T) :=
  let X := fresh "X" in
  assert (X : { opt : T & function ≈ opt});
  [ first [  refine (let f := _ in let g := _ in existT _ (fun x y => existT _ (f x y) (g x y)) _) |
             refine (let f := _ in let g := _ in existT _ (fun x => existT _ (f x) (g x)) _) | 
             refine (let f := _ in let g := _ in existT _ (existT _ f g) _) | 
             eexists] ; try unfold function; tc
  | exact X].

Ltac optimize f := let T := type of f in convert f : T. 

Ltac solve_with_lift A B := let e := fresh "e" in
                                       unshelve refine (let e : A ≈ B := _ in _);
                                         [tc | exact (ur_refl (e:=e) _)].

Ltac direct_lifting f g := assert (X : f ≈ g); 
   [match goal with | |- @ur ?A ?B _ f _ => solve_with_lift A B end | eapply X].

Definition Canonical_eq_sig A :=   {can_eq : forall (x y : A), x = y -> x = y &
    forall x, can_eq x x eq_refl = eq_refl }.

Instance issig_Canonical_eq A : Canonical_eq_sig A ≃ Canonical_eq A.
Proof.
  unfold Canonical_eq_sig.  
  issig (Build_Canonical_eq A) (@can_eq A) (@can_eq_refl A).
Defined.

Instance issig_Canonical_eq_inv A : Canonical_eq A ≃ Canonical_eq_sig A :=
  Equiv_inverse _.

Hint Extern 0 => progress (unfold Canonical_eq_sig) :  typeclass_instances.

Definition FP_Canonical_eq : Canonical_eq ≈ Canonical_eq.
  univ_param_record.
Defined.

Hint Extern 0 (Canonical_eq _ ⋈ Canonical_eq _) => erefine (ur_type FP_Canonical_eq _ _ _); simpl
:  typeclass_instances.

Hint Extern 0 (Canonical_eq _ ≃ Canonical_eq _) => erefine (ur_type FP_Canonical_eq _ _ _).(equiv); simpl
:  typeclass_instances.

Instance Transportable_DType : Transportable (fun A:DType => A) := 
  Transportable_default _.

Instance Canonical_eq_Forall A (B: A -> Type) : Canonical_eq (forall x:A, B x) := Canonical_eq_gen _.

Hint Extern 0 (sigT _) => unshelve refine (existT _ _ _): typeclass_instances.





(* Example doing change of representation à la CoqEAL *)

(* correspondance between libraries over nat and N *)

Definition compat_inverse (A A' B B':Type) (eA: A ≈ A') (eB: B ≈ B') (eA' := UR_Type_Inverse _ _ eA)
           (eB' := UR_Type_Inverse _ _ eB) (f : A -> B) (g : A' -> B') :
  f ≈ g -> g ≈ f.
  tc. 
Defined.

Definition compat_inverse2 {A A' B B' C C' :Type} {eA: A ≈ A'} (eA' := UR_Type_Inverse _ _ eA)
           {eB: B ≈ B'} (eB' := UR_Type_Inverse _ _ eB)
           {eC: C ≈ C'} (eC' := UR_Type_Inverse _ _ eC)
           {f : A -> B -> C} {g : A' -> B' -> C'} :
  f ≈ g -> g ≈ f.
  tc. 
Defined.

Lemma  to_nat_succ n : S (N.to_nat n) = N.to_nat (N.succ n).
Admitted. 


Definition compat_add : plus ≈ N.add.
  cbn; intros. revert y y0 x0 H H0. induction x; cbn; intros.
  + assert (y = 0%N). admit.
    rewrite X. exact H0.
  + assert (y = (N.succ (N.of_nat x))). admit.
    rewrite X. rewrite N.add_succ_l. rewrite <- to_nat_succ.
    apply ap. apply IHx. apply eq_sym. apply (e_sect' Equiv_N_nat).
    auto.
Admitted. 
  
Definition compat_mul : mult ≈ N.mul. Admitted. 
Definition compat_div : Nat.div ≈ N.div. Admitted.
Definition compat_pow : Nat.pow ≈ N.pow. Admitted.
Definition compat_sub : Nat.sub ≈ N.sub. Admitted.

(* alternative possible version *)

Section Alt_LE.

Fixpoint alt_le (n m : nat) : Prop :=
  match n,m with
    0 , _ => True
  | S n, S m => alt_le n m
  | _ , _ => False
  end.

Instance Decidable_alt_le n m : DecidableEq (alt_le n m).
constructor. revert m. induction n.
- cbn. intros _ [] []. exact (inl eq_refl).
- destruct m.
   + destruct a. 
   + cbn. apply IHn.
Defined. 

Fixpoint ne_comp (A B : comparison) : Prop :=
  match A,B with
    Datatypes.Eq, Datatypes.Eq => False
  | Lt, Lt => False
  | Gt, Gt => False                
  | _ , _ => True
  end.

Definition le_N x y := ne_comp (x ?= y)%N Gt.
(* Notation "n <= m" := (le_N n m) : N_scope. *)

Local Open Scope positive_scope.

Definition comp_succ_inj a b :
  (forall r, Pos.compare_cont r a b = Pos.compare_cont r (Pos.succ a) (Pos.succ b)) *
  (Pos.compare_cont Gt a b = Pos.compare_cont Lt (Pos.succ a) b) *
  (Pos.compare_cont Lt a b = Pos.compare_cont Gt a (Pos.succ b)).
revert b. induction a; destruct b; cbn; split; try split; try reflexivity. 
- exact (fun r => fst (fst (IHa _)) r).
- exact (snd (fst (IHa _))).
- exact (snd (IHa _)).
- intros _. exact (snd (fst (IHa _))).
- exact (snd (fst (IHa _))).
- destruct a; cbn; reflexivity.
- destruct a; cbn; reflexivity.
- intros _. exact (snd (IHa _)).
- exact (snd (IHa _)).
- destruct a; cbn; reflexivity.
- destruct a; cbn; reflexivity.
- destruct b; cbn; reflexivity.
- destruct b; cbn; reflexivity.
- destruct b; cbn; reflexivity.
- destruct b; cbn; reflexivity.
Defined. 
  
Definition comp_S_inj a b :
  (N.of_nat a ?= N.of_nat b)%N = (Pos.of_succ_nat a ?= Pos.of_succ_nat b)%positive.
  destruct a, b; cbn; try reflexivity.
  - destruct b. reflexivity.
    cbn. generalize (Pos.of_succ_nat b). clear. induction p; cbn; try reflexivity.
  - destruct a. reflexivity.
    cbn. generalize (Pos.of_succ_nat a). clear. induction p; cbn; try reflexivity.
  - exact (fst (fst (comp_succ_inj _ _)) _). 
Defined. 


(* Definition compat_alt_le : alt_le ≈ le_N. *)
(*   cbn; intros. rewrite H, H0. clear. *)
(*   revert y0; induction y; intro n; destruct n; cbn. *)
(*   all: try apply URType_Refl. *)
(*   Focus 2.  *)
(*   unfold le_N in *. rewrite <- comp_S_inj. apply IHx.  *)
(* Defined. *)

End Alt_LE. 

Definition compat_le : le ≈ N.le. Admitted.

Hint Extern 0 (plus _ _ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (mult _ _ = _) => eapply compat_mul : typeclass_instances.
Hint Extern 0 (Nat.div _ _ = _) => eapply compat_div : typeclass_instances.
Hint Extern 0 (Nat.pow _ _ = _) => eapply compat_pow : typeclass_instances.
Hint Extern 0 (Nat.sub _ _ = _) => eapply compat_sub : typeclass_instances.
Hint Extern 0 (le _ _ ≃ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (le _ _ ⋈ _) => eapply compat_le : typeclass_instances. 

(* Definition compat_add' : N.add ≈ plus eapply compat_inverse2 compat_add. *)
(* Definition compat_add' : N.add ≈ plus := compat_inverse2 compat_add. *)
(* Definition compat_mul' : N.mul ≈ mult := compat_inverse2 compat_mul. *)
(* Definition compat_div' : N.div ≈ Nat.div := compat_inverse2 compat_div. *)
(* Definition compat_pow' : N.pow ≈ Nat.pow := compat_inverse2 compat_pow. *)
(* Definition compat_sub' : N.sub ≈ Nat.sub := compat_inverse2 compat_sub. *)
(* Definition compat_le' : N.le ≈ le. *)
(*   cbn; intros. intros. apply UR_Type_Inverse. tc. *)
(* Defined. *)

Definition compat_add' : N.add ≈ plus. Admitted.
Definition compat_mul' : N.mul ≈ mult. Admitted. 
Definition compat_div' : N.div ≈ Nat.div. Admitted.
Definition compat_pow' : N.pow ≈ Nat.pow. Admitted.
Definition compat_sub' : N.sub ≈ Nat.sub. Admitted.
Definition compat_le' : N.le ≈ le. Admitted.

Hint Extern 0 (N.add _ _ = _) => eapply compat_add' : typeclass_instances.
Hint Extern 0 (N.mul _ _ = _) => eapply compat_mul' : typeclass_instances.
Hint Extern 0 (N.div _ _ = _) => eapply compat_div' : typeclass_instances.
Hint Extern 0 (N.pow _ _ = _) => eapply compat_pow' : typeclass_instances.
Hint Extern 0 (N.sub _ _ = _) => eapply compat_sub' : typeclass_instances.
Hint Extern 0 (N.le _ _ ≃ _) => eapply compat_le' : typeclass_instances.
Hint Extern 0 (N.le _ _ ⋈ _) => eapply compat_le' : typeclass_instances.

Arguments N.mul : simpl never.
Arguments N.pow : simpl never.
Arguments N.sub : simpl never.
Arguments N.add : simpl never.
Arguments mult  : simpl never.
Arguments Nat.pow : simpl never.
Arguments Nat.sub  : simpl never.
Arguments Nat.div : simpl never.

Lemma nat_distrib : forall (c a b: nat), c * (a + b) = c * a + c * b.
Proof.
  induction c; intros; cbn.
  - reflexivity.
  - apply can_eq. tc.
    unfold mult; cbn. rewrite IHc. repeat rewrite <- plus_assoc.
    rewrite (plus_assoc b). rewrite (plus_comm b).
    repeat rewrite <- plus_assoc. reflexivity.
Defined.


(* And after adding the relation in the correspondance table, 
   we can convert proofs over converted functions *)

Lemma nat_distrib' : forall (c a b: nat), (a + b) * c = a * c + b * c.
Proof.
  intros. rewrite mult_comm. rewrite nat_distrib.
  rewrite mult_comm. rewrite (mult_comm c b). reflexivity. 
Defined.



(* we can even convert dependent functions *)

Notation "n <= m" := (le n m) : nat_scope.

Definition lt (n m : nat) := (S n <= m)%nat. 
Notation "n < m" := (lt n m) : nat_scope.
Hint Extern 0 => progress (unfold lt) :  typeclass_instances.

Definition divide n (m : {m : nat & 0 < m }) : nat := n / m.1.

Hint Extern 0 => progress (unfold projT1) :  typeclass_instances.

(* the original definition of N.lt is using compare and is more compicated to deal with *)

Definition lt_N (n m : N) := (N.succ n <= m)%N. 
Notation "n < m" := (lt_N n m) : N_scope.
Hint Extern 0 => progress (unfold lt_N) :  typeclass_instances.

Instance Decidable_leq_N n m : DecidableEq (n <= m)%N.
apply (DecidableEq_equiv (↑n <= ↑m) (n <= m)%N); tc. 
Defined.



Definition fix_nat_1 : (fun P X0 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | S n => XS n (f n)
  end) ≈
       (fun P X0 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | S n => XS n (f n)
  end).
Proof. 
  cbn; intros. equiv_elim. 
Defined. 

Definition fix_nat_2 : (fun P X0 X1 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | S n => XS n (f n)
  end) ≈
       (fun P X0 X1 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | S n => XS n (f n)
  end).
Proof. 
  cbn; intros. repeat equiv_elim.
Defined. 

Definition fix_nat_3 : (fun P X0 X1 X2 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | 2 => X2
  | S n => XS n (f n)
  end) ≈
       (fun P X0 X1 X2 XS => fix f (n : nat) {struct n} : P :=
  match n with
  | 0 => X0
  | 1 => X1
  | 2 => X2
  | S n => XS n (f n)
  end).
Proof. 
  cbn; intros. repeat equiv_elim.
Defined.



Ltac replace_goal :=
  let X := fresh "X" in
  match goal with | |- ?P =>
                    pose (X := ltac: (convert P : Prop));
                    apply (e_inv' (equiv X.2)); simpl; clear X
  end.

Hint Extern 0 => progress (unfold ge) : typeclass_instances. 


Hint Extern 0 (nat_rect ?P _ _ _ = _)
=> refine (FP_nat_rect_cst _ _ compat_nat_N _ _ _ _ _ _ _ _ _) ;
     try eassumption : typeclass_instances.


