(* ET: 
   this file should be in theories, ALaCarte.v, or something like that, eg. URTactics *)

Require Import HoTT Tactics UnivalentParametricity.theories.UR UnivalentParametricity.theories.StdLib.UR URTactics UnivalentParametricity.theories.FP Record UnivalentParametricity.theories.StdLib.FP UnivalentParametricity.theories.Transportable CanonicalEq DecidableEq Nat_binnat.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

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


Definition compat_add : plus ≈ N.add. Admitted. 
Definition compat_mul : mult ≈ N.mul. Admitted. 
Definition compat_div : Nat.div ≈ N.div. Admitted.
Definition compat_pow : Nat.pow ≈ N.pow. Admitted.
Definition compat_sub : Nat.sub ≈ N.sub. Admitted.
Definition compat_le : Peano.le ≈ N.le. Admitted.

Hint Extern 0 (plus _ _ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (mult _ _ = _) => eapply compat_mul : typeclass_instances.
Hint Extern 0 (Nat.div _ _ = _) => eapply compat_div : typeclass_instances.
Hint Extern 0 (Nat.pow _ _ = _) => eapply compat_pow : typeclass_instances.
Hint Extern 0 (Nat.sub _ _ = _) => eapply compat_sub : typeclass_instances.
Hint Extern 0 (Peano.le _ _ ≃ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (Peano.le _ _ ⋈ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (Nat.le _ _ ≃ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (Nat.le _ _ ⋈ _) => eapply compat_le : typeclass_instances. 

Definition compat_add' : N.add ≈ plus. Admitted.
Definition compat_mul' : N.mul ≈ mult. Admitted. 
Definition compat_div' : N.div ≈ Nat.div. Admitted.
Definition compat_pow' : N.pow ≈ Nat.pow. Admitted.
Definition compat_sub' : N.sub ≈ Nat.sub. Admitted.
Definition compat_le' : N.le ≈ Peano.le. Admitted.

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

Notation "n <= m" := (Nat.le n m) : nat_scope.

Definition lt (n m : nat) := (S n <= m)%nat. 
Notation "n < m" := (lt n m) : nat_scope.
Hint Extern 0 => progress (unfold lt) :  typeclass_instances.

Hint Extern 0 => progress (unfold projT1) :  typeclass_instances.

(* the original definition of N.lt is using compare and is more complicated to deal with *)

Definition lt_N (n m : N) := (N.succ n <= m)%N. 
Notation "n < m" := (lt_N n m) : N_scope.
Hint Extern 0 => progress (unfold lt_N) :  typeclass_instances.

Instance Decidable_leq_N (n m:N) : DecidableEq (n <= m)%N.
apply (DecidableEq_equiv (Peano.le (↑n) (↑m)) (n <= m)%N); tc.
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

Tactic Notation "convert" constr(function) ":" constr(T) :=
  let X := fresh "X" in
  assert (X : { opt : T & function ≈ opt});
  [ first [  refine (let f := _ in let g := _ in existT _ (fun x y => existT _ (f x y) (g x y)) _) |
             refine (let f := _ in let g := _ in existT _ (fun x => existT _ (f x) (g x)) _) | 
             refine (let f := _ in let g := _ in existT _ (existT _ f g) _) | 
             eexists] ; try unfold function; cbn; intros;
    first [pose (F := fix_nat_3); simpl in F; eapply F (* refine (F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) *) | idtac ]; tc
  | exact X].

Ltac optimize f := let T := type of f in convert f : T. 

Ltac replace_goal :=
  let X := fresh "X" in
  match goal with | |- ?P =>
                    first [
                        pose (X := ltac: (convert P : Prop)) |
                        pose (X := ltac: (convert P : Type))]; 
                    apply (e_inv' (equiv X.2)); simpl; clear X
  end.

Hint Extern 0 => progress (unfold ge) : typeclass_instances. 


Hint Extern 0 (nat_rect ?P _ _ _ = _)
=> refine (FP_nat_rect_cst _ _ compat_nat_N _ _ _ _ _ _ _ _ _) ;
     try eassumption : typeclass_instances.


