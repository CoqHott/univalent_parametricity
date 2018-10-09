Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable .
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega.

Set Universe Polymorphism.


Tactic Notation "convert" constr(function) ":" constr(T) :=
  let X := fresh "X" in
  assert (X : { opt : T & function ≈ opt});
  [eexists; tc | exact X].

Ltac optimize f := let T := type of f in convert f : T. 

Tactic Notation "lift" constr(function) ":" constr(T) :=
  let X := fresh "X" in
  let e := fresh "e" in
  assert (X : { opt : T & function ≈ opt});
  [exists (↑ function); intros;
          match goal with | |- @ur ?A ?B _ _ _ =>
                            unshelve refine (let e : A ≈ B := _ in _);
                            [tc | exact (ur_refl (e:=e) _)] end
        | exact X].



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


(* This file contains 3 examples: Lib, Monoid, and pow. 
   Lib and pow are mentioned in the paper. Monoid is not. *)

(*****************************)
(* we start with the Lib example (Section 1) *)

Record Lib (C : Type -> nat -> Type) :=
  { head : forall {A : Type} {n : nat}, C A (S n) -> A;
    map : forall {A B} (f:A -> B) {n}, C A n -> C B n;
    lib_prop : forall n A (B : DType) (f : A -> B) (v : C A (S n)), head (map f v) = f (head v) }.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.
Arguments lib_prop {_} _ {_ _ _} _ _.

(* the proof that Lib is a univalent type constructor requires to 
   use an equivalent representation with dependent sums *)

Definition Lib_sig C :=   {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A (B:DType) (f : A -> B) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}.

Instance issig_lib_hd_map C : Lib_sig C ≃ Lib C.
Proof.
  issig (Build_Lib C) (@head C) (@map C) (@lib_prop C).
Defined.

Instance issig_lib_hd_map_inv C : Lib C ≃ Lib_sig C :=
  Equiv_inverse _.

Hint Extern 0 => progress (unfold Lib_sig) :  typeclass_instances.

(* the proof is automatic using the univ_param_record tactic *)

Definition FP_Lib : Lib ≈ Lib.
  cbn;   split ; [typeclasses eauto | ]; intros;
    unshelve refine (UR_Type_Equiv_gen _ _ _ _ _ _ _ _).
  tc. erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn in *; intros. tc.
  econstructor. tc. intros.
  
  erefine (ur_type (@FP_Sigma _ _ _) _ _ _); cbn in *; intros. tc.
  econstructor. tc. cbn. intros.

  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros. tc. tc. 
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros. tc. tc. 
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros. tc. tc. 
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros. tc. tc. 
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type := _|}); cbn in *; intros. tc. tc. 
  cbn. unshelve notypeclasses refine (ur_type (FP_eq _ _ _ _ _ _) _ _ _); cbn. tc.  tc. cbn; tc. 
Defined.

Hint Extern 0 (Lib _ ≃ Lib _) => erefine (ur_type FP_Lib _ _ _).(equiv); simpl
:  typeclass_instances.

(* we now define an instance of Lib for vectors *)

Definition lib_vector_prop : forall n A (B:DType) (f : A -> B) (v : t A (S n)),
  Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  intros.
  apply (Vector.caseS (fun _ v => Vector.hd (Vector.map f v) = f (Vector.hd v))).
  intros. reflexivity.
Defined.
                                                   
Definition libvec : Lib Vector.t :=
  {| head := fun A n x => @Vector.hd A n x;
     map := fun A B f n => Vector.map f;
     lib_prop := lib_vector_prop |}.

Definition libvec' : Lib_sig Vector.t :=
  (fun A n x => @Vector.hd A n x;
     (fun A B f n => Vector.map f;
      lib_vector_prop)).

(* using the equivalence between vectors and sized lists
   we can automatically infer the Lib structure on sized lists. 
*)

Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑ libvec.

Notation vect_to_list := (vector_to_list _ _ (Equiv_id _) _ _ _).
Notation list_to_vect := (list_to_vector _ _ (Equiv_id _) _ _ _).

(* Definition lib_list'' : Lib (fun A n => {l: list A & length l = n}) := *)
(*   {| *)
(*     head := fun A n l => hd (list_to_vect l); *)
(*     map := fun A B f n l => vect_to_list (Vector.map f (list_to_vect l));  *)
(*     lib_prop := fun n A B f (l : {l : list A & length l = S n}) => *)
(*                   transport_eq (fun l => hd (Vector.map f l) = f (hd l)) *)
(*                                (e_sect _ _) *)
(*                                (lib_vector_prop n A B f _) |}. *)

Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((FP.cons x (FP.cons y .. (FP.cons z FP.nil) ..)) ;eq_refl).

(* Eval compute in (lib_list.(lib_prop)). *)

Eval compute in (lib_list.(lib_prop) (B := Build_DType nat _ ) S [[1; 2; 3 ; 4 ; 5 ; 6]]).

(* the induced lib_list.(map) function behaves as map on sized lists. *)

Time Eval compute in lib_list.(map) S [[1;2]].

(* Some more tests using the append function *)

Definition app {A} : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | FP.nil => m
   | a :: l1 => a :: app l1 m
  end.

Lemma app_length {A} : forall l l' : list A, length (app l l') = length l + length l'.
Proof.
  induction l; simpl; intros. reflexivity. apply ap. auto.
Defined.

Definition app_list {A:Type} {n n'} `{A ⋈ A} :
  {l: list A & length l = n} -> {l: list A & length l = n'}
  -> {l: list A & length l = n+n'} := ↑ Vector.append.

Definition app_list' {A:Type} {n n'} `{A ⋈ A} :
  {l: list A & length l = n} -> {l: list A & length l = n'}
  -> {l: list A & length l = n+n'}.
   intros l l'. exists (app l.1 l'.1). etransitivity. apply app_length. apply ap2; [exact l.2 | exact l'.2].
Defined.

Eval compute in (app_list [[1;2]] [[1;2]]).

Eval compute in (app_list' [[1;2]] [[1;2]]).

Eval compute in (lib_list.(map) S (app_list [[1;2]] [[5;6]])).

(* the lib_prop theorem has been lifted as expected. *)

Check lib_list.(lib_prop).

(* and can be effectively used *)

(* Eval compute in (lib_list.(lib_prop) S [[1; 2; 3]]). *)


(*****************************)
(* we now turn to a similar example, the record for Monoid *)

Record Monoid A :=
  Build_Monoid {
      mon_e : A;
      mon_m : A -> A -> A;
      mon_unitL : forall x, mon_m x mon_e = x;
      mon_unitR : forall x, mon_m mon_e x = x;
      mon_assoc : forall x y z, mon_m x (mon_m y z) = mon_m (mon_m x y) z
    }.

(* Again, the fact that it is univalent can be almost automatically inferred
   using its equivalent presentation with dependent sums *)

Instance issig_monoid {A : Type} :
  { e:A & {m:A -> A -> A & {uL : forall x, m x e = x & { uR : forall x, m e x = x &
                                            forall x y z, m x (m y z) = m (m x y) z}}}}
  ≃ Monoid A.
Proof.
  issig (Build_Monoid A) (@mon_e A) (@mon_m A) (@mon_unitL A) (@mon_unitR A) (@mon_assoc A).
Defined.

Instance issig_monoid_inv {A : Type} :
  Monoid A ≃
         { e:A & {m:A -> A -> A & {uL : forall x, m x e = x & { uR : forall x, m e x = x &
                                                                               forall x y z, m x (m y z) = m (m x y) z}}}}
         := Equiv_inverse _.


Definition FP_Monoid : Monoid ≈ Monoid.
Proof.
  univ_param_record.
Defined. 

Hint Extern 0 (Monoid ≈ Monoid) => exact (ur_type FP_Monoid) : typeclass_instances. 

Hint Extern 0 (Monoid _ ≃ Monoid _) => unshelve refine (equiv (ur_type FP_Monoid _ _ _)) : typeclass_instances. 

(* we define the monoid structure on N *)

Definition N_mon : Monoid N.
Proof.
  unshelve refine (Build_Monoid _ _ _ _ _ _).
  - exact N0.
  - exact N.add.
  - intro x. destruct x; reflexivity. 
  - intro x. destruct x; reflexivity.
  - intros. cbn. apply logic_eq_is_eq. exact (N.add_assoc x y z).  
Defined.

(* Then we can deduce automatically a monoid structure on nat *)

Definition n_mon : Monoid nat := ↑ N_mon.


(*****************************)

(* As mentioned in Sections 1 and 6, we can lift functions on 
   binary nats to operate on normal nats, sometimes considerably
   improving performance. *)

Definition nat_pow_ : nat -> nat -> nat := ↑ N.pow.

Definition nat_pow : nat -> nat -> nat := Eval compute in ↑ N.pow.


(* (the use of [Eval compute] in the definition above is to 
   force reduction of some noise produced by the lifting.) *)

Print Assumptions nat_pow_.
Print Assumptions nat_pow.

Definition lib_map_eff := Eval compute in lib_list.(@map _).
Definition lib_map_noeff := lib_list.(@map _).

Print Assumptions lib_map_eff.
Print Assumptions lib_map_noeff.


(* Definition lib_prop_eff := Eval compute in lib_list.(lib_prop) S [[5;6]]. *)

(* Eval compute in lib_list.  *)

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


Definition compat_alt_le : alt_le ≈ le_N.
  cbn; intros. rewrite H, H0. clear.
  revert x0; induction x; intro n; destruct n; cbn.
  all: try apply URType_Refl.
  unfold le_N in *. rewrite <- comp_S_inj. apply IHx. 
Defined.

End Alt_LE. 

Definition compat_le : le ≈ N.le. Admitted.

Hint Extern 0 (_ = _) => eapply compat_add : typeclass_instances.
Hint Extern 0 (_ = _) => eapply compat_mul : typeclass_instances.
Hint Extern 0 (_ = _) => eapply compat_div : typeclass_instances.
Hint Extern 0 (_ ⋈ _) => eapply compat_le : typeclass_instances. 
Hint Extern 0 (_ ≃ _) => eapply compat_le : typeclass_instances. 

Definition compat_add' : N.add ≈ plus := compat_inverse2 compat_add.
Definition compat_mul' : N.mul ≈ mult := compat_inverse2 compat_mul.
Definition compat_div' : N.div ≈ Nat.div := compat_inverse2 compat_div. 
Definition compat_le' : N.le ≈ le.
  cbn; intros. intros. apply UR_Type_Inverse. tc. 
Defined.

Hint Extern 0 (_ = _) => eapply compat_add' : typeclass_instances.
Hint Extern 0 (_ = _) => eapply compat_mul' : typeclass_instances.
Hint Extern 0 (_ = _) => eapply compat_div' : typeclass_instances.
Hint Extern 0 (_ ⋈ _) => eapply compat_le' : typeclass_instances. 
Hint Extern 0 (_ ≃ _) => eapply compat_le' : typeclass_instances. 


(* we can lift properties up to the correspondance table *)

Local Open Scope nat_scope.

Lemma nat_distrib : forall (c a b: nat), c * (a + b) = c * a + c * b.
Proof.
  induction c; intros; cbn.
  - reflexivity.
  - apply can_eq. tc.
    rewrite IHc. repeat rewrite <- plus_assoc.
    rewrite (plus_assoc b). rewrite (plus_comm b).
    repeat rewrite <- plus_assoc. reflexivity.
Defined.

Definition N_distrib : forall (c a b: N), (c * (a + b) = c * a + c * b)%N :=
  ↑ nat_distrib.

Eval compute in (N_distrib 1 2 3).

(* we can also convert functions from one setting to another *)

Definition square : nat -> nat := fun n => n * n.  

Definition N_square_def := ltac: (convert square : (N -> N)).

Definition N_square := N_square_def.1.

Check eq_refl : N_square = (fun x => (x * x)%N).

Hint Extern 0 (N_square_def.1 _ ≈ square _) => eapply N_square_def.2 : typeclass_instances. 

(* not that a direct lifting does not using the correspondance table *)

Fail Check eq_refl : ↑ square = (fun x:N => (x * x)%N).

(* And after adding the relation in the correspondance table, 
   we can convert proofs over converted functions *)

Lemma nat_distrib' : forall (c a b: nat), (a + b) * c = a * c + b * c.
Proof.
  intros. rewrite mult_comm. rewrite nat_distrib.
  rewrite mult_comm. rewrite (mult_comm c b). reflexivity. 
Defined.


Definition square_prop : forall n, square (2 * n) = 4 * square n.
  intro n. cbn. repeat rewrite plus_0_r. repeat rewrite nat_distrib.
  repeat rewrite nat_distrib'. repeat rewrite plus_assoc. reflexivity.
Defined. 

Opaque N.mul mult.

Definition N_square_prop : forall n, (N_square (2 * n) = 4 * N_square n)%N :=
  ↑ square_prop. 

Transparent N.mul mult.

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
apply (DecidableEq_equiv (↑n <= ↑m) (n <= m)%N).
apply compat_le; cbn; apply inverse. refine (e_retr N.of_nat n). refine (e_retr N.of_nat m).
tc. 
Defined.
 
Definition N_divide_conv :=
  ltac: (convert divide : (forall (n:N) (m : {m : N & (0 < m)%N}), N)).
Definition N_divide := N_divide_conv.1.

(* N_divide is really the division on N *)
Check eq_refl : N_divide = (fun x y => (x / y.1)%N).

(* more dependent version of divide (on Nat)*)

Definition divide_dep n (m : {m : nat & 0 < m }) : {res: nat & res <= n}.
  apply (existT _) with (x:=divide n m).
  destruct m as [m Hm]. destruct m.
  - inversion Hm.
  - apply Nat.div_le_upper_bound.
    + apply Nat.neq_succ_0.
    + rewrite <- Nat.mul_1_l at 1.
      apply Nat.mul_le_mono_r. apply le_n_S. apply Nat.le_0_l.
Defined.

Definition divide_dep_f := fun n m => (divide_dep n m).1.
Definition divide_dep_p := fun n m => (divide_dep n m).2.

(* Approach 1: start from divide_dep, convert first proj, lift second proj... *)

Definition N_divide_dep_f_conv :=
  ltac: (convert divide_dep_f : (forall (n:N) (m: {m : N & (0 < m)%N}), N)).
Definition N_divide_dep_f := N_divide_dep_f_conv.1.

Definition N_divide_dep_p_lift :=
  ltac: (lift divide_dep_p :
           (forall (n:N) (m : {m : N & (0 < m)%N}), (N_divide_dep_f n m <= n)%N)).
Definition N_divide_dep_p := N_divide_dep_p_lift.1.

(* ... and put the pieces together *)
Definition N_divide_dep_comp : forall (n:N) (m : {m : N & (0 < m)%N}),
    {res:N & (res <= n)%N} :=
  fun n m => existT _ (N_divide_dep_f n m) (N_divide_dep_p n m).

Definition arg : {m : N & (0 < m)%N}.
  apply (existT _) with (x:=N.succ (N.succ 0)). unfold lt_N.
  apply -> N.succ_le_mono. apply N.le_succ_diag_r.
Defined.
Eval lazy in (N_divide_dep_comp 10%N arg).1.

(* Approach 2: working with N_divide: lift the property wrt N_divide *)

Definition N_divide_dep_p'_lift := 
  ltac: (lift divide_dep_p : 
           (forall (n:N) (m : {m : N & (0 < m)%N}), (N_divide n m <= n)%N)).

Definition N_divide_dep_p' := N_divide_dep_p'_lift.1.

(* ... and basically lifting "by hand"... *)
Definition N_divide_dep_comp' : {function : forall (n:N) (m : {m : N & (0 < m)%N}),
                                  {res:N & (res <= n)%N} & divide_dep ≈ function}.
  exists (fun n m => (N_divide n m ; N_divide_dep_p' n m)).
  intros. unshelve eexists. cbn; tc. apply N_divide_dep_p'_lift.2.
Defined.
Eval lazy in (N_divide_dep_comp'.1 10%N arg).1.

(* Approach 3: more automatic, ad-hoc to the { conv & lift } setting *)

(* with a small tactic to do the job... *)
Tactic Notation "conv&lift" constr(function) :=
  let opt := fresh "opt" in
  match goal with | |-
    forall x:?A, forall y : ?B , @sigT ?T1 ?P =>
      unshelve refine (let opt : { opt : forall x:A, forall y : B, T1 & (fun a b => (function a b).1) ≈ opt} := _ in _) ;
      [ convert (fun a b => (function a b).1) : (forall x:A, forall y : B, T1) |
        intros a b; 
        exact (opt.1 a b ; (↑ (fun n  m => (function n m).2) : forall x:A, forall y : B,
                               P (opt.1 x y) ) a b)]
   | |- forall x:?A, @sigT ?T1 ?P =>
      unshelve refine (let opt : { opt : forall x:A, T1 & (fun a => (function a).1) ≈ opt} := _ in _) ;
      [ convert (fun a => (function a).1) : (forall x:A, T1) |
        intros a; 
        exact (opt.1 a ; (↑ (fun n => (function n).2) : forall (x:A),
                               P (opt.1 x) ) a)] 
  end.

(* ... it's direct! *)
Definition N_divide_dep_auto : forall (n:N) (m : {m : N & (0 < m)%N}), {res:N & (res <= n)%N}.
  conv&lift divide_dep.
Defined.
Eval lazy in (N_divide_dep_auto 10%N arg).1.

(* the two versions we derive manually are indeed equal *)
Check eq_refl : N_divide_dep_comp'.1 = N_divide_dep_comp.
(* can't prove it directly for the auto version (does not seem to terminate) *)
(* Check eq_refl : N_divide_dep_comp = N_divide_dep_auto. *)


(* In the timing experiments below, we use const0 to avoid 
   let binder optimization in newer versions of Coq. *)
Definition const0 {A} : A -> nat := fun _ => 0. 

(* Observe the evolution of time as the exponent increases, 
   in first the standard nat version, and in the lifted N version. 
   (all Time Eval commands are commented in order to not affect
   compilation time - just uncomment and eval to test.)

   Also, times commented below were produced on an iMac with 
   3.5 GHz Intel Core i5 -- results on your machine would certainly 
   differ, but the relative results is what matter.
*)

(* with the standard nat function: *)
(* Time Eval vm_compute in let x := Nat.pow 3 18 in const0 x. *)
(* 26:  8.221u *)
(* 27: 28.715u *)
(* 28: 83.669u *)

(* with the lifted function *)
(* Time Eval vm_compute in let x := nat_pow 2 26 in const0 x. *)
(* 26:  5.086u *)
(* 27: 12.173u *)
(* 28: 37.205u *)

(* The results are much better than with the standard nat function,
   but in fact, ALL the cost here in the lifted case is the conversion of 
   the resulting binary number back to a nat! (the power itself takes 0.u) *)

(* To illustrate, consider another function that also uses pow, but does 
   not necessarily produce big numbers: *)

(* a- the N version *)
Definition diffN x y n := N.sub (N.pow x n) (N.pow y n).

(* b- the nat version *)
Definition diff x y n := (Nat.pow x n) - (Nat.pow y n).

(* c- the nat version obtained by lifting the N version *)
Definition diff' : nat -> nat -> nat -> nat := Eval compute in ↑ diffN.

(* In the following, the computed value is 0 (so converting back 
   in the lifted version costs nothing). *)

(* the standard nat function is expectedly slow *)
(* Time Eval vm_compute in let x := diff 2 2 25 in const0 x. *)
(* 25:  8.322u *)
(* 26: 21.105u *)

(* the lifted function is blazzing fast! *)
(* Time Eval vm_compute in let x := diff' 2 2 25 in const0 x. *)
(* 25: 0.u *)
(* 26: 0.u *)
(* 27: 0.u *)
(* 28: 0.u *)

Definition nat_sub : nat -> nat -> nat := ↑ N.sub.

(* d- the combined version *)
Definition diff_comb x y n := nat_sub (nat_pow_ x n) (nat_pow_ y n).


Definition diff_opt := ltac: (optimize diff_comb).

Definition diff_comb_ := Eval compute in diff_comb.

(* Time Eval vm_compute in let x := diff_comb_ 2 2 25 in const0 x. *)

Check eq_refl : diff_opt.1 =
                fun x y n => ↑(N.pow (↑x) (↑n) - N.pow (↑y) (↑n))%N.

Fail Check eq_refl : diff_comb_ =
                (fun (x y n : nat) => ↑(N.pow (↑x) (↑n) - N.pow (↑y) (↑n))%N).

Time Eval vm_compute in let x := diff_opt.1 2 2 25 in const0 x.
