Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable .
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega.

Set Universe Polymorphism.


Tactic Notation "convert" constr(function) ":" constr(T) :=
  let X := fresh "X" in
  assert (X : { opt : T & function ≈ opt});
  [eexists; tc | exact X].

Ltac optimize f := let T := type of f in convert f : T. 

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

(* This file contains 3 examples: Lib, Monoid, and pow. 
   Lib and pow are mentioned in the paper. Monoid is not. *)

(*****************************)
(* we start with the Lib example (Section 1) *)

Record Lib (C : Type -> nat -> Type) :=
  { head : forall {A : Type} {n : nat}, C A (S n) -> A;
    map : forall {A B} (f:A -> B) {n}, C A n -> C B n;
    lib_prop : forall n A B (f : A -> B) (v : C A (S n)), head (map f v) = f (head v) }.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.
Arguments lib_prop {_} _ {_ _ _} _ _.

(* the proof that Lib is a univalent type constructor requires to 
   use an equivalent representation with dependent sums *)

Definition Lib_sig C :=   {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A B (f : A -> (B:Type)) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}.

Instance issig_lib_hd_map C : Lib_sig C ≃ Lib C.
Proof.
  issig (Build_Lib C) (@head C) (@map C) (@lib_prop C).
Defined.

Instance issig_lib_hd_map_inv C : Lib C ≃ Lib_sig C :=
  Equiv_inverse _.

Hint Extern 0 => progress (unfold Lib_sig) :  typeclass_instances.

(* the proof is automatic using the univ_param_record tactic *)

Definition FP_Lib : Lib ≈ Lib.
  univ_param_record.
Defined.

Hint Extern 0 (Lib _ ≃ Lib _) => erefine (ur_type FP_Lib _ _ _).(equiv); simpl
:  typeclass_instances.

(* we now define an instance of Lib for vectors *)

Definition lib_vector_prop : forall (n : nat) (A B : Type) (f : A -> B) (v : t A (S n)),
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

Definition FP_Lib_sig : Lib_sig ≈ Lib_sig.
  tc. 
Defined.

Hint Extern 0 (Lib_sig _ ≃ Lib_sig _) => erefine (ur_type FP_Lib_sig _ _ _).(equiv); simpl
:  typeclass_instances.

Definition lib_list' : Lib_sig (fun A n => {l: list A & length l = n}) := ↑ libvec'.

Notation vect_to_list := (vector_to_list _ _ (Equiv_id _) _ _ _).
Notation list_to_vect := (list_to_vector _ _ (Equiv_id _) _ _ _).

Definition lib_list'' : Lib (fun A n => {l: list A & length l = n}) :=
  {|
    head := fun A n l => hd (list_to_vect l);
    map := fun A B f n l => vect_to_list (Vector.map f (list_to_vect l));
    lib_prop := fun n A B f (l : {l : list A & length l = S n}) =>
                  transport_eq (fun l => hd (Vector.map f l) = f (hd l))
                               (e_sect _ _) 
                               (lib_vector_prop n A B f _) |}.

Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((FP.cons x (FP.cons y .. (FP.cons z FP.nil) ..)) ;eq_refl).

(* Eval compute in (lib_list'.2.2). *)

(* Eval compute in (lib_list''.2.2 _ _ _ S [[1; 2; 3 ; 4 ; 5 ; 6]]). *)
(* Eval compute in (lib_list''.(lib_prop) S [[1; 2; 3 ; 4 ; 5 ; 6]]). *)

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

Definition compat_add : plus ≈ N.add. Admitted.

Hint Extern 0 (_ = _) => eapply compat_add : typeclass_instances.

Definition compat_mul : mult ≈ N.mul. Admitted. 

Hint Extern 0 (_ = _) => eapply compat_mul : typeclass_instances.

Definition compat_add' : N.add ≈ plus. Admitted.

Hint Extern 0 (_ = _) => eapply compat_add' : typeclass_instances.

Definition compat_mul' : N.mul ≈ mult. Admitted. 

Hint Extern 0 (_ = _) => eapply compat_mul' : typeclass_instances.

Definition compat_div : Nat.div ≈ N.div. Admitted. 

Hint Extern 0 (_ = _) => eapply compat_div : typeclass_instances.

Definition compat_div' : N.div ≈ Nat.div. Admitted. 

Hint Extern 0 (_ = _) => eapply compat_div' : typeclass_instances.

Definition compat_lt : lt ≈ N.lt. Admitted.

Hint Extern 0 (_ ⋈ _) => eapply compat_lt : typeclass_instances. 

Definition compat_lt' : N.lt ≈ lt. Admitted.

Hint Extern 0 (_ ⋈ _) => eapply compat_lt' : typeclass_instances. 

Definition compat_le : le ≈ N.le. Admitted.

Hint Extern 0 (_ ⋈ _) => eapply compat_le : typeclass_instances. 

Definition compat_le' : N.le ≈ le. Admitted.

Hint Extern 0 (_ ⋈ _) => eapply compat_le' : typeclass_instances. 


(* we can lift properties up to the correspondance table *)

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

Lemma nat_distrib' : forall (c a b: nat), (a + b) * c = a * c + b * c.
Proof.
  intros. rewrite mult_comm. rewrite nat_distrib.
  rewrite mult_comm. rewrite (mult_comm c b). reflexivity. 
Defined.

(* And after adding the relation in the correspondance table, 
   we can convert proofs over converted functions *)

Hint Extern 0 (N_square_def.1 _ ≈ square _) => eapply N_square_def.2 : typeclass_instances. 

Definition square_prop : forall n, square (2 * n) = 4 * square n.
  intro n. cbn. repeat rewrite plus_0_r. repeat rewrite nat_distrib.
  repeat rewrite nat_distrib'. repeat rewrite plus_assoc. reflexivity.
Defined. 

Opaque N.mul mult.

Definition N_square_prop : forall n, (N_square (2 * n) = 4 * N_square n)%N :=
  ↑ square_prop. 

Transparent N.mul mult.

(* not that a direct lifting does not using the correspondance table *)

Fail Check eq_refl : ↑ square = (fun x:N => (x * x)%N).

(* we can even convert dependent functions *)

Definition divide n (m : {m : nat & 0 < m }) : nat := n / m.1.

Hint Extern 0 => progress (unfold projT1) :  typeclass_instances.

Definition N_divide_def :=
  ltac: (convert divide : (forall (n:N) (m : {m : N & (0 < m)%N}), N)).

Definition N_divide := N_divide_def.1.

Check eq_refl : N_divide = (fun x y => (x / y.1)%N).
 
Hint Extern 0 (N_divide_def.1 _ _ ≈ divide _ _) => eapply N_divide_def.2 : typeclass_instances. 


Definition Decidable_eq_N_leq k : forall (x y : {m : N & (k < m)%N}),  (x = y) + (x = y -> False).
Admitted.

Instance Transportable_N_leq k (P: {m : N & (k < m)%N} -> Type) : Transportable P :=
  Transportable_decidable P (Decidable_eq_N_leq k).

Definition Decidable_eq_nat_leq k : forall (x y : {m : nat & (k < m)}),  (x = y) + (x = y -> False).
Admitted.

Instance Transportable_nat_leq k (P: {m : nat & (k < m)} -> Type) : Transportable P :=
  Transportable_decidable P (Decidable_eq_nat_leq k).
  

(* more dependent version... *)
Definition divide_dep n (m : {m : nat & 0 < m }) : {res: nat & res <= n}.
  apply (existT _) with (x:=divide n m).
  unfold divide. destruct m as [m Hm]. cbn.  
  destruct m.
  - inversion Hm.
  - apply Nat.div_le_upper_bound.
    + apply Nat.neq_succ_0.
    + rewrite <- Nat.mul_1_l at 1.
      apply Nat.mul_le_mono_r. apply le_n_S. apply Nat.le_0_l.
Defined.


(* we need to do it in two steps, as the first projection is a conversion 
   while the second is a lifting *)

Definition N_divide_dep : forall (n:N) (m : {m : N & (0 < m)%N}),
    (N_divide n m <= n)%N := ↑ (fun n  m => (divide_dep n m).2).

Definition N_divide_dep_def : forall (n:N) (m : {m : N & (0 < m)%N}),
    {res:N & (res <= n)%N} :=
  fun n m => (N_divide n m ; N_divide_dep n m).


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
