Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable DecidableEq URStdLib.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith Conversion_table. 

Set Universe Polymorphism.


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
  univ_param_record.
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

(* using the equivalence between vectors and sized lists
   we can automatically infer the Lib structure on sized lists. 
*)

Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑ libvec.

Notation vect_to_list := (vector_to_list _ _ (Equiv_id _) _ _ _).
Notation list_to_vect := (list_to_vector _ _ (Equiv_id _) _ _ _).

Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((URStdLib.cons x (URStdLib.cons y .. (URStdLib.cons z URStdLib.nil) ..)) ;eq_refl).


(* the lib_prop theorem has been lifted as expected. *)

Check lib_list.(lib_prop).

(* and can be effectively used *)

Time Eval lazy in (lib_list.(lib_prop) S [[1; 2; 3 ; 4 ; 5 ; 6 ; 7 ; 8]]).

(* the induced lib_list.(map) function behaves as map on sized lists. *)

Time Eval lazy in lib_list.(map) S [[1; 2; 3 ; 4 ; 5 ; 6 ; 7 ; 8]].

(* Some more tests using the append function *)

Definition app {A} : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | URStdLib.nil => m
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
   intros l l'. exists (app l.1 l'.1). eapply concat. apply app_length. apply ap2; [exact l.2 | exact l'.2].
Defined.

Eval compute in (app_list [[1;2]] [[1;2]]).

Eval compute in (app_list' [[1;2]] [[1;2]]).

Eval compute in (lib_list.(map) S (app_list [[1;2]] [[5;6]])).

Eval compute in (lib_list.(map) neg (app_list [[true;false]] [[true;false]])).

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

Goal forall n m, nat_pow n (S m) = n * nat_pow n m.
  intros. simpl. unfold nat_pow at 1. 
Abort. 
  
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


(* Observe the evolution of time as the exponent increases, 
   in first the standard nat version, and in the lifted N version. 
   (all Time Eval commands are commented in order to not affect
   compilation time - just uncomment and eval to test.)

   Also, times commented below were produced on an iMac with 
   3.5 GHz Intel Core i5 -- results on your machine would certainly 
   differ, but the relative results is what matter.
*)

(* In the timing experiments below, we use const0 to avoid 
   let binder optimization in newer versions of Coq. *)
Definition const0 {A} : A -> nat := fun _ => 0. 

(* with the standard nat function: *)
Time Eval vm_compute in let x := Nat.pow 3 15 in const0 x.
(* 26:  8.221u *)
(* 27: 28.715u *)
(* 28: 83.669u *)

(* with the lifted function *)
Time Eval vm_compute in let x := nat_pow 3 15 in const0 x.
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

(* Example doing change of representation à la CoqEAL *)

(* correspondance between libraries over nat and N *)
(* we can also convert functions from one setting to another *)

Definition square : nat -> nat := fun n => n * n.  

(* not that a direct lifting does not using the correspondance table *)

Fail Check eq_refl : (↑ square : N -> N) = (fun x:N => (x * x)%N).

Check eq_refl : (↑ square : N -> N) = (fun x:N => ↑ (square (↑ x))).



Definition N_square_def := ltac: (convert square : (N -> N)).

Check (N_square_def :{opt : N -> N & square ≈ opt}). 

Definition N_square := N_square_def.1.

Check eq_refl : N_square = (fun x => (x * x)%N).

(* add square and N_square in the conversion table *)

Hint Extern 0 (square _ = _) => eapply N_square_def.2 : typeclass_instances.

Arguments square : simpl never.

(* we can lift properties up to the correspondance table *)


Lemma nat_distrib : forall (c a b: nat), c * (a + b) = c * a + c * b.
Proof.
  induction c; intros; cbn.
  - reflexivity.
  - apply can_eq. tc.
    unfold mult; fold mult. rewrite IHc. repeat rewrite <- plus_assoc.
    rewrite (plus_assoc b). rewrite (plus_comm b).
    repeat rewrite <- plus_assoc. reflexivity.
Defined.

Definition N_distrib : forall (c a b: N), (c * (a + b) = c * a + c * b)%N :=
  ↑ nat_distrib.

Eval compute in (N_distrib 1 2 3).

(* And after adding the relation in the correspondance table, 
   we can convert proofs over converted functions *)

Lemma nat_distrib' : forall (c a b: nat), (a + b) * c = a * c + b * c.
Proof.
  intros. rewrite mult_comm. rewrite nat_distrib.
  rewrite mult_comm. rewrite (mult_comm c b). reflexivity. 
Defined.

Definition square_prop : forall n, square (2 * n) = 4 * square n.
  unfold square, mult; fold mult.
  intro n. cbn. repeat rewrite plus_0_r. repeat rewrite nat_distrib.
  repeat rewrite nat_distrib'. repeat rewrite plus_assoc.  reflexivity.
Defined. 

Definition N_square_prop : forall n, (N_square (2 * n) = 4 * N_square n)%N :=
  ↑ square_prop. 

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


Definition N_divide_conv :=
  ltac: (convert divide : (forall (n:N) (m : {m : N & (0 < m)%N}), N)).
Arguments divide : simpl never.
Hint Extern 0 => eapply N_divide_conv.2 : typeclass_instances.

Definition N_divide := N_divide_conv.1.

(* N_divide is really the division on N *)
Check eq_refl : N_divide = (fun x y => (x / y.1)%N).

(* more dependent version of divide (on Nat)*)

Definition divide_dep_p n (m : {m : nat & 0 < m }) : divide n m <= n.
  destruct m as [m Hm]. destruct m.
  - inversion Hm.
  - apply Nat.div_le_upper_bound.
    + apply Nat.neq_succ_0.
    + rewrite <- Nat.mul_1_l at 1.
      apply Nat.mul_le_mono_r. apply le_n_S. apply Nat.le_0_l.
Qed.

Definition divide_dep n (m : {m : nat & 0 < m }) : {res: nat & res <= n} :=
  (divide n m ; divide_dep_p n m).

(* divide_dep_p is a proof with no computational meaning, so we want to lift it globally *)

Hint Extern 0 (divide_dep_p _ _ ≈ ?g _ _) => direct_lifting divide_dep_p g : typeclass_instances.

(* Approach 1: start from divide, N_divide and divide_dep, convert first proj, lift second proj... *)

Definition N_divide_dep_p_conv := ltac: (convert divide_dep_p : (forall (n:N) (m : {m : N & (0 < m)%N}), (N_divide n m <= n)%N)).

Definition N_divide_dep_p := N_divide_dep_p_conv.1.

(* ... and put the pieces together *)
Definition N_divide_dep_comp : forall (n:N) (m : {m : N & (0 < m)%N}),
    {res:N & (res <= n)%N} :=
  fun n m => (N_divide n m; N_divide_dep_p n m).

Definition N_two : {m : N & (0 < m)%N}.
  apply (existT _) with (x:=N.succ (N.succ 0)). unfold lt_N.
  apply -> N.succ_le_mono. apply N.le_succ_diag_r.
Defined.

Eval lazy in (N_divide_dep_comp 10%N N_two).1.

(* Approach 2: more automatic *)
(* ... it's direct! *)

Definition N_divide_dep_auto_conv :=
  ltac: (convert divide_dep : (forall (n:N) (m : {m : N & (0 < m)%N}), {res:N & (res <= n)%N})). 

Definition N_divide_dep_auto := N_divide_dep_auto_conv.1.

Eval lazy in (N_divide_dep_auto 10%N N_two).1.

(* the two versions we derive are indeed equal *)

Goal N_divide_dep_comp = N_divide_dep_auto.
  reflexivity.
Defined. 


(* Now, we can exploit the new divide - N_divide correspondance 
to efficiently convert nat functions that use divide, such as avg below *)

Definition two_zero : 0 < 2.
  apply -> Nat.succ_le_mono. apply Nat.le_succ_diag_r.
Qed.

Definition two : {n:nat & 0 < n} := (2 ; two_zero).

Definition avg (x y: nat) := divide (x + y) two.

(* first, make sure that TC resolution exploits the correspondance *)

Definition N_two_lift := ltac: (convert two : {n:N & (0 < n)%N}).

Eval compute in N_two_lift.1.

(* here also, feed the TC resolution *)
Hint Extern 0  => eapply N_two_lift.2 : typeclass_instances.

(* instruct resolution to dive into avg if helpful *)
Hint Extern 0 => progress (unfold avg) :  typeclass_instances.

(* now convert  *)

Definition N_avg_conv := ltac: (convert avg : (N -> N -> N)).

Definition N_avg := N_avg_conv.1.

(* it works... *)
Eval lazy in N_avg 10%N 30%N.

(* and is needed the same as the hand-written N-based version *)
Check eq_refl : N_avg = (fun x y => N_divide (x + y) N_two).
