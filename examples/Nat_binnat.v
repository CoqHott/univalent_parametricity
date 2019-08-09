Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable DecidableEq.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.

(* Moving stuff that was in MoreInductive.v related to nat/binnat *)

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

Instance Equiv_N_nat : nat ≃ N := BuildEquiv _ _ N.of_nat _. 

Instance Equiv_nat_N : N ≃ nat := Equiv_inverse _.

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

Goal N -> nat-> N ⋈ nat -> nat -> nat.
  tc.
Qed. 



(*****************************)

(* As mentioned in Sections 1 and 6, we can lift functions on 
   binary nats to operate on normal nats, sometimes considerably
   improving performance. *)

Definition nat_pow_ : nat -> nat -> nat := ↑ N.pow.

Print Assumptions nat_pow_.

(* (the use of [Eval compute] in the definition above is to 
   force reduction of some noise produced by the lifting.) *)

Definition nat_pow : nat -> nat -> nat := Eval compute in ↑ N.pow.

Print Assumptions nat_pow.


Definition const0 {A} : A -> nat := fun _ => 0. 

(* with the standard nat function: *)
(* Time Eval vm_compute in let x := Nat.pow 3 15 in const0 x. *)

(* with the lifted function *)
(* Time Eval vm_compute in let x := nat_pow 3 15 in const0 x. *)



Goal forall n m, nat_pow n (S m) = n * nat_pow n m.
  intros. simpl. unfold nat_pow at 1.
Abort. 


Definition diff n (e : 0 = S n) : False :=
  let P := nat_rect (fun _ => Type) (0 = 0) (fun n _ => False) in
  eq_rect nat 0 (fun n' _ => P n') eq_refl (S n) e.

Definition N0 : N := ↑ 0.
Definition NS : N -> N := ↑ S.

Definition O_correct : 0 ≈ N0.
  refine (@ur_refl nat N _ _).
Defined.
Definition S_correct : S ≈ NS.
  refine (@ur_refl (nat -> nat) (N -> N) _ _).
Defined.

Hint Extern 10 (0 = _) => apply O_correct : typeclass_instances.
Hint Extern 10 (S _ = _) => apply S_correct : typeclass_instances.

Arguments S_correct : simpl never.
 (* nat_rect not polymorphic *)
Definition nat'_rect :
           forall P : N -> Type, P N0 -> (forall n : N, P n -> P (NS n)) -> forall n : N, P n
 := ↑ nat_rect.

Lemma decidable_eq_false : DecidableEq False.
Proof.
  constructor. intuition.
Defined.

Instance FP_False : False ⋈ False := URType_Refl_decidable False decidable_eq_false.

Definition diff_N : forall n, N0 = NS n -> False := ↑ diff.

Definition diff_N_5 : N0 = NS 5 -> False := ↑ (diff 5).
Example diff_N_5' := Eval compute in diff_N_5.
Print Assumptions diff_N_5'.

Definition diff' n (e : N0 = NS n) : False.
  (* refine ( *)
  (* match e in eq _ _ n' return *)
  (*       nat'_rect (fun _ => Type) *)
  (*                (N0 = N0) *)
  (*                (fun n _ => False) n' *)
  (* with *)
  (*   | eq_refl => _ *)
  (* end). *)

  set (foo :=
         nat'_rect (fun _ : N => Type) (N0 = N0) (fun (_ : N) (_ : Type) => False) (NS n)).
  hnf in foo.
  set (foo' := e_fun (equiv _)) in foo.
  lazy in foo'. subst foo'.
  unfold ur_type in foo.
  unfold ur_refl in foo. unfold ur_coh in foo.
  set (foo' := e_fun (equiv _)) in foo.
  lazy in foo'.
  subst foo'. unfold NS in foo.
  unfold ur_coh in foo. unfold univalent_transport in foo.
  set (foo' := Equiv_Arrow _ _ _ _ _ _ _ _) in foo.
  lazy in foo'. subst foo'. cbv beta iota fix in foo.
  set (foo' := equiv _) in foo.
Abort.


(* Definition my_plus (n m : nat) : nat := nat_rect (fun _ => nat) m (fun _ res => S res) n. *)

Definition plus_N (n m : N) : N := nat'_rect (fun _ => N) m (fun _ res => NS res) n.

Definition plus_N' : N -> N -> N := ↑ plus.

Eval lazy in plus_N' (2%N) (3%N).


Definition funvector A n := Fin.t n -> A.

Fixpoint vector_to_funvector A n (v : vector A n) : funvector A n.
  destruct v.
  - intro bot. inversion bot.
  - intro k. inversion k.
    + exact h.
    + subst. exact (vector_to_funvector _ _ v H0).
Defined.

Fixpoint funvector_to_vector A n (f : funvector A n) {struct n} : vector A n.
  destruct n.
  - exact (nil _).
  - refine (vcons _ _).
    + exact (f Fin.F1).
    + exact (funvector_to_vector _ _ (fun k =>  f (Fin.FS k))).
Defined.

Instance isequiv_vector_to_funvector A n : IsEquiv (vector_to_funvector A n).
Proof.
  unshelve refine (isequiv_adjointify _ (funvector_to_vector A n) _ _).
  - induction x; cbn.
    + reflexivity.
    + now apply ap. 
  - intro f. apply funext. intro k. induction k; cbn.
    + reflexivity.
    + apply IHk.
Defined.

Instance Equiv_vector_funvector A n : Equiv (vector A n) (funvector A n)
  := BuildEquiv _ _ (vector_to_funvector A n) _. 

Instance Equiv_funvector_vector A n : Equiv (funvector A n) (vector A n)
 := Equiv_inverse _.

Instance UR_Fin n n' (e : n = n') : UR (Fin.t n) (Fin.t n').
destruct e. exact (UR_gen (Fin.t n)).
Defined. 

Definition FP_finvector : funvector ≈ funvector. 
  cbn. intros. econstructor. tc. intros n n' e.
  erefine (ur_type (FP_forall _ _ _) _ _ {| transport_ := _; ur_type
                                                             := _|}); cbn in *.
  destruct e. apply  URType_Refl_can. econstructor. reflexivity. tc.
  intros. exact H.
Defined. 

Instance Equiv_funvector_instance : forall x y : Type, x ⋈ y -> forall
  n n' (e:n=n'), (funvector x n) ⋈ (funvector y n') :=
  fun x y e n n' en => ur_type (FP_finvector x y e) n n' en. 

Definition compat_vector_funvector : vector ≈ funvector.
Proof.
  cbn; intros. econstructor. tc. intros.
  eapply UR_Type_Equiv. apply Equiv_funvector_vector. tc. 
Defined. 

