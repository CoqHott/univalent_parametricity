Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable Conversion_table.
Require Import BinInt BinNat Nnat Vector Arith.Plus Omega ZArith.

Set Universe Polymorphism.


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


Definition plus (n m : nat) : nat := nat_rect (fun _ => nat) m (fun _ res => S res) n.

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


