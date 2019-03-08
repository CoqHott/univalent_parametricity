Require Import HoTT HoTT_axioms Tactics UR URTactics FP Record MoreInductive Transportable .
Require Import BinInt BinNat Nnat Vector.

Set Universe Polymorphism.

(* This file contains 3 examples: Lib, Monoid, and pow. 
   Lib and pow are mentioned in the paper. Monoid is not. *)

(*****************************)
(* we start with the Lib example (Section 1) *)

Record Lib (C : Type -> nat -> Type) :=
  { head : forall {A : Type} {n : nat}, C A (S n) -> A;
    map : forall {A B} (f:A -> B) {n}, C A n -> C B n;
    lib_prop : forall n A (f : A -> nat) (v : C A (S n)), head (map f v) = f (head v) }.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.
Arguments lib_prop {_} _ {_ _} _ _.

(* the proof that Lib is a univalent type constructor requires to 
   use an equivalent representation with dependent sums *)

Definition Lib_sig C :=   {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A (f : A -> (nat:Type)) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v) : Type}}.

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

Definition lib_vector_prop : forall (n : nat) (A : Type) (f : A -> nat) (v : t A (S n)),
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

Definition lib_list' : Lib (fun A n => {l: list A & length l = n}) :=
  {|
    head := fun A n l => hd (list_to_vect l);
    map := fun A B f n l => vect_to_list (Vector.map f (list_to_vect l));
    lib_prop := fun n A f (l : {l : list A & length l = S n}) =>
                  transport_eq (fun l => hd (Vector.map f l) = f (hd l))
                               (e_sect _ _) 
                               (lib_vector_prop n A f _) |}.


Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((FP.cons x (FP.cons y .. (FP.cons z FP.nil) ..)) ;eq_refl).

Eval compute in (lib_list'.(lib_prop)).
Eval compute in (lib_list'.(lib_prop) S [[1; 2; 3 ; 4 ; 5 ; 6]]).

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

Eval compute in (lib_list.(lib_prop) S [[1; 2; 3]]).

Goal forall A B x n m e,  @e_inv _ _ _ (IsEquiv_vector_list A B (equiv x) n m e) = @e_inv _ _ _ (IsEquiv_vector_list A B (equiv x) n m e).
  intros. compute. 
Abort.

(* Set Printing Implicit. *)

Definition Equiv_Sigma_unfold A A' e B B' e' :
  (let (e_fun, _) := Equiv_Sigma A A' e B B' e' in e_fun) =
  @sigma_map A A' B B' (@univalent_transport A A' (@equiv _ _ e))
    (fun a : A =>
     @univalent_transport (B a) (B' (@univalent_transport A A' (@equiv _ _ e) a))
       (@equiv _ _
          (@ur_type _ _ _ _ _ e' a (@univalent_transport A A' (@equiv _ _ e) a)
             (@ur_refl A A' e a)))) := eq_refl.

Arguments Build_UR_Type _ _ _ {_ _ _ _}.

(* Goal lib_list.(@lib_prop _) = lib_list.(@lib_prop _).  *)
(* Proof. *)
(*   unfold lib_list, univalent_transport. *)
(*   unfold FP_Lib. unfold UR_Type_Equiv_gen. unfold ur_type. unfold equiv.  *)
(*   unfold UR_Type_Equiv', UR_Type_Equiv, equiv. unfold Equiv_inverse. *)
(*   unfold equiv_compose. unfold e_fun. unfold e_inv. unfold issig_lib_hd_map_inv. *)
(*   unfold Equiv_inverse. unfold e_isequiv. unfold isequiv_inverse. unfold equiv. *)
(*   unfold issig_lib_hd_map. unfold e_fun. unfold lib_prop. unfold ur_type. *)
(*   unfold isequiv_adjointify, e_inv. *)
(*   cbv delta [FP_Sigma]. unfold e_fun. *)
(*   match goal with | |- ((let (e_fun, _) := Equiv_Sigma ?A ?A' ?e ?B ?B' ?e' in e_fun) *)
(*                           ?X).2.2 = *)
(*                        ((let (e_fun, _) := Equiv_Sigma ?A ?A' ?e ?B ?B' ?e' in e_fun) *)
(*                           ?X).2.2 => change ((@sigma_map A A' B B' (@univalent_transport A A' (@equiv _ _ e)) *)
(*     (fun a : A => *)
(*      @univalent_transport (B a) (B' (@univalent_transport A A' (@equiv _ _ e) a)) *)
(*        (@equiv _ _ *)
(*           (@ur_type _ _ _ _ _ e' a (@univalent_transport A A' (@equiv _ _ e) a) *)
(*              (@ur_refl A A' e a)))) X).2.2 = (@sigma_map A A' B B' (@univalent_transport A A' (@equiv _ _ e)) *)
(*     (fun a : A => *)
(*      @univalent_transport (B a) (B' (@univalent_transport A A' (@equiv _ _ e) a)) *)
(*        (@equiv _ _ *)
(*           (@ur_type _ _ _ _ _ e' a (@univalent_transport A A' (@equiv _ _ e) a) *)
(*                     (@ur_refl A A' e a)))) X).2.2 ) end. *)
(*   unfold sigma_map. *)
(*   match goal with | |- (?X;?Y).2.2 = (?X;?Y).2.2 => change (Y.2 = Y.2) end. *)
(*   unfold univalent_transport. unfold ur_type. unfold equiv. unfold e_fun. *)
(*   match goal with | |- ((let (e_fun, _) := Equiv_Sigma ?A ?A' ?e ?B ?B' ?e' in e_fun) *)
(*                           ?X).2 = *)
(*                        ((let (e_fun, _) := Equiv_Sigma ?A ?A' ?e ?B ?B' ?e' in e_fun) *)
(*                           ?X).2 => change ((@sigma_map A A' B B' (@univalent_transport A A' (@equiv _ _ e)) *)
(*     (fun a : A => *)
(*      @univalent_transport (B a) (B' (@univalent_transport A A' (@equiv _ _ e) a)) *)
(*        (@equiv _ _ *)
(*           (@ur_type _ _ _ _ _ e' a (@univalent_transport A A' (@equiv _ _ e) a) *)
(*              (@ur_refl A A' e a)))) X).2 = (@sigma_map A A' B B' (@univalent_transport A A' (@equiv _ _ e)) *)
(*     (fun a : A => *)
(*      @univalent_transport (B a) (B' (@univalent_transport A A' (@equiv _ _ e) a)) *)
(*        (@equiv _ _ *)
(*           (@ur_type _ _ _ _ _ e' a (@univalent_transport A A' (@equiv _ _ e) a) *)
(*                     (@ur_refl A A' e a)))) X).2 ) end. *)
(*   unfold sigma_map. *)
(*   match goal with | |- (?X;?Y).2 = (?X;?Y).2 => change (Y = Y) end. *)
(*   unfold univalent_transport. unfold ur_type. unfold equiv. unfold e_fun. *)
  
(*   unfold FP_forall. *)
(*   cbv delta [FP_forall]. unfold e_fun. *)

(*   match goal with | |- ((let (e_fun, _) := equiv (ur_type (FP_forall ?A ?A' ?e)) ?B ?B' ?e' in e_fun) *)
(*                           ?X) = *)
(*                        ((let (e_fun, _) := equiv (ur_type (FP_forall ?A ?A' ?e)) ?B ?B' ?e' in e_fun) *)
(*                           ?X) => change ((@Equiv_forall A A' e B B' e' X) =  ) end. *)
  
(*   cbv delta [FP_forall]. *)
(*   unfold projT2. *)
(*   rewrite Equiv_Sigma_unfold. *)
(*   unfold Equiv_Sigma. *)
(*   unfold e_fun.  *)
(*   match goal with  *)
(*   Opaque sigma_map. unfold Equiv_Sigma. e_fun. *)
(*   simpl.  *)
 
(*   compute - [ur_type Transportable_Forall_default Transportable_Type Transportable_cst FP_forall *)
(*                      UR_Type_Equiv_gen Equiv_vector_list_ Transportable_nat libvec]. *)
  
(*   set (ur_type FP_Lib t (fun (A : Set) (n : nat) => {l : list A & length l = n}) *)
(*            (fun (x y : Set) (H : x ⋈ y) => *)
(*             {| transport_ := Transportable_nat (t x); ur_type := fun (x0 y0 : nat) (H0 : x0 ≈ y0) => ur_type (Equiv_vector_list_ x y H) x0 y0 H0 |})).  *)
(*   change . *)
(*   compute - [FP_Lib Equiv_vector_list_ Transportable_nat]. *)
(*   unfold FP_Lib. unfold equiv.  *)
(*   unfold ur_type. *)
(*   unfold UR_Type_Equiv_gen. unfold UR_Type_Equiv, equiv. *)
(*   unfold issig_lib_hd_map_inv. *)
(*   unfold issig_lib_hd_map. unfold isequiv_adjointify. *)
(*   unfold Equiv_inverse. unfold equiv_compose. unfold e_fun. unfold e_inv. *)
  
(*   unfold e_inv. unfold UR_Type_Equiv'. equiv. *)
(*   unfold libvec. unfold equiv.  *)
(*   cbv delta - [FP_Sigma FP_forall Equiv_vector_list_ Transportable_Forall_default]. *)
  
(*   unfold libvec. unfold UR_Type_Equiv', equiv. unfold ur_type. *)
(*   unfold FP_Sigma, equiv. unfold Equiv_inverse. FP_forall.  *)
(*   compute - [ *)
    
  

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

(* Eval compute in lib_list.  *)

Require Import Arith.Plus.

Definition compat_add : plus ≈ N.add.
Admitted.

Hint Extern 0 (_ = N.to_nat _) => apply compat_add :  typeclass_instances.

Definition compat_mul : mult ≈ N.mul.
Admitted. 

Hint Extern 0 (_ = N.to_nat _) => apply compat_mul :  typeclass_instances.

Definition compat_add' : N.add ≈ plus.
Admitted.

Hint Extern 0 (_ = N.of_nat _) => apply compat_add' :  typeclass_instances.

Definition compat_mul' : N.mul ≈ mult.
Admitted. 

Hint Extern 0 (_ = N.of_nat _) => apply compat_mul' :  typeclass_instances.

Lemma nat_distrib : forall (c a b: nat), c * (a + b) = c * a + c * b.
Proof.
  induction c; intros; cbn.
  - reflexivity.
  - rewrite IHc. repeat rewrite <- plus_assoc.
    rewrite (plus_assoc b). rewrite (plus_comm b).
    repeat rewrite <- plus_assoc. reflexivity.
Defined.

Definition N_distrib : forall (c a b: N), (c * (a + b) = c * a + c * b)%N :=
  ↑ nat_distrib. 

Definition square : forall (n : nat), nat := fun n => n * n.  

Definition N_square_unopt : { f : N -> N & f ≈ square}.
  exists (fun x => ↑ (square (↑ x))).
  cbn. tc.
Defined. 

Check eq_refl : N_square_unopt.1 = ↑ square. 

Definition N_square_opt : { f : N -> N & f ≈ square}.
  eexists. tc.
Defined.

Check eq_refl : N_square_opt.1 = (fun x:N => (x * x)%N).

Goal { lib_prop_opt : forall (n : nat) (A : Set)
                  (f : A -> nat) (v : {l : list A & length l = S n}),
       head lib_list (map lib_list f v) = f (head lib_list v) & lib_list.(@lib_prop _) = lib_prop_opt }.
  Opaque lib_list. 
  refine (existT _ _ _).
  Transparent lib_list.

  reflexivity.
Abort.

Definition lib_prop_eff := Eval compute in lib_list.(lib_prop) S [[5;6]].

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

Time Eval vm_compute in let x := N.pow 3 23 in x.


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

Tactic Notation "optimize" constr(function) "with" constr(f) constr(g) constr(equiv) :=
  let X := fresh "X" in
  assert (X : { opt : _ & function = opt});
  [eexists; repeat (apply funext ; intros) ;
  compute - [f g];
  repeat rewrite (e_sect' equiv);
  repeat rewrite (e_retr' equiv);
  reflexivity | exact X.1].

Definition diff'_opt := ltac: (optimize diff_comb with N.of_nat N.to_nat Equiv_N_nat).

Definition diff_comb_ := Eval compute in diff_comb.

(* Time Eval vm_compute in let x := diff_comb_ 2 2 25 in const0 x. *)

Time Eval vm_compute in let x := diff'_opt 2 2 25 in const0 x.


Nat.pow = 
fix pow (n m : nat) {struct m} : nat := match m with
                                        | 0 => 1
                                        | S m0 => n * pow n m0
                                        end


                                          
                                         