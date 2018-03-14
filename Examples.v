Require Import HoTT Tactics UR URTactics FP Record MoreInductive Transportable.
Require Import BinInt BinNat Nnat Vector.

Set Universe Polymorphism.

Definition append_list {A:Type} {n p} {H : A ⋈ A} :
  {l : list A & length l = n} ->
  {l : list A & length l = p} ->
  {l : list A & length l = n+p}   := ↑ Vector.append.

Eval compute in ((append_list ([1;2];eq_refl) ([4;5;6];eq_refl)).1).

Definition map_list {A B} (e : A ≃ B)
           {HA : ur A A} {HB : ur B B}
           (f:A -> B) {n} :
  {l : list A & length l = n} ->
  {l : list B & length l = n}
  := ↑ (Vector.map f).

Typeclasses Transparent map_list.

Typeclasses Opaque vector_to_list list_to_vector.

Opaque vector_to_list list_to_vector.

Record Lib (C : Type -> nat -> Type) :=
  { head : forall {A : Type} {n : nat}, C A (S n) -> A;
    map : forall {A B} (f:A -> B) {n}, C A n -> C B n;
    lib_prop : forall n A B (f : A -> B) (v : C A (S n)), head (map f v) = f (head v)}.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.
Arguments lib_prop {_} _ {_ _ _} _ _.

(*
Definition FL_Lib_Noneff : Lib ≈ Lib.
  split; [apply Transportable_default | ].
  
  intros C C' e.
  pose (@URForall Type Type (fun _ : Type => forall _ : nat, Type)
       (fun _ : Type => forall _ : nat, Type) UR_Type_def
       (fun (x y : Type) (_ : @ur Type Type UR_Type_def x y) =>
        @URForall nat nat (fun _ : nat => Type) (fun _ : nat => Type)
	          (UR_gen nat) (fun (x0 y0 : nat) (_ : eq nat x0 y0) => UR_Type_def))).
  pose (@ur_coh _ _ _ u). cbn in e0.
  pose (@Ur_Coh (Type -> nat -> Type) (Type -> nat -> Type) _). cbn in u0.
  unfold u in *. clear u. 
  unfold Equiv_Arrow in e0.
  pose (e_inv (e0 u0 C C')).
  cbn in e.
  specialize  (e1 (fun _ _ _ =>  ur_type (e _ _ _))). 
  destruct e1. apply Canonical_UR. apply Equiv_id.
Defined.
*)
  
Instance issig_lib_hd_map C :
  {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A B (f : A -> B) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v)}}
  ≃ Lib C.
Proof.
  issig (Build_Lib C) (@head C) (@map C) (@lib_prop C).
Defined.

Instance issig_lib_hd_map_inv C :
  Lib C ≃
  {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
           forall n A B (f : A -> B) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v)}} :=
  Equiv_inverse _.
  
Definition FP_Lib : Lib ≈ Lib.
Proof.
  univ_param_record.
Defined.

Hint Extern 0 (Lib _ ≃ Lib _) => erefine (ur_type FP_Lib _ _ _).(equiv); simpl
:  typeclass_instances.

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

Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑ libvec.


Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((FP.cons x (FP.cons y .. (FP.cons z FP.nil) ..)) ;eq_refl).

Time Eval compute in lib_list.(map) S [[1;2]].

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


Record Monoid A :=
  Build_Monoid {
      mon_e : A;
      mon_m : A -> A -> A;
      mon_unitL : forall x, mon_m x mon_e = x;
      mon_unitR : forall x, mon_m mon_e x = x;
      mon_assoc : forall x y z, mon_m x (mon_m y z) = mon_m (mon_m x y) z
    }.

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

Definition N_mon : Monoid N.
Proof.
  unshelve refine (Build_Monoid _ _ _ _ _ _).
  - exact N0.
  - exact N.add.
  - intro x. destruct x; reflexivity. 
  - intro x. destruct x; reflexivity.
  - intros. cbn. apply logic_eq_is_eq. exact (N.add_assoc x y z).  
Defined.

Definition n_mon : Monoid nat := ↑ N_mon.

Notation "a ++ b" := (n_mon.(mult) a b).

Fixpoint even (n:nat) := match n with
                             0 => true
                           | 1 => false
                           | S (S n) => even n
                           end. 

Definition nat_pow : nat -> nat -> nat := ↑ N.pow.
 
(* Those tests are commented at compilation time *)

(* Time Eval vm_compute in let x := nat_pow 2 26 in 0. *)
(* 18.725u *)

(* Time Eval vm_compute in let x := Nat.pow 2 26 in 0. *)
(* 36.493u *)

(* Time Eval vm_compute in let x := N.pow 2 26 in 0. *)
(* 0.1u *)

Fixpoint incrVector n : Vector.t nat n :=
  match n with
    0 => nil _
  | S n => cons _ n _ (incrVector n)
  end. 

Definition largeVector := incrVector 200.

Definition largeVectorN : Vector.t N 200 := ↑ largeVector.

Time Eval vm_compute in largeVectorN.

(* 3 secs *) 

Definition largeVectorN' : Vector.t N 200 := e_fun (Equiv_Vector _ _ _ _ _ eq_refl) largeVector.

Time Eval vm_compute in largeVectorN'.

Fixpoint ConstantVector {A} (a:A) n : vector A n :=
  match n with 0 => nil _
          | S n => cons _ a _ (ConstantVector a n)
  end.

Definition foo : forall f: nat -> nat, f = f:= fun f => eq_refl.

Definition bar := ↑ foo : forall f: N -> N, f = f.

(* Definition bar_equiv : (forall f: nat -> nat, f = f) ≃ (forall f: N -> N, f = f) := _. *)

Eval compute in foo S.

(* Eval compute in (bar N.succ). *)

Definition foo' : forall f: nat -> nat, vector nat (f 0)
  := fun f => ConstantVector 1 (f 0).


Definition bar' := ↑ foo' : forall f: N -> nat, vector N (f (↑ 0)).

(* Definition bar_equiv : (forall f: nat -> nat, f = f) ≃ (forall f: N -> N, f = f) := _. *)

Eval compute in foo' S.

Eval compute in bar' (↑ S).

Definition testType := { f : nat -> nat & vector nat (f 0)}.

Definition testType2 := { f : nat -> nat & {l : list nat & length l = f 0}}.

Transparent vector_to_list list_to_vector.

Notation "[[ ]]" := ([ ]; eq_refl).
Notation "[[ x ]]" := ([x]; eq_refl).
Notation "[[ x ; y ; .. ; z ]]" := ((FP.cons x (FP.cons y .. (FP.cons z FP.nil) ..)) ;eq_refl).

Definition foo'' : testType2 := (S ; [[4]]).


Definition testType'' := { f : forall x : N, { n : N & n = N.add x 1%N} & vector nat (↑ ((f (N.add N0 N0)).1))}.

Definition testType2'' := { f : forall x : nat, { n : nat & n = x + 1} & {l : list nat & length l = (f (0+0)).1}}.

Definition foo'''' : testType2'' := (fun n => (n+1; eq_refl) ; [[1]]).

Hint Extern 0 => progress (unfold testType'', testType2'') :  typeclass_instances.

Definition to_nat_add : forall x y, N.to_nat (N.add x y) = N.to_nat x + N.to_nat y.
  intros. pose (N2Nat.inj_add x y). destruct e. reflexivity.
Defined. 

Hint Extern 0 (_ = _) => rewrite to_nat_add :  typeclass_instances.

Ltac destruct_sigma2 := repeat (match goal with | H : forall (x:_) (y:_) (z:_) , @sigT _ ?P |- _ => 
                    let H1 := fresh "H1" in 
                    let H2 := fresh "H2" in
                    let P' := fresh "P'" in
                    pose (H1:= fun x y z => (H x y z).1);
                    pose (P' := forall x y z, P (H1 x y z));
                    pose (H2:= (fun x y z => (H x y z).2) : P'); cbn in H2;
                    clearbody H1; clearbody H2; clear H; unfold P' in H2; clear P' 
  end).

Hint Extern 0 (_ = _) => progress destruct_sigma2 : typeclass_instances.

(* Hint Extern 0 (_ = _) => match goal with | H : forall _ _ _, _ |- ?G => is_ground G; refine (H _ _ _) end: typeclass_instances. *)

Goal nat = N ->  (forall x : nat, {n : nat & n = x + 1})
                 =
                 (forall x : N, {n : N & n = (x + 1)%N}).
  intro e.   
  pose (P := fun X (pp : X -> X -> X) (one : X) => forall x:X, {n : X & n = pp x one}).
  change (P nat plus 1 = P N N.add 1%N).
  assert (P nat Nat.add 1 = P N (fun x y => transport_eq (fun X => X) e ((transport_eq (fun X => X) e^ x) + (transport_eq (fun X => X) e^ y))) (transport_eq (fun X => X) e 1)).
  destruct e. reflexivity. etransitivity; try exact X.
Abort. 
  
Instance toto :  Equiv testType2'' testType''.
  erefine (@Equiv_Sigma _ _ _ _ _ _); cbn in *; intros.
  typeclasses eauto.
  econstructor.   typeclasses eauto.
  intros. erefine (ur_type (Equiv_list_vector_ _ _ _) _ _ _) .
  typeclasses eauto. cbn in *.
  destruct_sigma2. refine (H1 _ _ _). 
Defined.
  
Definition bar'''' : testType'' := ↑ foo''''.

Eval compute in (bar''''.1 0%N).2 .
Eval compute in bar''''.2.

Definition testTypeForall := forall f : { f : N -> Type & N}, N.

Definition testTypeForall' := forall f : { f : nat -> Type & nat}, nat.

Definition fooForall : testTypeForall' := fun f => f.2.

Hint Extern 0 => progress (unfold testTypeForall, testTypeForall') :  typeclass_instances.

Definition barForall : testTypeForall := ↑ fooForall.

Eval compute in fooForall (fun n => n = n; 1).

Eval compute in barForall (fun n => n = n; 1%N).

Definition barForall_equiv : testTypeForall' ≃ testTypeForall := _.

Definition testTypeForall2 := forall f : {n : nat & N}, vector N f.1.

Definition testTypeForall2' := forall f : { x : nat & nat}, vector nat f.1.
                                                   
Definition fooForall2 : testTypeForall2' := fun f => ConstantVector 10 f.1.

Hint Extern 0 => progress (unfold testTypeForall2, testTypeForall2') :  typeclass_instances.

Ltac destruct_sigma := repeat (match goal with | H : {_ : _ & _} |- _ => destruct H end).

Hint Extern 100 (_ = _) => progress destruct_sigma : typeclass_instances.

Ltac destruct_prod := repeat (match goal with | H : _ * _ |- _ => destruct H end).

Hint Extern 100 (_ = _) => progress destruct_prod : typeclass_instances.

Definition barForall2 : testTypeForall2 := ↑ fooForall2.

Eval compute in fooForall2 (2;10).

Eval compute in barForall2 (2;10%N).

Definition barForall2_equiv : testTypeForall2' ≃ testTypeForall2 := _.

Definition testTypeForall3 := forall f : ((N -> N) * (nat * N)), vector N (fst (snd f)).

Definition testTypeForall3' := forall f : ((nat -> nat) * (nat * nat)), vector nat (fst (snd f)).

Definition fooForall3 : testTypeForall3' := fun f => ConstantVector 10 (fst (snd f)).

Hint Extern 0 => progress (unfold testTypeForall3, testTypeForall3') :  typeclass_instances.

Definition barForall3 : testTypeForall3 := ↑ fooForall3.

Eval compute in fooForall3 (S, (1,10)).

Eval compute in barForall3 (N.succ, (1,10%N)).

Definition barForall3_equiv : testTypeForall3' ≃ testTypeForall3 := _.

Definition testTypeForall4 := forall f : {f : N -> nat & { x : nat & N}}, vector N (f.1 0%N).

Definition testTypeForall4' := forall f : {f : nat -> nat & { x : nat & nat}}, vector nat (f.1 0).

Definition fooForall4 : testTypeForall4' := fun f => ConstantVector 10 (f.1 0).

Hint Extern 0 => progress (unfold testTypeForall4, testTypeForall4') :  typeclass_instances.

Definition barForall4 : testTypeForall4 := ↑ fooForall4.

Eval compute in fooForall4 (S; (1;10)).

Eval compute in barForall4 (fun n => ↑ (N.succ n); (1;10%N)).


Definition testTypeForall5 := forall f : (N -> N) * { x : nat & N}, vector N (snd f).1.

Definition testTypeForall5' := forall f : (nat -> nat) * { x : nat & nat}, vector nat (snd f).1.

Definition fooForall5 : testTypeForall5' := fun f => ConstantVector 10 (snd f).1.

Hint Extern 0 => progress (unfold testTypeForall5, testTypeForall5') :  typeclass_instances.

Definition barForall5 : testTypeForall5 := ↑ fooForall5.

Eval compute in fooForall5 (S, (1;10)).

Eval compute in barForall5 (N.succ, (2;10%N)).


Definition testTypeForall6 := forall X : {f : (N -> nat) & vector N (f 0%N)}, vector N (S (X.1 0%N)).

Definition testTypeForall6' := forall X : {f : (nat -> nat) & vector nat (f 0)}, vector nat (S (X.1 0)).

Definition fooForall6 : testTypeForall6 := fun X => cons _ 0%N _ X.2.

Hint Extern 0 => progress (unfold testTypeForall6, testTypeForall6') :  typeclass_instances.

Definition barForall6 : testTypeForall6' := ↑ fooForall6.

Eval compute in fooForall6 (fun n => S (↑ n) ; ConstantVector (6%N) 1).

Eval compute in barForall6 (S; ConstantVector 6 1).



Definition foo_Eq : forall f: N -> N, forall n, f n = f n := fun f n => eq_refl.

Definition bar_Eq := ↑ foo_Eq : forall f: nat -> nat, forall n,  f n = f n.

Eval compute in foo_Eq N.succ 0.
