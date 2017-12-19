Require Import HoTT Tactics UR URTactics FP Record MoreInductive.
Require Import BinInt BinNat Nnat Vector.

Set Universe Polymorphism.

Definition univalent_transport_eff {A B : Type} {e: A ≃ B} `{@Equiv_eff A B e} : A -> B := e_fun e.  

Notation "↑eff" := univalent_transport_eff (at level 65, only parsing).

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
    prop : forall n A B (f : A -> B) (v : C A (S n)), head (map f v) = f (head v)}.

Arguments map {_} _ {_ _} _ {_} _.
Arguments head {_} _ {_ _} _.


(* Definition FL_Lib_Noneff : Lib ≈ Lib.  *)
(*   split; [apply Transportable_default | ]. *)
  
(*   intros C C' e.  *)
(*   pose (eqCC' := e_inv (ur_coh (H := @URForall Type Type (fun _ : Type => forall _ : nat, Type) *)
(*        (fun _ : Type => forall _ : nat, Type) UR_Type_def *)
(*        (fun (x y : Type) (_ : @ur Type Type UR_Type_def x y) => *)
(*         @URForall nat nat (fun _ : nat => Type) (fun _ : nat => Type) UR_nat *)
(*                   (fun (x0 y0 : nat) (_ : @ur nat nat UR_nat x0 y0) => UR_Type_def))) _ _) e). *)
(*   destruct eqCC'. apply Canonical_UR. apply Equiv_id. *)
(* Defined. *)

Instance issig_lib_hd_map C :
  {hd : forall {A : Type} {n : nat}, C A (S n) -> A  &
                      {map : forall {A B} (f:A -> B) {n},
  C A n -> C B n &
  forall n A B (f : A -> B) (v : C A (S n)), hd _ _ (map _ _ f _ v) = f (hd _ _ v)}}
  ≃ Lib C.
Proof.
  issig (Build_Lib C) (@head C) (@map C) (@prop C).
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
  cbn. split ; [apply Transportable_default | ]. intros.
  unshelve refine (UR_Type_Equiv_gen _ _ _ _ _ _ _ _).
  cbn; intros. apply H; typeclasses eauto.
  unshelve refine (snd (FP_Sigma _ _ _) _ _ _).
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  cbn. intros.
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances. 
  (* maybe better here *)
  apply Transportable_default.
  intros.
  erefine (snd (FP_forall _ _ _) _ _ (Transportable_arrow _ _,_)).
  apply H. cbn. 
  typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
  split. apply Transportable_default.
  intros.
  unshelve refine (snd (FP_Sigma _ _ _) _ _ _).
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  cbn. intros.
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances. 
  (* maybe better here *)
  apply Transportable_default.
  intros.
  erefine (snd (FP_forall _ _ _) _ _ (Transportable_arrow _ _,_)).
  erefine (snd (FP_forall _ _ _) _ _ (Transportable_arrow _ _,_)).
  typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
  intros.
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  pose (fst (H x1 x1 (ur_refl x1))). destruct t. unshelve econstructor. intros. apply admit. apply admit. 
  intros.
  erefine (snd (FP_forall _ _ _) _ _ (Transportable_arrow _ _,_)).
  apply H. 
  typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
  intros; apply H. typeclasses eauto with typeclass_instances.
  typeclasses eauto with typeclass_instances.
  cbn. split. apply Transportable_default. 
  intros.
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  intros. cbn.
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  cbn. intros. 
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  cbn. intros. 
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  cbn. intros. 
  unshelve refine (snd (FP_forall _ _ _) _ _ (_,_)).
  apply H; typeclasses eauto with typeclass_instances.
  apply Transportable_default.
  cbn. intros. 
  typeclasses eauto with typeclass_instances.

  (* univ_param_record. *)
Defined.

Hint Extern 0 (Lib _ ≃ Lib _) => erefine (snd FP_Lib _ _ _).(equiv); simpl
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
     prop := lib_vector_prop |}.

Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑ libvec.

(* Definition lib_list : Lib (fun A n => {l: list A & length l = n}) := ↑eff libvec. *)

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

(*
Definition FP_Monoid : Monoid ≈ Monoid.
Proof.
  univ_param_record.
Defined. 

Hint Extern 0 (Monoid ≈ Monoid) => exact FP_Monoid : typeclass_instances. 

Hint Extern 0 (Monoid _ ≃ Monoid _) => unshelve refine (equiv (FP_Monoid _ _ _)) : typeclass_instances. 

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
 *)

(* Those tests are commented at compilation time *)

(* Time Eval vm_compute in lt x := nat_pow 2 26 in 0. *)
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

Definition largeVector := incrVector 20.

Definition largeVectorN : Vector.t N 20 := ↑ largeVector.

(* Time Eval vm_compute in largeVectorN. *)

(* 3 secs *) 

Definition largeVectorN' : Vector.t N 20 := e_fun (Equiv_Vector _ _ _ _ _ eq_refl) largeVector.

(* Time Eval vm_compute in largeVectorN'. *)


Definition foo : forall f: nat -> nat, f = f:= fun f  => eq_refl.

(* Set Typeclasses Debug Verbosity 2. *)

Instance Transportable_eq A B (f g : A -> B) : Transportable (fun a => f a = g a) := Transportable_default _.

Definition bar := ↑ foo : forall f: N -> N, f = f.

(* Definition bar_equiv : (forall f: nat -> nat, f = f) ≃ (forall f: N -> N, f = f) := _. *)

(* Goal Equiv_eff _ _ bar_equiv. *)
(*   Fail typeclasses eauto.  *)
(* Abort.  *)

(* does not compute because of the index on a dependent product *)

Eval compute in foo S.

(* Eval compute in (bar N.succ). *)

Definition testType := { f : nat -> nat & vector nat (f 0)}.

Definition testType2 := { f : nat -> nat & {l : list nat & length l = f 0}}.

Definition foo' : testType2 := (S ; [[4]]).

Hint Extern 100 (_ = _) => solve [typeclasses eauto with typeclass_instances] : typeclass_instances.

Hint Extern 0 => progress (unfold testType, testType2) :  typeclass_instances.

Instance Transportable_sigma (A:Type) `{A ≈ A} A' B (f : A -> B) (x:A') :
  Transportable (fun g => {a: A & f a = g x}).
Proof.
  unshelve econstructor. intros. erefine (@Equiv_Sigma _ _ _ _ _ _).
  exact H. cbn. split.
  typeclasses eauto. 
  intros. apply admit. 
  apply admit.
Defined.

Instance Transportable_eq2 (A B:Type) (a:A) (b:B):
  Transportable (fun f => f a = b) := Transportable_default _ . 


Definition bar' : testType := ↑ foo'.

Eval cbn in bar'.2.

Definition testType' := { f : N -> N & vector nat (↑ (f (N.add N0 N0)))}.

Definition testType2' := { f : nat -> nat & {l : list nat & length l = f (0+0)}}.

Definition foo'' : testType2' := (S ; [[1]]).

Hint Extern 0 => progress (unfold testType', testType2') :  typeclass_instances.

Definition bar'' : testType' := ↑ foo''.

Eval compute in bar''.2.

Definition foo''' : testType' := (N.succ ; cons nat 1 0 (nil nat)).

Definition Transportable_lift_ A B C (g : B -> C) (P : C -> Type) `{Transportable C P} x:
  forall f f': A -> B, f = f' -> P (g (f x)) ≃ P (g (f' x)). 
  intros. assert (g (f x) = g (f' x)). destruct X; reflexivity.
  apply H. typeclasses eauto.
Defined.

Instance Transportable_lift A B C (g : B -> C) (P : C -> Type) `{Transportable C P} x:
  Transportable (fun (f:A -> B) => P (g (f x))). 
Proof.
  refine (Build_Transportable _ _ (Transportable_lift_ A B C g P x) _). 
  intros. apply H. 
Defined. 

Instance Transportable_lift_cst B C (g : B -> C) (P : C -> Type) `{Transportable C P}:
  Transportable (fun (f:B) => P (g f)).
Proof.
  unshelve econstructor. intros. apply H. 
Defined. 

Definition bar''' : testType2' := ↑ foo'''.
Eval compute in bar'''.2.1.

Definition testEquiv : testType2' ≃ testType' := _.

Definition bar2''' : testType2' := e_inv' testEquiv foo'''.
 
Eval compute in bar2'''.2.1.

Definition testTypeForall := forall f : {f : N -> N & f 0%N = 1%N}, N.

Definition testTypeForall' := forall f : {f : nat -> nat & f 0 = 1}, nat.

Definition fooForall : testTypeForall' := fun f => f.1 0 + 1.

Hint Extern 0 => progress (unfold testTypeForall, testTypeForall') :  typeclass_instances.

Definition barForall : testTypeForall := ↑ fooForall.

Eval compute in fooForall (S; eq_refl).

Eval compute in barForall (N.succ; eq_refl).

Definition barForall_equiv : testTypeForall' ≃ testTypeForall := _.

(* Goal Equiv_eff _ _ barForall_equiv. *)
(*   Fail typeclasses eauto. *)
(* Abort.  *)


Definition testTypeForall2 := forall f : {n : nat & N}, vector N f.1.

Definition testTypeForall2' := forall f : { x : nat & nat}, vector nat f.1.

Fixpoint ConstantVector {A} (a:A) n : vector A n :=
  match n with 0 => nil _
          | S n => cons _ a _ (ConstantVector a n)
  end.
                                                   
Definition fooForall2 : testTypeForall2' := fun f => ConstantVector 10 f.1.

Hint Extern 0 => progress (unfold testTypeForall2, testTypeForall2') :  typeclass_instances.

Hint Extern 100 (_ = _) => progress destruct_sigma : typeclass_instances.

Ltac destruct_prod := repeat (match goal with | H : _ * _ |- _ => destruct H end).

Hint Extern 100 (_ = _) => progress destruct_prod : typeclass_instances.

Definition barForall2 : testTypeForall2 := ↑ fooForall2.

Eval compute in fooForall2 (2;10).

Eval compute in barForall2 (2;10%N).

Definition barForall2_equiv : testTypeForall2' ≃ testTypeForall2 := _.

Instance Equiv_eff_compose A B C (e: A ≃ B) (e': B ≃ C)
         `{@Equiv_eff _ _ e} `{@Equiv_eff _ _ e'} : Equiv_eff _ _ (e' ∘∘ e).

(* Goal Equiv_eff _ _ barForall2_equiv. *)
(*   typeclasses eauto.  *)
(* Defined.  *)

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




