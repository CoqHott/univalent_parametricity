Set Polymorphic Inductive Cumulativity. 

Set Universe Polymorphism.

Require Import HoTT UR FP Coq.Program.Tactics.

(* HSet and Hedberg *)

Class DecidableEq A := { dec_paths : forall a b : A, (a = b) + (a = b -> False)}.

(**
Hedberg theorem is a standard theorem of HoTT: it states that if a
type [A] has decidable equality, then it is a hSet, i.e. its equality
is proof-irrelevant. See the proof at [https://github.com/HoTT] in
[HoTT/theories/Basics/Decidable.v] *)

Instance Hedberg A `{DecidableEq A} : HSet A.
Proof.
  econstructor. 
  intros a b.
  assert (lemma: forall p: a = b,  
             match dec_paths a a, dec_paths a b with
             | inl r, inl s => p = r^ @ s
             | _, _ => False
             end).
  {
    destruct p.
    destruct (dec_paths a a) as [pr | f].
    - apply inverse_left_inverse.
    - exact (f eq_refl).
  }
  intros p q.
  assert (p_given_by_dec := lemma p).
  assert (q_given_by_dec := lemma q).
  destruct (dec_paths a b); try contradiction.
  destruct (dec_paths a a); try contradiction.
  apply (p_given_by_dec @ q_given_by_dec ^).
Defined.


Instance IsHSet_compare : HSet comparison.
  apply Hedberg.
  econstructor. destruct a, b; try solve [now left]; solve [now right].
Defined.

Definition DecidableEq_equiv A B (eB : A ≃ B) `{DecidableEq A} : DecidableEq B. 
Proof.
  constructor. pose (eB' := Equiv_inverse eB).
  intros x y. destruct (dec_paths (↑ x) (↑ y)). 
  - left. apply (@isequiv_ap _ _ eB'). exact e.
  - right. intro e. apply f. exact (ap _ e).
Defined. 

Instance DecidableEq_Sigma A (B : A -> Type) `{DecidableEq A} `{forall a, DecidableEq (B a)} :
  DecidableEq {a : A & B a}.
Proof.
  constructor. intros [a b] [a' b' ].
  destruct (dec_paths a a').
  - destruct e. destruct (dec_paths b b').
    + apply inl. apply path_sigma_uncurried. exists eq_refl. exact e.
    + apply inr; intro Hf; apply f. pose (Hf..2).
      assert (Hf..1 = eq_refl). apply is_hset. rewrite X in e. exact e.
  - apply inr; intro Hf; apply f. exact (Hf..1).
Defined.





Instance Transportable_decidable {A} (P:A -> Type) `{DecidableEq A} : Transportable P.
Proof.
  unshelve econstructor.
  - intros x y e. destruct (dec_paths x y) as [e0 | n0].
    destruct e0. apply Equiv_id.
    destruct (n0 e).
  - intro x. cbn. destruct (dec_paths x x); cbn.
    assert (e = eq_refl) by (eapply is_hset).
    rewrite X. reflexivity.
    destruct (f eq_refl).
Defined. 


Definition Canonical_eq_decidable_ A `{DecidableEq A} :
  forall x y:A , x = y -> x = y :=
  fun x y e => match (dec_paths x y) with
               | inl e0 => e0
               | inr n => match (n e) with end
               end. 

Instance Canonical_eq_decidable A `{DecidableEq A} : Canonical_eq A.
Proof. 
  refine {| can_eq := @Canonical_eq_decidable_ A H |}.
  - unfold Canonical_eq_decidable_. intro x. cbn. destruct (dec_paths x x); cbn.
    assert (e = eq_refl) by (eapply is_hset).
    rewrite X. reflexivity.
    destruct (f eq_refl).
Defined.



(*! Establishing FP for Type with a decidable equality !*)

Definition URType_Refl_decidable A (dec:DecidableEq A)
  : A ⋈ A :=
  URType_Refl_can A (@Canonical_eq_decidable  _ dec).

Structure DType@{i} :=
  { carrier :> Type@{i} ;
    dec : DecidableEq@{i} carrier }.

Instance DTypeDec (A : DType) : DecidableEq A.(carrier) := A.(dec). 

Instance UR_DType_def@{i j} : UR@{j j j} DType@{i} DType@{i} :=
  Build_UR@{j j j} _ _ (fun A B => UR_Type@{i i i} A.(carrier) B.(carrier)).

Program Definition URDType_Refl : URRefl DType DType (Equiv_id _) _ :=
   {| ur_refl_ := fun a : DType => URType_Refl_decidable a.(carrier) (DTypeDec a) |}.

Definition path_DType (A B : DType)
           (pq : {p : A.(carrier) = B.(carrier) & A.(dec) = p^ # B.(dec)})
: A = B.
Proof.
  destruct pq as [p q]. destruct A, B. simpl in *. destruct p.
  simpl in q; destruct q; reflexivity.
Defined.

Definition path_DecidableEq A (dec dec': DecidableEq A) : dec.(@dec_paths A) = dec'.(@dec_paths A) -> dec = dec'. 
  destruct dec, dec'. cbn. destruct 1. reflexivity.
Defined. 

Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => False
                 end)
: z = z'.
  destruct z, z'.
  all:try apply ap, pq.
  all:elim pq.
Defined.

Definition dec_hprop A : IsHProp (DecidableEq A).
  intros decA decA'. apply path_DecidableEq. apply funext. intro a. apply funext. intro a'.
  apply path_sum. destruct (dec_paths a a'); destruct (dec_paths a a'); auto. 
  apply is_hset. apply funext. intro e. destruct (f e).
Defined.

Definition path_DType_simple A B (decA : DecidableEq A) (decB : DecidableEq B) (e : A = B) :
  {| carrier := A; dec := decA |} = {| carrier := B; dec := decB |}.
  apply path_DType. exists e. destruct e. apply dec_hprop. 
Defined. 

Definition dec_hprop_hprop A (decA : DecidableEq A) :
  dec_hprop A decA decA = eq_refl.
  apply IsHProp_IsHprop. apply dec_hprop. 
Defined.

Definition path_DType_simple_refl A (decA : DecidableEq A) :
  path_DType_simple A A decA decA eq_refl = eq_refl.
Proof.
  unfold path_DType_simple. cbn. rewrite dec_hprop_hprop.
  reflexivity. 
Defined. 

Definition path_DType_proj {A B : DType} :
  A = B -> carrier A = carrier B.
  destruct 1. reflexivity.
Defined. 

Definition path_DType_eq (A B:DType)
           (e : @eq DType A B) :
  match A,B return forall (e:A = B), Type with (Build_DType A decA),(Build_DType B decB)
=> fun e => 
     path_DType_simple A B decA decB (path_DType_proj e) = e end e.
  destruct e, A. cbn. rewrite dec_hprop_hprop. reflexivity. 
Defined. 

Definition path_DType_eq' A B (decA : DecidableEq A) (decB : DecidableEq B)
           (e : {| carrier := A; dec := decA |} = {| carrier := B; dec := decB |}) :
  path_DType_simple _ _ _ _ (path_DType_proj e) = e := path_DType_eq _ _ e.

Opaque path_DType_simple.

Definition can_eq_eq_dec {A} {decA} (e :Canonical_eq A) : e.(can_eq) = Canonical_eq_decidable_ A.
Proof.
  apply funext; intros x. apply funext; intros y. apply funext; intro E.
  apply is_hset. 
Defined.

Definition Canonical_contr_dec A (ecanA : Canonical_eq A) (e : DecidableEq A) :
  ecanA = Canonical_eq_decidable A.
Proof.
  unshelve eapply Canonical_eq_eq. cbn.
  apply can_eq_eq_dec. apply IsHProp_IsHprop.
  repeat (apply IsHProp_forall; intro). 
  intros E E'. apply is_hset.
Defined.

Instance URDType_IsEq : URIsEq DType DType (Equiv_id _) _ URDType_Refl.
Proof.
  intros A B. destruct A as [A decA], B as [B decB]. cbn.
  unshelve refine (isequiv_adjointify _ _ _ _).
  - intros e. cbn in *. apply path_DType_simple. apply univalence. typeclasses eauto.
  - intros e.  cbn.
    refine (transport_eq (fun (E: {| carrier := A; dec := decA |} = {| carrier := B; dec := decB |}) => path_DType_simple A B decA decB
    (e_inv (eq_to_equiv A B)
           (equiv (transport_eq (fun X : DType => A ⋈ X) E (URType_Refl_decidable A decA)))) = E)
                         (path_DType_eq _ _ e) _).
    set (path_DType_proj e). cbn in *. apply ap. destruct e0. clear e. 
    assert (decA = decB). apply dec_hprop. destruct X. cbn.
    rewrite path_DType_simple_refl. 
    exact (@e_sect _ _ _ (univalence _ _) eq_refl).
  - intro e; cbn.
    destruct e as [e eur ecoh ecanA ecanB].
    revert eur ecoh ecanA ecanB. rewrite <- (@e_retr _ _ _ (univalence _ _) _).
    set (eeq := (e_inv _ e)).
    clearbody eeq;clear e.
    destruct eeq. intros eur ecoh ecanA ecanB.
    simpl.
    destruct eur as [eur].
    destruct ecoh as [ecoh].
    simpl in *.
    change (Equiv_id A) with (eq_to_equiv A A eq_refl).
    rewrite (@e_sect _ _ _ (univalence _ _) _). simpl.
    assert (decA = decB). apply dec_hprop. destruct X. cbn.
    rewrite path_DType_simple_refl. cbn. 
    unfold URType_Refl_decidable, URType_Refl_can, UR_gen. cbn. 
    rewrite <- (@e_retr _ _ (e_fun (equiv_relation_equiv_fun _ _ _ _)) _ ecoh).
    set (p := (e_inv _ ecoh)).
    clearbody p. clear ecoh.
    destruct p. cbn. 
    assert (ecanA = Canonical_eq_decidable A) by apply Canonical_contr_dec.
    assert (ecanB = Canonical_eq_decidable A) by apply Canonical_contr_dec.
    destruct X, X0. 
    reflexivity.
Defined.

Instance Canonical_eq_DType : Canonical_eq DType := Canonical_eq_gen _.

Instance FP_DType : DType ⋈ DType.
Proof. 
  econstructor; try typeclasses eauto.
Defined.

(* nat *)

Instance DecidableEq_eq_nat : DecidableEq (nat:Type).
constructor. intros x y; revert y. 
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (ap S H).
    intro H; right. intro e. inversion e. apply (H (logic_eq_is_eq H1)).
Defined.

Canonical Structure Dnat : DType := Build_DType nat _.

(*! bool !*)

Instance DecidableEq_eq_bool : DecidableEq bool.
constructor. intros x y; revert y. induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- destruct y.
 + right; intro H; inversion H.
 + left ;reflexivity.
Defined.

Canonical Structure Dbool : DType := Build_DType bool _.

Instance Decidable_leq n m : DecidableEq (n <= m).
constructor. revert m n. intros n m.  
assert (forall n n'
(e : n = n'), forall (le_mn1 : m <= n) (le_mn2 : m <= n'), Logic.eq (e # le_mn1) le_mn2).
clear.
intros. revert n' e le_mn2.
induction le_mn1 using le_rect; intros. 
- destruct le_mn2 using le_rect.
  + assert (e = eq_refl). apply is_hset. rewrite X. reflexivity.
  + assert False. clear - e le_mn2. rewrite e in le_mn2. apply (inv_leq _ 0 le_mn2). destruct H.
- destruct le_mn2 using le_rect; try clear IHle_mn2.
  + assert False. clear - e le_mn1. rewrite <- e in le_mn1. apply (inv_leq _ 0 le_mn1). destruct H. 
  + assert (m0 = m1). clear - e. inversion e. reflexivity.
    specialize (IHle_mn1 _ X le_mn2). rewrite <- IHle_mn1.
    assert (e = ap S X). apply is_hset. rewrite X0 in *. clear e X0.
    destruct X. reflexivity. 
- intros a b; apply inl. destruct (H _ _ eq_refl a b). reflexivity. 
Defined. 


Definition DecidableEq_hprop : forall (A B : DType), A.(carrier) = B.(carrier) -> A = B.
  intros A B e. destruct A as [A decA], B as [B decB]. cbn in *. assert (HSet A). apply Hedberg. auto. 
  apply path_DType. cbn in *. exists e. apply path_DecidableEq. apply funext. intro a. apply funext. intro b.
  destruct decA, decB. destruct e. cbn. apply path_sum. destruct (dec_paths0 a b), (dec_paths1 a b); auto. 
  apply is_hset. apply funext. intro e. destruct (f e).
Defined. 
