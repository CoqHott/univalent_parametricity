(************************************************************************)
(* This file introduces the univalent logical relation framework, and
   defines the relation for basic type constructors *)
(************************************************************************)
Require Import HoTT CanonicalEq.
Require Import UnivalentParametricity.theories.Transportable.
Require Import URTactics.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import TransparentState.
From Ltac2 Require Import Bool.
From Ltac2 Require Import Constr.
Require Export UnivalentParametricity.theories.Ltac2Utils.


Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Unset Collapse Sorts ToType.

#[export] Set Typeclasses Unique Instances.
#[export] Set Typeclasses Strict Resolution.

(* basic class for parametric relations *)
Variant parametricity_kind : Set :=
  | plain
  | univalent.

Class PR@{sA sB sR;uA uB uR} (k : parametricity_kind)
(A: Type@{sA;uA}) (B : Type@{sB;uB}) : Type@{max(uA,uB,uR+1)} := {
  pr : A -> B -> Type@{sR;uR}
}.

Arguments pr k {_ _ _} a b.

Notation "x ≈[ k ] y" := (pr k x y) (at level 20).
Notation "x ≈p y" := (x ≈[plain] y) (at level 20).
Notation "x ≈u y" := (x ≈[univalent] y) (at level 20).
Definition PR_Type_plain@{sA sB sR;uA uB uR j} : PR@{Type Type Type | j j j} plain Type@{sA|uA} Type@{sB|uB} :=
  Build_PR@{Type Type Type | j j j} _ _ _ (PR@{sA sB sR; uA uB uR} plain).

Definition UR_Coh@{sA sB sR;uA uB uR} (A: Type@{sA;uA}) (B : Type@{sB;uB})
  (e : A ≃ B) (H: PR@{sA sB sR;uA uB uR} plain A B) :=
  forall (a a':A), (iff@{sR sR SProp; uR uR Set uR}(a = a') (@pr _ _ _ H a (↑ a'))).

Definition UR_Irr@{sA sB sR;uA uB uR} (A :Type@{sA;uA}) (B :Type@{sB;uB}) (H: PR@{sA sB sR;uA uB uR} plain A B) :=
  forall (a:A) (b:B) (e e' : a ≈p b), e = e'.

Record UR_Type@{sA sB sR;uA uB uR} A B : Type@{max(uA,uB,uR+1)}:=
  {
    Ur : PR@{sA sB sR;uA uB uR} plain A B;
    equiv : Equiv@{sA sB;uA uB} A B;
    Ur_Coh : UR_Coh@{sA sB sR;uA uB uR} A B equiv Ur;
    Ur_Irr : UR_Irr@{sA sB sR;uA uB uR} A B Ur
  }.

Ltac2 shelve_non_PR () :=
  match! reverse goal with
  | [ |- PR _ _ _ ] => ()
  | [ |- UR_Type _ _ ] => ()
  | [ |- pr _ _ _ ] => ()
  | [ |- _ ] => Control.shelve ()
  end.

Ltac2 ur_type_of_ur_tc (ur_tc : constr) : constr * constr :=
  let ty := Constr.type ur_tc in
  let ty := eval hnf in $ty in
  match! ty with
  | UR_Type ?a ?b => (a, b)
  | _ => fail "ur_type_of_ur_tc: expected %t ?a ?b, got %t" 'UR_Type ty
  end.

Ltac2 shelve_non_PR_multi () := Control.enter (fun _ => shelve_non_PR ()).

Ltac shelve_non_PR := ltac2:(shelve_non_PR_multi ()).

Definition PR_Type_univ@{sA sB sR;uA uB uR j} : PR@{Type Type Type ; j j j} univalent Type@{sA;uA} Type@{sB;uB} :=
  Build_PR@{Type Type Type | j j j} _ _ _ UR_Type@{sA sB sR ; uA uB uR}.

Definition PR_Type@{sA sB sR;uA uB uR j} k : PR@{Type Type Type ; j j j} k Type@{sA;uA} Type@{sB;uB} :=
  match k with
  | plain => PR_Type_plain@{sA sB sR; uA uB uR j}
  | univalent => PR_Type_univ@{sA sB sR; uA uB uR j}
  end.

Arguments Ur {_ _} _.
Arguments equiv {_ _} _.
Arguments Ur_Coh {_ _} _.

#[export] Hint Extern 100 (_ ≃ _) => erefineb (equiv _): typeclass_instances ur_typeclass_instances.

Typeclasses Opaque pr Ur equiv UR_Coh.

Ltac2 apply_PR_Type_gen () :=
  match! reverse goal with
  | [ |- PR _ Prop  _ ] => exact (@PR_Type@{Prop SProp SProp;_ _ _ _} _)
  | [ |- PR _ SProp _ ] => exact (@PR_Type@{SProp SProp SProp;_ _ _ _} _)
  | [ |- PR _ _ _ ] => exact (@PR_Type _)
  | [ |- Prop ≈[ _ ] _ ] => exact (@PR_Type@{Prop SProp SProp;_ _ _ _} _)
  | [ |- SProp ≈[ _ ] _ ] => exact (@PR_Type@{SProp SProp SProp;_ _ _ _} _)
  | [ |- _ ≈[ _ ] _ ] => exact (@PR_Type _)
  end.

#[export] Hint Extern 0 => apply_PR_Type_gen () : typeclass_instances ur_typeclass_instances.

(* This hint is to remove let in declaration *)

#[export] Hint Extern 0 (_ ≈[ _ ] _) =>
  progress (cbn head zeta) : typeclass_instances ur_typeclass_instances.

Definition PR_Type_plain_univ {A B : Type} (H: A ≈u B) : PR plain A B := Ur H.

Definition PR_Type_univ_univ {A B : Type} (H: A ≈u B) : PR univalent A B :=
  {|pr := @pr plain _ _ (Ur H) |}.

Definition PR_Type_gen k (A B:Type) (H:@pr _ _ _ (PR_Type k) A B) : PR k A B :=
  match k return pr k A B -> PR k A B with
  | plain => fun H => H
  | univalent => fun H => PR_Type_univ_univ H
  end H.

Definition pr_Type_univ {A B : Type} (H: A ≈u B) : A ≈p B := Ur H.

Definition UR_Type_from_Prop (P:Prop) (Q:SProp)
  (H : UR_Type@{Prop SProp SProp; _ _ _} P Q) :
  UR_Type@{Type SProp SProp; _ _ _} P Q.
Proof.
unshelve econstructor.
- assert (H' := @Ur _ _ H). econstructor. intros p q. eapply (p ≈p q).
- unshelve econstructor.
  + eapply (equiv H).
  + unshelve econstructor.
    * eapply (e_inv (e_fun (equiv H))).
    * intro x. assert (H' := e_sect (e_fun (equiv H)) x). cbn. rewrite H'. reflexivity.
    * intro x. assert (H' := e_retr (e_fun (equiv H)) x). cbn. rewrite H'. reflexivity.
    * reflexivity.
- intros; split.
  + intros e. eapply (fst (Ur_Coh H a a')). now destruct e.
  + intros e. now destruct (snd (Ur_Coh H a a') e).
- econstructor.
Defined.

Definition UR_Prop_from_Type (P:Prop) (Q:SProp)
  (H : UR_Type@{Type SProp SProp; _ _ _} P Q) :
  UR_Type@{Prop SProp SProp; _ _ _} P Q.
Proof.
unshelve econstructor.
- assert (H' := @Ur _ _ H). econstructor. intros p q. eapply (p ≈p q).
- unshelve econstructor.
  + eapply (equiv H).
  + unshelve econstructor.
    * eapply (e_inv (e_fun (equiv H))).
    * intro x. eapply PI.
    * intro x. reflexivity.
    * reflexivity.
- intros; split.
  + intros e. eapply (fst (Ur_Coh H a a')). now destruct e.
  + intros e. now destruct (snd (Ur_Coh H a a') e).
- econstructor.
Defined.

Hint Extern 1 (UR_Type ?P ?Q) => erefineb (UR_Type_from_Prop _ _ _); shelve_non_PR_multi () : typeclass_instances ur_typeclass_instances.

(* Definition UR_Type_from_Prop' (P:Prop) (Q:SProp)
  (H : P ≈u Q) : (P:Type) ≈u Q := UR_Type_from_Prop P Q H.
*)
Hint Extern 1 (?P ≈[ _] ?Q) => erefineb (UR_Type_from_Prop _ _ _); shelve_non_PR_multi () : typeclass_instances ur_typeclass_instances.

Ltac2 uR_Type_from_Prop_tac () := match! reverse goal with | [ |- ?p ≈u ?q] => erefineb (UR_Type_from_Prop $p $q _); shelve_non_PR_multi () end.
Ltac2 uR_Prop_from_Type_tac () := match! reverse goal with | [ |- UR_Type ?p ?q] => erefineb (UR_Prop_from_Type $p $q _); shelve_non_PR_multi () end.

#[global]
Ltac2 Set pre_tc_hint_hook := fun () => first [cbn ; uR_Type_from_Prop_tac () | cbn ; uR_Prop_from_Type_tac () | ()].
Ltac2 pre_tc_hint_hook_contra := fun () => cbn; uR_Prop_from_Type_tac ().

Ltac2 head_is_var (c:constr) :=
  let (c_head, _) := Constr.decompose_app_nocast c in
  is_var c_head.

Ltac2 hyp_not_value (h:ident) :=
   match Control.hyp_value h with
  | Some _ => false
  | None => true
  end.

Ltac2 check_blacklist_PR_Type (lhs:constr) :=
  match! lhs with
  | Type => false
  | Prop => false
  | SProp => false
  | forall _, _ => false
  | _ => true
  end.

Ltac2 apply_Type_gen () :=
  match! goal with
  | [ |- PR _ ?lhs ?rhs] =>
    if (check_blacklist_PR_Type lhs) ||
       (check_blacklist_PR_Type rhs)
    then
      first [
          erefineb (PR_Type_univ_univ _); shelve_non_PR_multi () |
          erefineb (PR_Type_plain_univ _); shelve_non_PR_multi ()]
    else
      fail "not a variable"
  end.

#[export] Hint Extern 2 => apply_Type_gen () : typeclass_instances ur_typeclass_instances.

(* Definition of univalent relation for basic type constructors *)
(*! Forall !*)

Definition URArrow k A A' B B' {HA : PR k A A'}
           {HB: PR k B B'} : PR k (A -> B) (A' -> B')
  :=
  {| pr := fun f g => forall x y (H:x ≈[ k ] y), f x ≈[ k ] g y |}.

Definition URForall k A A' (B : A -> Type) (B' : A' -> Type) {HA : PR k A A'}
           {HB: forall x y (H: x ≈[ k ] y), PR k (B x) (B' y)} : PR k (forall x, B x) (forall y, B' y)
  :=
  {| pr := fun f g => forall x y (H:x ≈[ k ] y), @pr k _ _ (HB x y H) (f x) (g y) |}.

Ltac2 get_constant (c:constr) :=
  match Unsafe.kind c with
  | Unsafe.Constant k _ => k
  | _ => Control.throw (Tactic_failure (Some (Message.of_string "not a constant")))
  end.

Ltac2 is_forall_inst (c:constr) :=
  match Unsafe.kind c with
  | Unsafe.Constant k _ =>
    if Constant.equal k (get_constant (constr:(URArrow))) then true else
      if Constant.equal k (get_constant (constr:(URForall))) then true else false
  | _ => false
  end.

Ltac2 mutable rec failure_white_message (_lhs_head:constr) (_rhs_head:constr) (iso_head:constr) :=
  Message.concat (Message.of_string "the following instance should be white boxed: ")
                 (Message.of_constr iso_head).

Ltac2 mutable failure_white_message_conflict (lhs_head:constr) (lhs_head':constr) (rhs_head:constr) (rhs_head':constr) (iso_head:constr) (iso_head':constr) :=
  match (Std.is_forcibly_unfoldable_head lhs_head, Std.is_forcibly_unfoldable_head lhs_head') with
  | (true, true) | (false, false) =>
  Message.concat (Message.of_string "one of the following two instances should be white boxed: ")
 (Message.concat (Message.of_constr iso_head)
 (Message.concat (Message.of_string " and ")
                 (Message.of_constr iso_head')))
  | (true, false) => failure_white_message lhs_head rhs_head iso_head
  | (false, true) => failure_white_message lhs_head' rhs_head' iso_head'
  end.

Ltac2 failure_white_message_args_of_inst (ur_inst : constr) :=
  let (pr_head, _) := Constr.decompose_app_nocast ur_inst in
  let (lhs, rhs) := Control.throw_on_error (fun () => ur_type_of_ur_tc ur_inst) in
  let (lhs_head, _) := Constr.decompose_app_nocast lhs in
  let (rhs_head, _) := Constr.decompose_app_nocast rhs in
  (lhs_head, rhs_head, pr_head).

Ltac2 print_ur () :=
  match! reverse goal with
  | [ |- @pr _ _ _ (@Ur _ _ ?pr_inst) _ _] =>
      let (lhs_head, rhs_head, pr_head) := failure_white_message_args_of_inst pr_inst in
      Control.throw (Tactic_failure (Some (failure_white_message lhs_head rhs_head pr_head)))
  end.

Ltac2 refine_n_holes (c : constr) (n : int) : unit :=
  Control.refine (fun () =>
    let holes := Array.init n (fun _ => open_constr:(_)) in
    Constr.Unsafe.make (Constr.Unsafe.App c holes)).

Ltac2 apply_var_tac c :=
  let (c_head, c_args) := Constr.decompose_app_nocast c in
  let cbn_h () := match! reverse goal with
        | [ h : ?c ≈[_] _ |- _] => if Constr.equal c_head c && hyp_not_value h
          then cbn in $h
          else Control.zero Match_failure
      end in
  let nargs := Array.length c_args in
  if is_var c_head
  then
    if Int.equal nargs 0
    then
    let error () := match! goal with
              | [ h : @pr _ _ _ (@Ur _ _ ?pr_inst) ?c _ |- @pr _ _ _ (@Ur _ _ ?pr_inst') ?c' _] =>
                if Constr.equal c' c && hyp_not_value h
                then
                  let (lhs_head, rhs_head, pr_head) := failure_white_message_args_of_inst pr_inst in
                  let (lhs_head', rhs_head', pr_head') := failure_white_message_args_of_inst pr_inst' in
                  Control.throw (Tactic_failure (Some (failure_white_message_conflict lhs_head lhs_head' rhs_head rhs_head' pr_head pr_head')))
                else
                  Control.zero Match_failure
              | [ _ : UR_Type ?c ?d |- UR_Type ?c' ?d'] =>
                if Constr.equal c' c && Bool.neg (Constr.equal_nocumul (Constr.type d) (Constr.type d'))
                then
                  Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "the following variable has been used in a cumulative context: ")
                    (Message.concat (Message.of_constr (Constr.type d')) (Message.of_constr (Constr.type d))))))
                else
                  Control.zero Match_failure
              end in
    let local_assumption () := match! reverse goal with
              | [ h : @pr _ _ _ _ ?c _ |- _] =>
                if Constr.equal c_head c && hyp_not_value h
                then
                  let h := Control.hyp h in
                    refine $h
                else
                  Control.zero Match_failure
              end
    in first [local_assumption () |
              erefineb (PR_Type_gen _ _ _ _) ; local_assumption () |
              erefineb (PR_Type_plain_univ _); local_assumption () |
              pre_tc_hint_hook_contra (); local_assumption () |
              erefineb (PR_Type_gen _ _ _ _) ; pre_tc_hint_hook_contra (); local_assumption () |
              erefineb (PR_Type_plain_univ _); pre_tc_hint_hook_contra (); local_assumption () |
              intros ? ? ? |
              cbn_h () ; cbn ; error ()]
    else
      let apply_h () := match! reverse goal with
        | [ h : @pr _ _ _ _ ?c _ |- _] => if Constr.equal_nocumul c_head c && hyp_not_value h
            then
              let h' := Control.hyp h in
              let type_h := Std.eval_cbn RedFlags.all (type h') in
              if Constr.is_prod type_h
              then
                first [
                  unshelve (refine_n_holes h' (Int.mul 3 nargs)) |
                  forward_apply h' c];
                shelve_non_PR_multi ()
              else (cbn_h (); match! reverse goal with
              | [ _ : @pr _ _ _ (@Ur _ _ ?pr_inst) ?c _ |- _] =>
                if Constr.equal c_head c && hyp_not_value h
                then
                  let (lhs_head, rhs_head, pr_head) := failure_white_message_args_of_inst pr_inst in
                  Control.throw (Tactic_failure (Some (failure_white_message lhs_head rhs_head pr_head)))
                else
                  Control.zero Match_failure
              end)
            else Control.zero Match_failure
      end in
      first [apply_h () |
             erefineb (PR_Type_univ_univ _); apply_h ()|
             erefineb (PR_Type_gen _ _ _ _); apply_h ()]
  else
    Control.zero Match_failure.

Ltac2 apply_var_tac_goal () :=
  match! reverse goal with
  | [ |- PR _ ?lhs _] => apply_var_tac lhs
  | [ |- PR _ _ ?rhs] => apply_var_tac rhs
  | [ |- ?lhs ≈[_] _] => apply_var_tac lhs
  | [ |- _ ≈[_] ?rhs] => apply_var_tac rhs
  | [ |- UR_Type ?lhs _] => apply_var_tac lhs
  | [ |- UR_Type _ ?rhs] => apply_var_tac rhs
  end.

#[export] Hint Extern 0 => apply_var_tac_goal (); intros : typeclass_instances ur_typeclass_instances.

Definition ur_refl {A B: Type} (e : A ≈u B) :
  forall a : A, a ≈u ↑ a.
Proof.
  exact (fun a => fst (Ur_Coh e a a) idpath).
Defined.

Definition ur_refl' {A B: Type} (e : A ≈u B) :
  forall b : B, e_inv (e_fun (equiv e)) b ≈u b.
Proof.
  intro b; pose (p := ur_refl e). specialize (p (e_inv (e_fun (equiv e)) b)).
  now rewrite (e_retr (e_fun (equiv e)) b) in p.
Defined.

Ltac2 apply_closed_tac c :=
  if Constr.has_var_or_evar_or_meta c || neg (Unsafe.is_closed c)
  then
    Control.zero Match_failure
  else
    first [erefineb (ur_refl _ $c) |
           erefineb (ur_refl' _ $c)].

Ltac2 apply_closed_tac_goal () :=
  match! reverse goal with
  | [ |- ?lhs ≈u _] => apply_closed_tac lhs
  | [ |- _ ≈u ?rhs] => apply_closed_tac rhs
  end.

#[export] Hint Extern 0 => apply_closed_tac_goal () : typeclass_instances ur_typeclass_instances.

Ltac2 tc () := typeclasses_eauto with ur_typeclass_instances.

(* test Prop SProp instances *)

Goal PR plain Prop SProp. Proof. tc (). Abort.
Goal PR univalent Prop SProp. Proof. tc (). Abort.
Goal PR plain SProp SProp. Proof. tc (). Abort.
Goal PR univalent SProp SProp. Proof. tc (). Abort.
Goal PR plain Type Type. Proof. tc (). Abort.

(* some facilities to create an instance of UR_Type *)

Definition UR_gen A : PR plain A A := {| pr := (path A) |}.

Definition PR_inverse k {A B : Type} (ur: PR k A B) : PR k B A :=
  {| pr := fun b a => pr k a b |}.
(* This is the Black Box Property *)

(* The definition of Ur_coh given in the paper is equivalent to *)
(* the definition given here, but technically, this one is more convenient to use *)

Definition alt_UR_Coh@{sA sB sR;uA uB uR j +} {A : Type@{sA;uA}}
  {B:Type@{sB;uB}} (H: A ≈u B)
  (einv := Equiv_inverse (equiv H)) :
  forall (a:A) (b:B), iff@{sR sR SProp; uR uR Set uR} (a = ↑ b) (a ≈p b).
Proof.
  intros a b. cbn. set (e_inv _ _). rewrite <- (e_sect _ b).
  unshelve (refine (Ur_Coh H _ _)).
Defined.

Definition alt_UR_Coh_inv@{sA sB sR;uA uB uR j +} {A : Type@{sA;uA}}
      {B:Type@{sB;uB}} (e:A ≃ B) (H:A ≈p B) (einv := Equiv_inverse e)
      (HCoh : forall (a:A) (b:B), iff@{sR sR SProp; uR uR Set uR} (a = ↑ b) (a ≈p b)):
  UR_Coh A B e H.
Proof.
  intros a a'. set a' at 2. rewrite <- (e_sect _ a').
  refine (HCoh _ _).
Defined.

Ltac2 apply_forall_tac () :=
  match! reverse goal with
  | [ |- PR _ (_ -> _) _] => first [
    erefineb (@URArrow _ _ _ _ _ _ _); intros; shelve_non_PR_multi ()
    ]
  | [ |- PR _ _ (_ -> _)] => first [
    erefineb (@URArrow _ _ _ _ _ _ _); intros; shelve_non_PR_multi ()
    ]
  | [ |- PR _ (forall x:_, _) _] => first [
    erefineb (@URForall _ _ _ _ _ _ _); intros; shelve_non_PR_multi ()
    ]
  | [ |- PR _ _ (forall x:_, _)] => first [
    erefineb (@URForall _ _ _ _ _ _ _); intros; shelve_non_PR_multi ()
    ]
  end.

#[export] Hint Extern 0 => apply_forall_tac () : typeclass_instances ur_typeclass_instances.

  (*! UR is symmetric on types !*)
Definition UR_Type_Inverse (A B : Type) : A ≈u B -> B ≈u A.
Proof.
intro e. unshelve econstructor.
- eapply PR_inverse. eapply Ur. tc ().
- apply Equiv_inverse; tc ().
- apply alt_UR_Coh_inv.
  intros b a. cbn.
  destruct (alt_UR_Coh e a b) as [l r].
  split; intro.
  + eapply l. rewrite H. eapply inverse, e_sect.
  + eapply r in X. rewrite X. eapply inverse, e_retr.
- intros a b. unshelve (eapply Ur_Irr).
Defined.

Definition compat_inverse k (A A' B B':Type) (pA: PR k A A') (pB: PR k B B')
           (pA' := PR_inverse k pA)
           (pB' := PR_inverse k pB) (f : A -> B) (g : A' -> B') :
  f ≈[k] g -> g ≈[k] f.
Proof.
  cbn. tc ().
Defined.

Definition compat_inverse2 k {A A' B B' C C' :Type} {eA: PR k A A'} (eA' := PR_inverse k eA)
           {eB: PR k B B'} (eB' := PR_inverse k eB)
           {eC: PR k C C'} (eC' := PR_inverse k eC)
           {f : A -> B -> C} {g : A' -> B' -> C'} :
  f ≈[k] g -> g ≈[k] f.
Proof.
  cbn. tc ().
Defined.
(*! Canonical UR from a type equivalence !*)

Definition Canonical_PR k (A B:Type) `{e : A ≃ B} (einv := Equiv_inverse e) : PR k A B :=
    ({| pr := fun a b => a = ↑ b |}).

Definition Canonical_UR (A B:Type) `{A ≃ B} : A ≈u B.
Proof.
  unshelve econstructor.
  - eapply Canonical_PR.
  - intros a a'. cbn. unfold univalent_transport.
    rewrite (e_sect' H _). split; intro; eauto.
  - econstructor; reflexivity.
Defined.
(* some generic ways of getting UR instances *)

Definition UR_Equiv (A B C:Type) `{C ≃ B} (eAB:A ≈p B) : A ≈p C :=
  {| pr := fun a b => a ≈p ↑ b |}.

Definition UR_Equiv' (A B C:Type) `{C ≃ A} (eAB :A ≈p B) : C ≈p B :=
  {| pr := fun c b => (↑ c : A) ≈p b |}.

Definition UR_Type_Equiv (A B C:Type) `{C ≃ B} `{A ≈u B} : A ≈u C.
Proof.
  unshelve econstructor.
  - eapply UR_Equiv; eauto. eapply H0.
  - apply (equiv_compose (equiv H0)). apply Equiv_inverse. exact H.
  - intros a a'. cbn. unfold univalent_transport.
    rewrite (e_retr' H (e_fun (equiv H0) a')). unshelve (eapply Ur_Coh); tc ().
  - intros a b. cbn in *.  unshelve (eapply Ur_Irr).
Defined.

Definition UR_Type_Equiv' (A B C:Type) `{C ≃ A} `{A ≈u B} : C ≈u B.
Proof.
    unshelve econstructor.
  - eapply UR_Equiv'; eauto. eapply Ur. tc ().
  - apply (equiv_compose H (equiv H0)).
  - intros ? ?. cbn.
    unfold univalent_transport.
    split; intros.
    + unshelve (eapply (fst (Ur_Coh H0 (e_fun H a) (e_fun H a')) (ap (e_fun H) H1))).
    + eapply isequiv_ap. unshelve (eapply (snd (Ur_Coh H0 (e_fun H a) (e_fun H a')))); tc ().
  - intros a b. cbn in *. unshelve (eapply Ur_Irr).
Defined.

Definition UR_Equiv_gen (X:Type) (eX : X ≈p X) (A B: X -> Type)
  (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈p y) (H:A x ≈p A y)
  : B x ≈p B y.
Proof.
  unshelve (refine (UR_Equiv _ _ _ _)). 2:eauto.
  unshelve (refine (UR_Equiv' _ _ _ _)). 2: eauto.
  eauto.
Defined.

Definition UR_Type_Equiv_gen (X:Type) (eX : X ≈u X)
  (A B: X -> Type) (HAB: forall x, B x ≃ A x) (x y:X) (e : x ≈u y) (H:A x ≈u A y)
  (H':A x ≈u A y)
  : B x ≈u B y.
Proof.
  unshelve (refine (UR_Type_Equiv _ _ _)). 2:eauto.
  unshelve (refine (UR_Type_Equiv' _ _ _)). 2:eauto. tc ().
Defined.

(* Some Ltac2 faciilites *)

Ltac2 univparamtc_statement_type (f : constr) : constr :=
  type_of_refresh f.

Ltac2 postreduce (c : constr) :=
  eval cbn [UR.pr
    UR.PR_Type
    UR.PR_Type_gen
    UR.PR_Type_plain
    UR.PR_Type_univ
    UR.PR_Type_univ_univ
    UR.URForall
    UR.URArrow
  ] in $c.

Ltac2 iso_statement (k:constr) (f : constr) (g : constr) (fty : constr option) :=
  let ty := match fty with Some ty => ty | None => univparamtc_statement_type f end in
  let c := constr:(@pr $k $ty _ _ $f $g) in
  c.

Ltac2 iso_statement_with_sorts
    (k:constr) (f : constr) (g : constr) (_sorts : constr list) (fty : constr option) :=
  iso_statement k f g fty.

Ltac2 import_of_with_sorts (k:constr) (f : constr) (sorts : constr list) (fty : constr option) :=
  let (_h, args) := Constr.decompose_app f in
  if Bool.neg (Int.equal (Array.length args) 0) then
    Control.throw
      (Tactic_failure
        (Some
          (Message.of_string
            "import_of should be called on a reference, not an application")))
  else
    let fty := match fty with Some ty => Some ty | None => Some (univparamtc_statement_type f) end in
    let t := '_ in
    let f2 := Fresh.in_goal @f2 in
    let _ := Constr.in_context f2 t (fun () =>
      Control.refine (fun () => iso_statement_with_sorts k f (Control.hyp f2) sorts fty)) in
    t.

Ltac2 import_of (k:constr) (f : constr) (fty : constr option) := import_of_with_sorts k f [] fty.

Abbreviation iso_statement f g :=
  (match tt return _ with tt =>
    ltac2:(Control.refine
      (fun () => iso_statement 'univalent (Constr.open_pretype f) (Constr.open_pretype g) None))
  end) (only parsing).

Abbreviation iso_statement_plain f g :=
  (match tt return _ with tt =>
    ltac2:(Control.refine
      (fun () => iso_statement 'plain (Constr.open_pretype f) (Constr.open_pretype g) None))
  end) (only parsing).

Abbreviation import_of f :=
  (match tt return _ with tt =>
    ltac2:(Control.refine (fun () => import_of 'univalent (Constr.open_pretype_no_tc f) None))
  end) (only parsing).

Abbreviation import_of_plain f :=
  (match tt return _ with tt =>
    ltac2:(Control.refine (fun () => import_of 'plain (Constr.open_pretype_no_tc f) None))
  end) (only parsing).

(*
#[global]
Ltac2 Set compute_triple := fun (t:constr) (f:ident) (g:ident) =>
  unshelve refine '(let t' : _ := _ in let t'' : $t ≈u @t' := _ in _); shelve_non_PR_multi ();
   Control.extend [ (fun _ => tc ()) ; (fun _ => unfold &t'; tc () ) ; (fun _ => Std.rename [(@t',f);(@t'',g)]) ] (fun _ => ()) [].
*)
#[global]
Ltac2 Set compute_triple := fun (t:constr) (f:ident) (g:ident) =>
  unshelve refine '(let t' := _ in let t'' : $t ≈u @t' := _ in _); shelve_non_PR_multi ();
   Control.extend [ (fun _ => tc ()) ; (fun _ => unfold &t'; tc () ) ; (fun _ => Std.rename [(@t',f);(@t'',g)]) ] (fun _ => ()) [].


#[global]
Ltac2 Set shelve_and_tc := fun _ => shelve_non_PR_multi (); tc ().
