(** * Techniques for applying theorems from [Sigma.v] to record types. *)
(** * From the HoTT Library *)

Require Import UnivalentParametricity.theories.Basics.

Set Primitive Projections.
Set Universe Polymorphism.

(** The following tactic proves automatically that a two-component record type is equivalent to a Sigma-type.  Specifically, it proves a goal that looks like
<<
   { x : A & B x } <~> Some_Record
>>
   You have to give it the record constructor and the two record projections as arguments (it has no way to guess what those might be). *)

Definition eta_sigma {A} `{P : A -> Type} (u : sigT P)
	  : (u.1; u.2) = u 
	  := match u with (x;y) => eq_refl end.

Ltac issig2 build pr1 pr2 :=
  (** Just in case the user supplied a goal which only *reduces* to one of the desired form. *)
  hnf;
  (** Extract the fibration of which our Sigma-type is the total space, as well as the record type. We pull the terms out of a [match], rather than leaving everything inside the [match] because this gives us better error messages. *)
  let fibration := match goal with |- sigT ?fibration ≃ ?record => constr:(fibration) end in
  let record := match goal with |- sigT ?fibration ≃ ?record => constr:(record) end in
  exact (BuildEquiv (sigT fibration) record
                     (fun u => build u.1 u.2)
                     (isequiv_adjointify
                        (fun u => build u.1 u.2)
                       (fun v => existT fibration (pr1 v) (pr2 v))
                       eta_sigma
                       (fun v => let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v') := v in eq_refl)
                       )).
                       (** Since [sigT] is primitve, we get judgmental η, and so we can just use the identity here *)
                       (* (fun _ => eq_refl))). *)

(** This allows us to use the same notation for the tactics with varying numbers of variables. *)
Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) :=
  issig2 build pr1 pr2.

(** We show how the tactic works in a couple of examples. *)

Record Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Definition issig_contr (A : Type)
  : { x : A & forall y:A, x = y } ≃ Contr A.
Proof.
  issig (BuildContr A) (@center A) (@contr A).
Defined.

Definition issig_equiv (A B : Type)
  : { f : A -> B & IsEquiv f } ≃ Equiv A B.
Proof.
  issig (BuildEquiv A B) (@e_fun A B) (@e_isequiv A B).
Defined.


(** Here is a version of the [issig] tactic for three-component records, which proves goals that look like
<<
   { x : A & { y : B x & C x y } } <~> Some_Record.
>>
   It takes the record constructor and its three projections as arguments, as before. *)


Definition eta2_sigma {A B} `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) = u.
Proof.
  destruct u as [a [b c]]. reflexivity.
Defined.

Ltac issig3 build pr1 pr2 pr3 :=
  hnf;
  let A := match goal with |- ?A ≃ ?B => constr:(A) end in
  let B := match goal with |- ?A ≃ ?B => constr:(B) end in
  exact (BuildEquiv A B
                    (fun u => build u.1 u.2.1 u.2.2)
                    (isequiv_adjointify
                       (fun u => build u.1 u.2.1 u.2.2)
                       (fun v => (pr1 v; (pr2 v; pr3 v)))
                       eta2_sigma
                       (fun v => let (v1, v2, v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v') := v in eq_refl)
                       )).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) :=
  issig3 build pr1 pr2 pr3.

Definition eta3_sigma {A B C} `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) = u.
Proof.
  destruct u as [a [b [c d]]]. reflexivity.
Defined.

(** And a similar version for four-component records.  It should be clear how to extend the pattern indefinitely. *)
Ltac issig4 build pr1 pr2 pr3 pr4 :=
  hnf;
  let A := match goal with |- ?A ≃ ?B => constr:(A) end in
  let B := match goal with |- ?A ≃ ?B => constr:(B) end in
  exact (BuildEquiv  A B
                       (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
                       (isequiv_adjointify
                          (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
                          (fun v => (pr1 v; (pr2 v; (pr3 v; pr4 v))))
                          eta3_sigma
                          (fun v => let (v1, v2, v3, v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v') := v in eq_refl))).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) :=
  issig4 build pr1 pr2 pr3 pr4.

Definition eta4_sigma {A B C D} `{P : forall (a : A) (b : B a) (c : C a b) (d : D a b c), Type}
           (u : sigT (fun a => sigT (fun b => sigT (fun c => sigT (P a b c)))))
  : (u.1; (u.2.1; (u.2.2.1; (u.2.2.2.1; u.2.2.2.2)))) = u.
Proof.
  destruct u as [a [b [c [d e]]]]. reflexivity.
Defined.

Ltac issig5 build pr1 pr2 pr3 pr4 pr5 :=
  hnf;
  let A := match goal with |- ?A ≃ ?B => constr:(A) end in
  let B := match goal with |- ?A ≃ ?B => constr:(B) end in
  exact (BuildEquiv  A B
                       (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)
                       (isequiv_adjointify
                          (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)
                          (fun v => (pr1 v; (pr2 v; (pr3 v; (pr4 v ; pr5 v)))))
                          eta4_sigma
                          (fun v => let (v1, v2, v3, v4, v5) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') (pr5 v') = v') := v in eq_refl))).


Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) constr(pr5) :=
  issig5 build pr1 pr2 pr3 pr4 pr5.
  

(* A tactic to show that record type are univalent type constructor *)
Ltac univ_param_record := 
  cbn;   split ; [typeclasses eauto | ]; intros;
  unshelve refine (UR_Type_Equiv_gen _ _ _ _ _ _ _ _);
  typeclasses eauto with typeclass_instances. 

