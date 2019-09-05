
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.FP.

Set Universe Polymorphism.


Ltac solve_with_lift A B := let e := fresh "e" in
                                       unshelve refine (let e : A ≈ B := _ in _);
                                         [tc | exact (ur_refl (e:=e) _)].

Ltac direct_lifting f g := assert (X : f ≈ g); 
   [match goal with | |- @ur ?A ?B _ f _ => solve_with_lift A B end | eapply X].


Tactic Notation "convert" constr(function) ":" constr(T) :=
  let X := fresh "X" in
  assert (X : { opt : T & function ≈ opt});
  [ first [  refine (let f := _ in let g := _ in existT _ (fun x y => existT _ (f x y) (g x y)) _) |
             refine (let f := _ in let g := _ in existT _ (fun x => existT _ (f x) (g x)) _) | 
             refine (let f := _ in let g := _ in existT _ (existT _ f g) _) | 
             eexists] ; try unfold function; cbn; intros;
    first [pose (F := fix_nat_3); simpl in F; eapply F (* refine (F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) *) | idtac ]; tc
  | exact X].

Ltac optimize f := let T := type of f in convert f : T. 

Ltac replace_goal :=
  let X := fresh "X" in
  match goal with | |- ?P =>
                    first [
                        pose (X := ltac: (convert P : Prop)) |
                        pose (X := ltac: (convert P : Type))]; 
                    apply (e_inv' (equiv X.2)); simpl; clear X
  end.
