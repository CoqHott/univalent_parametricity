From Stdlib Require Import FunctionalExtensionality.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import TransparentState.
From Ltac2 Require Import Scheme.

Ltac2 Notation "refine" c(open_constr) := Control.refine (fun _ => c).

Module Bool.
  Export Ltac2.Bool.
  Ltac2 to_string (b : bool) := if b then "true" else "false".

  Ltac2 pr_bool (b : bool) := Message.of_string (to_string b).
End Bool.
Ltac2 pr_bool (b : bool) := Bool.pr_bool b.

Module List.
  Export Ltac2.List.
  Import Ltac2.Bool.BoolNotations.

  Ltac2 rec filter_map (f : 'a -> 'b option) (ls : 'a list) :=
    match ls with
    | [] => []
    | x :: xs =>
        match f x with
        | Some fx => fx :: filter_map f xs
        | None => filter_map f xs
        end
    end.

  Ltac2 rec shared_prefix_full (eq : 'a -> 'a -> bool) (ls1 : 'a list) (ls2 : 'a list) :=
    match ls1, ls2 with
    | [], _ => ([], (ls1, ls2))
    | _, [] => ([], (ls1, ls2))
    | x1 :: xs1, x2 :: xs2 =>
        if eq x1 x2 then
          let (prefix, (rest1, rest2)) := shared_prefix_full eq xs1 xs2 in
          ((x1, x2) :: prefix, (rest1, rest2))
        else
          ([], (ls1, ls2))
    end.

  Ltac2 shared_prefix eq ls1 ls2 :=
    let (prefix, (rest1, rest2)) := shared_prefix_full eq ls1 ls2 in
    (List.map (fun (x, _y) => x) prefix, (rest1, rest2)).

  (** [firstn_relaxed n ls] returns the first [n] elements of [ls].
    Throws an exception if [n < 0]. Returns [ls] if [n > length ls]. *)
  Ltac2 rec firstn_relaxed (n : int) (ls : 'a list) : 'a list :=
    Control.assert_valid_argument "List.firstn" (Int.ge n 0);
    match Int.equal n 0 with
    | true => []
    | false
      => match ls with
        | [] => []
        | x :: xs
          => x :: firstn_relaxed (Int.sub n 1) xs
        end
    end.

  (** [skipn_relaxed n ls] removes the first [n] elements of [ls].
    Throws an exception if [n < 0]. Returns [ls] if [n > length ls]. *)
  Ltac2 rec skipn_relaxed (n : int) (ls : 'a list) : 'a list :=
    Control.assert_valid_argument "List.skipn" (Int.ge n 0);
    match Int.equal n 0 with
    | true => ls
    | false
      => match ls with
        | [] => []
        | _ :: xs
          => skipn_relaxed (Int.sub n 1) xs
     end
    end.

  Ltac2 uniq (eq : 'a -> 'a -> bool) (ls : 'a list) :=
    let rec aux acc ls :=
      match ls with
      | [] => List.rev acc
      | x :: xs =>
          if List.exist (eq x) acc then aux acc xs else aux (x :: acc) xs
      end
    in
    aux [] ls.

  (** [find_index f xs] returns the index of the _first_ element of the list [xs] satisfying [f].
    Returns [None] if no element is found. *)
  Ltac2 find_index (f : 'a -> bool) (xs : 'a list) : int option :=
    let rec aux i xs :=
      match xs with
      | [] => None
      | x :: xs => match f x with
                  | true => Some i
                  | false => aux (Int.add i 1) xs
                  end
      end in
    aux 0 xs.

  Ltac2 take_drop_while (f : 'a -> bool) (ls : 'a list) :=
    let rec aux acc ls :=
      match ls with
      | [] => (List.rev acc, [])
      | x :: xs => if f x then aux (x :: acc) xs else (List.rev acc, xs)
      end in
    aux [] ls.

  (** [topological_sort eq deps ls] returns [ls] topologically sorted so
      that dependencies come first.  [eq] is equality on ['a].
      [deps x] returns the immediate dependencies of [x] (need not be
      restricted to elements of [ls] — the function filters internally,
      and self-dependencies are ignored).
      In case of cycles, the remaining elements are appended at the end
      in their original relative order.

      Complexity: O(D + E·n) where n = |ls|, D = total cost of all
      [deps] calls, E = total dependency edges after filtering.
      The E·n term is from O(n) index lookups per edge; the sort
      itself (Kahn's algorithm) is O(n + E). *)
  Ltac2 topological_sort (eq : 'a -> 'a -> bool) (deps : 'a -> 'a list) (ls : 'a list) : 'a list :=
    let n := List.length ls in
    if Int.equal n 0 then [] else
    let ls_arr := Array.of_list ls in
    let for_n (f : int -> unit) :=
      let rec aux i := if Int.lt i n then (f i; aux (Int.add i 1)) else () in
      aux 0
    in
    let find_idx x :=
      let rec aux i :=
        if Int.ge i n then None
        else if eq (Array.get ls_arr i) x then Some i
        else aux (Int.add i 1)
      in aux 0
    in
    (* Precompute deps as index lists, filtering to elements of ls and excluding self *)
    let deps_idx := Array.init n (fun i =>
      let x := Array.get ls_arr i in
      List.filter_map (fun d =>
        if eq d x then None else find_idx d
      ) (deps x)
    ) in
    (* Reverse adjacency: rev_adj[j] lists indices i that depend on j *)
    let rev_adj := Array.init n (fun _ => []) in
    for_n (fun i =>
      List.iter (fun j =>
        Array.set rev_adj j (i :: Array.get rev_adj j)
      ) (Array.get deps_idx i)
    );
    (* In-degrees and initial queue *)
    let in_deg := Array.init n (fun i => List.length (Array.get deps_idx i)) in
    let queue := Ref.ref [] in
    for_n (fun i =>
      if Int.equal (Array.get in_deg i) 0
      then Ref.set queue (i :: Ref.get queue) else ()
    );
    (* Kahn's algorithm *)
    let result := Ref.ref [] in
    let rec process () :=
      match Ref.get queue with
      | [] => ()
      | i :: rest =>
          Ref.set queue rest;
          Ref.set result (i :: Ref.get result);
          List.iter (fun j =>
            let d := Int.sub (Array.get in_deg j) 1 in
            Array.set in_deg j d;
            if Int.equal d 0
            then Ref.set queue (j :: Ref.get queue) else ()
          ) (Array.get rev_adj i);
          process ()
      end
    in
    process ();
    (* Append cycle elements in original order *)
    let visited := Array.init n (fun _ => false) in
    List.iter (fun i => Array.set visited i true) (Ref.get result);
    let remaining := Ref.ref [] in
    for_n (fun i =>
      if Bool.neg (Array.get visited i)
      then Ref.set remaining (i :: Ref.get remaining) else ()
    );
    List.map (Array.get ls_arr)
      (List.append (List.rev (Ref.get result)) (List.rev (Ref.get remaining))).
End List.
Ltac2 rec pr_list_with_sep (sep : message) (pr : 'a -> message) (ls : 'a list) :=
  match ls with
  | [] => Message.of_string ""
  | [x] => pr x
  | x :: xs => Message.concat (pr x) (Message.concat sep (pr_list_with_sep sep pr xs))
  end.
Module Preterm.
  Ltac2 specialize_n_gen (n : int) (t : preterm) (mk_hole : int -> preterm) :=
    let rec aux i t :=
      if Int.lt i n
      then
        let hole := mk_hole i in
        aux (Int.add i 1) (preterm:($preterm:t $preterm:hole))
      else t
    in
    aux 0 t.
  Ltac2 specialize_n (n : int) (t : preterm) := specialize_n_gen n t (fun _i => preterm:(_)).
  Ltac2 rec mkApp_list (f : preterm) (args : preterm list) :=
    match args with
    | [] => f
    | arg :: args => mkApp_list (preterm:($preterm:f $preterm:arg)) args
    end.

End Preterm.
Module Constr.
  Export Ltac2.Constr.
  Import Ltac2.Printf.
  Ltac2 open_pretype (c:preterm) :=
    Pretype.pretype Pretype.Flags.open_constr_flags_with_tc Pretype.expected_without_type_constraint c.
  Ltac2 open_pretype_with_tc (c:preterm) :=
    Pretype.pretype Pretype.Flags.open_constr_flags_with_tc Pretype.expected_without_type_constraint c.
  Ltac2 open_pretype_no_tc (c:preterm) :=
    Pretype.pretype Pretype.Flags.open_constr_flags_no_tc Pretype.expected_without_type_constraint c.
  Ltac2 rec strip_cast (c : constr) :=
    match Unsafe.kind c with
    | Unsafe.Cast v _ _ => strip_cast v
    | _ => c
    end.
  Ltac2 is_meta (c : constr) :=
    match Unsafe.kind c with
    | Unsafe.Meta _ => true
    | _ => false
    end.
  (* TODO: upstream is_sort*)
  Ltac2 is_sort(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Sort _ => true
    | _ => false
    end.
  Ltac2 is_type (c : constr) :=
    match Unsafe.kind c with
    | Unsafe.Sort _ => lazy_match! c with Type => true | _ => false end
    | _ => false
    end.
  Ltac2 is_prop (c : constr) := Constr.equal c 'Prop.
  Ltac2 is_set (c : constr) := Constr.equal c 'Set.
  Ltac2 is_sprop (c : constr) := Constr.equal c 'SProp.
  Ltac2 is_type_or_set (c : constr) := if is_type c then true else is_set c.
  Ltac2 is_sort_or_evar(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Sort _ => true
    | Unsafe.Evar _ _ => true
    | _ => false
    end.
  Ltac2 is_rel(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Rel _ => true
    | _ => false
    end.
  Ltac2 is_ind_or_evar(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Ind _ _ => true
    | Unsafe.Evar _ _ => true
    | _ => false
    end.
  Ltac2 is_prod(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Prod _ _ => true
    | _ => false
    end.
  Ltac2 is_prod_nd(c: constr) :=
    if is_prod c then
      match Control.case (fun () => lazy_match! c with ?_a -> ?_b => () end) with
      | Val ((), _) => true
      | Err _ => false
      end
    else
      false.
  Ltac2 is_lambda(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Lambda _ _ => true
    | _ => false
    end.
  Ltac2 is_case(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Case _ _ _ _ _ => true
    | _ => false
    end.
  Ltac2 is_constructor(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Constructor _ _ => true
    | _ => false
    end.
  Ltac2 is_constant(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Constant _ _ => true
    | _ => false
    end.
  Ltac2 is_proj(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Proj _ _ _ => true
    | _ => false
    end.
  Ltac2 is_uint63(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Uint63 _ => true
    | _ => false
    end.
  Ltac2 is_float(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Float _ => true
    | _ => false
    end.
  Ltac2 is_string(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.String _ => true
    | _ => false
    end.
  Ltac2 is_array(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.Array _ _ _ _ => true
    | _ => false
    end.
  Ltac2 is_letin(c: constr) :=
    match Unsafe.kind c with
    | Unsafe.LetIn _ _ _ => true
    | _ => false
    end.

  (** [equal_nounivs c1 c2] compares two constrs structurally,
      ignoring universe instances on constants/inductives/constructors/arrays,
      and treating all sorts as equal.  Mirrors Rocq's kernel
      [eq_constr_nounivs]. *)
  Import Ltac2.Bool.BoolNotations.
  Ltac2 rec equal_nounivs (c1 : constr) (c2 : constr) : bool :=
    Constr.equal c1 c2 ||
    (match Unsafe.kind c1, Unsafe.kind c2 with
    | Unsafe.Rel n1, Unsafe.Rel n2 => Int.equal n1 n2
    | Unsafe.Var id1, Unsafe.Var id2 => Ident.equal id1 id2
    | Unsafe.Meta m1, Unsafe.Meta m2 => Meta.equal m1 m2
    | Unsafe.Evar e1 l1, Unsafe.Evar e2 l2 =>
        Evar.equal e1 e2 && Array.equal equal_nounivs l1 l2
    | Unsafe.Sort _ , Unsafe.Sort _ => true
    | Unsafe.Cast c1' _ t1, Unsafe.Cast c2' _ t2 =>
        equal_nounivs c1' c2' && equal_nounivs t1 t2
    | Unsafe.Prod b1 t1, Unsafe.Prod b2 t2 =>
        equal_nounivs (Binder.type b1) (Binder.type b2)
        && equal_nounivs t1 t2
    | Unsafe.Lambda b1 t1, Unsafe.Lambda b2 t2 =>
        equal_nounivs (Binder.type b1) (Binder.type b2)
        && equal_nounivs t1 t2
    | Unsafe.LetIn b1 v1 t1, Unsafe.LetIn b2 v2 t2 =>
        equal_nounivs (Binder.type b1) (Binder.type b2)
        && equal_nounivs v1 v2
        && equal_nounivs t1 t2
    | Unsafe.App f1 args1, Unsafe.App f2 args2 =>
        equal_nounivs f1 f2
        && Array.equal equal_nounivs args1 args2
    | Unsafe.Constant c1' _, Unsafe.Constant c2' _ =>
        Constant.equal c1' c2'
    | Unsafe.Ind ind1 _, Unsafe.Ind ind2 _ =>
        Ind.equal ind1 ind2
    | Unsafe.Constructor ctor1 _, Unsafe.Constructor ctor2 _ =>
        Constructor.equal ctor1 ctor2
    | Unsafe.Case ci1 (x1, _) iv1 y1 bl1,
      Unsafe.Case ci2 (x2, _) iv2 y2 bl2 =>
        Unsafe.Case.equal ci1 ci2
        && equal_nounivs x1 x2
        && (match iv1, iv2 with
            | Unsafe.NoInvert, Unsafe.NoInvert => true
            | Unsafe.CaseInvert a1, Unsafe.CaseInvert a2 =>
                Array.equal equal_nounivs a1 a2
            | _, _ => false
            end)
        && equal_nounivs y1 y2
        && Array.equal equal_nounivs bl1 bl2
    | Unsafe.Fix structs1 idx1 tl1 bl1,
      Unsafe.Fix structs2 idx2 tl2 bl2 =>
        Int.equal idx1 idx2
        && Array.equal Int.equal structs1 structs2
        && Array.equal (fun b1 b2 =>
             equal_nounivs (Binder.type b1) (Binder.type b2))
           tl1 tl2
        && Array.equal equal_nounivs bl1 bl2
    | Unsafe.CoFix idx1 tl1 bl1,
      Unsafe.CoFix idx2 tl2 bl2 =>
        Int.equal idx1 idx2
        && Array.equal (fun b1 b2 =>
             equal_nounivs (Binder.type b1) (Binder.type b2))
           tl1 tl2
        && Array.equal equal_nounivs bl1 bl2
    | Unsafe.Proj p1 _ c1', Unsafe.Proj p2 _ c2' =>
        Proj.equal p1 p2 && equal_nounivs c1' c2'
    | Unsafe.Uint63 n1, Unsafe.Uint63 n2 => Uint63.equal n1 n2
    | Unsafe.Float f1, Unsafe.Float f2 => Float.equal f1 f2
    | Unsafe.String _ , Unsafe.String _ => Constr.equal c1 c2
    | Unsafe.Array _ vals1 def1 ty1,
      Unsafe.Array _ vals2 def2 ty2 =>
        Array.equal equal_nounivs vals1 vals2
        && equal_nounivs def1 def2
        && equal_nounivs ty1 ty2
    | _, _ => false
    end).

  Ltac2 Type exn ::= [ DestKO (string, constr) ].
  Ltac2 decompose_app_list (c : constr) :=
    match Unsafe.kind c with
      | Unsafe.App f cl => (f, Array.to_list cl)
      | _ => (c,[])
    end.
  Ltac2 decompose_app_list_nocast (c : constr) :=
    match Unsafe.kind_nocast c with
      | Unsafe.App f cl => (f, Array.to_list cl)
      | _ => (c,[])
    end.
  Ltac2 destConstant c := match Unsafe.kind c with
    | Unsafe.Constant kn inst => (kn, inst)
    | _ => Control.throw (DestKO "Constant" c)
  end.
  Ltac2 destCast c := match Unsafe.kind c with
    | Unsafe.Cast v cst ty => (v, cst, ty)
    | _ => Control.throw (DestKO "Cast" c)
  end.
  Ltac2 destVar c := match Unsafe.kind c with
    | Unsafe.Var id => id
    | _ => Control.throw (DestKO "Var" c)
  end.
  Ltac2 destProj c := match Unsafe.kind c with
    | Unsafe.Proj p r c => (p, r, c)
    | _ => Control.throw (DestKO "Proj" c)
  end.
  Ltac2 destEvar c := match Unsafe.kind c with
    | Unsafe.Evar id _ => id
    | _ => Control.throw (DestKO "Evar" c)
  end.
  Ltac2 destLambda c := match Unsafe.kind c with
    | Unsafe.Lambda n b => (n, b)
    | _ => Control.throw (DestKO "Lambda" c)
  end.
  Ltac2 destProd c := match Unsafe.kind c with
    | Unsafe.Prod n b => (n, b)
    | _ => Control.throw (DestKO "Prod" c)
  end.

  Ltac2 decompose_app (c : constr) :=
    match Unsafe.kind c with
      | Unsafe.App f cl => (f, cl)
      | _ => (c,[| |])
    end.

  Ltac2 decompose_app_nocast1 (c : constr) :=
    match Unsafe.kind_nocast c with
      | Unsafe.App f cl => (f, cl)
      | _ => (c,[| |])
    end.
  Ltac2 decompose_app_nocast (c : constr) :=
    let rec aux c :=
      match Unsafe.kind_nocast c with
        | Unsafe.App f cl => let (f, cl0) := aux f in (f, cl::cl0)
        | _ => (c,[])
      end in
    let (f, cl) := aux c in
    (f, Array.concat (List.rev cl)).
  Ltac2 rec head_nocast (c : constr) :=
    match Unsafe.kind_nocast c with
    | Unsafe.App f _cl => head_nocast f
    | _ => c
    end.
  Ltac2 head (c : constr) := let (h, _args) := Constr.decompose_app c in h.
  Ltac2 is_evar_head (c : constr) := is_evar (head_nocast c).

  Ltac2 in_context_prod n t f :=
    let c := Constr.in_context n t f in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Lambda n b => Constr.Unsafe.make (Constr.Unsafe.Prod n b)
    | _ => Control.throw (Invalid_argument (Some (Message.of_constr c)))
    end.

  Ltac2 mkApp (f : constr) (args : constr array) :=
    Constr.Unsafe.make (Constr.Unsafe.App f args).
  Ltac2 mkApp_list (f : constr) (args : constr list) :=
    mkApp f (Array.of_list args).
  Ltac2 mkLambda (b : binder) (t : constr) :=
    Constr.Unsafe.make (Constr.Unsafe.Lambda b t).
  Ltac2 mkProd (b : binder) (t : constr) :=
    Constr.Unsafe.make (Constr.Unsafe.Prod b t).
  Ltac2 mkArrow (r : Constr.Binder.relevance option) (a : constr) (b : constr) :=
    let a :=
      match r with
      | Some r => Constr.Binder.unsafe_make None r a
      | None => Constr.Binder.make None a
      end in
    let b := Constr.Unsafe.liftn 1 0 b in
    mkProd a b.
  Ltac2 mkRel n := Constr.Unsafe.make (Constr.Unsafe.Rel n).
  Ltac2 mkVar n := Constr.Unsafe.make (Constr.Unsafe.Var n).
  Ltac2 mkCast v cst ty := Constr.Unsafe.make (Constr.Unsafe.Cast v cst ty).
  Ltac2 mkProj p r c := Constr.Unsafe.make (Constr.Unsafe.Proj p r c).

  Ltac2 rec count_prod (t : constr) :=
    match Constr.Unsafe.kind_nocast t with
    | Constr.Unsafe.Prod _ t' => Int.add 1 (count_prod t')
    | _ => 0
    end.

  Ltac2 to_string t := Message.to_string (Message.of_constr t).

  Module Unsafe.
    Export Unsafe.
    Import Printf.
    Ltac2 rec under_lambda_prod_gen (lambda : bool) (prod : bool) (f : constr -> 'a) (t : constr) :=
      match Constr.Unsafe.kind_nocast t with
      | Constr.Unsafe.Lambda _ t' =>
          if lambda then
            under_lambda_prod_gen lambda prod f t'
          else
            f t
      | Constr.Unsafe.Prod _ t' =>
          if prod then
            under_lambda_prod_gen lambda prod f t'
          else
            f t
      | _ => f t
      end.
    Ltac2 under_lambda_prod f t := under_lambda_prod_gen true true f t.
    Ltac2 under_prod f t := under_lambda_prod_gen false true f t.
    Ltac2 under_lambda f t := under_lambda_prod_gen true false f t.
    Ltac2 decompose_app_under_lambda_prod_gen (lambda : bool) (prod : bool) (t : constr) :=
      under_lambda_prod_gen lambda prod decompose_app t.
    Ltac2 decompose_app_under_lambda_prod t := decompose_app_under_lambda_prod_gen true true t.
    Ltac2 decompose_app_under_lambda t := decompose_app_under_lambda_prod_gen true false t.
    Ltac2 decompose_app_under_prod t := decompose_app_under_lambda_prod_gen false true t.
    Ltac2 decompose_app_list_under_lambda_prod_gen (lambda : bool) (prod : bool) (t : constr) :=
      let (f, args) := decompose_app_under_lambda_prod_gen lambda prod t in
      (f, Array.to_list args).
    Ltac2 decompose_app_list_under_lambda_prod t := decompose_app_list_under_lambda_prod_gen true true t.
    Ltac2 decompose_app_list_under_lambda t := decompose_app_list_under_lambda_prod_gen true false t.
    Ltac2 decompose_app_list_under_prod t := decompose_app_list_under_lambda_prod_gen false true t.
    Ltac2 head_under_lambda_prod_gen (lambda : bool) (prod : bool) (t : constr) :=
      let (f, _args) := decompose_app_under_lambda_prod_gen lambda prod t in
      f.
    Ltac2 head_under_lambda_prod t := head_under_lambda_prod_gen true true t.
    Ltac2 head_under_lambda t := head_under_lambda_prod_gen true false t.
    Ltac2 head_under_prod t := head_under_lambda_prod_gen false true t.
    Ltac2 decompose_app_nocast_under_lambda_prod_gen (lambda : bool) (prod : bool) (t : constr) :=
      under_lambda_prod_gen lambda prod decompose_app_nocast t.
    Ltac2 decompose_app_nocast_under_lambda_prod t := decompose_app_nocast_under_lambda_prod_gen true true t.
    Ltac2 decompose_app_nocast_under_lambda t := decompose_app_nocast_under_lambda_prod_gen true false t.
    Ltac2 decompose_app_nocast_under_prod t := decompose_app_nocast_under_lambda_prod_gen false true t.
    Ltac2 decompose_app_nocast_list_under_lambda_prod_gen (lambda : bool) (prod : bool) (t : constr) :=
      let (f, args) := decompose_app_nocast_under_lambda_prod_gen lambda prod t in
      (f, Array.to_list args).
    Ltac2 decompose_app_nocast_list_under_lambda_prod t := decompose_app_nocast_list_under_lambda_prod_gen true true t.
    Ltac2 decompose_app_nocast_list_under_lambda t := decompose_app_nocast_list_under_lambda_prod_gen true false t.
    Ltac2 decompose_app_nocast_list_under_prod t := decompose_app_nocast_list_under_lambda_prod_gen false true t.
    Ltac2 head_nocast_under_lambda_prod_gen (lambda : bool) (prod : bool) (t : constr) :=
      let (f, _args) := decompose_app_nocast_under_lambda_prod_gen lambda prod t in
      f.
    Ltac2 head_nocast_under_lambda_prod t := head_nocast_under_lambda_prod_gen true true t.
    Ltac2 head_nocast_under_lambda t := head_nocast_under_lambda_prod_gen true false t.
    Ltac2 head_nocast_under_prod t := head_nocast_under_lambda_prod_gen false true t.

    Ltac2 kind_to_message (k : kind) :=
      match Control.case (fun () => make k) with
      | Val (c, _) => Message.of_constr c
      | Err err => fprintf "<exception in printing kind: %a>" (fun () => Message.of_exn) err
      end.

    Ltac2 iter_with_binders (lift : 'a -> binder -> 'a) (f : 'a -> constr -> unit) (n : 'a) (c : constr) :=
      let __ := Constr.Unsafe.map_with_binders lift (fun v c => let __ := f v c in c) n c in
      ().
  End Unsafe.
  (*Module Preterm.
  Module Pretype.
    Export Ltac2.Constr.Pretype.

    TODO: rapply version
  Ltac2 rec specialize_pretype *)
  Ltac2 fast_type (t : constr) :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Cast _ _ ty => ty
    | _ => Constr.type t
    end.

  Ltac2 fold_thunked (f : constr -> (unit -> 'a) -> 'a) (init : 'a) (t : constr) :=
    let cell := Ref.ref init in
    let rec aux t :=
      Ref.set cell (f t (fun () => Constr.Unsafe.iter aux t; Ref.get cell)) in
    aux t;
    Ref.get cell.

  Ltac2 fold_left (f : 'a -> constr -> 'a) (init : 'a) (t : constr) :=
    let cell := Ref.ref init in
    let rec aux t :=
      Ref.set cell (f (Ref.get cell) t); Constr.Unsafe.iter aux t in
    aux t;
    Ref.get cell.

  Ltac2 fold_right (f : constr -> 'a -> 'a) (init : 'a) (t : constr) :=
    fold_thunked (fun c mk_acc => f c (mk_acc ())) init t.

  (* Ltac2 has_evar (t : constr) :=
    fold_thunked (fun c c_has_evar => Constr.is_evar c || (c_has_evar ())) false t. *)

  Import Ltac2.Bool.BoolNotations.

  Ltac2 has_of_is (is_X : constr -> bool) (t : constr) :=
    fold_thunked (fun c c_has_X => is_X c || (c_has_X ())) false t.

  Ltac2 has_var (t : constr) := has_of_is Constr.is_var t.
  Ltac2 is_var_or_evar_or_meta (t : constr) :=
    match Unsafe.kind t with
    | Unsafe.Evar _ _ | Unsafe.Meta _ | Unsafe.Var _ => true
    | _ => false
    end.
  Ltac2 has_var_or_evar_or_meta (t : constr) := has_of_is is_var_or_evar_or_meta t.

  Ltac2 rec is_only_constructors (t : constr) :=
    match Constr.Unsafe.kind_nocast t with
    | Constr.Unsafe.App f args =>
        is_only_constructors f && Array.for_all is_only_constructors args
    | Constr.Unsafe.Prod _ body => is_only_constructors body
    | Constr.Unsafe.Lambda _ body => is_only_constructors body
    | Constr.Unsafe.Ind _ _ => true
    | Constr.Unsafe.Constructor _ _ => true
    | Constr.Unsafe.Sort _ => true
    | _ => false
    end.

  (** [map2_with_binders lift f mismatch align_app n c1 c2] iterates [f n]
      over pairs of immediate subterms of [c1] and [c2] when they have the
      same top-level kind. Calls [mismatch n c1 c2] when the kinds differ.
      [lift] updates the accumulator [n] at each binder traversal.
      When [align_app] is true and both sides are [App] with different argument
      counts, the shorter argument list is aligned to the tail of the longer
      one, with the excess prefix arguments folded back into the head. *)
  Ltac2 map2_with_binders
    (lift : 'a -> binder -> 'a)
    (f : 'a -> constr -> constr -> unit)
    (mismatch : 'a -> constr -> constr -> unit)
    (align_app : bool)
    (n : 'a)
    (c1 : constr) (c2 : constr) : unit :=
    match Constr.Unsafe.kind c1, Constr.Unsafe.kind c2 with
    | Constr.Unsafe.Rel _, Constr.Unsafe.Rel _ => ()
    | Constr.Unsafe.Meta _, Constr.Unsafe.Meta _ => ()
    | Constr.Unsafe.Var _, Constr.Unsafe.Var _ => ()
    | Constr.Unsafe.Sort _, Constr.Unsafe.Sort _ => ()
    | Constr.Unsafe.Constant _ _, Constr.Unsafe.Constant _ _ => ()
    | Constr.Unsafe.Ind _ _, Constr.Unsafe.Ind _ _ => ()
    | Constr.Unsafe.Constructor _ _, Constr.Unsafe.Constructor _ _ => ()
    | Constr.Unsafe.Uint63 _, Constr.Unsafe.Uint63 _ => ()
    | Constr.Unsafe.Float _, Constr.Unsafe.Float _ => ()
    | Constr.Unsafe.String _, Constr.Unsafe.String _ => ()
    | Constr.Unsafe.Cast c1' _k1 t1, Constr.Unsafe.Cast c2' _k2 t2 =>
        f n c1' c2'; f n t1 t2
    | Constr.Unsafe.Prod b1 body1, Constr.Unsafe.Prod b2 body2 =>
        f n (Constr.Binder.type b1) (Constr.Binder.type b2);
        f (lift n b1) body1 body2
    | Constr.Unsafe.Lambda b1 body1, Constr.Unsafe.Lambda b2 body2 =>
        f n (Constr.Binder.type b1) (Constr.Binder.type b2);
        f (lift n b1) body1 body2
    | Constr.Unsafe.LetIn b1 t1 body1, Constr.Unsafe.LetIn b2 t2 body2 =>
        f n (Constr.Binder.type b1) (Constr.Binder.type b2);
        f n t1 t2;
        f (lift n b1) body1 body2
    | Constr.Unsafe.App h1 args1, Constr.Unsafe.App h2 args2 =>
        let len1 := Array.length args1 in
        let len2 := Array.length args2 in
        if align_app || Int.equal len1 len2 then
          let min_len := if Int.le len1 len2 then len1 else len2 in
          let excess1 := Int.sub len1 min_len in
          let excess2 := Int.sub len2 min_len in
          let new_h1 := if Int.equal excess1 0 then h1
                        else Constr.Unsafe.make (Constr.Unsafe.App h1 (Array.sub args1 0 excess1)) in
          let new_h2 := if Int.equal excess2 0 then h2
                        else Constr.Unsafe.make (Constr.Unsafe.App h2 (Array.sub args2 0 excess2)) in
          f n new_h1 new_h2;
          let _ := Array.init min_len (fun i =>
            f n (Array.get args1 (Int.add excess1 i)) (Array.get args2 (Int.add excess2 i)))
          in ()
        else
          mismatch n c1 c2
    | Constr.Unsafe.Evar _e1 l1, Constr.Unsafe.Evar _e2 l2 =>
        if Int.equal (Array.length l1) (Array.length l2) then
          Array.iter2 (f n) l1 l2
        else
          mismatch n c1 c2
    | Constr.Unsafe.Case _info1 (x1, _rel1) _ci1 y1 bl1,
      Constr.Unsafe.Case _info2 (x2, _rel2) _ci2 y2 bl2 =>
        f n x1 x2;
        f n y1 y2;
        if Int.equal (Array.length bl1) (Array.length bl2) then
          Array.iter2 (f n) bl1 bl2
        else
          mismatch n c1 c2
    | Constr.Unsafe.Proj _p1 _r1 c1', Constr.Unsafe.Proj _p2 _r2 c2' =>
        f n c1' c2'
    | Constr.Unsafe.Fix _structs1 _which1 tl1 bl1,
      Constr.Unsafe.Fix _structs2 _which2 tl2 bl2 =>
        let len_tl := Array.length tl1 in
        if Int.equal len_tl (Array.length tl2)
           && Int.equal (Array.length bl1) (Array.length bl2) then (
          Array.iter2 (fun b1 b2 => f n (Constr.Binder.type b1) (Constr.Binder.type b2)) tl1 tl2;
          let n_bl := Array.fold_left lift n tl1 in
          Array.iter2 (f n_bl) bl1 bl2
        ) else
          mismatch n c1 c2
    | Constr.Unsafe.CoFix _which1 tl1 bl1,
      Constr.Unsafe.CoFix _which2 tl2 bl2 =>
        let len_tl := Array.length tl1 in
        if Int.equal len_tl (Array.length tl2)
           && Int.equal (Array.length bl1) (Array.length bl2) then (
          Array.iter2 (fun b1 b2 => f n (Constr.Binder.type b1) (Constr.Binder.type b2)) tl1 tl2;
          let n_bl := Array.fold_left lift n tl1 in
          Array.iter2 (f n_bl) bl1 bl2
        ) else
          mismatch n c1 c2
    | Constr.Unsafe.Array _u1 t1 def1 ty1,
      Constr.Unsafe.Array _u2 t2 def2 ty2 =>
        f n ty1 ty2;
        f n def1 def2;
        if Int.equal (Array.length t1) (Array.length t2) then
          Array.iter2 (f n) t1 t2
        else
          mismatch n c1 c2
    | _, _ => mismatch n c1 c2
    end.

  (** [map2 f mismatch align_app c1 c2] iterates [f] over pairs of immediate
      subterms of [c1] and [c2]. See [map2_with_binders] for details. *)
  Ltac2 map2
    (f : constr -> constr -> unit)
    (mismatch : constr -> constr -> unit)
    (align_app : bool)
    (c1 : constr) (c2 : constr) : unit :=
    map2_with_binders (fun n _b => n) (fun _n => f) (fun _n => mismatch) align_app () c1 c2.

End Constr.
Module Printf.
  Import Ltac2.Message.
  Export Ltac2.Printf.
  Ltac2 no_printf fmt := Format.kfprintf (fun _ => ()) fmt.
  Ltac2 printf_if b fmt := Format.kfprintf (fun x => if b then Message.print x else ()) fmt.
  Ltac2 Notation "printf_if" b(tactic) fmt(format) := printf_if b fmt.
End Printf.
Ltac2 Type 'a result_bt := [ Val_bt ('a) | Err_bt (exn, exninfo) ].
Module Control.
  Export Ltac2.Control.
  Import Ltac2.Printf.
  Import Ltac2.Bool.BoolNotations.
  Module Exninfo.
    Ltac2 capture (err : exn) :=
      plus_bt (fun () => zero err) (fun err exn => (err, exn)).
    Ltac2 inject (err : exn) (info : exninfo) :=
      match Control.case (fun () => zero_bt err info) with
      | Val _ => throw Assertion_failure
      | Err err => err
      end.

    Ltac2 Type exn ::= [ EnrichedError (exn, exninfo) ].
    Ltac2 Type exn ::= [ WrapBtMissingInfo (exn) ].

    Ltac2 rec strip_enrichment (err : exn) :=
      match err with
      | EnrichedError err _ => strip_enrichment err
      | _ => err
      end.
    Ltac2 unwrap_enrichment (err : exn) f :=
      match err with
      | EnrichedError err info => f err info
      | _ => Control.throw (WrapBtMissingInfo err)
      end.
    Ltac2 maybe_unwrap_enrichment g err info :=
      match err with
      | EnrichedError err info => g err info (* shadow arguments to discard them *)
      | _ => g err info
      end.

    Ltac2 rec wrap_bt (f : unit -> 'a) :=
      match Control.case (fun () => plus_bt f (fun err info => zero_bt (EnrichedError (strip_enrichment err) info) info)) with
      | Val (v, alt) => plus_bt (fun () => v) (fun err info => wrap_bt (fun () => alt (EnrichedError (strip_enrichment err) info)))
      | Err err => unwrap_enrichment err (fun _err info => zero_bt err info)
      end.
  End Exninfo.

  (* we override the stdlib Control.plus_bt with a version that prefers the exninfo from enriched errors *)
  Ltac2 plus_bt (f : unit -> 'a) (g : exn -> exninfo -> 'a) :=
    plus_bt f (Exninfo.maybe_unwrap_enrichment g).

  Ltac2 case_bt (f : unit -> 'a) :=
    match Control.case (fun () => plus_bt f (fun err info => zero_bt (Exninfo.EnrichedError (Exninfo.strip_enrichment err) info) info)) with
    | Val (v, alt) => Val_bt (v, (fun err info => alt (Exninfo.EnrichedError err info)))
    | Err err => Exninfo.unwrap_enrichment err (fun err info => Err_bt err info)
    end.

  Ltac2 rec replace_errors f err :=
    Control.plus f (fun _err => Control.zero err).
    (* match Control.case f with
    | Val (v, alt) => Control.plus (fun () => v) (fun err' => replace_errors (fun () => alt err') err)
    | Err _ => Control.zero err
    end. *)
  Ltac2 rec replace_errors_bt f err info :=
    Control.plus_bt f (fun _err _info => Control.zero_bt err info).
    (* match Control.case_bt f with
    | Val_bt (v, alt) => Control.plus_bt (fun () => v) (fun err' info' => replace_errors_bt (fun () => alt err' info') err info)
    | Err_bt _ _ => Control.zero_bt err info
    end. *)
  Ltac2 discard_errors f :=
    match Control.case_bt f with
    | Val_bt (v, alt) => Control.plus_bt (fun () => v) (fun err info => replace_errors_bt (fun () => alt err info) err info)
    | Err_bt err info => Control.zero_bt err info
    end.
  Ltac2 case_plus f :=
    Control.plus (fun () => Val (f ())) (fun err => Err err).
  (* Ltac2 rec case_plus_any_errors f :=
    match Control.case f with
    | Val (v, alt) => Control.plus (fun () => Val (v, alt)) (fun err => case_plus_any_errors (fun () => alt err))
    | Err err => Err err
    end. *)
  (* Ltac2 case_plus f :=
    match Control.case f with
    | Val (v, alt) =>
        let alt := fun err => replace_errors (fun () => alt err) err in
        Control.plus
          (fun () => Val (v, alt))
          (fun err => case_plus_any_errors (fun () => alt err))
    | Err err => Err err
    end. *)
  Ltac2 case_discard_errors_plus f :=
    Control.case_plus (fun () => Control.discard_errors f).
    (* match Control.case (fun () => Control.discard_errors f) with
    | Val (v, alt) => Control.plus (fun () => Val v) (fun err => Val (alt err))
    | Err err => Err err
    end. *)
  Ltac2 throw_on_error f :=
    match Control.case_bt f with
    | Val_bt (v, _) => v
    | Err_bt err info => Control.throw_bt err info
    end.
  Ltac2 rec throw_on_error_rec f :=
    match Control.case_bt f with
    | Val_bt (v, alt) => Control.plus_bt (fun () => v) (fun err info => throw_on_error_rec (fun () => alt err info))
    | Err_bt err info => Control.throw_bt err info
    end.
  (* takes successes of f, then successes of g, then errors of f
  i.e., it is like f + g + f, but it does not duplicate effort *)
  Ltac2 plus_keep_error f g :=
    Control.plus_bt f (fun err info => Control.plus (fun () => g err) (fun _ => Control.zero_bt err info)).
    (* match Control.case f with
    | Val (v, alt) => Control.plus (fun () => v) (fun err => plus_keep_error (fun () => alt err) g)
    | Err err =>
        match Control.case (fun () => g err) with
        | Err _ => Control.zero err
        | Val (v, alt) =>
            Control.plus
              (fun () => v)
              (fun err' => plus_keep_error (fun () => Control.zero err) (fun _err => alt err'))
        end
    end. *)
  Ltac2 rec successes_from f err :=
    match Control.case f with
    | Val (v, alt) => v :: successes_from (fun () => alt err) err
    | Err _err => []
    end.
  Ltac2 successes f := successes_from f (Tactic_failure None).

  Ltac2 assert_true_bt b :=
    if b then () else zero Assertion_failure.

  Ltac2 assert_false_bt b :=
    if b then zero Assertion_failure else ().

  Ltac2 fprint_hyp_gen (before : string) (after : string) (n : ident) (body : constr option) (ty : constr) (f : constr -> constr) :=
    match body with
    | Some body => fprintf "%s%I : %t := %t%s" before n (f ty) (f body) after
    | None => fprintf "%s%I : %t%s" before n (f ty) after
    end.

  Ltac2 Type FPrintHypOptions := { parens : bool ; transform_hyp : constr -> constr }.
  Ltac2 Type FPrintGoalOptions := { transform_goal : constr -> constr }.
  Ltac2 Type FPrintContextOptions := { print_forall : bool ; red_beta_zeta : bool }.

  Ltac2 fprint_hyp_opt (opt : FPrintHypOptions) (n : ident) (body : constr option) (ty : constr) :=
    let (before, after) := if opt.(parens) then ("(", ")") else ("", "") in
    fprint_hyp_gen before after n body ty (opt.(transform_hyp)).

  Ltac2 fprint_hyp_nl_opt (opt : FPrintHypOptions) (n : ident) (body : constr option) (ty : constr) :=
    Message.concat (fprint_hyp_opt opt n body ty) Message.force_new_line.

  Ltac2 fprint_context_opt (opt : FPrintHypOptions) :=
    List.fold_left (fun acc (n, body, ty) => Message.concat acc (fprint_hyp_nl_opt opt n body ty)) (Message.of_string "") (Control.hyps ()).

  Ltac2 fprint_context () := fprint_context_opt { parens := false ; transform_hyp := (fun x => x) }.

  Ltac2 print_context_opt (opt : FPrintHypOptions) := Message.print (fprint_context_opt opt).
  Ltac2 print_context () := Message.print (fprint_context ()).

  Ltac2 fprint_goal_opt (opt : FPrintGoalOptions) := fprintf "%t%a" (opt.(transform_goal) (Control.goal ())) (fun () a => a) Message.force_new_line.
  Ltac2 fprint_goal () := fprint_goal_opt { transform_goal := (fun x => x) }.
  Ltac2 print_goal () := Message.print (fprint_goal ()).

  Ltac2 fprint_context_and_goal_opt (opt : FPrintContextOptions) :=
    let transform := if opt.(red_beta_zeta) then (fun x => eval cbv beta zeta in $x) else (fun x => x) in
    let hyp_opt := { parens := opt.(print_forall) ; transform_hyp := transform } in
    let goal_opt := { transform_goal := transform } in
    if opt.(print_forall) then
      fprintf "forall%a%a%a,%a%a"
        (fun () a => a) Message.force_new_line
        (fun () a => a) (fprint_context_opt hyp_opt)
        (fun () a => a) Message.force_new_line
        (fun () a => a) Message.force_new_line
        (fun () a => a) (fprint_goal_opt goal_opt)
    else
      let dash := Message.of_string "─" in
      fprintf "%a%a%a%a"
        (fun () a => a) (fprint_context_opt hyp_opt)
        (fun () a => a) (List.fold_left Message.concat (Message.of_string "") (List.repeat dash 80))
        (fun () a => a) Message.force_new_line
        (fun () a => a) (fprint_goal_opt goal_opt).

  Ltac2 fprint_context_and_goal () := fprint_context_and_goal_opt { print_forall := false ; red_beta_zeta := false }.
  Ltac2 fprint_context_and_goal_red () := fprint_context_and_goal_opt { print_forall := false ; red_beta_zeta := true }.
  Ltac2 fprint_forall_context_and_goal () := fprint_context_and_goal_opt { print_forall := true ; red_beta_zeta := false }.
  Ltac2 fprint_forall_context_and_goal_red () := fprint_context_and_goal_opt { print_forall := true ; red_beta_zeta := true }.

  Ltac2 print_context_and_goal () := Message.print (fprint_context_and_goal ()).
  Ltac2 print_context_and_goal_red () := Message.print (fprint_context_and_goal_red ()).
  Ltac2 print_forall_context_and_goal () := Message.print (fprint_forall_context_and_goal ()).
  Ltac2 print_forall_context_and_goal_red () := Message.print (fprint_forall_context_and_goal_red ()).

  Ltac2 print_goals () :=
    let n := Ref.ref 1 in
    let total := Control.numgoals () in
    Control.enter (fun () =>
      printf "Goal %i of %i" (Ref.get n) total;
      Ref.incr n;
      print_context_and_goal ()
    ).

  Ltac2 unsafe_enter : (unit -> 'a) -> 'a list := fun f =>
    let res := Ref.ref [] in
    let g () := Ref.set res (f () :: Ref.get res) in
    Control.enter g;
    List.rev (Ref.get res).

  Ltac2 reorder_arr (perm : int array) : unit :=
    let n := Control.numgoals () in
    if Int.equal n 0 then () else
      let remember_and_shelve () :=
        let g := '_ in
        let ev := Constr.destEvar g in
        Control.refine (fun () => g);
        ev
      in
      let arr := Array.of_list (List.map (fun x => Some x) (unsafe_enter remember_and_shelve)) in
      let fn j :=
        let ev :=
          match (Array.get arr j) with
          | Some ev => Array.set arr j None; ev
          | None =>
              let msg := fprintf "[perm] argument contains duplicate entry: %i" j in
              Control.zero (Invalid_argument (Some msg))
          end
        in
        Control.new_goal ev
      in
      Array.iter fn perm.

  Ltac2 reorder (perm : int list) : unit := reorder_arr (Array.of_list perm).

  (* Ltac2 Notation "reorder" "[" l(list0(tactic, ",")) "]" := reorder l. *)


  Ltac2 test_fails f :=
    match Control.case (fun () =>
      match Control.case f with
      | Val _ => Control.zero (Tactic_failure None)
      | Err _ => ()
      end)
    with
    | Val _ => true
    | Err _ => false
    end.
  Ltac2 test_succeeds f := Bool.neg (test_fails f).
  Ltac2 succeeds f :=
    match Control.case f with
    | Val ((), _) => true
    | Err _ => false
    end.
  Ltac2 fails f := Bool.neg (succeeds f).
  Ltac2 Type exn ::= [ Tactic_success (message) | Erase_side_effects (exn) | Tactic_succeeds ].
  Ltac2 save_proofview () :=
    match Control.case (fun () => Control.plus (fun () => ()) (fun _ => ())) with
    | Err _ => Control.throw Assertion_failure
    | Val ((), k) => (fun () => k No_value) (* which exn is used doesn't matter *)
    end.
  Ltac2 erase_side_effects f :=
    let reset := save_proofview () in let res := f () in reset (); res.
  Ltac2 case_erase_side_effects f :=
    Control.case (fun () => erase_side_effects f).
  Ltac2 once_erase_side_effects f :=
    once (fun () => erase_side_effects f).
  Ltac2 succeeds_message f :=
    match erase_side_effects (fun () => Tactic_success (f ())) with
    | Tactic_success msg => msg
    | err => Control.zero err
    end.
  Ltac2 erase_side_effects_or_error f :=
    erase_side_effects f.

  Ltac2 in_evar (ev : evar) f :=
    Control.new_goal ev > [ .. | f (); shelve () ].
  Ltac2 in_evar_constr (ev : constr) f := in_evar (Constr.destEvar ev) f.
  Ltac2 goal_evars () :=
    Constr.fold_left
      (fun acc c => if Constr.is_evar c && Bool.neg (List.mem Constr.equal c acc) then c :: acc else acc)
      []
      (Control.goal ()).

  (* TODO: remove when we upgrade Coq *)
  Ltac2 solve_constraints () := ltac1:(solve_constraints).

  Ltac2 better_refine (f : unit -> constr) :=
    unshelve (fun () => let c := f () in eexact $c).
  Ltac2 better_refine_or_red (f : unit -> constr) :=
    once (fun () => unshelve (fun () =>
      let c := f () in
      (*Control.plus_bt (fun () => eexact $c) (fun _err _info =>*)(
        cbv beta iota zeta in *;
        let c := eval cbv beta iota zeta in $c in
        eexact $c))).
End Control.

Module Fresh.
  Import Ltac2.Fresh.
  Ltac2 fresh' (b : Free.t) (id : ident) := let id := fresh b id in (id, Fresh.Free.union b (Free.of_ids [id])).
End Fresh.

Module Int.
  Import Ltac2.Int.
  Module IntNotations.
    Ltac2 Notation x(self) "+" y(self) : 2 := Int.add x y.
    Ltac2 Notation x(self) "-" y(self) : 2 := Int.sub x y.
    Ltac2 Notation x(self) "*" y(self) : 2 := Int.mul x y.
    Ltac2 Notation x(self) "/" y(self) : 2 := Int.div x y.
    Ltac2 Notation x(self) "%" y(self) : 2 := Int.mod x y.
    Ltac2 Notation x(self) "==" y(self) : 2 := Int.equal x y.
    Ltac2 Notation x(self) "!=" y(self) : 2 := Bool.neg (Int.equal x y).
    Ltac2 Notation x(self) "<" y(self) : 2 := Int.lt x y.
    Ltac2 Notation x(self) "<=" y(self) : 2 := Int.le x y.
    Ltac2 Notation x(self) ">" y(self) : 2 := Int.gt x y.
    Ltac2 Notation x(self) ">=" y(self) : 2 := Int.ge x y.
  End IntNotations.
  Ltac2 min (x : int) (y : int) := if Int.lt x y then x else y.
End Int.
Module Option.
  Import Ltac2.Printf.
  Ltac2 is_some (o : 'a option) :=
    match o with
    | Some _ => true
    | None => false
    end.
  Ltac2 is_none (o : 'a option) :=
    match o with
    | Some _ => false
    | None => true
    end.
  Ltac2 filter (f : 'a -> bool) (o : 'a option) :=
    match o with
    | Some x => if f x then Some x else None
    | None => None
    end.
  Ltac2 pr_option (pr : 'a -> message) (o : 'a option) :=
    match o with
    | Some x => fprintf "Some %a" (fun () => pr) x
    | None => Message.of_string "None"
    end.
  Ltac2 pr_option_parens (pr : 'a -> message) (o : 'a option) :=
    match o with
    | Some x => fprintf "(Some %a)" (fun () => pr) x
    | None => Message.of_string "None"
    end.
End Option.
Ltac2 pr_option (pr : 'a -> message) (o : 'a option) := Option.pr_option pr o.
Ltac2 pr_option_parens (pr : 'a -> message) (o : 'a option) := Option.pr_option_parens pr o.
Module Message.
  Ltac2 of_exn_pretty (err : exn) :=
    match err with
    | Tactic_failure (Some msg) => msg
    | _ => Message.of_exn err
    end.
  Ltac2 of_exn_bt (err : exn) (info : exninfo) :=
    match Control.case (fun () => Control.zero_bt err info) with
    | Val _ => Control.throw Assertion_failure
    | Err err => Message.of_exn err
    end.
  Ltac2 of_exn_bt_pretty (err : exn) (info : exninfo) :=
    match Control.case (fun () => Control.zero_bt err info) with
    | Val _ => Control.throw Assertion_failure
    | Err err => Message.of_exn_pretty err
    end.
End Message.

Module Char.
  Import Ltac2.Char.
  Import Ltac2.Bool.BoolNotations.
  Import Int.IntNotations.
  Ltac2 is_space (c : char) :=
    let c := Char.to_int c in
    (c == 32) || (c == 12) || (c == 10) || (c == 13) || (c == 9).
  Ltac2 nl () := Char.of_int 10.
  Ltac2 cr () := Char.of_int 13.
  Ltac2 lf () := Char.of_int 10.
  Ltac2 tab () := Char.of_int 9.
  Ltac2 space () := Char.of_int 32.
  Ltac2 formfeed () := Char.of_int 12.
  Ltac2 newline () := Char.of_int 10.
  Ltac2 comma () := Char.of_int 44.
End Char.
Module String.
  Import Ltac2.String.
  Import Ltac2.Bool.BoolNotations.
  Ltac2 starts_with (prefix : string) (s : string) :=
    let len_s := length s in
    let len_pre := length prefix in
    let rec aux i :=
      if Int.equal i len_pre then true
      else if Bool.neg (Char.equal (get s i) (get prefix i)) then false
      else aux (Int.add i 1)
    in Int.ge len_s len_pre && aux 0.

  Ltac2 ends_with (suffix : string) (s : string) :=
    let len_s := length s in
    let len_suf := length suffix in
    let diff := Int.sub len_s len_suf in
    let rec aux i :=
      if Int.equal i len_suf then true
      else if Bool.neg (Char.equal (get s (Int.add diff i)) (get suffix i)) then false
      else aux (Int.add i 1)
    in Int.ge diff 0 && aux 0.

  Ltac2 rec index_rec (s : string) (lim : int) (i : int) (c : char) :=
    if Int.ge i lim then Control.throw Not_found else
      if Char.equal (get s i) c then i else index_rec s lim (Int.add i 1) c.

  Ltac2 rec index_rec_opt (s : string) (lim : int) (i : int) (c : char) :=
    if Int.ge i lim then None else
      if Char.equal (get s i) c then Some i else index_rec_opt s lim (Int.add i 1) c.

  Ltac2 index_opt (s : string) (c : char) :=
    index_rec_opt s (length s) 0 c.

  Ltac2 index_from (s : string) (i : int) (c : char) :=
    let l := length s in
    if Int.lt i 0 || Int.gt i l then
      Control.throw (Invalid_argument (Some (Message.of_string "String.index_from")))
    else
      index_rec s l i c.

  Ltac2 index_from_opt (s : string) (i : int) (c : char) :=
    let l := length s in
    if Int.lt i 0 || Int.gt i l then
      Control.throw (Invalid_argument (Some (Message.of_string "String.index_from_opt")))
    else
      index_rec_opt s l i c.

  Ltac2 index (s : string) (c : char) := index_rec s (length s) 0 c.

  Ltac2 split_on_char (sep : char) (s : string) :=
    let l := length s in
    let rec aux from :=
      if Int.lt from l then
        match index_from_opt s from sep with
        | Some i =>
            sub s from (Int.sub i from) :: aux (Int.add i 1)
        | None => [sub s from (Int.sub l from)]
        end
      else
        []
    in
    aux 0.

  Ltac2 trim (s : string) :=
    let l := length s in
    let rec aux_up i :=
      if Int.lt i l && Char.is_space (get s i) then
        aux_up (Int.add i 1)
      else
        i
    in
    let rec aux_down i :=
      let i' := Int.sub i 1 in
      if Int.ge i' 0 && Char.is_space (get s i') then
        aux_down i'
      else
        i
    in
    let i := aux_up 0 in
    let l := Int.sub (aux_down l) i in
    sub s i l.

  Ltac2 length_common_prefix (s1 : string) (s2 : string) :=
    let l1 := length s1 in
    let l2 := length s2 in
    let rec aux i :=
      if Int.lt i l1 && Int.lt i l2 && Char.equal (get s1 i) (get s2 i) then
        aux (Int.add i 1)
      else
        i
    in
    aux 0.

  Ltac2 common_prefix (s1 : string) (s2 : string) :=
    String.sub s1 0 (String.length_common_prefix s1 s2).

  Ltac2 strip_brackets (start_char : string) (end_char : string) (s : string) :=
    if String.starts_with start_char s && String.ends_with end_char s
    then
      let start_char_len := String.length start_char in
      let end_char_len := String.length end_char in
      String.sub s start_char_len (Int.sub (String.length s) (Int.add start_char_len end_char_len))
    else
      s.

  Ltac2 strip_prefix (prefix : string) (s : string) :=
    if String.starts_with prefix s
    then
      let prefix_len := String.length prefix in
      String.sub s prefix_len (Int.sub (String.length s) prefix_len)
    else
      s.

  Ltac2 replace_char (c : char) (s : string) (in_str : string) :=
    String.concat s (String.split_on_char c in_str).
  Ltac2 replace_nl_with_space str := replace_char (Char.nl ()) " " (replace_char (Char.cr ()) " " str).
  Ltac2 collapse_spaces str := String.concat " " (List.filter (fun s => Bool.neg (String.equal s "")) (String.split_on_char (Char.space ()) (replace_nl_with_space str))).

  Ltac2 split_firstword (s : string) :=
    match String.index_opt s (Char.space ()) with
    | Some idx =>
        let word := String.sub s 0 idx in
        let rest := String.sub s (Int.add idx 1) (Int.sub (String.length s) (Int.add idx 1)) in
        (word, rest)
    | None => (s, "")
    end.
End String.
Module Reference.
  Import Ltac2.Printf.
  Ltac2 of_constr_opt (c : constr) :=
    match Constr.Unsafe.kind_nocast c with
    | Constr.Unsafe.Constant kn _ => Some (Std.ConstRef kn)
    | Constr.Unsafe.Var id => Some (Std.VarRef id)
    | Constr.Unsafe.Ind ind _ => Some (Std.IndRef ind)
    | Constr.Unsafe.Constructor c _ => Some (Std.ConstructRef c)
    | Constr.Unsafe.Proj p _ _ => Option.map (fun c => Std.ConstRef c) (Proj.to_constant p)
    | _ => None
    end.
  Ltac2 of_constr_exn (c : constr) :=
    match of_constr_opt c with
    | Some r => r
    | None => Control.zero (Invalid_argument (Some (fprintf "Reference.of_constr: could not get reference for %t" c)))
    end.
  Ltac2 of_constr (c : constr) :=
    match Control.case (fun () => of_constr_exn c) with
    | Val (r, _) => r
    | Err err => Control.throw err
    end.
  Ltac2 to_message (r : Std.reference) := Message.of_constr (Env.instantiate r).
  Ltac2 to_qualified_string (r : Std.reference) :=
    String.concat "." (List.map Ident.to_string (Env.path r)).
  Ltac2 pr_qualified (r : Std.reference) := pr_list_with_sep (Message.of_string ".") Message.of_ident (Env.path r).
End Reference.
Module Export ExtraConstr.
  Import Ltac2.Printf.
  Module Constr.
    (** Print a constr as its fully qualified reference name (bypassing notations),
        or return None if the constr is not a reference. *)
    Ltac2 pr_qualified_reference_opt (c : constr) : message option :=
      Option.map Reference.pr_qualified (Reference.of_constr_opt c).
    (** Print a constr as its fully qualified reference name (bypassing notations),
        or fall back to [Message.of_constr] if the constr is not a reference. *)
    Ltac2 pr_maybe_qualified_reference (c : constr) : message :=
      match pr_qualified_reference_opt c with
      | Some msg => msg
      | None => Message.of_constr c
      end.
    Ltac2 to_qualified_string_opt (c : constr) : string option :=
      Option.map Reference.to_qualified_string (Reference.of_constr_opt c).
    Ltac2 to_qualified_string (c : constr) : string :=
      match to_qualified_string_opt c with
      | Some s => s
      | None => Constr.to_string c
      end.
  End Constr.
End ExtraConstr.
Module Std.
  Import Ltac2.TransparentState.
  Ltac2 Type unify_goal_kind := [ UseGoalConstraint | UnifyGoalTypes ((constr -> constr -> unit) option) | NoUnifyGoal ].
  Ltac2 refine_preterm_gen (ev : bool) (tc : bool) (eager_tc : bool) (unify_goal : unify_goal_kind) (h : preterm) :=
    let fl := if ev then if eager_tc then Constr.Pretype.Flags.open_constr_flags_with_tc else Constr.Pretype.Flags.open_constr_flags_no_tc else Constr.Pretype.Flags.constr_flags in
    Control.better_refine_or_red (fun () =>
      match unify_goal with
      | UseGoalConstraint =>
          Constr.Pretype.pretype fl (Constr.Pretype.expected_oftype (Control.goal ())) h
      | UnifyGoalTypes unify_goal =>
          let unify_goal := Option.default (fun x y => unify $x $y) unify_goal in
          let c := Constr.Pretype.pretype fl Constr.Pretype.expected_without_type_constraint h in
          let ty := Constr.type c in
          let gl := Control.goal () in
          unify_goal ty gl;
          c
      | NoUnifyGoal =>
          Constr.Pretype.pretype fl Constr.Pretype.expected_without_type_constraint h
      end);
    (if tc then try (solve [ unshelve typeclasses_eauto ]) else ());
    Control.shelve_unifiable ();
    cbv beta.
  Ltac2 apply_via_preterm_gen (ev : bool) (tc : bool) (eager_tc : bool) (f : constr) (mk_hole : int -> preterm) :=
    let n := Constr.count_prod (Constr.type f) in
    let h := Preterm.specialize_n_gen n (preterm:($f)) mk_hole in
    refine_preterm_gen ev tc eager_tc (UnifyGoalTypes None) h.
  Ltac2 apply_via_preterm (ev : bool) (tc : bool) (eager_tc : bool) (f : constr) :=
    apply_via_preterm_gen ev tc eager_tc f (fun _i => preterm:(_)).
  Ltac2 unfold_constant_in (force: bool) (c_unfold: constr) (c_in: constr) :=
    match Reference.of_constr_opt c_unfold with
    | Some r =>
        let do_eval () := eval cbv delta [ $r ] in $c_in in
        match Control.case (fun () => if force then with_strategy Expand [r] do_eval else do_eval ()) with
        | Val (v, _) => Some v
        | Err _ => None
        end
    | _ => None
    end.
  Ltac2 progress_unfold_constant_in (force: bool) (c_unfold: constr) (c_in: constr) :=
    match unfold_constant_in force c_unfold c_in with
    | Some v => if Constr.equal v c_in then None else Some v
    | None => None
    end.
  Ltac2 unfold_constant (c: constr) := unfold_constant_in false c c.
  Ltac2 force_unfold_constant (c: constr) := unfold_constant_in true c c.
  Ltac2 progress_unfold_constant (c: constr) := progress_unfold_constant_in false c c.
  Ltac2 progress_force_unfold_constant (c: constr) := progress_unfold_constant_in true c c.

  Ltac2 is_unfoldable_constant (c: constr) := Option.is_some (progress_unfold_constant c).
  Ltac2 is_forcibly_unfoldable_constant (c: constr) := Option.is_some (progress_force_unfold_constant c).

  Ltac2 is_unfoldable_head (c: constr) :=
    let (h, _args) := Constr.decompose_app_nocast c in
    is_unfoldable_constant h.
  Ltac2 is_forcibly_unfoldable_head (c: constr) :=
    let (h, _args) := Constr.decompose_app_nocast c in
    is_forcibly_unfoldable_constant h.

  Ltac2 is_unfoldable_head_under_lambda_prod (c: constr) :=
    let h := Constr.Unsafe.head_under_lambda_prod c in
    is_unfoldable_constant h.
  Ltac2 is_forcibly_unfoldable_head_under_lambda_prod (c: constr) :=
    let h := Constr.Unsafe.head_under_lambda_prod c in
    is_forcibly_unfoldable_constant h.

  (* Work around COQBUG(https://github.com/rocq-prover/rocq/issues/14286) *)
  Ltac2 eval_red_safe (c : constr) :=
    let c := eval cbv beta in $c in
    if is_unfoldable_head_under_lambda_prod c
    then eval red in $c
    else c.

  Ltac2 unify_or_instantiate_evar (x : constr) (y : constr) :=
    Control.plus_bt
      (fun () => unify $x $y) (fun unif_err unif_info =>
        if Constr.is_evar x then
          Control.in_evar_constr x (fun () => eexact $y)
        else if Constr.is_evar y then
          Control.in_evar_constr y (fun () => eexact $x)
        else
          Control.zero_bt unif_err unif_info).
End Std.

Module Proj.
  Export Ltac2.Proj.
  Ltac2 to_constr (p : projection) := Env.instantiate (Std.ConstRef (Option.get (Proj.to_constant p))).
  Ltac2 to_message (p : projection) := Message.of_constr (to_constr p).
  Ltac2 strip_projection_args (c : constr) :=
    match Constr.Unsafe.kind_nocast c with
    | Constr.Unsafe.Proj p _ _ => to_constr p
    | _ => c
    end.
End Proj.
Module Constant.
  Export Ltac2.Constant.
  Ltac2 to_constr (c : constant) := Env.instantiate (Std.ConstRef c).
  Ltac2 to_message (c : constant) := Message.of_constr (to_constr c).
  Ltac2 pr (c : constant) := to_message c.
  Ltac2 pr_qualified (c : constant) := Reference.pr_qualified (Std.ConstRef c).
  Ltac2 to_qualified_string (c : constant) := Reference.to_qualified_string (Std.ConstRef c).
End Constant.
Ltac2 better_apply0 adv ev cb cl :=
enter_h ev (fun _ () => Std.apply adv true cb cl) (fun () => ()).

Ltac2 Notation "better_apply"
cb(list1(thunk(seq(open_constr, with_bindings)), ","))
cl(opt(seq("in", ident, opt(seq("as", intropattern))))) :=
better_apply0 true false cb cl.

Module Export Notations.
  Export Ltac2.Notations.

  Ltac2 Notation "eval" "red" "in" c(constr) :=
    Std.eval_red_safe c.

  Ltac2 Abbreviation shelve_unifiable := Control.shelve_unifiable ().

  Ltac2 apply_via_preterm0_gen ev tc eager_tc mk_hole f:=
    enter_h ev (fun _ () => Std.apply_via_preterm_gen ev tc eager_tc f mk_hole) (fun () => ()).
  Ltac2 apply_via_preterm0 ev tc eager_tc simple_unify f :=
    let mk_hole := if simple_unify then (fun _i => preterm:(ltac2:(intros))) else (fun _i => preterm:(_)) in
    apply_via_preterm0_gen ev tc eager_tc mk_hole f.
  Ltac2 Notation "apply_via_preterm" f(open_constr) := apply_via_preterm0 false true false f.
  Ltac2 Notation "eapply_via_preterm_no_tc" f(open_constr) := apply_via_preterm0 true false false false f.
  Ltac2 Notation "eapply_via_preterm_eager_tc" f(open_constr) := apply_via_preterm0 true true true false f.
  Ltac2 Notation "eapply_via_preterm" f(open_constr) := apply_via_preterm0 true true false false f.
  Ltac2 Notation "simple_apply_via_preterm" f(open_constr) := apply_via_preterm0 false true false true f.
  Ltac2 Notation "simple_eapply_via_preterm_no_tc" f(open_constr) := apply_via_preterm0 true false false true f.
  Ltac2 Notation "simple_eapply_via_preterm_eager_tc" f(open_constr) := apply_via_preterm0 true true true true f.
  Ltac2 Notation "simple_eapply_via_preterm" f(open_constr) := apply_via_preterm0 true true false true f.

  (* TODO Remove once we update Coq, this has been upstreamed *)
  Ltac2 Notation "rename" renames(list1(seq(ident, "into", ident), ",")) :=
    Std.rename renames.

  (* more general form of Ltac2.Notations.exact1 *)
  Ltac2 exact2 ev tc c :=
    Control.enter (fun () =>
      let c :=
        Constr.Pretype.pretype
          (if ev then if tc then Constr.Pretype.Flags.open_constr_flags_with_tc else Constr.Pretype.Flags.open_constr_flags_no_tc else Constr.Pretype.Flags.constr_flags)
          (Constr.Pretype.expected_oftype (Control.goal()))
          c
      in
      Std.exact_no_check c).

  Ltac2 Notation "eexact_no_tc" c(preterm) := exact2 true false c.
  Ltac2 Notation "erefine" c(preterm) := unshelve (eexact_no_tc $preterm:c).
  Ltac2 Notation "erefineb" c(preterm) := unshelve (eexact_no_tc $preterm:c); cbv beta.
End Notations.
Import Ltac2.Printf.
Import Ltac2.Bool.BoolNotations.

Ltac2 fail fmt := Message.Format.kfprintf (fun msg => Control.zero (Tactic_failure (Some msg))) fmt.
Ltac2 Notation "fail" fmt(format) := fail fmt.
Ltac2 fail_bt info fmt := Message.Format.kfprintf (fun msg => Control.zero_bt (Tactic_failure (Some msg)) info) fmt.
Ltac2 Notation "fail_bt" info(tactic(0)) fmt(format) := fail_bt info fmt.
Ltac2 throw fmt := Message.Format.kfprintf (fun msg => Control.throw (Tactic_failure (Some msg))) fmt.
Ltac2 Notation "throw" fmt(format) := throw fmt.
Ltac2 throw_bt info fmt := Message.Format.kfprintf (fun msg => Control.throw_bt (Tactic_failure (Some msg)) info) fmt.
Ltac2 Notation "throw_bt" info(tactic(0)) fmt(format) := throw_bt info fmt.
Ltac2 backtrack_invalid_argument fmt := Message.Format.kfprintf (fun msg => Control.zero (Invalid_argument (Some msg))) fmt.
Ltac2 Notation "backtrack_invalid_argument" fmt(format) := backtrack_invalid_argument fmt.

Ltac2 pr_list (pr : 'a -> message) (ls : 'a list) :=
  fprintf "[%a]" (fun () => pr_list_with_sep (fprintf ", ") pr) ls.

Ltac2 pr_array_with_sep (sep : message) (pr : 'a -> message) (arr : 'a array) :=
  pr_list_with_sep sep pr (Array.to_list arr).

Ltac2 pr_array (pr : 'a -> message) (arr : 'a array) :=
  fprintf "[%a]" (fun () => pr_array_with_sep (fprintf "; ") pr) arr.

Ltac2 get_ind_sort (sort : constr) (c : constr) :=
  let ind := '(ltac2:(induction 1; exact (fun a v => v)) : $c -> forall a : $sort, a -> a) in
  let ind := (eval cbv beta in $ind) in
  let ind := lazy_match! ind with
              | (fun v => ?f v) => f
              | _ => ind
              end in
  match Constr.Unsafe.kind ind with
  | Constr.Unsafe.App f _args => f
  | _ => fail "get_ind: expected an application, not %t" ind
  end.
Ltac2 get_ind (c : constr) := get_ind_sort 'Type c.

Ltac2 get_ind_from_goal () :=
  lazy_match! goal with
  | [ |- ?a -> _ ] => get_ind a
  end.

(* Unfolds the head of a term if it's a reference (constant) *)
Ltac2 rec unfold_head_under_lambda_gen (under_lambda : bool) (c : constr) : constr * constant option :=
  let (h, _args) := Constr.decompose_app_nocast c in
  match Constr.Unsafe.kind_nocast h with
  | Constr.Unsafe.Constant kn _ =>
    let r := Std.ConstRef kn in
    match Control.case (fun () => eval cbv [ $r ] in $c) with
    | Val (v, _) => if Constr.equal v c then (c, None) else (v, Some kn)
    | Err _ => (c, None)
    end
  | Constr.Unsafe.Lambda b t =>
    if under_lambda then
      let (v, kn) := unfold_head_under_lambda_gen under_lambda t in
      (Constr.mkLambda b v, kn)
    else
      (c, None)
  | _ => (c, None)
  end.

(* Unfolds the head of a term if it's a reference (constant) *)
Ltac2 unfold_head (c : constr) : constr * constant option := unfold_head_under_lambda_gen false c.

(* Unfolds the head of a term if it's a reference (constant) *)
Ltac2 unfold_head_under_lambda (c : constr) : constr * constant option := unfold_head_under_lambda_gen true c.

(* Recursively unfolds a term until it reaches a fixed point *)
Ltac2 rec unfold_head_under_lambda_rec_gen (under_lambda : bool) (c : constr) : constr * (constant list) :=
  let (c', r) := unfold_head_under_lambda_gen under_lambda c in
  match r with
  | Some r =>
      let (c'', rs) := unfold_head_under_lambda_rec_gen under_lambda c' in
      (c'', r :: rs)
  | None =>
      (c', [])
  end.

(* Recursively unfolds a term until it reaches a fixed point *)
Ltac2 unfold_head_rec (c : constr) : constr * (constant list) := unfold_head_under_lambda_rec_gen false c.

(* Recursively unfolds a term until it reaches a fixed point *)
Ltac2 unfold_head_under_lambda_rec (c : constr) : constr * (constant list) := unfold_head_under_lambda_rec_gen true c.

Polymorphic Cumulative Inductive sort_poly_eq@{s s';u u'|u <= u'} {A : Type@{s;u}} : A -> A -> Type@{s';u'} := sort_poly_eq_refl : forall x : A, sort_poly_eq x x.

Ltac2 Notation "strategy:(" s(strategy) ")" := s.
Ltac2 Notation "clause:(" c(clause) ")" := c.
Ltac2 Notation "strategy_clause:(" s(strategy) c(opt(clause)) ")" := (s, Notations.default_on_concl c).

Ltac2 try_clear_all_hyps () :=
  let hyps := Control.hyps () in
  List.iter (fun (n, _, _) => try (clear $n)) (List.rev hyps).

Ltac2 force_clear_all_hyps () :=
  let hyps := Control.hyps () in
  List.iter (fun (n, _, _) => clear $n) (List.rev hyps).

Ltac2 revert_all_hyps () :=
  let hyps := Control.hyps () in
  List.iter (fun (n, _, _) => revert $n) (List.rev hyps).

Ltac try_clear_all_hyps := ltac2:(try_clear_all_hyps ()).
Ltac force_clear_all_hyps := ltac2:(force_clear_all_hyps ()).
Ltac revert_all_hyps := ltac2:(revert_all_hyps ()).

Ltac2 clear_lastn (n : int) :=
  if Int.equal n 0
  then ()
  else
    let hyps := Control.hyps () in
    let hyps := List.lastn n hyps in
    let hyps := List.map (fun (n, _, _) => n) hyps in
    Std.clear hyps.

Ltac2 revert_lastn (n : int) :=
  let hyps := Control.hyps () in
  let hyps := List.map (fun (n, _, _) => n) hyps in
  Std.revert (List.lastn n hyps).

Ltac2 revert_last () := revert_lastn 1.

Ltac2 revert_until (h : ident) :=
  let hyps := Control.hyps () in
  let hyps := List.map (fun (h', _, _) => h') hyps in
  let idx := Option.get (List.find_index (Ident.equal h) hyps) in
  Std.revert (List.lastn (Int.sub (List.length hyps) (Int.add 1 idx)) hyps).

Ltac2 revert_clear_lastn (n : int) :=
  clear_lastn (Int.sub n 1);
  revert_last ().

Ltac2 revert_per_goal () :=
  let n := Ref.ref 1 in
  Control.enter (fun () =>
    revert_clear_lastn (Ref.get n);
    Ref.incr n).

Ltac2 mutable debug_intros_revert_clear_rec := false.

Ltac2 rec intros_count_clear_rec (rec_head : constr) :=
  lazy_match! goal with
  | [ |- forall x : ?t _, _ ] =>
      let introed :=
        if Constr.equal t rec_head then
          match Control.case (fun () => intros _) with
          | Val _ => true
          | Err err =>
            (if debug_intros_revert_clear_rec then (
              printf "intros_revert_clear_rec: Could not intros _: %a" (fun () => Message.of_exn_pretty) err;
              Control.print_goal ()
            ) else ());
            false
          end
        else false in
      if introed then
        intros_count_clear_rec rec_head
      else (
        intro;
        let n_hyps_to_revert := intros_count_clear_rec rec_head in
        Int.add 1 n_hyps_to_revert
      )
  | [ |- forall x : _, _ ] => intro; Int.add 1 (intros_count_clear_rec rec_head)
  | [ |- let _ := _ in _ ] => intro; Int.add 1 (intros_count_clear_rec rec_head)
  | [ |- _ ] => 0
  end.

Ltac2 rec intros_revert_clear_rec (rec_head : constr) :=
  let n := intros_count_clear_rec rec_head in
  revert_lastn n.

Ltac2 fold_match_force_nondep_around f :=
  lazy_match! goal with
  | [ |- ?p ?_x ] =>
      let p' := Fresh.in_goal @p' in
      set ($p' := $p);
      let p'c := Control.hyp p' in
      (*change ($p'c $x); *)
      f ();
      Control.enter (fun () =>
        intros_revert_clear_rec p'c;
        subst $p'
      )
  end.

Ltac2 Type exn ::= [ SchemeRegistrationError (message) ].

(** Map a sort constr to the dependent induction/recursion scheme kind. *)
Ltac2 sort_to_ind_dep_scheme_kind (sort : constr) : Scheme.kind :=
  if Constr.is_set sort then Scheme.rec_dep
  else if Constr.is_prop sort then Scheme.ind_dep
  else if Constr.is_sprop sort then Scheme.sind_dep
  else Scheme.rect_dep.

(** Map a sort constr to the dependent case analysis scheme kind.
    The Ltac2 Scheme API provides case kinds for Type, Prop, and SProp.
    Set maps to case_dep (Type) since there is no Set-specific case kind. *)
Ltac2 sort_to_case_dep_scheme_kind (sort : constr) : Scheme.kind :=
  if Constr.is_prop sort then Scheme.casep_dep
  else if Constr.is_sprop sort then Scheme.scase_dep
  else Scheme.case_dep.

(** All dependent induction scheme kinds. *)
Ltac2 all_ind_dep_scheme_kinds () : Scheme.kind list :=
  [Scheme.rect_dep; Scheme.rec_dep; Scheme.ind_dep; Scheme.sind_dep].

(** All case analysis scheme kinds (both dep and nodep). *)
Ltac2 all_case_scheme_kinds () : Scheme.kind list :=
  [Scheme.case_dep; Scheme.case_nodep; Scheme.casep_dep; Scheme.casep_nodep; Scheme.scase_dep; Scheme.scase_nodep].


Ltac2 fold_match_maybe_force_nondep_around (nondep : bool) f :=
  if nondep
  then fold_match_force_nondep_around f
  else f ().

Ltac2 sanity_check_fold_match_msg (loc : message) :=
  Control.enter (fun () =>
    match Control.case (fun () => constr:(ltac2:(try_clear_all_hyps (); let x := Fresh.in_goal @x in intro $x; let x := Control.hyp x in induction $x; exact (fun v => v)) :> forall x : nat, nat -> nat)) with
    | Val _ => ()
    | Err err => throw "sanity_check_fold_match: %a: induction failed with %a" (fun () a => a) loc (fun () => Message.of_exn_pretty) err
    end).

Ltac2 sanity_check_fold_match (loc : string) := sanity_check_fold_match_msg (fprintf "%s" loc).

Ltac2 get_induction_scheme_for_gen (c : constr) (ty : constr) (_pre_tac : unit -> unit) :=
  let (c_head, _) := Constr.decompose_app_nocast c in
  let c_ref := Reference.of_constr c_head in
  let sort := Constr.type ty in
  let kind := sort_to_ind_dep_scheme_kind sort in
  match Scheme.lookup kind c_ref with
  | Some ref => Env.instantiate ref
  | None =>
      Control.zero (SchemeRegistrationError
        (fprintf "Register a scheme for `Scheme Induction for %t Sort %t.`" c sort))
  end.

Ltac2 get_induction_scheme_for (c : constr) :=
  let (c_head, _) := Constr.decompose_app_nocast c in
  let c_ref := Reference.of_constr c_head in
  let sort := Constr.type c in
  let kind := sort_to_ind_dep_scheme_kind sort in
  match Scheme.lookup kind c_ref with
  | Some ref => Env.instantiate ref
  | None =>
      Control.zero (SchemeRegistrationError
        (fprintf "Register a scheme for `Scheme Induction for %t Sort %t.`" c sort))
  end.


(* Consider [nat_rect
     : forall P : nat -> Type,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n] and
       [option_rect
     : forall (A : Type) (P : option A -> Type),
       (forall a : A, P (Some a)) -> P None -> forall o : option A, P o]
  A term [t] is a case analysis scheme if we can resolve [_ : CaseScheme _ _ $t].
  A term [t] is a recursion scheme if, given [ty := Constr.type t], [ty] is of the form [forall b1 ... bn, final], and when we assert [forall b1 ... bn, final -> final] and induct on [bn], the head constant of the resulting term unifies with [t]. *)

Ltac2 rec last_forall_domain (ty : constr) : constr :=
  match Constr.Unsafe.kind_nocast ty with
  | Constr.Unsafe.Prod b body =>
      match Constr.Unsafe.kind_nocast body with
      | Constr.Unsafe.Prod _ _ => last_forall_domain body
      | _ => Constr.Binder.type b
      end
  | _ => throw "last_forall_domain: expected a product, not %t" ty
  end.


(** [is_induction_scheme t] returns [true] if [t] is a registered induction/recursion
    scheme for the inductive type it eliminates (via [Scheme.lookup]). *)
Ltac2 is_induction_scheme (t : constr) : bool :=
  let ty := Constr.type t in
  let n := Constr.count_prod ty in
  if Int.gt n 0 then
    let (ind_ty, _) := Constr.decompose_app_nocast (last_forall_domain ty) in
    match Reference.of_constr_opt ind_ty with
    | Some ind_ref =>
        List.exist (fun kind =>
          match Scheme.lookup kind ind_ref with
          | Some sref =>
              let scheme := Env.instantiate sref in
              Control.succeeds (fun () => unify $scheme $t)
          | None => false
          end
        ) (all_ind_dep_scheme_kinds ())
    | None => false
    end
  else false.

Ltac2 constructor_per_goal_then tac :=
  let n := Ref.ref 1 in
  Control.unshelve (fun () =>
    Control.enter (fun () =>
      Std.constructor_n true (Ref.get n) Std.NoBindings;
      Ref.incr n;
      tac ())).

Ltac2 constructor_per_goal () :=
  constructor_per_goal_then (fun () => ()).

Ltac2 rec prod_to_lambda (t : constr) :=
  match Constr.Unsafe.kind_nocast t with
  | Constr.Unsafe.Prod b t' => Constr.mkLambda b (prod_to_lambda t')
  | _ => t
  end.

Ltac2 lazy_head_beta_keepcast (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Cast c cst ty =>
      let c := eval lazy head beta in $c in
      Constr.mkCast c cst ty
  | _ => (* TODO: keep cast when it is under app *) eval lazy head beta in $c
  end.

Ltac2 specialize_with_evars_aux (c : constr) (t : constr) :=
  let n := Constr.count_prod t in
  let evs := Array.init n (fun _ => '_) in
  match Constr.Unsafe.check (Constr.mkApp c evs) with
  | Val app =>
      let app := lazy_head_beta_keepcast app in
      let evs := Array.to_list evs in
      let evs := List.filter (fun ev => Constr.is_evar ev) evs in
      (app, evs)
  | Err err => Control.zero err
  end.

Ltac2 specialize_with_evars_full (c : constr) :=
  specialize_with_evars_aux c (Constr.type c).

Ltac2 specialize_prod_with_evars_full (t : constr) :=
  specialize_with_evars_aux (prod_to_lambda t) t.

Ltac2 specialize_with_evars (c : constr) :=
  let (app, _evs) := specialize_with_evars_full c in
  app.

Ltac2 specialize_prod_with_evars (t : constr) :=
  let (app, _evs) := specialize_prod_with_evars_full t in
  app.

Ltac2 find_first_with_preference f pref xs :=
  let rec aux xs :=
    match xs with
    | [] => None
    | x :: xs =>
      match f x with
      | Some v =>
          if pref x
          then Some (v, true)
          else
            match aux xs with
            | Some (v, true) => Some (v, true)
            | _ => Some (v, false)
            end
      | None => aux xs
      end
    end in
  Option.map (fun (v, _) => v) (aux xs).

Ltac2 find_first2_with_preference f pref xs ys := find_first_with_preference (fun (x, y) => f x y) (fun (x, y) => pref x y) (List.combine xs ys).
Ltac2 find_first3_with_preference f pref xs ys zs := find_first_with_preference (fun ((x, y), z) => f x y z) (fun ((x, y), z) => pref x y z) (List.combine (List.combine xs ys) zs).
Ltac2 find_first4_with_preference f pref xs ys zs ws := find_first_with_preference (fun (((x, y), z), w) => f x y z w) (fun (((x, y), z), w) => pref x y z w) (List.combine (List.combine (List.combine xs ys) zs) ws).

Ltac2 find_first f xs := find_first_with_preference f (fun _ => true) xs.
Ltac2 find_first2 f xs ys := find_first2_with_preference f (fun _ _ => true) xs ys.
Ltac2 find_first3 f xs ys zs := find_first3_with_preference f (fun _ _ _ => true) xs ys zs.
Ltac2 find_first4 f xs ys zs ws := find_first4_with_preference f (fun _ _ _ _ => true) xs ys zs ws.

Ltac2 rec find_non_unifying_subterms_such_that_gen prop_early prop_late prop_pref f g :=
  let find_non_unifying_subterms := find_non_unifying_subterms_such_that_gen prop_early prop_late prop_pref in
  match Control.case (fun () => unify $f $g; Control.solve_constraints ()) with
  | Val _ => None
  | Err _ =>
    let (f1, args1) := Constr.decompose_app_nocast f in
    let (f2, args2) := Constr.decompose_app_nocast g in
    if (Int.equal (Array.length args1) (Array.length args2)) && Control.succeeds (fun () => unify $f1 $f2; Control.solve_constraints ())
    then
      let mismatched := find_first2_with_preference (fun a b =>
        if prop_early a b && Control.fails (fun () => unify $a $b; Control.solve_constraints ()) && prop_late a b
        then Some (a, b)
        else None
      ) prop_pref (Array.to_list args1) (Array.to_list args2) in
      match mismatched with
      | Some (a, b) => find_non_unifying_subterms a b
      | None => if prop_early f g && prop_late f g then Some (f, g) else None
      end
    else if Int.equal (Array.length args1) (Array.length args2) && Constr.is_proj f1 && Constr.is_proj f2
    then
      let (f1p, _f1i, f1v) := Constr.destProj f1 in
      let (f2p, _f2i, f2v) := Constr.destProj f2 in
      if Proj.equal f1p f2p
      then
        match find_non_unifying_subterms f1v f2v with
        | Some (a, b) => Some (a, b)
        | None => if prop_early f g && prop_late f g then Some (f, g) else None
        end
      else
        if prop_early f g && prop_late f g then Some (f, g) else None
    else
      if prop_early f g && prop_late f g then Some (f, g) else None
  end.

Ltac2 decompose_app_nocast_zip (fs : constr list) :=
  let h_args := List.map Constr.decompose_app_nocast fs in
  let hs := List.map (fun (h, _args) => h) h_args in
  let args := List.map (fun (_h, args) => args) h_args in
  let args_lens := List.map (fun args => Array.length args) args in
  let args_min_len := match args_lens with [] => 0 | args_len :: args_lens => List.fold_left Int.min args_len args_lens end in
  let args_head_lens := List.map (fun args_len => Int.sub args_len args_min_len) args_lens in
  let args_heads := List.map2 (fun args args_head_len => Array.sub args 0 args_head_len) args args_head_lens in
  let args_tails := List.map2 (fun args args_head_len => Array.sub args args_head_len args_min_len) args args_head_lens in
  let hs := List.map2 Constr.mkApp hs args_heads in
  List.combine hs args_tails.

Ltac2 decompose_app_nocast4 (f1 : constr) (f2 : constr) (g1 : constr) (g2 : constr) :=
  match decompose_app_nocast_zip [f1; f2; g1; g2] with
  | [(f1h, f1args); (g1h, g1args); (f2h, f2args); (g2h, g2args)] => ((f1h, f1args), (f2h, f2args), (g1h, g1args), (g2h, g2args))
  | _ => Control.throw Assertion_failure
  end.

Ltac2 rec find_non_unifying_subterms4_such_that_gen prop_early prop_late do_unify do_unify_evar_heads check_equal_len f1 g1 f2 g2 :=
  let find_non_unifying_subterms := find_non_unifying_subterms4_such_that_gen prop_early prop_late do_unify do_unify_evar_heads check_equal_len in
  (* let do_unify x1 y1 x2 y2 := unify $x1 $x2; unify $y1 $y2; unify $x2 $y2 in *)
  (* let check_equal_len x1 y1 x2 y2 := Int.equal x1 x2 && Int.equal y1 y2 && Int.equal x2 y2 in *)
  match Control.case (fun () => do_unify f1 g1 f2 g2) with
  | Val _ => None
  | Err _ =>
    (* first we attempt to unify any evars *)
    (if Constr.is_evar_head f1 || Constr.is_evar_head f2 || Constr.is_evar_head g1 || Constr.is_evar_head g2 then
      let ((f1h, _f1args), (f2h, _f2args), (g1h, _g1args), (g2h, _g2args)) := decompose_app_nocast4 f1 f2 g1 g2 in
      match Control.case (fun () => do_unify_evar_heads f1h g1h f2h g2h) with
      | Val _ => ()
      | Err err =>
          printf "Warning: find_non_unifying_subterms4_such_that_gen: do_unify_evar_heads failed on evars in:";
          printf " f1h=%t : %t" f1h (Constr.type f1h);
          printf " g1h=%t : %t" g1h (Constr.type g1h);
          printf " f2h=%t : %t" f2h (Constr.type f2h);
          printf " g2h=%t : %t" g2h (Constr.type g2h);
          printf " err=%a" (fun () => Message.of_exn_pretty) err
      end
    else ()
    );
    let (f1h, f1args) := Constr.decompose_app_nocast f1 in
    let (f2h, f2args) := Constr.decompose_app_nocast f2 in
    let (g1h, g1args) := Constr.decompose_app_nocast g1 in
    let (g2h, g2args) := Constr.decompose_app_nocast g2 in
    let ((f1h, f1args), (f2h, f2args), (g1h, g1args), (g2h, g2args)) :=
      if Constr.is_evar f1h || Constr.is_evar f2h || Constr.is_evar g1h || Constr.is_evar g2h then
        decompose_app_nocast4 f1 f2 g1 g2
      else ((f1h, f1args), (f2h, f2args), (g1h, g1args), (g2h, g2args)) in
    if check_equal_len (Array.length f1args) (Array.length g1args) (Array.length f2args) (Array.length g2args)
       && Control.succeeds (fun () => do_unify f1h g1h f2h g2h)
    then
      let mismatched := find_first4 (fun a1 b1 a2 b2 =>
        if prop_early a1 b1 a2 b2 && Control.fails (fun () => do_unify a1 b1 a2 b2) && prop_late a1 b1 a2 b2
        then Some (a1, b1, a2, b2)
        else None
      ) (Array.to_list f1args) (Array.to_list g1args) (Array.to_list f2args) (Array.to_list g2args) in
      match mismatched with
      | Some (a1, b1, a2, b2) => find_non_unifying_subterms a1 b1 a2 b2
      | None => if prop_early f1 g1 f2 g2 && prop_late f1 g1 f2 g2 then Some (f1, g1, f2, g2) else None
      end
    else if prop_early f1h g1h f2h g2h && prop_late f1h g1h f2h g2h then
      Some (f1h, g1h, f2h, g2h)
    else if prop_early f1 g1 f2 g2 && prop_late f1 g1 f2 g2 then
      Some (f1, g1, f2, g2)
    else (
      printf "no match head %t, %t, %t, %t" f1h g1h f2h g2h;
      printf "no match %t, %t, %t, %t" f1 g1 f2 g2;
      None
    )
  end.

Ltac2 find_non_unifying_subterms_such_that_early prop pref f g :=
  find_non_unifying_subterms_such_that_gen prop (fun _ _ => true) pref f g.

Ltac2 find_non_unifying_subterms_such_that_late prop pref f g :=
  find_non_unifying_subterms_such_that_gen (fun _ _ => true) prop pref f g.

Ltac2 find_non_unifying_subterms_such_that prop pref f g :=
  find_non_unifying_subterms_such_that_late prop pref f g.

Ltac2 find_non_unifying_subterms_with_preference pref f g :=
  find_non_unifying_subterms_such_that (fun _ _ => true) pref f g.

Ltac2 find_non_unifying_subterms f g :=
  find_non_unifying_subterms_such_that (fun _ _ => true) (fun _ _ => true) f g.

Ltac2 capture_error f msg :=
  match Control.case_bt f with
  | Val_bt (v, alt) => Control.plus_bt (fun () => v) alt
  | Err_bt err bt =>
      let msg := msg err in
      Message.print msg;
      Control.zero_bt (Tactic_failure (Some msg)) bt
  end.

Ltac2 capture_error_keep_SchemeRegistrationError f msg :=
  match Control.case_bt f with
  | Val_bt (v, alt) => Control.plus_bt (fun () => v) alt
  | Err_bt (SchemeRegistrationError _ as err) bt => Control.zero_bt err bt
  | Err_bt err bt =>
      let msg := msg err in
      Message.print msg;
      Control.zero_bt (Tactic_failure (Some msg)) bt
  end.

Ltac2 rec map_err f f_err :=
  match Control.case_bt f with
  | Val_bt (v, alt) => Control.plus_bt (fun () => v) (fun err info => map_err (fun () => alt err info) f_err)
  | Err_bt err bt => Control.zero_bt (f_err err) bt
  end.

Ltac2 rec refresh_universes (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Sort _ =>
      if Constr.equal c 'Set then c
      else if Constr.equal c 'Prop then c
      else if Constr.equal c 'SProp then c
      else 'Type
  | _ => Constr.Unsafe.map refresh_universes c
  end.

Ltac2 collect_evars (t : constr) :=
  let evs := Ref.ref [] in
  let rec go t :=
    (if Constr.is_evar t then Ref.set evs (t :: Ref.get evs) else ());
    Constr.Unsafe.iter go t
  in
  go t; Ref.get evs.

(** [collect_evars_topologically_sorted t] collects all evars in [t],
    computes dependencies (evar X depends on evar Y if Y appears in the
    type of X or in an element of X's instance), and returns them
    topologically sorted with dependencies first.
    In case of cycles, the remaining evars are appended at the end. *)
Ltac2 collect_evars_topologically_sorted (t : constr) :=
  let raw_evars := collect_evars t in
  (* Compare evar constrs by evar id (ignoring instances) *)
  let evar_constr_id_equal e1 e2 :=
    Constr.equal
      (Constr.Unsafe.make (Constr.Unsafe.Evar (Constr.destEvar e1) [| |]))
      (Constr.Unsafe.make (Constr.Unsafe.Evar (Constr.destEvar e2) [| |]))
  in
  let all_evars := List.uniq evar_constr_id_equal raw_evars in
  (* Immediate dependencies of an evar: evars found in its type and the types of its instance arguments *)
  let evar_deps ev_constr :=
    let found := Ref.ref [] in
    let process c :=
      List.iter (fun e => Ref.set found (e :: Ref.get found)) (collect_evars c)
    in
    (match Control.case (fun () => Constr.type ev_constr) with
     | Val (ty, _) => process ty
     | Err _ => ()
     end);
    (match Constr.Unsafe.kind ev_constr with
     | Constr.Unsafe.Evar _ inst => Array.iter (fun v => process (Constr.type v)) inst
     | _ => ()
     end);
    Ref.get found
  in
  List.topological_sort evar_constr_id_equal evar_deps all_evars.

Ltac2 type_from_cast (c : constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Cast _ _ ty => ty
  | _ =>
      match Control.case (fun () => Constr.type c) with
      | Val (ty, _) => ty
      | Err _ => fail "type_from_cast: Expected cast, got %t" c
      end
  end.

Definition unused_for_evar_normalize := I.
Ltac2 evar_normalize (c : constr) :=
  let c := eval cbv delta [unused_for_evar_normalize] in $c in
  c.

Ltac2 get_sort_under_prod (unfold_fun : constr -> constr) (f : constr) :=
  let rec go f (do_unfold : bool) :=
    match Constr.Unsafe.kind_nocast f with
    | Constr.Unsafe.Sort _ => Some f
    | Constr.Unsafe.Prod _ body => go body true
    | Constr.Unsafe.App h _ =>
        match Constr.Unsafe.kind_nocast h with
        | Constr.Unsafe.Sort _ => Some f
        | _ =>
          if do_unfold
          then go (unfold_fun f) false
          else None
        end
    | _ => None
    end in
  go f true.

Ltac2 is_Prop_under_prod (unfold_fun : constr -> constr) (f : constr) :=
  match get_sort_under_prod unfold_fun f with
  | Some f => Constr.equal f 'Prop
  | None => false
  end.

(* N.B. a type is the motive of a recursor if (a) it is an argument at top-level of the overall type, and (b) it is a product which ends in a sort, and (c) the head of the final return type is the current variable *)
Ltac2 type_is_motive_of_recursor (t : constr) :=
  get_sort_under_prod (fun a => a) t.

Ltac2 rec rel_is_head_of_return_type (n : int) (t : constr) :=
  match Constr.Unsafe.kind_nocast t with
  | Constr.Unsafe.Rel n' => Int.equal n n'
  | Constr.Unsafe.App h _ => rel_is_head_of_return_type n h
  | Constr.Unsafe.Prod _ body => rel_is_head_of_return_type (Int.add 1 n) body
  | _ => false
  end.


(* NB: refreshes Type universes *)
Ltac2 min_sort (s1 : constr) (s2 : constr) :=
  if Constr.equal s1 s2
  then s1
  else if Constr.is_sprop s1 || Constr.is_sprop s2
  then fail "min_sort: incompatible sorts %t and %t" s1 s2
  else if Constr.is_prop s1 || Constr.is_prop s2
  then 'Prop
  else if Constr.is_set s1 || Constr.is_set s2
  then 'Set
  else 'Type.

(* NB: refreshes Type universes *)
Ltac2 max_sort (s1 : constr) (s2 : constr) :=
  if Constr.equal s1 s2
  then s1
  else if Constr.is_sprop s1 || Constr.is_sprop s2
  then fail "min_sort: incompatible sorts %t and %t" s1 s2
  else
    match Constr.is_prop s1, Constr.is_prop s2, Constr.is_set s1, Constr.is_set s2 with
    | true, _, _, _ => s2
    | _, true, _, _ => s1
    | false, false, true, _ => s2
    | false, false, _, true => s1
    | false, false, false, false => 'Type
    end.


Ltac2 rec struct_arg (f : constr) : int :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Fix structs which _ _ => Array.get structs which
  | Constr.Unsafe.Lambda _ body => Int.add 1 (struct_arg body)
  | _ => fail "not a fixpoint"
  end.


Ltac2 rec find_hnf_blocker (c : constr) : (Std.reference * (constr * constr array option) option) list :=
  let (f, args) := Constr.decompose_app_nocast c in
  (* printf "find_hnf_blocker: %t" c; *)
  match Constr.Unsafe.kind_nocast f with
  | Constr.Unsafe.Constant c _ => [(Std.ConstRef c, Some (f, Some args))]
  | Constr.Unsafe.Case _c _cs _ci x _branches => find_hnf_blocker x
  | Constr.Unsafe.Fix _ _ _ _ => find_hnf_blocker (Array.get args (struct_arg f))
  | Constr.Unsafe.Proj p _ c =>
    let rest := find_hnf_blocker c in
    match (Proj.unfolded p, Proj.to_constant p) with
    | (true, _) => rest
    | (false, Some p) => (Std.ConstRef p, None) :: rest
    | (false, None) => rest
    end
  | Constr.Unsafe.Var v => [(Std.VarRef v, Some (f, Some args))]
  | _ => []
  end.

Ltac2 is_case_or_fix_or_cofix_head_under_unfolding (c : constr) :=
  match Std.progress_unfold_constant c with
  | Some c =>
      let (h, _) := Constr.Unsafe.decompose_app_under_lambda c in
      Constr.is_case h || Constr.is_fix h || Constr.is_cofix h
  | None => false
  end.

Ltac2 is_fix_or_cofix_head_under_unfolding (c : constr) :=
  match Std.progress_unfold_constant c with
  | Some c =>
      let (h, _) := Constr.Unsafe.decompose_app_under_lambda c in
      Constr.is_fix h || Constr.is_cofix h
  | None => false
  end.

Ltac2 is_fix_head_under_unfolding (c : constr) :=
  match Std.progress_unfold_constant c with
  | Some c =>
      let (h, _) := Constr.Unsafe.decompose_app_under_lambda c in
      Constr.is_fix h
  | None => false
  end.

Ltac2 rec eval_hnf_no_match_fix_opt (c : constr) :=
  let blockers := find_hnf_blocker c in
  let is_case_or_fix_head c :=
    let (h, _) := Constr.decompose_app_nocast c in
    Constr.is_case h || Constr.is_fix h || Constr.is_cofix h in
  let rec red_blockers blockers c :=
    match blockers with
    | [] => c
    | (r, _) :: blockers =>
        let c := match Control.case (fun () => eval cbv [$r] in $c) with
        | Val (c, _) => c
        | Err _ => c
        end in
        red_blockers blockers c
    end in
  let c' := red_blockers blockers c in
  if Constr.equal c' c then
    None
  else
    if is_case_or_fix_head c' && Bool.neg (is_case_or_fix_head c) then
      match eval_hnf_no_match_fix_opt c' with
      | Some c' =>
          if is_case_or_fix_head c' then
            None
          else
            Some c'
      | None => None
      end
    else
      Some (Option.default c' (eval_hnf_no_match_fix_opt c')).

Ltac2 eval_hnf_no_match_fix (c : constr) := Option.default c (eval_hnf_no_match_fix_opt c).

Ltac2 with_preterm_via_constr (f : constr -> 'a) (with_exn : exn -> 'a) (t : preterm) :=
  match Control.case_erase_side_effects (fun () =>
      f (Constr.open_pretype_no_tc t)
  ) with
  | Val (msg, _) => msg
  | Err err => with_exn err
  end.

Ltac2 wrap_solve_constraints_msg msg :=
  match Control.case Control.solve_constraints with
  | Val _ => msg
  | Err err => fprintf "%a (Constraint failure: %a)" (fun () a => a) msg (fun () => Message.of_exn_pretty) err
  end.

Ltac2 message_of_preterm_via_constr_map (f : constr -> constr) (include_type : bool) (t : preterm) :=
  with_preterm_via_constr (fun t => wrap_solve_constraints_msg (if include_type then fprintf "%t : %t" (f t) (f (Constr.type t)) else Message.of_constr (f t))) (fun err => fprintf "<exception in pretyper: %a>" (fun () => Message.of_exn_pretty) err) t.

Ltac2 message_of_preterm_via_constr_maybe_red (include_type : bool) (do_red : bool) (t : preterm) := message_of_preterm_via_constr_map (fun x => if do_red then eval cbv beta zeta in $x else x) include_type t.
Ltac2 message_of_preterm_via_constr (include_type : bool) (t : preterm) := message_of_preterm_via_constr_maybe_red include_type false t.
Ltac2 message_of_preterm_via_constr_red (include_type : bool) (t : preterm) := message_of_preterm_via_constr_maybe_red include_type true t.

Module Autoinduct.

Ltac2 find_applied (f : (constr * int) option) : constr * int :=
  match! goal with
  | [ |- context [ ?t ] ] =>
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.App g args =>
          let farg :=
            match f with
            | Some (f,farg) =>
                if Constr.equal f g then farg
                else fail "applies a different function"
            | None =>
                (* NB: if we encounter a Qed definition, eval red will
                  fail without backtracking (API limitation of ltac2).
                  We could work around this by doing the eval red
                  through ltac1 which does backtrack. *)
                if Constr.is_const g then struct_arg (Std.eval_red_safe g)
                else fail "not a constant"
            end
          in
          if Int.le farg (Array.length args)
          then (Array.get args farg, farg)
          else fail "not applied enough"
      | _ => fail "not an application"
      end
  end.

Ltac2 autofind_applied (f: constr option) : constr * int :=
  match f with
  | Some f =>
      let i := struct_arg (eval red in $f) in
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.App _f args =>
          (* mode 1: induct on an argument from the given term *)
          (Array.get args i, i)
      | _ =>
          (* mode 2: find f applied in the goal and induct on its argument *)
          find_applied (Some (f, i))
      end
  | None =>
      (* mode 3: find the first suitable function and argument in the goal *)
      find_applied None
  end.

Ltac2 autoinduct0 (f: constr option) : unit :=
  let (arg, _i) := autofind_applied f in
  induction $arg.
(*
Ltac2 autofix0 (name : ident) (f: constr option) : unit :=
let (arg, i) := autofind_applied f in
Std.fix_ name i;
destruct $arg. *)

Ltac2 Notation "autoinduct" "on" f(constr) := (autoinduct0 (Some f)).

Ltac2 Notation "autoinduct" := (autoinduct0 None).
End Autoinduct.

Ltac2 is_none_or_equal (equal : 'a -> 'a -> bool) (f : 'a) (g : 'a option) :=
  match g with
  | None => true
  | Some g' => equal f g'
  end.

Ltac2 printf_fn_args (fn : string) (args : message list) :=
  Message.print (Message.hvbox 2 (pr_list_with_sep (Message.break 1 0) (Message.hovbox 2) (Message.of_string fn :: args))).

Ltac2 with_closed_prefix (f : constr -> constr) (c : constr) :=
  if Constr.Unsafe.is_closed c
  then f c
  else
    let (h, args) := Constr.decompose_app_list_nocast c in
    if Constr.Unsafe.is_closed h
    then
      let (args_closed, args_open) := List.take_drop_while Constr.Unsafe.is_closed args in
      let c := Constr.mkApp_list h args_closed in
      let c := f c in
      let c := Constr.mkApp_list c args_open in
      c
    else
      c.

(** Find the last hypothesis whose type contains c *)
Ltac2 find_last_hyp_containing (c : constr) : ident option :=
  match! goal with
  | [ h : context[?v] |- _ ] => if Constr.equal v c then Some h else Control.zero Match_failure
  | [ |- _ ] => None
  end.

(** Helper: build [forall x1...xn, c x1...xn = c' x1...xn] as a preterm,
  then convert to constr at the end. Takes the type upfront. *)
Ltac2 rec build_eq_ty_aux (c_partial : preterm) (c'_partial : preterm) (ty : constr) : constr :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod b body =>
      let arg_ty := Constr.Binder.type b in
      let arg_name := Fresh.in_goal (Option.default @x (Constr.Binder.name b)) in
      Constr.in_context_prod arg_name arg_ty (fun () =>
        let x := Control.hyp arg_name in
        let c_app := preterm:($preterm:c_partial $x) in
        let c'_app := preterm:($preterm:c'_partial $x) in
        let body := Constr.Unsafe.substnl [x] 0 body in
        let inner := build_eq_ty_aux c_app c'_app body in
        eexact ($inner)
      )
  | _ =>
      '(@eq $ty $preterm:c_partial $preterm:c'_partial)
  end.

Ltac2 build_eq_ty (c : constr) (c' : constr) : constr :=
  let ty := Constr.type c in
  build_eq_ty_aux (preterm:($c)) (preterm:($c')) ty.

Ltac2 set_evars () :=
  let evs := Control.goal_evars () in
  List.map (fun ev =>
    let nm := Fresh.in_goal @__case_ev in
    set ($nm := $ev);
    nm
  ) evs.

Ltac2 rec get_unfold_list (c : constr) :=
  let (h, _args) := Constr.decompose_app_nocast c in
  match Constr.Unsafe.kind_nocast h with
  | Constr.Unsafe.Constant cst _ =>
      Std.ConstRef cst ::
        (match Std.progress_unfold_constant h with
        | Some c' => get_unfold_list c'
        | None => []
        end)
  | Constr.Unsafe.Lambda _ body => get_unfold_list body
  | Constr.Unsafe.Prod _ body => get_unfold_list body
  | _ => []
  end.

(** [fix_to_ind c] converts a fixpoint-defined constant [c] into an equivalent
  function [c'] defined via the induction principle, together with a proof that
  [forall x1 ... xn, c x1 ... xn = c' x1 ... xn].

  ** Algorithm:

  1. **Validation**: Verify [c] is a constant and its δ-expansion is a [fix]
     under zero or more lambdas.

  2. **Goal Construction**: Build [forall x1...xn, c x1...xn = ?c' x1...xn]
     using preterms for efficiency.

  3. **Evar Instantiation**: Use [in_evar_constr] to run [move], [revert_until],
     and [induction] in the [c'] evar first, instantiating it with the
     induction principle.

  4. **Set Evars**: Set any evars present in the goal to local definitions.

  5. **Main Induction**: Perform the same operations in the main goal.

  6. **Branch Resolution**: For each case, reduce and rewrite to close.
*)
Ltac2 fix_to_ind_funext (c : constr) : constr * constr :=
  (* Validate c is a constant *)
  let c_ref :=
    match Reference.of_constr_opt c with
    | Some (Std.ConstRef _ as r) => r
    | _ => throw "fix_to_ind: expected a constant, got %t" c
    end in

  (* Validate the body is a fix under lambdas *)
  let c_unfolded :=
    match Std.progress_unfold_constant c with
    | Some c' => c'
    | None => throw "fix_to_ind: constant %t has no body (opaque?)" c
    end in
  let c_body_head := Constr.Unsafe.head_under_lambda c_unfolded in
  (if Constr.is_fix c_body_head
  then ()
  else throw "fix_to_ind: body of %t is not a fixpoint (got %t)" c c_body_head);

  (* Build equality type *)
  let c_ty := Constr.type c in
  let c'_evar := '(_ :> $c_ty) in
  (* let eq_ty := build_eq_ty c c'_evar in *)
  let eq_ty := '(@eq $c_ty $c $c'_evar) in
  let struct_idx := struct_arg c_unfolded in

  let eq_proof := '(ltac2:(
    try_clear_all_hyps ();

    do struct_idx (apply functional_extensionality_dep; intro);
    apply functional_extensionality_dep;
    let arg_id := Fresh.in_goal @x in
    intro $arg_id;

    (* intros; *)

    (* Do move/revert/induction in c'_evar first *)
    Control.in_evar_constr c'_evar (fun () =>
      do struct_idx intro;
      let arg_id := Fresh.in_goal @x in
      intro $arg_id;
      move $arg_id at top;
      revert_until arg_id;
      let arg := Control.hyp arg_id in
      induction $arg;
      Control.enter (fun () => Std.revert (List.map (fun (n, _, _) => n) (Control.hyps ())))
    );
    cbv beta;

    (* Get head of c'_evar after induction (the rect) *)
    let rhs := lazy_match! goal with | [ |- @eq ?_ty ?_lhs ?rhs ] => rhs | [ |- ?g ] => throw "fix_to_ind: goal is not an equality: %t" g end in
    let (c'_head, c'_args) := Constr.decompose_app_list rhs in
    let c'_head_refs := get_unfold_list c'_head in
    (match c'_head_refs with
    | Std.ConstRef _ :: _ => ()
    | _ => throw "fix_to_ind: c'_head is not a constant: %t" c'_head
    end);

    (* Set evars that appeared from induction in the evar *)
    let set_names :=
      List.filter_map
        (fun arg =>
          if Constr.has_evar arg then
            let nm := Fresh.in_goal @__case_ev in
            set ($nm := $arg);
            Some nm
          else
            None
        ) c'_args in

    (* Now do move/revert/induction in main goal *)
    move $arg_id at top;
    List.iter (fun n => move $n at top) set_names;
    revert_until arg_id;
    let main_arg := Control.hyp arg_id in
    induction $main_arg;

    (* Process each subgoal *)
    Control.enter (fun () =>
      intros;

      (* cbn c *)
      cbn [$c_ref];

      (* cbn c' head (the induction principle) *)
      let (s, cl) := strategy_clause:([id]) in
      let s := { s with Std.rConst := c'_head_refs } in
      Std.cbn s cl;

      (* Use change to unfold set-evar at head of RHS *)
      (lazy_match! goal with
      | [ |- @eq ?ty ?lhs ?rhs ] =>
          let (rhs_head, rhs_args) := Constr.decompose_app rhs in
          match Constr.Unsafe.kind rhs_head with
          | Constr.Unsafe.Var id =>
              if List.mem Ident.equal id set_names then
                match List.find_opt (fun (h, _, _) => Ident.equal h id) (Control.hyps ()) with
                | Some (_, Some body, _) =>
                    let new_rhs := Constr.mkApp body rhs_args in
                    change (@eq $ty $lhs $new_rhs)
                | _ => throw "fix_to_ind: no hypothesis found for variable %I" id
                end
              else ()
          | _ => throw "fix_to_ind: rhs_head is not a variable: %t" rhs_head
          end
      | [ |- ?g ] => throw "fix_to_ind: goal is not an equality: %t" g
      end);
      cbv beta;

      (* Clearbody all set-evars *)
      first
        [ Std.clearbody set_names
        | List.iter (fun nm => try (Std.clearbody [nm])) set_names ];

      (* Find IH: last hyp containing c, try rewrite <- *)
      let set_names_ev := set_evars () in
      (match find_last_hyp_containing c with
      | Some ih_id =>
          let ih := Control.hyp ih_id in
          repeat (
            let ih' := specialize_with_evars ih in
            rewrite <- $ih';
            let lhs := match! Constr.type ih' with | @eq ?_ty ?lhs ?_rhs => lhs end in
            generalize $lhs; intro
          );
          try (clear $ih_id; reflexivity)
      | None => try reflexivity
      end);
      Std.subst set_names_ev;
      Control.enter (fun () =>
        lazy_match! goal with
        | [ |- @eq ?_ty ?_lhs ?rhs ] =>
            let (rhs_head, _rhs_args) := Constr.decompose_app rhs in
            if Constr.is_evar rhs_head then
              Control.in_evar_constr rhs_head (fun () => intros)
            else ()
        | [ |- _ ] => ()
        end);
      cbv beta;

      try (eexact eq_refl)
    );

    (* Check for remaining goals *)
    let remaining := Control.numgoals () in
    if Int.gt remaining 0 then (
      Control.enter (fun () => Control.print_context_and_goal ());
      throw "fix_to_ind: %i goals remain unsolved" remaining
    ) else ()
  ) : $eq_ty) in

  let c' := evar_normalize c'_evar in
  (if Constr.has_evar c' then
    throw "fix_to_ind: c' still contains evars: %t" c'
  else ());

  (c', eq_proof).

Ltac2 fix_to_ind (c : constr) : constr * constr :=
  let (c', _pf_funext) := fix_to_ind_funext c in
  let c_ref :=
    match Reference.of_constr_opt c with
    | Some (Std.ConstRef _ as r) => r
    | _ => throw "fix_to_ind: expected a constant, got %t" c
    end in

  (* Build equality type *)
  (* let c_ty := Constr.type c in *)
  let eq_ty := build_eq_ty c c' in

  let (c'_head, _c'_args) := Constr.decompose_app_list c' in
  let c'_head_refs := get_unfold_list c'_head in
  (match c'_head_refs with
  | Std.ConstRef _ :: _ => ()
  | _ => throw "fix_to_ind: c'_head is not a constant: %t" c'_head
  end);

  let eq_proof := '(ltac2:(
    try_clear_all_hyps ();
    intros;
    let (arg, _i) := Autoinduct.autofind_applied (Some c) in
    let id :=
      match Constr.Unsafe.kind arg with
      | Constr.Unsafe.Var id => id
      | _ => throw "fix_to_ind: arg is not a variable: %t" arg
      end in

    let arg := Control.hyp id in
    move $id at top;
    revert_until id;
    induction $arg;

    cbv beta;

    Control.enter (fun () =>
      (* cbn c *)
      cbn [$c_ref];

      (* cbn c' head (the induction principle) *)
      let (s, cl) := strategy_clause:([id]) in
      let s := { s with Std.rConst := c'_head_refs } in
      Std.cbn s cl;

      try reflexivity;

      repeat (match! goal with
      | [ h : _ |- _ ] => let h := Control.hyp h in rewrite <- $h; try reflexivity
      end))
  ) :> $eq_ty) in
  (c', eq_proof).

Module Import Tags.
  Ltac2 Type 'a t := { open : message ; close_success : 'a -> message ; close_failure : exn -> exninfo -> message ; reenter : exn -> exninfo -> message }.
End Tags.

Ltac2 wrap_tags_gen (debug : bool) (tags : unit -> 'a Tags.t) (f : unit -> 'a) :=
  if debug then
    let tags := tags () in
    Message.print (tags.(open));
    let rec wrap_tags f :=
      match Control.case_bt f with
      | Val_bt (v, alt) =>
          Message.print (tags.(close_success) v);
          Control.plus_bt
            (fun () => v)
            (fun err info =>
              Message.print (tags.(reenter) err info);
              wrap_tags (fun () => alt err info))
      | Err_bt err info =>
          Message.print (tags.(close_failure) err info);
          Control.zero_bt err info
      end in
    wrap_tags f
  else
    f ().

Ltac2 wrap_tags_msg (debug : bool) (tag : unit -> message) (f : unit -> 'a) :=
  wrap_tags_gen debug
    (fun () =>
      let open := fprintf "<%a>" (fun () a => a) (tag ()) in
      let close_success := fprintf "{success}</%a>" (fun () a => a) (tag ()) in
      let close_failure := fprintf "{failure}</%a>" (fun () a => a) (tag ()) in
      let reenter := fprintf "<%a>{reenter}" (fun () a => a) (tag ()) in
      let close_success _ := close_success in
      let close_failure _ _ := close_failure in
      let reenter _ _ := reenter in
      { open ; close_success ; close_failure ; reenter } )
    f.

Ltac2 wrap_tags (debug : bool) (tag : string) (f : unit -> 'a) :=
  wrap_tags_msg debug (fun () => fprintf "%s" tag) f.
Ltac2 wrap_tags_printf_fn_args (debug : bool) (fn : string) (args : unit -> message list) (f : unit -> 'a) :=
  wrap_tags debug fn (fun () => (if debug then printf_fn_args fn (args ()) else ()); f ()).
Ltac2 Notation "wrap_tags_printf_fn_args" debug(tactic(0)) fn(tactic(0)) args(thunk(tactic(0))) f(thunk(tactic)) := wrap_tags_printf_fn_args debug fn args f.
(* Ltac2 Notation "wrap_tags" debug(bool) f(thunk(tactic)) tag(thunk(tactic(0))) *)

(* Run typechecking to enforce universe constraints *)
Ltac2 wrap_check tac :=
  Control.refine (fun () =>
    let g := Control.goal () in
    '(ltac2:(tac ()) :> $g)).


Ltac post_tc_hint_hook := idtac.
Ltac pre_tc_hint_hook := idtac.

Ltac2 mutable post_tc_hint_hook () := ltac1:(post_tc_hint_hook).
Ltac2 mutable pre_tc_hint_hook () := ltac1:(pre_tc_hint_hook).

Ltac2 tc_hint_for (fatal : bool) (warn : bool) (key : constr) (lem : constr) (goal_lhs : constr) :=
  let (goal_lhs, _) := Constr.decompose_app goal_lhs in
  intros;
  let tac () := first [unshelve (eapply $lem) |pre_tc_hint_hook () ; unshelve (eapply $lem)]; post_tc_hint_hook () in
  if Constr.equal_nounivs goal_lhs key then
    if fatal then
      Control.throw_on_error tac
    else if warn then
      match Control.case_bt tac with
      | Val_bt (v, _k) => v
      | Err_bt err info => printf "Warning: %a\n" (fun () => Message.of_exn_pretty) err; Control.zero_bt err info
      end
    else
      tac ()
  else
    Control.zero Match_failure.

Ltac tc_hint_for key lem goal_lhs :=
  let tac := ltac2:(key lem goal_lhs |-
  tc_hint_for true false (Option.get (Ltac1.to_constr key)) (Option.get (Ltac1.to_constr lem)) (Option.get (Ltac1.to_constr goal_lhs))) in
  tac key lem goal_lhs.

Ltac tc_hint_for_warn key lem goal_lhs :=
  let tac := ltac2:(key lem goal_lhs |- tc_hint_for false true (Option.get (Ltac1.to_constr key)) (Option.get (Ltac1.to_constr lem)) (Option.get (Ltac1.to_constr goal_lhs))) in
  tac key lem goal_lhs.

Ltac tc_hint_for_nofatal key lem goal_lhs :=
  let tac := ltac2:(key lem goal_lhs |- tc_hint_for false false (Option.get (Ltac1.to_constr key)) (Option.get (Ltac1.to_constr lem)) (Option.get (Ltac1.to_constr goal_lhs))) in
  tac key lem goal_lhs.
