Require Import UnivalentParametricity.theories.UR
  UnivalentParametricity.theories.StdLib.FP.
From mathcomp Require Import algebra.
Require Import UnivalentParametricity.theories.Basics UnivalentParametricity.theories.StdLib.UR Record.


Module Type Interface49 (Import args : Args).

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.


Parameter imported_Corelib__ssr__ssrbool__pred : import_of (@Corelib.ssr.ssrbool.pred).
Parameter Corelib__ssr__ssrbool__pred_iso : iso_statement (@Corelib.ssr.ssrbool.pred) imported_Corelib__ssr__ssrbool__pred.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrbool.pred) [Corelib__ssr__ssrbool__pred_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrbool.pred) [Corelib__ssr__ssrbool__pred_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.ssr.ssrbool.pred)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 10 => progress (unfold mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD_ : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD__iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD_.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD_ : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD__iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD_.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Fail Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__Exports__GRingD_SubLalgebraD_classD_D_toD_D_GRingD_SubRingD_class : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.Exports.GRing_SubLalgebra_class__to__GRing_SubRing_class).

End Interface49.


Module Type Interface50 (Import args : Args).

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

(* Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.GRing_Lalgebra__to__GRing_Ring) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__joinD_GRingD_LalgebraD_betweenD_GRingD_LSemiModuleD_andD_GRingD_Ring. *)
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Lalgebra__Exports__GRingD_LalgebraD_D_toD_D_GRingD_Ring_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Lalgebra.Exports.join_GRing_Lalgebra_between_GRing_LSemiModule_and_GRing_Ring)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.


Parameter imported_Corelib__ssr__ssrbool__pred : import_of (@Corelib.ssr.ssrbool.pred).
Parameter Corelib__ssr__ssrbool__pred_iso : iso_statement (@Corelib.ssr.ssrbool.pred) imported_Corelib__ssr__ssrbool__pred.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrbool.pred) [Corelib__ssr__ssrbool__pred_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrbool.pred) [Corelib__ssr__ssrbool__pred_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.ssr.ssrbool.pred)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Ring__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 10 => progress (unfold mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Ring.sort) : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD_ : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD__iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD_.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.axioms_)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD_ : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD__iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD_.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubRing__axiomsD__iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubRing.axioms_)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__Exports__GRingD_SubLalgebraD_classD_D_toD_D_GRingD_SubRingD_class : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.Exports.GRing_SubLalgebra_class__to__GRing_SubRing_class).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__Exports__GRingD_SubLalgebraD_classD_D_toD_D_GRingD_SubRingD_class_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.Exports.GRing_SubLalgebra_class__to__GRing_SubRing_class) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__Exports__GRingD_SubLalgebraD_classD_D_toD_D_GRingD_SubRingD_class.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.Exports.GRing_SubLalgebra_class__to__GRing_SubRing_class) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__Exports__GRingD_SubLalgebraD_classD_D_toD_D_GRingD_SubRingD_class_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.Exports.GRing_SubLalgebra_class__to__GRing_SubRing_class) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__SubLalgebra__Exports__GRingD_SubLalgebraD_classD_D_toD_D_GRingD_SubRingD_class_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.SubLalgebra.Exports.GRing_SubLalgebra_class__to__GRing_SubRing_class)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

End Interface50.
Module Type Interface54 (Import args : Args).

Parameter imported_elpi__apps__derive__derive__param2__paramD_db : import_of (@elpi.apps.derive.derive.param2.param_db).
Parameter elpi__apps__derive__derive__param2__paramD_db_iso : iso_statement (@elpi.apps.derive.derive.param2.param_db) imported_elpi__apps__derive__derive__param2__paramD_db.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@elpi.apps.derive.derive.param2.param_db) [elpi__apps__derive__derive__param2__paramD_db_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@elpi.apps.derive.derive.param2.param_db) [elpi__apps__derive__derive__param2__paramD_db_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@elpi.apps.derive.derive.param2.param_db)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_Corelib__Init__Logic__and : import_of (@Corelib.Init.Logic.and).
Parameter Corelib__Init__Logic__and_iso : iso_statement (@Corelib.Init.Logic.and) imported_Corelib__Init__Logic__and.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.Init.Logic.and) [Corelib__Init__Logic__and_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.Init.Logic.and) [Corelib__Init__Logic__and_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.Init.Logic.and)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__arithmeticD_tactic__Internals__andD_R : import_of (@mathcomp.algebra.arithmetic_tactic.Internals.and_R).
Parameter mathcomp__algebra__arithmeticD_tactic__Internals__andD_R_iso : iso_statement (@mathcomp.algebra.arithmetic_tactic.Internals.and_R) imported_mathcomp__algebra__arithmeticD_tactic__Internals__andD_R.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.arithmetic_tactic.Internals.and_R) [mathcomp__algebra__arithmeticD_tactic__Internals__andD_R_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.arithmetic_tactic.Internals.and_R) [mathcomp__algebra__arithmeticD_tactic__Internals__andD_R_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.arithmetic_tactic.Internals.and_R)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

(* [param_and_R] is generated over an anonymous [Prop -> Prop -> Prop]
   relation, which the importer does not yet support. *)
Parameter imported_mathcomp__algebra__arithmeticD_tactic__Internals__paramD_andD_R : import_of (@mathcomp.algebra.arithmetic_tactic.Internals.param_and_R).

End Interface54.


Module Type Interface55 (Import args : Args).

Parameter imported_Corelib__ssr__ssrfun__morphismD_2 : import_of (@Corelib.ssr.ssrfun.morphism_2).
Parameter Corelib__ssr__ssrfun__morphismD_2_iso : iso_statement (@Corelib.ssr.ssrfun.morphism_2) imported_Corelib__ssr__ssrfun__morphismD_2.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrfun.morphism_2) [Corelib__ssr__ssrfun__morphismD_2_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrfun.morphism_2) [Corelib__ssr__ssrfun__morphismD_2_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.ssr.ssrfun.morphism_2)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type) imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__Additive__type : import_of (@mathcomp.boot.nmodule.Algebra.Additive.type).
Parameter mathcomp__boot__nmodule__Algebra__Additive__type_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.Additive.type) imported_mathcomp__boot__nmodule__Algebra__Additive__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.type) [mathcomp__boot__nmodule__Algebra__Additive__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.type) [mathcomp__boot__nmodule__Algebra__Additive__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.Additive.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__type : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddMagma__type_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type) imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma) imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort) imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort) imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__Additive__sort : import_of (@mathcomp.boot.nmodule.Algebra.Additive.sort).
Parameter mathcomp__boot__nmodule__Algebra__Additive__sort_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.Additive.sort) imported_mathcomp__boot__nmodule__Algebra__Additive__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.sort) [mathcomp__boot__nmodule__Algebra__Additive__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.sort) [mathcomp__boot__nmodule__Algebra__Additive__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.Additive.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__add : import_of (@mathcomp.boot.nmodule.Algebra.add).
Parameter mathcomp__boot__nmodule__Algebra__add_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.add) imported_mathcomp__boot__nmodule__Algebra__add.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.add) [mathcomp__boot__nmodule__Algebra__add_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.add) [mathcomp__boot__nmodule__Algebra__add_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.add)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Fail Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Theory__raddfD : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Theory.raddfD).

End Interface55.

Module Type Interface56 (Import args : Args).

Parameter imported_Corelib__ssr__ssrfun__morphismD_2 : import_of (@Corelib.ssr.ssrfun.morphism_2).
Parameter Corelib__ssr__ssrfun__morphismD_2_iso : iso_statement (@Corelib.ssr.ssrfun.morphism_2) imported_Corelib__ssr__ssrfun__morphismD_2.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrfun.morphism_2) [Corelib__ssr__ssrfun__morphismD_2_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@Corelib.ssr.ssrfun.morphism_2) [Corelib__ssr__ssrfun__morphismD_2_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@Corelib.ssr.ssrfun.morphism_2)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type) imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__Additive__type : import_of (@mathcomp.boot.nmodule.Algebra.Additive.type).
Parameter mathcomp__boot__nmodule__Algebra__Additive__type_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.Additive.type) imported_mathcomp__boot__nmodule__Algebra__Additive__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.type) [mathcomp__boot__nmodule__Algebra__Additive__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.type) [mathcomp__boot__nmodule__Algebra__Additive__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.Additive.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__type : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddMagma__type_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type) imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__type.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__type_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.type)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma) imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.Exports.Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort : import_of (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort).
Parameter mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort) imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddMagma.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Definition mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort) 
  (fun x => imported_mathcomp__boot__nmodule__Algebra__BaseAddMagma__sort (imported_mathcomp__boot__nmodule__Algebra__BaseAddUMagma__Exports__AlgebraD_BaseAddUMagmaD_D_toD_D_AlgebraD_BaseAddMagma x)).
Proof. intros ? ? ?. change (Algebra.BaseAddUMagma.sort x) with 
((Algebra.BaseAddMagma.sort (Algebra_BaseAddUMagma__to__Algebra_BaseAddMagma x))). tc.
Defined.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort) [mathcomp__boot__nmodule__Algebra__BaseAddUMagma__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.BaseAddUMagma.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__Additive__sort : import_of (@mathcomp.boot.nmodule.Algebra.Additive.sort).
Parameter mathcomp__boot__nmodule__Algebra__Additive__sort_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.Additive.sort) imported_mathcomp__boot__nmodule__Algebra__Additive__sort.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.sort) [mathcomp__boot__nmodule__Algebra__Additive__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.Additive.sort) [mathcomp__boot__nmodule__Algebra__Additive__sort_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.Additive.sort)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__boot__nmodule__Algebra__add : import_of (@mathcomp.boot.nmodule.Algebra.add).
Parameter mathcomp__boot__nmodule__Algebra__add_iso : iso_statement (@mathcomp.boot.nmodule.Algebra.add) imported_mathcomp__boot__nmodule__Algebra__add.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.add) [mathcomp__boot__nmodule__Algebra__add_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.boot.nmodule.Algebra.add) [mathcomp__boot__nmodule__Algebra__add_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.boot.nmodule.Algebra.add)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

Parameter imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Theory__raddfD : import_of (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Theory.raddfD).
Parameter mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Theory__raddfD_iso : iso_statement (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Theory.raddfD) imported_mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Theory__raddfD.
#[export] Hint Extern 0 (UR.UR_Type ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Theory.raddfD) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Theory__raddfD_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (UR.pr _ ?goal_lhs _) => tc_hint_for_ur_plain_list (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Theory.raddfD) [mathcomp__algebra__algebraicD_hierarchy__ringsD_modulesD_andD_algebras__GRing__Theory__raddfD_iso] [] goal_lhs : typeclass_instances ur_typeclass_instances.
#[export] Hint Extern 0 (IsoRegisteredFor UR.univalent (@mathcomp.algebra.algebraic_hierarchy.rings_modules_and_algebras.GRing.Theory.raddfD)) => exact Build_IsoRegisteredFor : typeclass_instances ur_typeclass_instances.

End Interface56.