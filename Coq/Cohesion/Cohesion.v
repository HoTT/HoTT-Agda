Add LoadPath "..".

Require Import Homotopy Cohesive_Topos.

Parameter BG : Type.
(* BG is inhabited (to be replaced by a connectedness hypothesis later). *)
Axiom pt : BG.

(* Here is the homotopy fiber of [map_from_flat BG] over [pt] *)
Definition flat_dR_BG : Type := hfiber (map_from_flat BG) pt.

(* This lemma says that if [X] and [Y] are equivalent, then [X] is discrete iff [Y] is discrete.
   This is a simple use of univalence (induction along equivalences) *)
Lemma discrete_preserved_by_equiv : forall X Y, forall e : X ≃> Y, is_discrete Y -> is_discrete X.
Proof.
  apply (equiv_induction (fun X Y e => is_discrete Y -> is_discrete X)).
  trivial.
Defined.

(* The terminal object is discrete *)
Lemma is_discrete_unit : is_discrete unit.
Proof.
  apply discrete_preserved_by_equiv with (Y := pi unit).
  exact (tpair _ pi_preserve_terminal).
  apply pi_is_discrete.
Defined.

(* The space of points of [flat BG] is equivalent to the space of points of [BG], this is just a
   consequence of the fact tha [flat] is a coreflection and that the point is discrete.
   (Is this expected? Is seems strange) *)
Definition eq_points_flatBG_BG : (unit -> flat BG) ≃> (unit -> BG) :=
  tpair _ (flat_is_coreflection BG unit is_discrete_unit).

(* Therefore the point of [BG] can be transformed into a point of [flat BG], by first transforming
   [pt] into a function of type [unit -> BG] and then turning back the function of type
   [unit -> flat BG] into a point of [flat BG] *)
Definition pt_fun      : unit -> BG := fun x => match x with tt => pt end.
Definition pt_flat_fun : unit -> flat BG := eq_points_flatBG_BG⁻¹ pt_fun.
Definition pt_flat     : flat BG := pt_flat_fun tt.

(* And applying [map_from_flat BG] to the point of [flat BG] obtained will give [pt] back *)
Lemma pt_compatible_fun : compose (map_from_flat BG) pt_flat_fun ~~> pt_fun.
Proof.
  path_via (eq_points_flatBG_BG pt_flat_fun).
  apply inverse_is_section.
Defined.

Definition pt_compatible : map_from_flat BG pt_flat ~~> pt := map (fun p => p tt) pt_compatible_fun.


Definition G : Type := pt ~~> pt.

(* Given a path [l : pt ~~> pt] in [BG], we have to find a point [x] in [flat BG] together with a
   path from [map_from_flat BG x] (of type [BG]) to [pt]. We will take [x := pt_flat] and the path
   will be [l], pre-composed with the previous proof that there is a path from
   [map_from_flat BG pt_flat] to [pt] *)
Definition theta : G -> flat_dR_BG :=
  fun l => tpair pt_flat (pt_compatible @ l).