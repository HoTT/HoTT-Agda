Add LoadPath "..".
Add LoadPath "../Limits".

Require Import Homotopy Cohesive_Topos.
Require Import Pullbacks.

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
   consequence of the fact that [flat] is a coreflection and that the point is discrete.
   (Is this expected? It seems strange) *)
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
Definition theta1 : G -> flat_dR_BG :=
  fun l => tpair pt_flat (pt_compatible @ l).


(* Another definition of [theta] using the Pullbacks.v file. The terms [map_to_diagram] and [factor]
   are defined there.
   We first define the following homotopy commutative square :

   G ----------> *
   |             |
   v             |
   * --__        |
   |     --__    |
   v         --> v
  ♭BG ---------> BG

  by composing the homotopy pullback square defining [G] and the homotopy commutative triangle below.
*)
Definition maptodiag : map_to_diagram (flat BG) unit BG (map_from_flat BG) pt_fun G.
Proof.
  exists (compose pt_flat_fun (fun _ => tt)).
  exists (fun _ => tt).
  exact (fun l => pt_compatible @ l).
Defined.

(* Next, with the [factor] function from the Pullbacks.v file, we can transform this homotopy
   commutative square into a map from [G] to the homotopy pullback of [♭BG -> BG <- *].
   And then we map by hand this homotopy pullback into the homotopy fiber of [flat_to_map BG] (of
   course the two are supposed to be canonically identified, but it’s cumbersome to write it as an
   equivalence here) *)
Definition theta2 : G -> flat_dR_BG.
Proof.
  set (h := factor (flat BG) unit BG (map_from_flat BG) pt_fun G maptodiag).
  unfold hopullback_type in h.
  unfold flat_dR_BG, hfiber.
  intro g.
  destruct (h g) as [x [t p]].
  destruct t.
  exact (tpair x p).
Defined.


Lemma thetas_are_the_same : theta1 ~~> theta2.
Proof.
  apply idpath. (* This means that [theta1] and [theta2] are even *definitionally* equal *)
Defined.