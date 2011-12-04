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

Definition dumm (A : Type) : (unit -> A) ≃> A.
Proof.
  exists (fun f => f tt).
  apply hequiv_is_equiv with (g := fun x => (fun t => x)).
    auto.
  intro x.
  apply funext; intro t.
  destruct t.
  apply idpath.
Defined.

Definition everything_is_its_flat (A : Type) : A ≃> flat A.
Proof.
  apply (equiv_compose (B := (unit -> A))).
    apply equiv_inverse.
    apply dumm.
  apply (equiv_compose (B := (unit -> flat A))).
    apply equiv_inverse.
    exact (tpair _ (flat_is_coreflection A unit is_discrete_unit)).
  apply dumm.
Defined.

Lemma everything_is_discrete (A : Type) : is_discrete A.
Proof.
  apply discrete_preserved_by_equiv with (Y := flat A).
  apply everything_is_its_flat.
  apply flat_is_discrete.
Defined.

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

Definition eq_points_flatBG_BG_ (BG : Type) : (unit -> flat BG) ≃> (unit -> BG) :=
  tpair _ (flat_is_coreflection BG unit is_discrete_unit).

Definition flat_pointed_fun (BG : Type) (x : unit -> BG) : unit -> flat BG :=
  (eq_points_flatBG_BG_ BG)⁻¹ x.

Lemma flat_pointed (BG : Type) (x : BG) : flat BG.
Proof.
  generalize tt.
  apply flat_pointed_fun.
  exact (fun t => match t with tt => x end).
Defined.

Lemma pointed_compatible_fun (BG : Type) (x : unit -> BG) :
  compose (map_from_flat BG) (flat_pointed_fun BG x) ~~> x.
Proof.
  path_via (eq_points_flatBG_BG_ BG (flat_pointed_fun BG x)).
  apply inverse_is_section.
Defined.

Lemma pointed_compatible (BG : Type) (x : BG) : map_from_flat BG (flat_pointed BG x) ~~> x.
Proof.
  exact (map (fun p => p tt) (pointed_compatible_fun BG (fun t => match t with tt => x end))).
Defined.

Definition loop (A : Type) (a : A) := a ~~> a.

Lemma hom_commutes_loopspace (A B : Type) (b : B) :
  loop (A -> B) (fun _ : A => b) -> (A -> loop B b).
Proof.
  intro p.
  apply happly.
  exact p.
Defined.

Lemma hom_commutes_loopspace2 (A B : Type) (b : B) :
  (A -> loop B b) -> loop (A -> B) (fun _ : A => b).
  intro f.
  apply funext; intro t.
  exact (f t).
Defined.

Print map.

Lemma antimap {A B : Type} {x y : A} (g : A ≃> B) : (g x ~~> g y) -> (x ~~> y).
  intro p.
  path_via (g⁻¹ (g x)).
    apply opposite, inverse_is_retraction.
  path_via' (g⁻¹ (g y)).
    apply map.
    exact p.
  apply inverse_is_retraction.
Defined.

Lemma antimap_loop {A B : Type} {x : A} (g : A ≃> B) : loop B (g x) -> loop A x.
Proof.
  apply antimap.
Defined.  

Lemma map_loop {A B : Type} {x : A} (g : A ≃> B) : loop A x -> loop B (g x).
Proof.
  apply map.
Defined.  

Lemma loop_conj {A : Type} (a b : A) : a ~~> b -> loop A a -> loop A b.
Proof.
  path_induction.
Defined.

Lemma flat_commutes_loopspace (BG : Type) (x : BG) :
  flat (loop BG x) ->  loop (flat BG) (flat_pointed BG x).
Proof.
  apply hom_commutes_loopspace.
  set (f := tpair _ (flat_is_coreflection BG (flat (loop BG x)) (flat_is_discrete _)) : _ ≃> _).
  apply antimap_loop with (g := f).
  apply loop_conj with (a := fun _ : flat (loop BG x) => x).
    apply funext; intro t.
    simpl.
    unfold compose; simpl.
    apply opposite, pointed_compatible.
  apply hom_commutes_loopspace2.
  apply map_from_flat.
Defined.

(*Axiom pi_preserves_loopspace : forall (BG : Type) (x : BG), is_equiv (map_to_pi (loop BG x)).*)

Definition loop_disc (A : Type) (a : A) := flat (loop A a).
Definition loop_disc_discrete (A : Type) (a : A) : is_discrete (loop_disc A a) := flat_is_discrete _.
Definition loopspace_commutes_injection (BG : Type) (x : BG) :
  loop_disc (flat BG) (flat_pointed BG x) -> loop (flat BG) (flat_pointed BG x) := map_from_flat _.


(*
Definition loop_disc (A : Type) (a : A) := pi (loop A a).

Proof.
  unfold loop_disc.
  apply map_to_pi.
Defined.
*)
Lemma flat_commutes_loopspace2 (BG : Type) (x : BG) :
  loop_disc (flat BG) (flat_pointed BG x) -> flat (loop BG x).
Proof.
  apply (flat_is_coreflection).
    apply loop_disc_discrete.
  apply hom_commutes_loopspace.
  set (f := tpair _ (flat_is_coreflection BG (loop_disc (flat BG) (flat_pointed BG x)) (loop_disc_discrete _ _)) : _ ≃> _).
  apply loop_conj with (a := (fun _ : loop_disc (flat BG) (flat_pointed BG x) => map_from_flat BG (flat_pointed BG x))).
    apply funext; intro t.
    apply pointed_compatible.
  refine (map_loop f _).
  apply hom_commutes_loopspace2.
  apply loopspace_commutes_injection.
Defined.

Lemma commutes (BG : Type) (x : BG) :
  loop (flat BG) (flat_pointed BG x) -> loop_disc (flat BG) (flat_pointed BG x).
Proof.
  Check pi_is_reflection.
  refine ((tpair _ (pi_is_reflection _ (loop_disc (flat BG) (flat_pointed BG x)) _) : _ ≃> _) _).
    apply flat_is_discrete.
  unfold loop_disc.
  set (f := tpair _ (flat_is_coreflection (loop (flat BG) (flat_pointed BG x)) (pi (loop (flat BG) (flat_pointed BG x))) (pi_is_discrete _)) : _ ≃> _).
  refine (f⁻¹ _).
  apply hom_commutes_loopspace.
  set (g := tpair _ (pi_is_reflection (loop (flat BG) (flat_pointed BG x)) (flat BG) (flat_is_discrete _)) : _ ≃> _).
  apply (antimap g).
  apply idpath.
Defined.

Lemma theta_commutes_loopspace2 (BG : Type) (x : BG) :
  loop (flat BG) (flat_pointed BG x) -> flat (loop BG x).
Proof.
  apply (flat_is_coreflection).
    admit.
(*    apply discrete_preserved_by_equiv with (Y := pi (loop (flat BG) (flat_pointed BG x))).
    apply (tpair _ (pi_preserves_loopspace (flat BG) (flat_pointed BG x)) : _ ≃> _).
    apply pi_is_discrete.*)
  apply hom_commutes_loopspace.
  apply loop_conj with (a := (fun _ : loop (flat BG) (flat_pointed BG x) => map_from_flat BG (flat_pointed BG x))).
    apply funext; intro t.
    apply pointed_compatible.
  apply hom_commutes_loopspace2.
  exact (map (map_from_flat BG)).
Defined.

Print map_to_diagram.
Definition is_exact (A B C : Type) (c : C) (f : A -> B) (g : B -> C)
  (d : forall a : A, c ~~> g (f a)) :=
  is_homotopy_pullback unit B C (fun _ => c) g A (tpair (fun x => tt) (tpair f d)).


Lemma is_exact_hopullback (A B : Type) (b : B) (f : A -> B) :
  is_exact (hopullback_type unit A B (fun _ => b) f) A B b
  (fun x => pr1 (pr2 x)) f (fun x => pr2 (pr2 x)).
Proof.
  unfold is_exact.
  Print hopullback_map.
  refine (transport (P := fun x => is_homotopy_pullback unit A B (fun _ : unit => b) f
     (hopullback_type unit A B (fun _ : unit => b) f) x) _ _).
  2:apply homotopy_pullbacks.
  unfold hopullback_map.
  assert (pr1 ~~> (fun _ : hopullback_type unit A B (fun _ => b) f => tt)).
    apply funext; intros [[] t]; auto.
  apply total_path with (p := X).
  simpl.
  apply trans_trivial.
Defined.


Lemma is_exact_hfiber (A B : Type) (b : B) (f : A -> B) : is_exact (hfiber f b) A B b pr1 f
  (fun a => !pr2 a).
Proof.
  set (is_exact_hopullback A B b f).
  generalize (h