Add LoadPath "..".
Require Import Homotopy.

(** The 2-sphere as a higher inductive type (with all computation rules)

Inductive sphere : Type :=
  | pt0 : sphere
  | pt1 : sphere
  | lp0 : pt0 ~~> pt1
  | lp1 : pt0 ~~> pt1
  | sf0 : lp0 ~~> lp1
  | sf1 : lp0 ~~> lp1.

*)

(* Introduction rules *)
Axiom sphere : Type.
Axiom pt0 : sphere.
Axiom pt1 : sphere.
Axiom lp0 : pt0 ~~> pt1.
Axiom lp1 : pt0 ~~> pt1.
Axiom sf0 : lp0 ~~> lp1.
Axiom sf1 : lp0 ~~> lp1.

(* Dependent elimination rule *)
Axiom sphere_rect :
   forall P : sphere -> Type,
   forall x0 : P pt0,
   forall x1 : P pt1,
   forall p0 : transport (P := P) lp0 x0 ~~> x1,
   forall p1 : transport (P := P) lp1 x0 ~~> x1,
   forall s0 : transport (P := fun a => transport (P := P) a x0 ~~> x1) sf0 p0 ~~> p1,
   forall s1 : transport (P := fun a => transport (P := P) a x0 ~~> x1) sf1 p0 ~~> p1,
   (forall x : sphere, P x).

(* Dependent computation rules for points *)
Axiom compute_pt0 : forall P x0 x1 p0 p1 s0 s1, (sphere_rect P x0 x1 p0 p1 s0 s1) pt0 ~~> x0.
Axiom compute_pt1 : forall P x0 x1 p0 p1 s0 s1, (sphere_rect P x0 x1 p0 p1 s0 s1) pt1 ~~> x1.

(* Dependent computation rules for paths *)
Axiom compute_lp0 : forall P x0 x1 p0 p1 s0 s1,
  map_dep (P := P) (sphere_rect P x0 x1 p0 p1 s0 s1) lp0 ~~>
    map (transport (P := P) lp0) (compute_pt0 P x0 x1 p0 p1 s0 s1)
    @ p0
    @ !(compute_pt1 P x0 x1 p0 p1 s0 s1).
Axiom compute_lp1 : forall P x0 x1 p0 p1 s0 s1,
  map_dep (P := P) (sphere_rect P x0 x1 p0 p1 s0 s1) lp1 ~~>
    map (transport (P := P) lp1) (compute_pt0 P x0 x1 p0 p1 s0 s1)
    @ p1
    @ !(compute_pt1 P x0 x1 p0 p1 s0 s1).

(* Former computation rules for paths, for some reason I need them in the computation rules for
   2-paths*)
Lemma compute_lp0' : forall P x0 x1 p0 p1 s0 s1,
  !map (transport (P := P) lp0) (compute_pt0 P x0 x1 p0 p1 s0 s1)
  @ map_dep (P := P) (sphere_rect P x0 x1 p0 p1 s0 s1) lp0
  @ compute_pt1 P x0 x1 p0 p1 s0 s1 ~~>
    p0.
Proof.
  intros.
  moveright_onright.
  moveright_onleft.
  associate_left.
  apply compute_lp0.
Defined.

Lemma compute_lp1' : forall P x0 x1 p0 p1 s0 s1,
  !map (transport (P := P) lp1) (compute_pt0 P x0 x1 p0 p1 s0 s1)
  @ map_dep (P := P) (sphere_rect P x0 x1 p0 p1 s0 s1) lp1
  @ compute_pt1 P x0 x1 p0 p1 s0 s1 ~~>
    p1.
Proof.
  intros.
  moveright_onright.
  moveright_onleft.
  associate_left.
  apply compute_lp1.
Defined.

(* Dependent computation rules for 2-paths *)
Axiom compute_sf0 : forall P x0 x1 p0 p1 s0 s1,
  map_dep (P := fun a => transport (P := P) a x0 ~~> x1)
    (fun a => !map (transport (P := P) a) (compute_pt0 P x0 x1 p0 p1 s0 s1)
              @ map_dep (P := P) (sphere_rect P x0 x1 p0 p1 s0 s1) a
              @ compute_pt1 P x0 x1 p0 p1 s0 s1) sf0
  ~~> map (transport (P := fun a => transport (P := P) a x0 ~~> x1) sf0)
           (compute_lp0' P x0 x1 p0 p1 s0 s1)
      @ s0
      @ !compute_lp1' P x0 x1 p0 p1 s0 s1.

Axiom compute_sf1 : forall P x0 x1 p0 p1 s0 s1,
  map_dep (P := fun a => transport (P := P) a x0 ~~> x1)
    (fun a => !map (transport (P := P) a) (compute_pt0 P x0 x1 p0 p1 s0 s1)
              @ map_dep (P := P) (sphere_rect P x0 x1 p0 p1 s0 s1) a
              @ compute_pt1 P x0 x1 p0 p1 s0 s1) sf1
  ~~> map (transport (P := fun a => transport (P := P) a x0 ~~> x1) sf1)
           (compute_lp0' P x0 x1 p0 p1 s0 s1)
      @ s1
      @ !compute_lp1' P x0 x1 p0 p1 s0 s1.

(* Exercise: Prove that [sphere] is equivalent to [suspension (suspension (suspension empty))] *)
