Add LoadPath "..".
Require Import Homotopy.

(** Circle

Inductive circle :=
  | base : circle
  | loop : base ~~> base.
*)

(* Type *)
Axiom circle : Type.

(* Constructors *)
Axiom base : circle.
Axiom loop : base ~~> base.

(* Dependent elimination rule *)
Axiom circle_rect :
  forall (P : circle -> Type) (pt : P base) (lp : transport loop pt ~~> pt), 
    forall x : circle, P x.

(* Dependent computation rules *)
Axiom compute_base : forall P pt lp,
  circle_rect P pt lp base ~~> pt.

Axiom compute_loop : forall P pt lp,
  map_dep (circle_rect P pt lp) loop
  ~~> map (transport loop) (compute_base P pt lp) @ lp @ !compute_base P pt lp.

(* Non-dependent elimination rule *)
Definition circle_rect' :
  forall (B : Type) (pt : B) (lp : pt ~~> pt),
  circle -> B.
Proof.
  intros B pt lp.
  apply circle_rect with (P := fun _ => B) (pt := pt).
  apply @concat with (y := pt).
  apply trans_trivial.
  exact lp.
Defined.

(* Non-dependent computation rules *)
Definition compute_base' : forall B pt lp,
  circle_rect' B pt lp base ~~> pt.
Proof.
  intros B pt lp.
  unfold circle_rect'.
  apply compute_base with (P := fun _ => B).
Defined.

Definition compute_loop' : forall B pt lp,
    map (circle_rect' B pt lp) loop
    ~~> compute_base' B pt lp @ lp @ !compute_base' B pt lp.
Proof.
  intros B pt lp.
  eapply concat.
    apply map_dep_trivial2.
  moveright_onleft.
  eapply concat.
    apply compute_loop with (P := fun _ => B).
  unwhisker.
Defined.  
