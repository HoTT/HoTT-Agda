Add LoadPath "..".
Require Import Homotopy Common.

(** In this file I define the suspension and the cone of a type and prove a few properties *)

(** Suspension

Induction suspension (A : Type) :=
  | north_susp : suspension A
  | south_susp : suspension A
  | paths : A -> north_susp ~~> south_susp.
*)

(* Type *)
Axiom suspension : Type -> Type.

(* Constructors *)
Axiom north_susp : forall A : Type, suspension A.
Axiom south_susp : forall A : Type, suspension A.
Axiom paths_susp : forall A : Type, A -> north_susp A ~~> south_susp A.

(* Dependent elimination rule *)
Axiom suspension_rect : forall A : Type, forall P : suspension A -> Type,
  forall n : P (north_susp A), forall s : P (south_susp A),
  forall p : (forall a : A, transport (paths_susp A a) n ~~> s),
  forall x : suspension A, P x.

(* Dependent computation rules *)
Axiom compute_north_susp : forall A P n s p,
  suspension_rect A P n s p (north_susp A) ~~> n.

Axiom compute_south_susp : forall A P n s p,
  suspension_rect A P n s p (south_susp A) ~~> s.

Axiom compute_paths_susp : forall A P n s p, forall x : A,
  map_dep (suspension_rect A P n s p) (paths_susp _ x) ~~>
    map _ (compute_north_susp A P n s p) @ p x @ !compute_south_susp A P n s p.

(* Non-dependent elimination rule *)
Lemma suspension_rect' : forall A B : Type, forall n s : B, forall p : (A -> n ~~> s),
  suspension A -> B.
Proof.
  intros A B n s p.
  apply suspension_rect with (P := fun _ => B) (n := n) (s := s).
  intro a.
  path_via' n.
    apply trans_trivial.
  exact (p a).
Defined.

(* Non-dependent computation rules *)
Lemma compute_north_susp' : forall A B n s p,
  suspension_rect' A B n s p (north_susp A) ~~> n.
Proof.
  intros A B n s p.
  unfold suspension_rect'.
  apply compute_north_susp with (P := fun _  => B).
Defined.

Lemma compute_south_susp' : forall A B n s p,
  suspension_rect' A B n s p (south_susp A) ~~> s.
Proof.
  intros A B n s p.
  unfold suspension_rect'.
  apply compute_south_susp with (P := fun _  => B).
Defined.

Lemma compute_paths_susp' : forall A B n s p, forall x : A,
  map (suspension_rect' A B n s p) (paths_susp _ x) ~~>
  compute_north_susp' A B n s p @ p x @ !compute_south_susp' A B n s p.
Proof.
  intros A B n s p x.
  eapply concat.
    apply map_dep_trivial2.
  moveright_onleft.
  eapply concat.
    unfold suspension_rect'.
    apply compute_paths_susp with (P := fun _ => B).
  unwhisker.
Defined.

(** Cone

Induction cone (A : Type) :=
  | top : cone A
  | flat : A -> cone A
  | paths_cone : forall a : A, flat a ~~> top.

Note: We could probably define [cone A] to be a single point instead, given that [cone A] is
contractible this would work as well. I will not "cheat" and I will use the usual definition of the
cone.
*)

(* Type *)
Axiom cone : Type -> Type.

(* Constructors *)
Axiom top : forall A : Type, cone A.
Axiom flat : forall A : Type, A -> cone A.
Axiom paths_cone : forall A : Type, forall a : A, top A ~~> flat A a.

(* Dependent elimination rule *)
Axiom cone_rect : forall A : Type, forall P : cone A -> Type,
  forall t : P (top A), forall f : (forall a : A, P (flat A a)),
  forall p : (forall a : A, transport (paths_cone A a) t ~~> f a),
  forall x : cone A, P x.

(* Dependent computation rules *)
Axiom compute_top : forall A P t f p,
  cone_rect A P t f p (top A) ~~> t.

Axiom compute_flat : forall A P t f p,
  forall a : A,
  cone_rect A P t f p (flat A a) ~~> f a.

(* Axiom compute_paths_cone TODO (not needed for now) *)

(* Non-dependent elimination rule *)
Lemma cone_rect' : forall A B : Type,
  forall t : B, forall f : A -> B, forall p : (forall a : A, t ~~> f a),
  cone A -> B.
Proof.
  intros A B t f p.
  apply cone_rect with (P := fun _ => B) (t := t) (f := f).
  intro a.
  path_via' t.
    apply trans_trivial.
  apply p.
Defined.

(* Non-dependent computation rules *)
Lemma compute_top' : forall A B t f p,
  cone_rect' A B t f p (top A) ~~> t.
Proof.
  intros.
  unfold cone_rect'.
  apply compute_top with (P := fun _ => B).
Defined.

Lemma compute_flat' : forall A B t f p,
  forall a : A,
  cone_rect' A B t f p (flat A a) ~~> f a.
Proof.
  intros.
  unfold cone_rect'.
  apply compute_flat with (P := fun _ => B).
Defined.

(* Lemma compute_paths_cone' TODO *)
  
(** Properties *)

(* Topologically, there are two natural maps from [cone A] to [suspension A]. One is collapsing the
   base of the cone to a point and the other one is the injection of the gluing of two cones.
   But both maps are homotopic, so cannot be distinguished in HoTT *)
Lemma cone_to_susp : forall A : Type, cone A -> suspension A.
Proof.
  intro A.
  apply cone_rect' with (t := north_susp A) (f := fun _ => south_susp A).
  apply paths_susp.
Defined.

Definition P_contrtop (A : Type) := fun a : cone A => a ~~> top A.

Lemma contrtop_transp : forall A : Type, forall u v : cone A, forall p : u ~~> v,
  forall q : P_contrtop A u,
  transport (P := P_contrtop A) p q ~~> !p @ q.
Proof.
  path_induction.
  cancel_units.
Defined.

Lemma contrtop_top : forall A : Type, P_contrtop A (top A).
Proof.
  intro A.
  apply idpath.
Defined.

Lemma contrtop_flat : forall A : Type, forall a : A, P_contrtop A (flat A a).
Proof.
  intros.
  apply opposite.
  apply paths_cone.
Defined.

Lemma contrtop_paths_cone : forall A : Type, forall a : A,
  transport (paths_cone A a) (contrtop_top A) ~~> contrtop_flat A a.
Proof.
  intros.
  eapply concat.
    apply contrtop_transp.
  unfold contrtop_flat, contrtop_top.
  cancel_units.
Defined.

Definition contr_top (A : Type) : forall a : cone A, a ~~> top A :=
  cone_rect A (P_contrtop A) (contrtop_top A) (contrtop_flat A) (contrtop_paths_cone A).

Lemma contr_top_top : forall A : Type, contr_top A (top A) ~~> idpath (top A).
Proof.
  intro A.
  unfold contr_top.
  unfold contrtop_top.
  apply compute_top with (P := fun x => x ~~> top A).
Defined.