Add LoadPath "..".
Require Import Homotopy Common.
Require Import ConeSuspension.

(* We will only need the following from ConeSuspension.v here :

Parameter suspension : Type -> Type.
Parameter cone : Type -> Type.
Parameter top : forall A : Type, cone A.
Parameter flat : forall A : Type, A -> cone A.
Parameter cone_to_susp : forall A : Type, cone A -> suspension A.
Parameter contr_top : forall A : Type, forall a : cone A, a ~~> top A.
Parameter contr_top_top : forall A : Type, contr_top A (top A) ~~> idpath (top A).
*)

(** In this file we will define the infinite dimensional sphere and prove it’s contractibility *)

Inductive empty : Type :=
  .

(** We define the spheres with "towers of suspensions".
    The name of the term is misleading, [ndim_sphere n] is actually the (n-1)-dimensional
    sphere, it is easier to start with the (-1)-sphere which is empty *)

Fixpoint ndim_sphere (n : nat) : Type :=
  match n with 
    | 0 => empty
    | S n' => suspension (ndim_sphere n')
  end.

Definition injection_spheres (n : nat) : ndim_sphere n -> ndim_sphere (S n) :=
  fun x => cone_to_susp _ (flat _ x).

(** Here is the HIT definition of the infinite dimensional sphere:

Inductive infinite_sphere :=
  | points_Sinf : total ndim_sphere -> infinite_sphere
  | paths_Sinf  : forall n : nat, forall x : ndim_sphere n,
                  points_Sinf (tpair n x) ~~> points_Sinf (tpair (S n) (injection_spheres n x)).

The idea is that we take the disjoint union of all the (finite dimensional) spheres and we connect
each sphere with the next one with paths along the [injection_spheres] function we just defined.
Note that [injection_spheres] can be seen either as the injection of S_n as the equator of S_{n+1} or
as a constant function sending everything to a point. Up to homotopy, there is no difference between
those two functions.

Note: [paths_Sinf] could (should?) also be indexed by [total ndim_sphere], but this is more
      convenient to destruct the dependent sum directly in the type.

As usual with HITs, we need to use axioms for the constructors, the elimination rule and the
computation rules, and the computation rules will only hold propositionally which is very cumbersome
(but there is no better solution yet).
*)

(* Type *)
Axiom infinite_sphere : Type.

(* Constructors *)
Axiom points_Sinf : total ndim_sphere -> infinite_sphere.

Axiom paths_Sinf :
  forall n : nat, forall x : ndim_sphere n,
    points_Sinf (tpair n x) ~~> points_Sinf (tpair (S n) (injection_spheres n x)).

(* Dependent elimination rule *)
Axiom infinite_sphere_rect : forall P : infinite_sphere -> Type,
  forall points : (forall x : total ndim_sphere, P (points_Sinf x)),
  forall paths : (forall n : nat, forall x : ndim_sphere n,
                  transport (P := P) (paths_Sinf n x) (points (tpair n x)) ~~>
                  points (tpair (S n) (injection_spheres n x))),
  forall x : infinite_sphere, P x.

(* Dependent computation rules *)
Axiom compute_points_Sinf : forall P points paths,
  forall x, (infinite_sphere_rect P points paths) (points_Sinf x) ~~> points x.

Axiom compute_paths_Sinf : forall P points paths,
  forall n x,
    map_dep (infinite_sphere_rect P points paths) (paths_Sinf n x) ~~>
      map (transport (paths_Sinf n x)) (compute_points_Sinf P points paths _) @
      paths n x @ !compute_points_Sinf P points paths _.

(* Non-dependent elimination rule *)
Lemma infinite_sphere_rect' : forall A : Type,
  forall points : total ndim_sphere -> A,
  forall paths : (forall n : nat, forall x : ndim_sphere n,
                  points (tpair n x) ~~> points (tpair (S n) (injection_spheres n x))),
  infinite_sphere -> A.
Proof.
  intros A points paths.
  apply infinite_sphere_rect with (P := fun _ => A) (points := points).
  intros n x.
  eapply concat.
    apply trans_trivial.
  apply paths.
Defined.

(* Non-dependent computation rules *)
Lemma compute_points_Sinf' : forall A points paths,
  forall x, (infinite_sphere_rect' A points paths) (points_Sinf x) ~~> points x.
Proof.
  intros.
  unfold infinite_sphere_rect'.
  apply compute_points_Sinf with (P := fun _ => A).
Defined.

Lemma compute_paths_Sinf' : forall A points paths,
  forall n x,
  map (infinite_sphere_rect' A points paths) (paths_Sinf n x) ~~>
  compute_points_Sinf' _ _ _ _ @ paths n x @ !compute_points_Sinf' _ _ _ _.
Proof.
  intros A points paths n x.
  unfold infinite_sphere_rect'.
  eapply concat.
    apply map_dep_trivial2.
  moveright_onleft.
  eapply concat.
    apply compute_paths_Sinf with (P := fun _ => A).
  unfold compute_points_Sinf'.
  unwhisker.
Defined.

(** In order to prove that [infinite_sphere] is contractible, we notice that it can also be seen
    as an increasing reunion of balls, and it is easy to prove that the reunion of balls is
    contractible.
    So we will define [infinite_balls], show that it is contractible and show that it is equivalent
    to [infinite_sphere]. *)

(** [ndim_ball n] is a (n-1)-dimensional ball *)

Fixpoint ndim_ball (n : nat) : Type :=
  match n with
    | 0 => empty
    | S n' => cone (ndim_sphere n')
  end.

(** [ndim_ball n] can be embedded as one hemisphere of [ndim_sphere n].
    Or [ndim_ball n] can be projected onto [ndim_sphere n] by collapsing the boundary to a point,
    it’s the same map (up to homotopy) *)

Definition ball_to_sphere : forall n : nat, ndim_ball n -> ndim_sphere n.
Proof.
  intro n.
  induction n.
    apply idmap.
  simpl.
  apply cone_to_susp.
Defined.

(** The n-sphere is the boundary of the (n+1)-ball *)

Definition sphere_to_ball : forall n : nat, ndim_sphere n -> ndim_ball (S n) :=
  fun n => flat _.

Definition injection_balls : forall n : nat, ndim_ball n -> ndim_ball (S n) :=
  fun n => fun x => sphere_to_ball _ (ball_to_sphere _ x).

(** Here is the infinite dimensional ball (this is actually a copy-paste of the infinite dimensional
   ball with "sphere" replaced by "ball" and "Sinf" by "Binf"):

Inductive infinite_ball :=
  | points_Binf : total ndim_ball -> infinite_ball
  | paths_Binf  : forall n : nat, forall x : ndim_ball n,
                  tpair n x ~~> tpair (S n) (injection_balls n x).
*)

(* Type *)
Axiom infinite_ball : Type.

(* Constructors *)
Axiom points_Binf : total ndim_ball -> infinite_ball.

Axiom paths_Binf :
  forall n : nat, forall x : ndim_ball n,
    points_Binf (tpair n x) ~~> points_Binf (tpair (S n) (injection_balls n x)).

(* Dependent elimination rule *)
Axiom infinite_ball_rect : forall P : infinite_ball -> Type,
  forall points : (forall x : total ndim_ball, P (points_Binf x)),
  forall paths : (forall n : nat, forall x : ndim_ball n,
                  transport (P := P) (paths_Binf n x) (points (tpair n x)) ~~>
                  points (tpair (S n) (injection_balls n x))),
  forall x : infinite_ball, P x.

(* Dependent computation rules *)
Axiom compute_points_Binf : forall P points paths,
  forall x, (infinite_ball_rect P points paths) (points_Binf x) ~~> points x.

Axiom compute_paths_Binf : forall P points paths,
  forall n x,
    map_dep (infinite_ball_rect P points paths) (paths_Binf n x) ~~>
      map (transport (paths_Binf n x)) (compute_points_Binf P points paths _) @
      paths n x @ !compute_points_Binf P points paths _.

(* Non-dependent elimination rule *)
Lemma infinite_ball_rect' : forall A : Type,
  forall points : total ndim_ball -> A,
  forall paths : (forall n : nat, forall x : ndim_ball n,
                  points (tpair n x) ~~> points (tpair (S n) (injection_balls n x))),
  infinite_ball -> A.
Proof.
  intros A points paths.
  apply infinite_ball_rect with (P := fun _ => A) (points := points).
  intros n x.
  eapply concat.
    apply trans_trivial.
  apply paths.
Defined.

(* Non-dependent computation rules *)
Lemma compute_points_Binf' : forall A points paths,
  forall x, (infinite_ball_rect' A points paths) (points_Binf x) ~~> points x.
Proof.
  intros.
  unfold infinite_ball_rect'.
  apply compute_points_Binf with (P := fun _ => A).
Defined.

Lemma compute_paths_Binf' : forall A points paths,
  forall n x,
  map (infinite_ball_rect' A points paths) (paths_Binf n x) ~~>
  compute_points_Binf' _ _ _ _ @ paths n x @ !compute_points_Binf' _ _ _ _.
Proof.
  intros A points paths n x.
  unfold infinite_ball_rect'.
  eapply concat.
    apply map_dep_trivial2.
  moveright_onleft.
  eapply concat.
    apply compute_paths_Binf with (P := fun _ => A).
  unfold compute_points_Binf'.
  unwhisker.
Defined.


(** We will now prove that [infinite_ball] is contractible *)

(** We choose a point in each ball (except [ndim_ball 0] because it’s empty) *)

Definition points_in_ndim_balls : forall n : nat, ndim_ball (S n) := fun n => top _.

Definition points_in_ball : nat -> infinite_ball :=
  fun n : nat => points_Binf (tpair (S n) (points_in_ndim_balls n)).

(** And we prove that they are all related by a path *)

Lemma path_through_ball : forall n : nat, points_in_ball n ~~> points_in_ball 0.
Proof.
  intro n.
  induction n.
    apply idpath.
  eapply concat.
    2:apply IHn.
  apply opposite.
  eapply concat.
    apply paths_Binf.
  unfold points_in_ball.
  apply map.
  apply map.
  apply contr_top.
Defined.

(* Now we want a section of this fibration *)
Definition P_contr :=
  fun x : infinite_ball => x ~~> points_in_ball 0.

Lemma contr_transp : forall n : nat, forall x : ndim_ball n,
  forall u v : infinite_ball, forall p : u ~~> v, forall q : P_contr u,
  transport (P := P_contr) p q ~~> !p @ q.
Proof.
  path_induction.
  cancel_units.
Defined. 

(* Section of [P_contr] on the points of the form [points_Binf x] *)
Lemma contr_points_Binf : forall x : total ndim_ball, P_contr (points_Binf x).
Proof.
  intro x.
  unfold P_contr.
  destruct x as [n x].
  induction n.
    destruct x.
  path_via' (points_in_ball n).
    unfold points_in_ball.
    apply map.
    apply map.
    apply contr_top.
  apply path_through_ball.
Defined.

(* Simple elimination rule for the cone *)
Lemma cone_contr_rect : forall A : Type, forall P : cone A -> Type,
  P (top A) -> forall x : cone A, P x.
Proof.
  intros A P x y.
  set (p := contr_top _ y).
  exact (transport (P := P) (!p) x).
Defined.

Lemma contr_paths_Binf : forall n : nat, forall x : ndim_ball n,
  transport (P := P_contr) (paths_Binf n x) (contr_points_Binf (tpair n x)) ~~>
  contr_points_Binf (tpair (S n) (injection_balls n x)).
Proof.
  intros n x.
  eapply concat.
    apply (contr_transp n x).
  induction n.
    destruct x.
  generalize dependent x.
  apply cone_contr_rect.
  unfold contr_points_Binf at 1; simpl.
  rewr (contr_top_top (ndim_sphere n)).
    apply contr_top_top.
  undo_opposite_concat.
  unwhisker.
  apply opposite.
  cancel_opposites.
Defined.

Theorem ball_contr : is_contr infinite_ball.
Proof.
  exists (points_in_ball 0).
  exact (infinite_ball_rect P_contr contr_points_Binf contr_paths_Binf).
Defined.

(** We will now prove that [infinite_sphere] and [infinite_ball] are equivalent *)

(** Defining the two maps [s_to_b] and [b_to_s] is easy using [sphere_to_ball] and [ball_to_sphere]
*)

Definition points_s_to_b :=
  fun x : total ndim_sphere => let (n, x) := x in points_Binf (tpair (S n) (sphere_to_ball n x)).

Definition paths_s_to_b := 
  fun n x => paths_Binf (S n) (sphere_to_ball n x).

Definition s_to_b : infinite_sphere -> infinite_ball :=
  infinite_sphere_rect' _ points_s_to_b paths_s_to_b.


Definition points_b_to_s :=
  fun x : total ndim_ball => let (n, x) := x in points_Sinf (tpair n (ball_to_sphere n x)).

Definition paths_b_to_s :=  
  fun n x => paths_Sinf n (ball_to_sphere n x).

Definition b_to_s : infinite_ball -> infinite_sphere :=
  infinite_ball_rect' _ points_b_to_s paths_b_to_s.

(** Here is the proof that coming from the sphere to the ball and back to the sphere is homotopic to
   the identity (the other direction will be much easier) *)

(* We want a section of this fibration *)
Definition P_invs := fun x : infinite_sphere => b_to_s (s_to_b x) ~~> x.

Lemma invs_transp : forall n : nat, forall x : ndim_sphere n,
  forall u v : infinite_sphere, forall p : u ~~> v, forall q : P_invs u,
  transport (P := P_invs) p q ~~> !map (compose b_to_s s_to_b) p @ q @ p.
Proof.
  path_induction.
  cancel_units.
Defined.

Lemma invs_points_Sinf : forall x : total ndim_sphere, P_invs (points_Sinf x).
Proof.
  intro x.
  destruct x as [n x].
  unfold P_invs.
  unfold s_to_b.
  path_via (b_to_s (points_Binf (tpair (S n) (sphere_to_ball n x)))).
    exact (compute_points_Sinf' _ _ _ _). (* For some reason, [apply] doesn’t work *)
  unfold b_to_s.
  path_via' (points_Sinf (tpair (S n) (ball_to_sphere (S n) (sphere_to_ball n x)))).
    exact (compute_points_Binf' _ _ _ _).
  apply opposite.
  apply paths_Sinf.
Defined.

Lemma invs_paths_Sinf : forall n : nat, forall x : ndim_sphere n,
  transport (P := P_invs) (paths_Sinf n x) (invs_points_Sinf (tpair n x)) ~~>
    invs_points_Sinf (tpair (S n) (injection_spheres n x)).
Proof.
  intros.
  eapply @concat.
    apply (invs_transp n x).
  do_compose_map.
  unfold s_to_b.
  rewr (compute_paths_Sinf' infinite_ball points_s_to_b paths_s_to_b n x).
    apply compute_paths_Sinf'. (* rewr should be improved to do this automatically *)
  do_concat_map.
    apply concat_map with (f := b_to_s).
  undo_opposite_concat.
  do_opposite_map.
  unfold b_to_s at 13. (* This syntax is strange, why not [at 2]? *)
  unfold paths_s_to_b at 9.
  rewr (compute_paths_Binf' infinite_sphere points_b_to_s paths_b_to_s (S n) (sphere_to_ball n x)).
    apply compute_paths_Binf'.
  undo_opposite_concat.
  unfold invs_points_Sinf.
  unwhisker.
  cancel_opposite_of (paths_Sinf n x).
  moveright_onleft.
  moveright_onleft.
  moveright_onleft.
Defined.

Definition invs : forall x : infinite_sphere, P_invs x :=
  infinite_sphere_rect P_invs invs_points_Sinf invs_paths_Sinf.


(** The other direction is much simpler because we proved that [infinite_ball] is contractible so
   the composite is automatically homotopic to the identity. *)

Definition invb : forall x : infinite_ball, s_to_b (b_to_s x) ~~> x.
  intro x.
  path_via (points_in_ball 0).
    apply (pr2 ball_contr).
  apply opposite.
  apply (pr2 ball_contr).
Defined.

(** We can now conclude *)

Definition ball_equiv_sphere : infinite_ball ≃> infinite_sphere.
Proof.
  exists b_to_s.
  apply hequiv_is_equiv with (g := s_to_b).
    apply invs.
  apply invb.
Defined.

Theorem infinite_sphere_contr : is_contr infinite_sphere.
Proof.
  apply contr_equiv_contr with (A := infinite_ball).
    apply ball_equiv_sphere.
  apply ball_contr.
Defined.


(***
Aborted tentative to prove directly that [infinite_sphere] is contractible.
Not sure it is a good idea, because [f_points_Sinf] is already very complicated, and this will
likely be a nightmare to prove [f_paths_Sinf].

Definition f : infinite_sphere -> infinite_sphere :=
  infinite_sphere_rect' _ (fun _ => points_Sinf (tpair 0 north)) (fun _ _ => idpath _).

Definition P_f := fun x : infinite_sphere => f x ~~> x.

Lemma f_points_Sinf : forall x : total ndim_sphere, P_f (points_Sinf x).
Proof.
  intro x.
  unfold P_f.
  unfold f.
  eapply concat.
    apply compute_points_Sinf'.
  destruct x as [n x].
  induction n.
    destruct x.
      apply idpath.
    path_via' (points_Sinf (tpair 1 (north_susp (ndim_sphere 0) : ndim_sphere 1))).
      eapply concat.
        apply paths_Sinf.
      apply map.
      apply map.
      unfold injection_spheres.
      unfold cone_to_susp.
      eapply concat.
        apply compute_flat'.
      apply idpath.
    apply opposite.
    eapply concat.
      apply paths_Sinf.
    apply map.
    apply map.
    unfold injection_spheres.
    unfold cone_to_susp.
    eapply concat.
      apply compute_flat'.
    apply idpath.
  simpl in x.
  assert (points_Sinf (tpair 0 north) ~~> points_Sinf (tpair (S n) (north_susp (ndim_sphere n) : ndim_sphere (S n)))).
    eapply concat.
      2:apply paths_Sinf.
***)