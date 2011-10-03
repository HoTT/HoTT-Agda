Add LoadPath "..".

Require Import Homotopy ConeSuspension InfiniteSphere Circle Common.

(** Verification that low dimensional spheres are indeed what we expect.
NB : This is a draft, proofs are ugly, this has to be improved.
*)

(** Sphere of dimension -1 *)

Lemma sphere_minus1 : ndim_sphere 0 ≃> empty.
Proof.
  apply path_to_equiv.
  apply idpath. (* This is a definitional equality *)
Defined.


(** Sphere of dimension 0 *)

Inductive two_ :=
  | north_ : two_
  | south_ : two_.
Definition two := (two_ : Type).
Definition north := (north_ : two).
Definition south := (south_ : two).

Definition sphere_zero_to_two : ndim_sphere 1 -> two :=
  suspension_rect' empty two north south (fun x => match x with end).

Definition two_to_sphere_zero : two -> ndim_sphere 1 := fun x =>
  match x with
    | north => north_susp _
    | south => south_susp _
  end.

Lemma invtwo : forall x : two, sphere_zero_to_two (two_to_sphere_zero x) ~~> x.
Proof.
  intro x.
  destruct x.
    apply compute_north_susp'.
  apply compute_south_susp'.
Defined.

Definition P_invs0 := fun x : ndim_sphere 1 => two_to_sphere_zero (sphere_zero_to_two x) ~~> x.

Lemma invs0_north_susp : P_invs0 (north_susp _).
Proof.
  unfold P_invs0.
  path_via (two_to_sphere_zero north).
  apply compute_north_susp'.
Defined.

Lemma invs0_south_susp : P_invs0 (south_susp _).
Proof.
  unfold P_invs0.
  path_via (two_to_sphere_zero south).
  apply compute_south_susp'.
Defined.

Definition invs0 : forall x : ndim_sphere 1, two_to_sphere_zero (sphere_zero_to_two x) ~~> x :=
  suspension_rect _ _ invs0_north_susp invs0_south_susp (fun x => match x with end).

Lemma sphere_zero : ndim_sphere 1 ≃> two.
Proof.
  exists sphere_zero_to_two.
  apply hequiv_is_equiv with (g := two_to_sphere_zero).
    apply invtwo.
  apply invs0.
Defined.


(** Sphere of dimension 1 *)

Definition circle_to_sphere_one : circle -> ndim_sphere 2 :=
  circle_rect' _ (north_susp _) (paths_susp _ (north_susp _) @ !paths_susp _ (south_susp _)).

Definition sphere_one_to_circle : ndim_sphere 2 -> circle :=
  suspension_rect' _ _ base base
      (fun x : ndim_sphere 1 =>
        match sphere_zero_to_two x with
          | north => loop
          | south => idpath base
        end).


Definition P_invc := fun x : circle => sphere_one_to_circle (circle_to_sphere_one x) ~~> x.

Lemma invc_base : P_invc base.
Proof.
  path_via (sphere_one_to_circle (north_susp _)).
    apply compute_base'.
  apply compute_north_susp'.
Defined.

Lemma invc_transp : forall u v : circle, forall p : u ~~> v, forall q : P_invc u,
  transport (P := P_invc) p q ~~> !map (compose sphere_one_to_circle circle_to_sphere_one) p @ q @ p.
Proof.
  path_induction.
  cancel_units.
Defined.

Lemma invc_loop : transport (P := P_invc) loop invc_base ~~> invc_base.
Proof.
  eapply concat.
    apply invc_transp.
  do_compose_map.
  unfold circle_to_sphere_one.
  path_via ((!map sphere_one_to_circle
       ((compute_base' (suspension (suspension empty))
         (north_susp (suspension empty))
         (paths_susp (suspension empty) (north_susp empty) @
          !paths_susp (suspension empty) (south_susp empty)) @
       (paths_susp (suspension empty) (north_susp empty) @
        !paths_susp (suspension empty) (south_susp empty))) @
      !compute_base' (suspension (suspension empty))
         (north_susp (suspension empty))
         (paths_susp (suspension empty) (north_susp empty) @
          !paths_susp (suspension empty) (south_susp empty))) @
    invc_base) @ loop).
  apply compute_loop'.
  do_concat_map.
  undo_opposite_concat.
  do_opposite_map.
  unfold sphere_one_to_circle at 14.
  lazymatch goal with
    | |- @paths _ ?z _ => lazymatch z with
      | context ctx [map (suspension_rect' ?A ?B ?n ?s ?p) (paths_susp ?C ?x)] =>
        let new := context ctx [compute_north_susp' A B n s p @ p x @ !compute_south_susp' A B n s p]
          in
          path_via new
    end
  end.
    apply compute_paths_susp'.
  unfold sphere_one_to_circle.
  lazymatch goal with
    | |- @paths _ ?z _ => lazymatch z with
      | context ctx [map (suspension_rect' ?A ?B ?n ?s ?p) (paths_susp ?C ?x)] =>
        let new := context ctx [compute_north_susp' A B n s p @ p x @ !compute_south_susp' A B n s p]
          in
          path_via new
    end
  end.
    apply compute_paths_susp'.
  unfold invc_base.
  undo_opposite_concat.
  associate_right.
  moveright_onleft.
  moveright_onleft.
  moveright_onleft.
  unfold sphere_zero_to_two at 1.
  rewr (compute_north_susp' empty two north south
        (fun x : empty => match x return (north ~~> south) with
                          end)).
    exact (map (fun x => match x with north => loop | south => idpath base end)
      (compute_north_susp _ _ _ _ _)).
  unfold sphere_zero_to_two at 11.
  apply opposite.
  rewr (compute_south_susp' empty two north south
        (fun x : empty => match x return (north ~~> south) with
                          end)).
    exact (map (fun x => match x with north => loop | south => idpath base end)
      (compute_south_susp _ _ _ _ _)).
  simpl.
  cancel_opposites.
  simpl.
  apply opposite.
  do_concat_map.
  unfold sphere_one_to_circle.
  simpl.
  moveright_onleft.
  moveright_onleft.
  moveright_onleft.
Defined.  

Definition invc : forall x : circle, P_invc x := circle_rect P_invc invc_base invc_loop.


Definition P_invs1 := fun y : ndim_sphere 2 => circle_to_sphere_one (sphere_one_to_circle y) ~~> y.

Lemma invs1_transp : forall u v : ndim_sphere 2, forall p : u ~~> v, forall q : P_invs1 u,
  transport (P := P_invs1) p q ~~> !map (compose circle_to_sphere_one sphere_one_to_circle) p @ q @ p.
Proof.
  path_induction.
  cancel_units.
Defined.

Lemma invs1_north_susp : P_invs1 (north_susp (ndim_sphere 1)).
Proof.
  unfold P_invs1.
  path_via (circle_to_sphere_one base).
    apply compute_north_susp'.
  apply compute_base'.
Defined.

Lemma invs1_south_susp : P_invs1 (south_susp (ndim_sphere 1)).
Proof.
  unfold P_invs1.
  path_via (circle_to_sphere_one base).
    apply compute_south_susp'.
  eapply concat.
    apply compute_base'.
  apply paths_susp.
  apply south_susp. (* I think this will not work with [north_susp], to check *)
Defined.

Lemma invs1_paths_susp : forall x : ndim_sphere 1,
  transport (P := P_invs1) (paths_susp _ x) invs1_north_susp ~~> invs1_south_susp.
Proof.
  intro x.
  rewr (! invs0 x).
    apply map with (f := fun t => transport (paths_susp (ndim_sphere 1) t) invs1_north_susp).
    apply opposite.
    apply invs0.
  induction (sphere_zero_to_two x); simpl.
  eapply concat.
    apply invs1_transp.
  do_compose_map.
  unfold sphere_one_to_circle.
  set (compute_paths_susp' (ndim_sphere 1) circle base base
             (fun x0 : ndim_sphere 1 =>
              match sphere_zero_to_two x0 with
              | north => loop
              | south => idpath base
              end) (north_susp empty)).
  path_via ((!map circle_to_sphere_one
       ((compute_north_susp' (ndim_sphere 1) circle base base
         (fun x0 : ndim_sphere 1 =>
          match sphere_zero_to_two x0 with
          | north => loop
          | south => idpath base
          end) @
       (fun x0 : ndim_sphere 1 =>
        match sphere_zero_to_two x0 with
        | north => loop
        | south => idpath base
        end) (north_susp empty)) @
      !compute_south_susp' (ndim_sphere 1) circle base base
         (fun x0 : ndim_sphere 1 =>
          match sphere_zero_to_two x0 with
          | north => loop
          | south => idpath base
          end)) @ invs1_north_susp) @
   paths_susp (ndim_sphere 1) (north_susp empty)).
  simpl.
  do_concat_map.
  set (compute_north_susp' _ _ _ _ _ : sphere_zero_to_two (north_susp empty) ~~> _).
  rewr p0.
  simpl.
  exact (map (fun t => match t with north => loop | south => idpath base end) p0).
  simpl.
  set (compute_loop' _ _ _ : map circle_to_sphere_one loop ~~> _).
  path_via ((!((map circle_to_sphere_one
         (compute_north_susp' (suspension empty) circle base base
            (fun x0 : suspension empty =>
             match sphere_zero_to_two x0 with
             | north => loop
             | south => idpath base
             end)) @ ((compute_base' (ndim_sphere 2) (north_susp (suspension empty))
          (paths_susp (suspension empty) (north_susp empty) @
           !paths_susp (suspension empty) (south_susp empty)) @
        (paths_susp (suspension empty) (north_susp empty) @
         !paths_susp (suspension empty) (south_susp empty))) @
       !compute_base' (ndim_sphere 2) (north_susp (suspension empty))
          (paths_susp (suspension empty) (north_susp empty) @
           !paths_susp (suspension empty) (south_susp empty)))) @
      map circle_to_sphere_one
        (!compute_south_susp' (suspension empty) circle base base
            (fun x0 : suspension empty =>
             match sphere_zero_to_two x0 with
             | north => loop
             | south => idpath base
             end))) @ invs1_north_susp) @
   paths_susp (suspension empty) (north_susp empty)).
  unfold invs1_south_susp.
  simpl.
  undo_opposite_concat.
  undo_opposite_map.
  unwhisker.
  unfold invs1_north_susp.
  moveright_onleft.
  moveright_onleft.
  moveright_onleft.
  moveright_onleft.
  undo_opposite_map.
  unwhisker.

  eapply concat.
    apply invs1_transp.
  do_compose_map.
  rewr (compute_paths_susp' _ _ _ _ _ _ :
    map sphere_one_to_circle (paths_susp (suspension empty) (south_susp empty)) ~~> _).
    apply compute_paths_susp'.
  rewr (compute_south_susp' _ _ _ _ _ : sphere_zero_to_two (south_susp empty) ~~> _).
    exact (map (fun t => match t with north => _ | south => _ end) (compute_south_susp' _ _ _ _ _)).
  simpl.
  cancel_units.
  do_concat_map.
    apply concat_map with (f := circle_to_sphere_one).
  undo_opposite_concat.
  undo_opposite_map.
  unfold invs1_south_susp.
  unwhisker.
  unfold invs1_north_susp.
  moveright_onleft.
  undo_opposite_map.
Defined.  

Definition invs1 : forall y : ndim_sphere 2, P_invs1 y :=
  suspension_rect _ _ invs1_north_susp invs1_south_susp invs1_paths_susp.

Lemma sphere_one : ndim_sphere 2 ≃> circle.
Proof.
  exists sphere_one_to_circle.
  apply hequiv_is_equiv with (g := circle_to_sphere_one).
    apply invc.
  apply invs1.
Defined.
