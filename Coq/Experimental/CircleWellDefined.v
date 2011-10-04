Add LoadPath "..".
Require Import Homotopy Common Circle.
(*

I want to prove that two copies of the circle are equivalent (that is, that the higher inductive
definition of [circle] gives indeed a unique space up to equivalence). For simplicity I will only use
one copy (so that I do not need to write everything twice).

I first define the application [circle_to_circle : circle -> circle] by induction, and I want to
prove that this is an equivalence (remember that both [circle] are supposed to be different, so it
would be cheating to show that this application is equal to the identity map).
For that, I have to prove that for all [x : circle], there is a path from
[circle_to circle (circle_to_circle x)] to [x].

Calling [P_cc] this property of [x] ([P_cc] is a fibration over the circle), I want to prove 
[forall x : circle, P_cc x] by (dependent) induction on [x].

I first need to find a term [cc_base] of type [P_cc base]. This is easy, I just have to apply
the computation rule for [base] twice.

Then I have to find a term [cc_loop] of type [transport (P := P_cc) loop cc_base ~~> cc_base].
But given that I know nothing about [loop], I can’t prove something about it unless I prove
something about all paths in the circle and then I specialize it to [loop].
So I will find [cc_transp] which is of type [transport (P := P_cc) p x ~~> $$$] with [$$$]
replaced by something complicated, where [p] is any path of the circle, which explains how
something like [cc_base] is transported by any loop in the circle (this is very easy by
induction on [p] and with the [cancel_units] tactic).

Now the difficult part begins. I have to prove that [cc_transp] specialized to [loop] gives indeed
[transport (P := P_cc) loop cc_base ~~> cc_base]. I will here need to use the computation rule
for [loop] twice and make sure that everything cancels (and this is ugly because each
computation rule for loop adds two concatenations which have to pass through [map] and [!]).

*)

Definition circle_to_circle : circle -> circle := circle_rect' circle base loop.

Definition P_cc := fun x : circle => circle_to_circle (circle_to_circle x) ~~> x.

Lemma cc_base : P_cc base.
Proof.
  eapply concat.
    2:apply compute_base'.
  apply map.
  apply compute_base'.
Defined.

Lemma cc_transp : forall u v : circle, forall p : u ~~> v, forall x : P_cc u,
                  transport (P := P_cc) p x ~~>
                    (!map (compose circle_to_circle circle_to_circle ) p) @ x @ p.
Proof.
  path_induction.
  cancel_units.
Defined.

Lemma cc_loop : transport (P := P_cc) loop cc_base ~~> cc_base.
Proof.
  eapply concat.
    apply cc_transp.
  do_compose_map.
  rewr (compute_loop' _ _ _ : map circle_to_circle loop ~~> _).
    apply compute_loop'.
  do_concat_map.
    apply concat_map with (f := circle_to_circle). (* Why do I need to make [f] explicit? *)
  undo_opposite_concat.
  rewr (compute_loop' _ _ _ : map circle_to_circle loop ~~> _).
    apply compute_loop'.
  undo_opposite_concat.
  unfold cc_base.
  unfold circle_to_circle.
  do_opposite_map.
  moveright_onright.
  moveright_onright.
  undo_opposite_concat.
  associate_left.
Defined.

Lemma cc : forall x : circle, P_cc x.
Proof.
  exact (circle_rect P_cc cc_base cc_loop).
Defined.

Theorem circle_is_circle : circle ≃> circle.
Proof.
  exists (circle_to_circle).
  apply hequiv_is_equiv with (g := circle_to_circle); apply cc.
Defined.
