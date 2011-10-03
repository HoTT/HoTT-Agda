Add LoadPath "..".
Require Import Homotopy.

(** In this file I prove that the based/free loop space (fundamental group/groupoid) commutes with
   products *)

Definition space_to_product {A B : Type} {c c' : A * B}
           : c ~~> c' -> ((fst c ~~> fst c') * (snd c ~~> snd c')).
  intro p.
  induction p.
  auto.
Defined.

Definition product_to_space {A B : Type} {c c' : A * B}
           : ((fst c ~~> fst c') * (snd c ~~> snd c')) -> (c ~~> c').
  intro t; destruct t as [p q].
  destruct c as [a b].
  destruct c' as [a' b'].
  simpl in p, q.
  induction p as [x].
  induction q as [y].
  apply idpath.
Defined.

Definition inverse1 {A B : Type} {c c' : A * B} (x : (fst c ~~> fst c') * (snd c ~~> snd c'))
      : (space_to_product (product_to_space x)) ~~> x.
  destruct x as [p q].
  destruct c as [a b].
  destruct c' as [a' b'].
  simpl in p, q.
  induction p.
  induction q.
  simpl.
  apply idpath.
Defined.

Definition inverse2 {A B : Type} {c c' : A * B} (p : c ~~> c')
      : (product_to_space (space_to_product p)) ~~> p.
  induction p.
  path_via (product_to_space (idpath (fst x), idpath (snd x))).
  destruct x as [a b].
  simpl.
  apply idpath.
Defined.


Theorem free_loop_space_commutes_with_products (A B : Type) (c c' : A * B)
        : (fst c ~~> fst c') * (snd c ~~> snd c') ≃> (c ~~> c').
Proof.
  exists product_to_space.
  apply hequiv_is_equiv with (g := space_to_product).
    apply inverse2.
  apply inverse1.
Defined.

Theorem based_loop_space_commutes_with_products (A B : Type) (a : A) (b : B)
        : (a ~~> a) * (b ~~> b) ≃> ((a, b) ~~> (a, b)).
Proof.
  apply free_loop_space_commutes_with_products with (c := (a, b)) (c' := (a, b)).
Defined.

(** Some useful definitions, propositions and tactics *)

Definition combine {A B : Type} {a a' : A} {b b' : B}
  : ((a ~~> a') * (b ~~> b')) -> (a, b) ~~> (a', b') :=
  fun x => product_to_space x (c := (a, b)) (c' := (a', b')).

Lemma combine_concat : forall A B : Type, forall u v w : A, forall u' v' w' : B,
  forall p : u ~~> v, forall q : v ~~> w, forall p' : u' ~~> v', forall q' : v' ~~> w',
  combine (p @ q, p' @ q') ~~> combine (p, p') @ combine (q, q').
Proof.
  path_induction.
Defined.

Ltac do_combine_concat_in s :=
  match s with
    | context cxt [ combine (?p @ ?q, ?p' @ ?q') ] =>
      let mid := context cxt [ combine (p, p') @ combine (q, q') ] in path_using mid combine_concat
  end.

Ltac do_combine_concat :=
  repeat progress (
    match goal with
      |- ?s ~~> ?t => first [ do_combine_concat_in s | do_combine_concat_in t ]
    end
  ).

Lemma combine_opposite : forall A B : Type, forall u v : A, forall u' v' : B,
  forall p : u ~~> v, forall p' : u' ~~> v',
    combine (!p, !p') ~~> !combine (p, p').
Proof.
  path_induction.
Defined.

Ltac do_combine_opposite_in s :=
  match s with
    | context cxt [ combine (! ?p, ! ?p') ] =>
      let mid := context cxt [ !combine (p, p') ] in path_using mid combine_opposite
  end.

Ltac do_combine_opposite :=
  repeat progress (
    match goal with
      |- ?s ~~> ?t => first [ do_combine_opposite_in s | do_combine_opposite_in t ]
    end
  ).
