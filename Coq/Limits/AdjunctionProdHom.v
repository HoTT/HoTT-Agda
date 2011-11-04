Add LoadPath "..".

Require Import Homotopy.

Lemma adjunction_product_hom (X Y Z : Type) : (X -> (Y -> Z)) ≃> (X * Y -> Z).
Proof.
  set (left_to_right := fun (f : X -> (Y -> Z)) => fun (xy : X * Y) => let (x, y) := xy in f x y).
  set (right_to_left := fun (f : X * Y -> Z)    => fun x => fun y => f (x, y)).
  exists left_to_right.
  apply hequiv_is_equiv with (g := right_to_left).
    intro y.
    apply funext; intro t.
    destruct t.
    apply idpath.
  intro x.
  apply funext; intro t.
  apply funext; intro t'.
  apply idpath.
Defined.
