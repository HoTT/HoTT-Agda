{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pointed

module lib.types.BigWedge where

module _ {i j} {A : Type i} where

  private
    data #BigWedge-aux (X : A → Ptd j) : Type (lmax i j) where
      #bwbase : #BigWedge-aux X
      #bwin : (a : A) → fst (X a) → #BigWedge-aux X

    data #BigWedge (X : A → Ptd j) : Type (lmax i j) where
      #bigwedge : #BigWedge-aux X → (Unit → Unit) → #BigWedge X
      
  BigWedge : (A → Ptd j) → Type (lmax i j)
  BigWedge X = #BigWedge X

  bwbase : {X : A → Ptd j} → BigWedge X
  bwbase = #bigwedge #bwbase _

  bwin : {X : A → Ptd j} → (a : A) → fst (X a) → BigWedge X
  bwin a x = #bigwedge (#bwin a x) _

  Ptd-BigWedge : (A → Ptd j) → Ptd (lmax i j)
  Ptd-BigWedge X = ∙[ BigWedge X , bwbase ]

  postulate  -- HIT
    bwglue : {X : A → Ptd j} → (a : A) → bwbase {X} == bwin a (snd (X a))

  ptd-bwin : {X : A → Ptd j} → (a : A) → fst (X a ∙→ Ptd-BigWedge X)
  ptd-bwin a = (bwin a , ! (bwglue a))

  module BigWedgeElim {X : A → Ptd j} {k} {P : BigWedge X → Type k}
    (base* : P bwbase)
    (in* : (a : A) (x : fst (X a)) → P (bwin a x))
    (glue* : (a : A) → base* == in* a (snd (X a)) [ P ↓ bwglue a ]) where

    f : Π (BigWedge X) P
    f = f-aux phantom where

      f-aux : Phantom glue* → Π (BigWedge X) P
      f-aux phantom (#bigwedge #bwbase _) = base*
      f-aux phantom (#bigwedge (#bwin a x) _) = in* a x

    postulate  -- HIT
      glue-β : (a : A) → apd f (bwglue a) == glue* a

  open BigWedgeElim public using () renaming (f to BigWedge-elim)

  module BigWedgeRec {X : A → Ptd j} {k} {C : Type k}
    (base* : C)
    (in* : (a : A) → fst (X a) → C)
    (glue* : (a : A) → base* == in* a (snd (X a))) where

    private
      module M = BigWedgeElim base* in* (λ c → ↓-cst-in (glue* c))

    f : BigWedge X → C
    f = M.f

    glue-β : (a : A) → ap f (bwglue a) == glue* a
    glue-β a = apd=cst-in {f = f} (M.glue-β a)

