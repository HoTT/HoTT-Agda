{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import homotopy.SphereEndomorphism
open import groups.SphereEndomorphism
open import groups.CoefficientExtensionality
open import cw.CW
open import cw.WedgeOfCells

module cw.DegreeByProjection {i} where

  module DegreeAboveOne {n : ℕ} (skel : Skeleton {i} (S (S n)))
    (dec : has-cells-with-dec-eq skel)
    -- the cells at the upper and lower dimensions
    (upper : cells-last skel)
    (lower : cells-last (cw-init skel))
    where

    private
      lower-skel = cw-init skel
      lower-cells = cells-nth lteS skel
      lower-dec = cells-nth-has-dec-eq lteS skel dec

    degree-map : Sphere (S n) → Sphere (S n)
    degree-map = bwproj lower-dec lower
               ∘ <– (Bouquet-equiv-Xₙ/Xₙ₋₁ lower-skel)
               ∘ cfcod
               ∘ attaching-last skel upper

    degree : ℤ
    degree = Trunc-⊙SphereS-endo-degree n (Trunc-⊙SphereS-endo-in n [ degree-map ])

  module DegreeAtOne (skel : Skeleton {i} 1)
    (dec : has-cells-with-dec-eq skel)
    -- the cells at the upper and lower dimensions
    (line : cells-last skel)
    (point : cells-last (cw-init skel)) where

    private
      points-dec-eq = cells-nth-has-dec-eq (inr ltS) skel dec
      endpoint = attaching-last skel

    -- When [true] matches, [true] will be sent to [false],
    -- which is bad.
    degree-true : ℤ
    degree-true with points-dec-eq point (endpoint line true)
    degree-true | inl _ = -1
    degree-true | inr _ = 0

    -- When [false] matches, [false] will be sent to [false],
    -- which is good.
    degree-false : ℤ
    degree-false with points-dec-eq point (endpoint line false)
    degree-false | inl _ = 1
    degree-false | inr _ = 0

    degree : ℤ
    degree = degree-true ℤ+ degree-false

  degree-last : ∀ {n} (skel : Skeleton {i} (S n))
    → has-cells-with-dec-eq skel
    → cells-last skel → cells-last (cw-init skel) → ℤ
  degree-last {n = O} = DegreeAtOne.degree
  degree-last {n = S _} = DegreeAboveOne.degree

  degree-nth : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n)
    → has-cells-with-dec-eq skel
    → cells-nth Sm≤n skel → cells-last (cw-init (cw-take Sm≤n skel)) → ℤ
  degree-nth Sm≤n skel dec = degree-last (cw-take Sm≤n skel) (take-has-cells-with-dec-eq Sm≤n skel dec)

  has-degrees-with-finite-support : ∀ {n} (skel : Skeleton {i} n)
    → has-cells-with-dec-eq skel → Type i
  has-degrees-with-finite-support {n = O} _ _ = Lift ⊤
  has-degrees-with-finite-support {n = S n} skel dec =
    has-degrees-with-finite-support (cw-init skel) (init-has-cells-with-dec-eq skel dec) ×
    ∀ upper → has-finite-support (cells-nth-has-dec-eq (inr ltS) skel dec) (degree-last skel dec upper)

  init-has-degrees-with-finite-support : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-support skel dec
    → has-degrees-with-finite-support (cw-init skel) (init-has-cells-with-dec-eq skel dec)
  init-has-degrees-with-finite-support skel dec fin-sup = fst fin-sup

  take-has-degrees-with-finite-support : ∀ {m n} (m≤n : m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-support skel dec
    → has-degrees-with-finite-support (cw-take m≤n skel) (take-has-cells-with-dec-eq m≤n skel dec)
  take-has-degrees-with-finite-support (inl idp) skel dec fin-sup = fin-sup
  take-has-degrees-with-finite-support (inr ltS) skel dec fin-sup =
    init-has-degrees-with-finite-support skel dec fin-sup
  take-has-degrees-with-finite-support (inr (ltSR lt)) skel dec fin-sup =
    take-has-degrees-with-finite-support (inr lt) (cw-init skel)
      (init-has-cells-with-dec-eq skel dec)
      (init-has-degrees-with-finite-support skel dec fin-sup)

  degree-last-has-finite-support : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-support skel dec
    → ∀ upper → has-finite-support
        (cells-last-has-dec-eq (cw-init skel) (init-has-cells-with-dec-eq skel dec))
        (degree-last skel dec upper)
  degree-last-has-finite-support skel dec fin-sup = snd fin-sup

  degree-nth-has-finite-support : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-support skel dec
    → ∀ upper → has-finite-support
        (cells-last-has-dec-eq
          (cw-init (cw-take Sm≤n skel))
          (init-has-cells-with-dec-eq (cw-take Sm≤n skel) (take-has-cells-with-dec-eq Sm≤n skel dec)))
        (degree-nth Sm≤n skel dec upper)
  degree-nth-has-finite-support Sm≤n skel dec fin-sup =
    degree-last-has-finite-support (cw-take Sm≤n skel)
      (take-has-cells-with-dec-eq Sm≤n skel dec)
      (take-has-degrees-with-finite-support Sm≤n skel dec fin-sup)

  -- the following are named [boundary'] because it is not extended to the free groups

  boundary'-last : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-support skel dec
    → cells-last skel → FreeAbGroup.El (cells-last (cw-init skel))
  boundary'-last skel dec fin-sup upper = fst ((snd fin-sup) upper)

  boundary-last : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-support skel dec
    → FreeAbGroup.grp (cells-last skel) →ᴳ FreeAbGroup.grp (cells-last (cw-init skel))
  boundary-last skel dec fin-sup =
    FreeAbGroup-extend (FreeAbGroup (cells-last (cw-init skel))) (boundary'-last skel dec fin-sup)

  boundary'-nth : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-support skel dec
    → cells-nth Sm≤n skel → FreeAbGroup.El (cells-last (cw-init (cw-take Sm≤n skel)))
  boundary'-nth Sm≤n skel dec fin-sup =
    boundary'-last (cw-take Sm≤n skel)
      (take-has-cells-with-dec-eq Sm≤n skel dec)
      (take-has-degrees-with-finite-support Sm≤n skel dec fin-sup)

  boundary-nth : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-support skel dec
    →  FreeAbGroup.grp (cells-nth Sm≤n skel)
    →ᴳ FreeAbGroup.grp (cells-last (cw-init (cw-take Sm≤n skel)))
  boundary-nth Sm≤n skel dec fin-sup =
    FreeAbGroup-extend
      (FreeAbGroup (cells-last (cw-init (cw-take Sm≤n skel))))
      (boundary'-nth Sm≤n skel dec fin-sup)
