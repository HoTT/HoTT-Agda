{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import homotopy.SphereEndomorphism
open import homotopy.PinSn
open import groups.CoefficientExtensionality

module cw.DegreeBySquashing {i} where

  module DegreeAboveOne {n : ℕ} (skel : Skeleton {i} (S (S n)))
    (dec : has-cells-with-dec-eq skel)
    -- the cells at the upper and lower dimensions
    (upper : cells-last skel)
    (lower : cells-last (cw-init skel))
    where

    private
      lower-skel = cw-init skel
      lower-dec = init-has-cells-with-dec-eq skel dec
      lower-cells = cells-last lower-skel
      lower-cells-has-dec-eq = cells-last-has-dec-eq lower-skel lower-dec

    -- squash the lower CW complex except one of its cells [lower]
    cw-squash-lower-to-Sphere : ⟦ lower-skel ⟧ → Sphere (S n)
    cw-squash-lower-to-Sphere = Attached-rec (λ _ → north) squash-hubs squash-spokes where
      -- squash cells except [lower]
      squash-hubs : lower-cells → Sphere (S n)
      squash-hubs c with lower-cells-has-dec-eq c lower
      ... | (inl _) = south
      ... | (inr _) = north
      -- squash cells except [lower]
      squash-spokes : (c : lower-cells) → Sphere n
        → north == squash-hubs c
      squash-spokes c s with lower-cells-has-dec-eq c lower
      ... | (inl _) = merid s
      ... | (inr _) = idp

    degree-map : Sphere (S n) → Sphere (S n)
    degree-map = cw-squash-lower-to-Sphere ∘ attaching-last skel upper

    degree-map' : ℤ-group →ᴳ ℤ-group
    degree-map' = –>ᴳ (πS-SphereS-iso-ℤ n)
               ∘ᴳ Trunc-rec →ᴳ-level (πS-fmap n)
                    (⊙SphereS-endo-in n [ degree-map ])
               ∘ᴳ <–ᴳ (πS-SphereS-iso-ℤ n)

    degree' : ℤ → ℤ
    degree' = GroupHom.f degree-map'

    degree : ℤ
    degree = degree' 1

  module DegreeAtOne (skel : Skeleton {i} 1)
    (dec : has-cells-with-dec-eq skel)
    -- the cells at the upper and lower dimensions
    (line : cells-last skel)
    (point : cells-last (cw-init skel)) where

    private
      points-dec-eq = cells-nth-has-dec-eq (inr ltS) skel dec
      endpoint = attaching-last skel

    -- Maybe [true] can or should be mapped to [-1]. Not sure.
    degree : ℤ
    degree with points-dec-eq (endpoint line true) point
    degree | inl _ = 1
    degree | inr _ with points-dec-eq (endpoint line false) point
    degree | inr _ | inl _ = -1
    degree | inr _ | inr _ = 0

  degree-last : ∀ {n} (skel : Skeleton {i} (S n))
    → has-cells-with-dec-eq skel
    → cells-last skel → cells-last (cw-init skel) → ℤ
  degree-last {n = O} = DegreeAtOne.degree
  degree-last {n = S _} = DegreeAboveOne.degree

  degree-nth : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n)
    → has-cells-with-dec-eq skel
    → cells-nth Sm≤n skel → cells-last (cw-init (cw-take Sm≤n skel)) → ℤ
  degree-nth Sm≤n skel dec = degree-last (cw-take Sm≤n skel) (take-has-cells-with-dec-eq Sm≤n skel dec)

  has-degrees-with-finite-supports : ∀ {n} (skel : Skeleton {i} n)
    → has-cells-with-dec-eq skel → Type i
  has-degrees-with-finite-supports {n = O} _ _ = Lift ⊤
  has-degrees-with-finite-supports {n = S n} skel dec =
    has-degrees-with-finite-supports (cw-init skel) (init-has-cells-with-dec-eq skel dec) ×
    ∀ upper → has-finite-supports (cells-nth-has-dec-eq (inr ltS) skel dec) (degree-last skel dec upper)

  init-has-degrees-with-finite-supports : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-supports skel dec
    → has-degrees-with-finite-supports (cw-init skel) (init-has-cells-with-dec-eq skel dec)
  init-has-degrees-with-finite-supports skel dec fin-sup = fst fin-sup

  take-has-degrees-with-finite-supports : ∀ {m n} (m≤n : m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → has-degrees-with-finite-supports (cw-take m≤n skel) (take-has-cells-with-dec-eq m≤n skel dec)
  take-has-degrees-with-finite-supports (inl idp) skel dec fin-sup = fin-sup
  take-has-degrees-with-finite-supports (inr ltS) skel dec fin-sup =
    init-has-degrees-with-finite-supports skel dec fin-sup
  take-has-degrees-with-finite-supports (inr (ltSR lt)) skel dec fin-sup =
    take-has-degrees-with-finite-supports (inr lt) (cw-init skel)
      (init-has-cells-with-dec-eq skel dec)
      (init-has-degrees-with-finite-supports skel dec fin-sup)

  degree-last-has-finite-supports : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-supports skel dec
    → ∀ upper → has-finite-supports
        (cells-last-has-dec-eq (cw-init skel) (init-has-cells-with-dec-eq skel dec))
        (degree-last skel dec upper)
  degree-last-has-finite-supports skel dec fin-supp = snd fin-supp

  degree-nth-has-finite-supports : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → ∀ upper → has-finite-supports
        (cells-last-has-dec-eq
          (cw-init (cw-take Sm≤n skel))
          (init-has-cells-with-dec-eq (cw-take Sm≤n skel) (take-has-cells-with-dec-eq Sm≤n skel dec)))
        (degree-nth Sm≤n skel dec upper)
  degree-nth-has-finite-supports Sm≤n skel dec fin-supp =
    degree-last-has-finite-supports (cw-take Sm≤n skel)
      (take-has-cells-with-dec-eq Sm≤n skel dec)
      (take-has-degrees-with-finite-supports Sm≤n skel dec fin-supp)

  -- the following are named [boundary'] because it is not extended to the free groups

  boundary'-last : ∀ {n} (skel : Skeleton {i} (S n)) dec
    → has-degrees-with-finite-supports skel dec
    → cells-last skel → FreeAbGroup.El (cells-last (cw-init skel))
  boundary'-last skel dec fin-supp upper = fst ((snd fin-supp) upper)

  boundary'-nth : ∀ {m n} (Sm≤n : S m ≤ n) (skel : Skeleton {i} n) dec
    → has-degrees-with-finite-supports skel dec
    → cells-nth Sm≤n skel → FreeAbGroup.El (cells-last (cw-init (cw-take Sm≤n skel)))
  boundary'-nth Sm≤n skel dec fin-supp =
    boundary'-last (cw-take Sm≤n skel)
      (take-has-cells-with-dec-eq Sm≤n skel dec)
      (take-has-degrees-with-finite-supports Sm≤n skel dec fin-supp)
