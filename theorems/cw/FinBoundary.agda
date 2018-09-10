{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import homotopy.SphereEndomorphism
open import groups.SphereEndomorphism
open import groups.CoefficientExtensionality
open import cw.CW
open import cw.FinCW
open import cw.WedgeOfCells
open import cw.DegreeByProjection {lzero}

module cw.FinBoundary where

  open FreeAbelianGroup

  fdegree-last : ∀ {n} (fin-skel : FinSkeleton (S n))
    → cells-last (FinSkeleton-realize fin-skel)
    → cells-last (cw-init (FinSkeleton-realize fin-skel)) → ℤ
  fdegree-last fin-skel = degree-last (FinSkeleton-realize fin-skel) (FinSkeleton-has-cells-with-dec-eq fin-skel)

  fdegree-nth : ∀ {m n} (Sm≤n : S m ≤ n) (fin-skel : FinSkeleton n)
    → cells-nth Sm≤n (FinSkeleton-realize fin-skel)
    → cells-last (cw-init (cw-take Sm≤n (FinSkeleton-realize fin-skel))) → ℤ
  fdegree-nth Sm≤n fin-skel = degree-nth Sm≤n (FinSkeleton-realize fin-skel) (FinSkeleton-has-cells-with-dec-eq fin-skel)

  FinSkeleton-has-degrees-with-finite-support : ∀ {n} (fin-skel : FinSkeleton n)
    → has-degrees-with-finite-support
        (FinSkeleton-realize fin-skel)
        (FinSkeleton-has-cells-with-dec-eq fin-skel)
  FinSkeleton-has-degrees-with-finite-support {n = O} _ = _
  FinSkeleton-has-degrees-with-finite-support {n = S O} _ = _ , (λ _ → Fin→-has-finite-support _)
  FinSkeleton-has-degrees-with-finite-support {n = S (S n)} (attached-fin-skeleton skel _ _) =
    FinSkeleton-has-degrees-with-finite-support {n = S n} skel , (λ _ → Fin→-has-finite-support _)

  fboundary'-last : ∀ {n} (fin-skel : FinSkeleton (S n))
    → cells-last (FinSkeleton-realize fin-skel)
    → FreeAbelianGroup.El (cells-last (cw-init (FinSkeleton-realize fin-skel)))
  fboundary'-last fin-skel upper = boundary'-last
    (FinSkeleton-realize fin-skel)
    (FinSkeleton-has-cells-with-dec-eq fin-skel)
    (FinSkeleton-has-degrees-with-finite-support fin-skel)
    upper

  fboundary-last : ∀ {n} (fin-skel : FinSkeleton (S n))
    →  FreeAbGroup.grp (cells-last (FinSkeleton-realize fin-skel))
    →ᴳ FreeAbGroup.grp (cells-last (cw-init (FinSkeleton-realize fin-skel)))
  fboundary-last fin-skel = Freeness.extend _
    (FreeAbGroup (cells-last (cw-init (FinSkeleton-realize fin-skel))))
    (fboundary'-last fin-skel)
