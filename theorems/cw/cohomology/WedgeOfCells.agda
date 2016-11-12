{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import homotopy.PushoutSplit
open import homotopy.DisjointlyPointedSet
open import cw.CW

module cw.cohomology.WedgeOfCells {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
private
  G = C 0 (⊙Lift ⊙Bool)
open import cohomology.Sphere OT
open import cohomology.DisjointlyPointedSet OT

{- This is for the zeroth dimension. -}

C-points : ∀ n (⊙skel : ⊙Skeleton {i} 0)
  → ⊙has-cells-with-choice 0 ⊙skel i
  →  C n (⊙cw-head ⊙skel)
  ≃ᴳ Πᴳ (MinusPoint (⊙cw-head ⊙skel)) (λ _ → C n (⊙Lift ⊙Bool))
C-points n (⊙skeleton pts pt dec) ac = C-set n ⊙[ fst pts , pt ] (snd pts) dec ac

abstract
  C-points-≠-is-trivial : ∀ (n : ℤ) (n≠0 : n ≠ 0) (⊙skel : ⊙Skeleton {i} 0)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (C n (⊙cw-head ⊙skel))
  C-points-≠-is-trivial n n≠0 ⊙skel ac =
    iso-preserves'-trivial (C-points n ⊙skel ac) $
      Πᴳ-is-trivial (MinusPoint (⊙cw-head ⊙skel))
        (λ _ → C n (⊙Lift ⊙Bool))
        (λ _ → C-dimension n≠0)

{- This is for higher dimensions. -}

{- the equivalence is in the opposite direction because
   cohomology functors are contravariant. -}
⊙Cofiber-cw-incl-last : ∀ {n} (⊙skel : ⊙Skeleton {i} (S n))
  →  ⊙BigWedge {A = ⊙cells-last ⊙skel} (λ _ → ⊙Sphere (S n))
  ⊙≃ ⊙Cofiber (⊙cw-incl-last ⊙skel)
⊙Cofiber-cw-incl-last {n} ⊙skel = ≃-to-⊙≃
  (PS.split-equiv ∘e equiv to from to-from from-to) idp
  where
    open AttachedSkeleton (⊙Skeleton.skel ⊙skel)

    module PS = PushoutLSplit (uncurry attaching) (λ _ → tt) fst

    module SphereToCofiber (a : fst cells) = SuspRec {A = Sphere n}
      (cfbase' (fst :> (fst cells × Sphere n → fst cells)))
      (cfcod a) (λ s → cfglue (a , s))

    module To = BigWedgeRec {A = fst cells} {X = λ _ → ⊙Sphere (S n)}
      cfbase SphereToCofiber.f (λ _ → idp)
    to = To.f

    module From = CofiberRec {f = fst :> (fst cells × Sphere n → fst cells)}
      (bwbase {A = fst cells} {X = λ _ → ⊙Sphere (S n)})
      (λ a → bwin a south) (λ{(a , s) → bwglue a ∙ ap (bwin a) (merid s)})
    from = From.f

    from-to : ∀ b → from (to b) == b
    from-to = BigWedge-elim
      idp
      (λ a → Susp-elim (bwglue a) idp
        (λ s → ↓-='-from-square
          {f = from ∘ SphereToCofiber.f a} {p = merid s} $
          ( ap-∘ from (SphereToCofiber.f a) (merid s)
          ∙ ap (ap from) (SphereToCofiber.merid-β a s)
          ∙ From.glue-β (a , s))
          ∙v⊡ (tl-square (bwglue a) ⊡h vid-square)))
      (λ a → ↓-∘=idf-from-square from to {p = bwglue a} $
        ap (ap from) (To.glue-β a) ∙v⊡ br-square (bwglue a))

    to-from : ∀ c → to (from c) == c
    to-from = Cofiber-elim
      idp (λ a → idp)
      (λ{(a , s) → ↓-∘=idf-in' to from {p = glue (a , s)} $
          ap (ap to) (From.glue-β (a , s))
        ∙ ap-∙ to (bwglue a) (ap (bwin a) (merid s))
        ∙ ap2 _∙_ (To.glue-β a)
                  ( ∘-ap to (bwin a) (merid s)
                  ∙ SphereToCofiber.merid-β a s)})

C-Cofiber-cw-incl-last : ∀ n {m} (⊙skel : ⊙Skeleton {i} (S m))
  → ⊙has-cells-with-choice 0 ⊙skel i
  →  C n (⊙Cofiber (⊙cw-incl-last ⊙skel))
  ≃ᴳ Πᴳ (⊙cells-last ⊙skel) (λ _ → C n (⊙Lift (⊙Sphere (S m))))
C-Cofiber-cw-incl-last n {m} skel (_ , cells-ac)
  =   C-additive-iso n (λ _ → ⊙Lift (⊙Sphere (S m))) cells-ac
  ∘eᴳ C-emap n (   ⊙Cofiber-cw-incl-last skel
               ⊙∘e ⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))

C-Cofiber-cw-incl-last-diag : ∀ n (⊙skel : ⊙Skeleton {i} (S n))
  → ⊙has-cells-with-choice 0 ⊙skel i
  →  C (ℕ-to-ℤ (S n)) (⊙Cofiber (⊙cw-incl-last ⊙skel))
  ≃ᴳ Πᴳ (⊙cells-last ⊙skel) (λ _ → G)
C-Cofiber-cw-incl-last-diag n ⊙skel ac =
      Πᴳ-emap-r (⊙cells-last ⊙skel) (λ _ → C-Sphere-diag (S n))
  ∘eᴳ C-Cofiber-cw-incl-last (ℕ-to-ℤ (S n)) ⊙skel ac

abstract
  C-Cofiber-cw-incl-last-≠-is-trivial : ∀ (n : ℤ) {m} (n≠Sm : n ≠ ℕ-to-ℤ (S m))
    → (⊙skel : ⊙Skeleton {i} (S m))
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (C n (⊙Cofiber (⊙cw-incl-last ⊙skel)))
  C-Cofiber-cw-incl-last-≠-is-trivial n {m} n≠Sm ⊙skel ac =
    iso-preserves'-trivial (C-Cofiber-cw-incl-last n ⊙skel ac) $
      Πᴳ-is-trivial (⊙cells-last ⊙skel)
        (λ _ → C n (⊙Lift (⊙Sphere (S m))))
        (λ _ → C-Sphere-≠-is-trivial n (S m) n≠Sm)

  C-Cofiber-cw-incl-last-<-is-trivial : ∀ (n : ℕ) {m} (n<Sm : n < S m)
    → (⊙skel : ⊙Skeleton {i} (S m))
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (C (ℕ-to-ℤ n) (⊙Cofiber (⊙cw-incl-last ⊙skel)))
  C-Cofiber-cw-incl-last-<-is-trivial n n<Sm ⊙skel ac =
    C-Cofiber-cw-incl-last-≠-is-trivial (ℕ-to-ℤ n) (ℕ-to-ℤ-≠ (<-to-≠ n<Sm)) ⊙skel ac

  C-Cofiber-cw-incl-last->-is-trivial : ∀ (n : ℕ) {m} (n>Sm : S m < n)
    → (⊙skel : ⊙Skeleton {i} (S m))
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (C (ℕ-to-ℤ n) (⊙Cofiber (⊙cw-incl-last ⊙skel)))
  C-Cofiber-cw-incl-last->-is-trivial n n>Sm ⊙skel ac =
    C-Cofiber-cw-incl-last-≠-is-trivial (ℕ-to-ℤ n) (≠-inv (ℕ-to-ℤ-≠ (<-to-≠ n>Sm))) ⊙skel ac
