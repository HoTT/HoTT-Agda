{-# OPTIONS --without-K --termination-depth=2 #-}

open import HoTT
open import cw.CW

module cw.Sphere where

CWSphere-skel : ∀ n → Skeleton {lzero} n

CWSphere : ℕ → Type₀
CWSphere n = ⟦ CWSphere-skel n ⟧

Sphere-to-CWSphere : (n : ℕ) → Sphere n → CWSphere n

CWSphere-skel O = Bool
CWSphere-skel (S n) =
  (CWSphere-skel n , Bool , cst (Sphere-to-CWSphere n))

{-
  mapping:

  hub true <-> north
  hub false <-> south
  incl _ -> north
  spoke true x -> idp
  spoke fales x -> merid x
  ! spoke true x ∙ spoke false x  <- merid x
-}


private
  module PosToCW n = SuspensionRec
    {C = CWSphere (S n)}
    (hub true) (hub false)
    (λ x → (! (spoke true x)) ∙' spoke false x)

Sphere-to-CWSphere O = idf _
Sphere-to-CWSphere (S n) = PosToCW.f n

{-
  Now proving the equivalence
-}

private
  CWSphere-to-Sphere-incl : ∀ n → CWSphere n → Sphere (S n)
  CWSphere-to-Sphere-incl _ _ = north

  CWSphere-to-Sphere-hub : ∀ n → Bool → Sphere (S n)
  CWSphere-to-Sphere-hub _ true = north
  CWSphere-to-Sphere-hub _ false = south

  CWSphere-to-Sphere-spoke : ∀ n (b : Bool) (x : Sphere n)
    → CWSphere-to-Sphere-incl n (Sphere-to-CWSphere n x)
    == CWSphere-to-Sphere-hub n b
  CWSphere-to-Sphere-spoke _ true _ = idp
  CWSphere-to-Sphere-spoke _ false x = merid x

  module PosFromCW n = AttachRec
    {boundary = cst (Sphere-to-CWSphere n)}
    (CWSphere-to-Sphere-incl n)
    (CWSphere-to-Sphere-hub n)
    (CWSphere-to-Sphere-spoke n)

CWSphere-to-Sphere : ∀ n → CWSphere n → Sphere n
CWSphere-to-Sphere O = idf _
CWSphere-to-Sphere (S n) = PosFromCW.f n

private
  from-to : ∀ n x → CWSphere-to-Sphere n (Sphere-to-CWSphere n x) == x
from-to O _ = idp
from-to (S n) = SuspensionElim.f idp idp path
  where
    to = Sphere-to-CWSphere (S n)
    from = CWSphere-to-Sphere (S n)
    module To = PosToCW n
    module From = PosFromCW n

    path : ∀ x → idp == idp [ (λ x → from (to x) == x) ↓ merid x ]
    path x = ↓-app=idf-in $ ! $
      ap (from ∘ to) (merid x) ∙ idp
        =⟨ ∙-unit-r $ ap (from ∘ to) (merid x) ⟩
      ap (from ∘ to) (merid x)
        =⟨ ap-∘ from to (merid x) ⟩
      ap from (ap to (merid x))
        =⟨ To.merid-β x |in-ctx ap from ⟩
      ap from (! (spoke true x) ∙' spoke false x)
        =⟨ ap-∙' from (! (spoke true x)) (spoke false x) ⟩
      ap from (! (spoke true x)) ∙' ap from (spoke false x)
        =⟨ ap-! from (spoke true x) |in-ctx (λ p → p ∙' ap from (spoke false x)) ⟩
      ! (ap from (spoke true x)) ∙' ap from (spoke false x)
        =⟨ From.spoke-β true x |in-ctx (λ p → ! p ∙' ap from (spoke false x)) ⟩
      idp ∙' ap from (spoke false x)
        =⟨ From.spoke-β false x |in-ctx (idp ∙'_) ⟩
      idp ∙' merid x
        ∎

Sphere-to-CWSphere-is-equiv : ∀ n → is-equiv (Sphere-to-CWSphere n)
private
  to-from : ∀ n x → Sphere-to-CWSphere n (CWSphere-to-Sphere n x) == x
Sphere-to-CWSphere-is-equiv n = is-eq _ (CWSphere-to-Sphere n) (to-from n) (from-to n)

to-from O _ = idp
to-from (S n) = AttachElim.f to-from-incl to-from-hub to-from-spoke
  where
    to = Sphere-to-CWSphere (S n)
    from = CWSphere-to-Sphere (S n)
    module To = PosToCW n
    module From = PosFromCW n

    to-from-incl : ∀ (c : CWSphere n)
      → to (from (incl c)) == incl c
    to-from-incl c =
        ! (spoke true (CWSphere-to-Sphere n c))
      ∙ ap incl (is-equiv.f-g (Sphere-to-CWSphere-is-equiv n) c)

    to-from-hub : ∀ b → to (from (hub b)) == hub b
    to-from-hub true = idp
    to-from-hub false = idp

    to-from-incl-to : ∀ (x : Sphere n)
      → to-from-incl (Sphere-to-CWSphere n x) == ! (spoke true x)
    to-from-incl-to x =
      ! (spoke true (CWSphere-to-Sphere n (Sphere-to-CWSphere n x)))
      ∙ ap incl (is-equiv.f-g (Sphere-to-CWSphere-is-equiv n) (Sphere-to-CWSphere n x))
        =⟨ ! $ is-equiv.adj (Sphere-to-CWSphere-is-equiv n) x
          |in-ctx (λ p → ! (spoke true (CWSphere-to-Sphere n (Sphere-to-CWSphere n x))) ∙ ap incl p) ⟩
      ! (spoke true (CWSphere-to-Sphere n (Sphere-to-CWSphere n x)))
      ∙ ap incl (ap (Sphere-to-CWSphere n) (is-equiv.g-f (Sphere-to-CWSphere-is-equiv n) x))
        =⟨ ! $ ap-∘ incl (Sphere-to-CWSphere n) (is-equiv.g-f (Sphere-to-CWSphere-is-equiv n) x)
          |in-ctx (λ p → ! (spoke true (CWSphere-to-Sphere n (Sphere-to-CWSphere n x))) ∙ p) ⟩
      ! (spoke true (CWSphere-to-Sphere n (Sphere-to-CWSphere n x)))
      ∙ ap (incl ∘ Sphere-to-CWSphere n) (is-equiv.g-f (Sphere-to-CWSphere-is-equiv n) x)
          =⟨ htpy-natural-cst=app (λ x → ! (spoke true x)) (is-equiv.g-f (Sphere-to-CWSphere-is-equiv n) x) ⟩
      ! (spoke true x)
          ∎

    to-from-spoke : ∀ (b : Bool) (x : Sphere n)
      → to-from-incl (Sphere-to-CWSphere n x) == to-from-hub b
          [ (λ x → to (from x) == x) ↓ spoke b x ]
    to-from-spoke true x = ↓-app=idf-in $
      to-from-incl (Sphere-to-CWSphere n x) ∙' spoke true x
        =⟨ to-from-incl-to x |in-ctx (λ p → p ∙' spoke true x) ⟩
      ! (spoke true x) ∙' spoke true x
        =⟨ !-inv'-l (spoke true x) ⟩
      idp
        =⟨ ! $ From.spoke-β true x |in-ctx (λ p → ap to p ∙ idp) ⟩
      ap to (ap from (spoke true x)) ∙ idp
        =⟨ ∘-ap to from (spoke true x) |in-ctx (λ p → p ∙ idp) ⟩
      ap (to ∘ from) (spoke true x) ∙ idp
        ∎
    to-from-spoke false x = ↓-app=idf-in $
      to-from-incl (Sphere-to-CWSphere n x) ∙' spoke false x
        =⟨ to-from-incl-to x |in-ctx (λ p → p ∙' spoke false x) ⟩
      ! (spoke true x) ∙' spoke false x
        =⟨ ! $ To.merid-β x ⟩
      ap to (merid x)
        =⟨ ! $ From.spoke-β false x |in-ctx (ap to) ⟩
      ap to (ap from (spoke false x))
        =⟨ ∘-ap to from (spoke false x) ⟩
      ap (to ∘ from) (spoke false x)
        =⟨ ! $ ∙-unit-r _ ⟩
      ap (to ∘ from) (spoke false x) ∙ idp
        ∎

Sphere-to-CWSphere-equiv : ∀ n → Sphere n ≃ CWSphere n
Sphere-to-CWSphere-equiv n = _ , Sphere-to-CWSphere-is-equiv n
