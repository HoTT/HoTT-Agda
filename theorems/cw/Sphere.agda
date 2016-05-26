{-# OPTIONS --without-K --termination-depth=2 #-}

open import HoTT
open import cw.CW

module cw.Sphere where

CWSphere-skel : ∀ {i} n → Skeleton {i} n

CWSphere : ∀ {i} n → Type i
CWSphere n = ⟦ CWSphere-skel n ⟧

Sphere→CWSphere : ∀ {i} n → Sphere {i} n → CWSphere {i} n

CWSphere-skel {i} O = Lift Bool
CWSphere-skel {i} (S n) =
  (CWSphere-skel n , Lift Bool , cst (Sphere→CWSphere {i} n))

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
  module PosToCW i n = SuspensionRec
    (Sphere {i} n)
    {C = CWSphere {i} (S n)}
    (hub (lift true)) (hub (lift false))
    (λ x → (! (spoke (lift true) x)) ∙' spoke (lift false) x)

Sphere→CWSphere O = idf _
Sphere→CWSphere {i} (S n) = PosToCW.f i n

{-
  Now proving the equivalence
-}

private
  CWSphere→Sphere-incl : ∀ {i} n → CWSphere {i} n → Sphere {i} (S n)
  CWSphere→Sphere-incl _ _ = north _

  CWSphere→Sphere-hub : ∀ {i} n → Lift {j = i} Bool → Sphere {i} (S n)
  CWSphere→Sphere-hub _ (lift true) = north _
  CWSphere→Sphere-hub _ (lift false) = south _

  CWSphere→Sphere-spoke : ∀ {i} n (b : Lift Bool) (x : Sphere {i} n)
    → CWSphere→Sphere-incl n (Sphere→CWSphere n x)
    == CWSphere→Sphere-hub n b
  CWSphere→Sphere-spoke _ (lift true) _ = idp
  CWSphere→Sphere-spoke _ (lift false) x = merid _ x

  module PosFromCW i n = AttachRec
    {boundary = cst (Sphere→CWSphere {i} n)}
    (CWSphere→Sphere-incl {i} n)
    (CWSphere→Sphere-hub {i} n)
    (CWSphere→Sphere-spoke {i} n)

CWSphere→Sphere : ∀ {i} n → CWSphere {i} n → Sphere {i} n
CWSphere→Sphere O = idf _
CWSphere→Sphere {i} (S n) = PosFromCW.f i n

private
  from-to : ∀ {i} n x → CWSphere→Sphere {i} n (Sphere→CWSphere {i} n x) == x
from-to O _ = idp
from-to {i} (S n) = SuspensionElim.f _ idp idp path
  where
    to = Sphere→CWSphere {i} (S n)
    from = CWSphere→Sphere {i} (S n)
    module To = PosToCW i n
    module From = PosFromCW i n

    path : ∀ x → idp == idp [ (λ x → from (to x) == x) ↓ merid _ x ]
    path x = ↓-app=idf-in $ ! $
      ap (from ∘ to) (merid _ x) ∙ idp
        =⟨ ∙-unit-r $ ap (from ∘ to) (merid _ x) ⟩
      ap (from ∘ to) (merid _ x)
        =⟨ ap-∘ from to (merid _ x) ⟩
      ap from (ap to (merid _ x))
        =⟨ To.merid-β x |in-ctx ap from ⟩
      ap from (! (spoke (lift true) x) ∙' spoke (lift false) x)
        =⟨ ap-∙' from (! (spoke (lift true) x)) (spoke (lift false) x) ⟩
      ap from (! (spoke (lift true) x)) ∙' ap from (spoke (lift false) x)
        =⟨ ap-! from (spoke (lift true) x) |in-ctx (λ p → p ∙' ap from (spoke (lift false) x)) ⟩
      ! (ap from (spoke (lift true) x)) ∙' ap from (spoke (lift false) x)
        =⟨ From.spoke-β (lift true) x |in-ctx (λ p → ! p ∙' ap from (spoke (lift false) x)) ⟩
      idp ∙' ap from (spoke (lift false) x)
        =⟨ From.spoke-β (lift false) x |in-ctx (λ p → idp ∙' p) ⟩
      idp ∙' merid _ x
        ∎

Sphere→CWSphere-is-equiv : ∀ {i} n → is-equiv (Sphere→CWSphere {i} n)
private
  to-from : ∀ {i} n x → Sphere→CWSphere {i} n (CWSphere→Sphere {i} n x) == x
Sphere→CWSphere-is-equiv {i} n = is-eq _ (CWSphere→Sphere {i} n) (to-from {i} n) (from-to {i} n)

to-from O _ = idp
to-from {i} (S n) = AttachElim.f to-from-incl to-from-hub to-from-spoke
  where
    to = Sphere→CWSphere {i} (S n)
    from = CWSphere→Sphere {i} (S n)
    module To = PosToCW i n
    module From = PosFromCW i n

    to-from-incl : ∀ (c : CWSphere {i} n)
      → to (from (incl c)) == incl c
    to-from-incl c =
        ! (spoke (lift true) (CWSphere→Sphere n c))
      ∙ ap incl (is-equiv.f-g (Sphere→CWSphere-is-equiv n) c)

    to-from-hub : ∀ b → to (from (hub b)) == hub b
    to-from-hub (lift true) = idp
    to-from-hub (lift false) = idp

    to-from-incl-to : ∀ (x : Sphere {i} n)
      → to-from-incl (Sphere→CWSphere n x) == ! (spoke (lift true) x)
    to-from-incl-to x =
      ! (spoke (lift true) (CWSphere→Sphere n (Sphere→CWSphere n x)))
      ∙ ap incl (is-equiv.f-g (Sphere→CWSphere-is-equiv n) (Sphere→CWSphere n x))
        =⟨ ! $ is-equiv.adj (Sphere→CWSphere-is-equiv n) x
          |in-ctx (λ p → ! (spoke (lift true) (CWSphere→Sphere n (Sphere→CWSphere n x))) ∙ ap incl p) ⟩
      ! (spoke (lift true) (CWSphere→Sphere n (Sphere→CWSphere n x)))
      ∙ ap incl (ap (Sphere→CWSphere n) (is-equiv.g-f (Sphere→CWSphere-is-equiv n) x))
        =⟨ ! $ ap-∘ incl (Sphere→CWSphere n) (is-equiv.g-f (Sphere→CWSphere-is-equiv n) x)
          |in-ctx (λ p → ! (spoke (lift true) (CWSphere→Sphere n (Sphere→CWSphere n x))) ∙ p) ⟩
      ! (spoke (lift true) (CWSphere→Sphere n (Sphere→CWSphere n x)))
      ∙ ap (incl ∘ Sphere→CWSphere n) (is-equiv.g-f (Sphere→CWSphere-is-equiv n) x)
          =⟨ htpy-natural-fromcst (λ x → ! (spoke (lift true) x)) (is-equiv.g-f (Sphere→CWSphere-is-equiv n) x) ⟩
      ! (spoke (lift true) x)
          ∎

    to-from-spoke : ∀ (b : Lift Bool) (x : Sphere {i} n)
      → to-from-incl (Sphere→CWSphere n x) == to-from-hub b
          [ (λ x → to (from x) == x) ↓ spoke b x ]
    to-from-spoke (lift true) x = ↓-app=idf-in $
      to-from-incl (Sphere→CWSphere n x) ∙' spoke (lift true) x
        =⟨ to-from-incl-to x |in-ctx (λ p → p ∙' spoke (lift true) x) ⟩
      ! (spoke (lift true) x) ∙' spoke (lift true) x
        =⟨ !-inv'-l (spoke (lift true) x) ⟩
      idp
        =⟨ ! $ From.spoke-β (lift true) x |in-ctx (λ p → ap to p ∙ idp) ⟩
      ap to (ap from (spoke (lift true) x)) ∙ idp
        =⟨ ∘-ap to from (spoke (lift true) x) |in-ctx (λ p → p ∙ idp) ⟩
      ap (to ∘ from) (spoke (lift true) x) ∙ idp
        ∎
    to-from-spoke (lift false) x = ↓-app=idf-in $
      to-from-incl (Sphere→CWSphere n x) ∙' spoke (lift false) x
        =⟨ to-from-incl-to x |in-ctx (λ p → p ∙' spoke (lift false) x) ⟩
      ! (spoke (lift true) x) ∙' spoke (lift false) x
        =⟨ ! $ To.merid-β x ⟩
      ap to (merid _ x)
        =⟨ ! $ From.spoke-β (lift false) x |in-ctx (ap to) ⟩
      ap to (ap from (spoke (lift false) x))
        =⟨ ∘-ap to from (spoke (lift false) x) ⟩
      ap (to ∘ from) (spoke (lift false) x)
        =⟨ ! $ ∙-unit-r _ ⟩
      ap (to ∘ from) (spoke (lift false) x) ∙ idp
        ∎

Sphere≃CWSphere : ∀ {i} n → Sphere {i} n ≃ CWSphere {i} n
Sphere≃CWSphere n = _ , Sphere→CWSphere-is-equiv n
