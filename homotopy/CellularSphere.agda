{-# OPTIONS --without-K --termination-depth=2 #-}

open import HoTT
open import homotopy.CellComplex

module homotopy.CellularSphere where

CWSphere-skel : ∀ {i} n → Skeleton {i} n

CWSphere : ∀ {i} n → Type i
CWSphere n = ⟦ CWSphere-skel n ⟧

Sphere⇒CWSphere : ∀ {i} n → Sphere {i} n → CWSphere {i} n

CWSphere-skel {i} O = Lift {j = i} Bool
CWSphere-skel {i} (S n) =
  (CWSphere-skel n , Lift {j = i} Bool , Sphere⇒CWSphere {i} n ∘ snd)

private
  module PosToCW i n = SuspensionRec
    (Sphere {i} n)
    {C = CWSphere {i} (S n)}
    (left (lift true)) (left (lift false))
    (λ x → glue (lift true , x) ∙ (! (glue (lift false , x))))

Sphere⇒CWSphere O = idf _
Sphere⇒CWSphere {i} (S n) = PosToCW.f i n

{-
  Now proving the equivalence
-}

private
  CWSphere⇒Sphere-left : ∀ {i} n → Lift {j = i} Bool → Sphere {i} (S n)
  CWSphere⇒Sphere-left _ (lift true) = north _
  CWSphere⇒Sphere-left _ (lift false) = south _

  CWSphere⇒Sphere-right : ∀ {i} n → CWSphere {i} n → Sphere {i} (S n)
  CWSphere⇒Sphere-right _ _ = south _

  CWSphere⇒Sphere-glue : ∀ {i} n (bs : Lift Bool × Sphere {i} n)
    →  CWSphere⇒Sphere-left n (fst bs)
    == CWSphere⇒Sphere-right n (Sphere⇒CWSphere n (snd bs))
  CWSphere⇒Sphere-glue _ (lift true , x) = merid _ x
  CWSphere⇒Sphere-glue _ (lift false , _) = idp

  module PosFromCW i n = PushoutRec
    {d = attach-span n (Sphere⇒CWSphere {i} n ∘ snd)}
    (CWSphere⇒Sphere-left {i} n)
    (CWSphere⇒Sphere-right {i} n)
    (CWSphere⇒Sphere-glue {i} n)

CWSphere⇒Sphere : ∀ {i} n → CWSphere {i} n → Sphere {i} n
CWSphere⇒Sphere O = idf _
CWSphere⇒Sphere {i} (S n) = PosFromCW.f i n

private
  from-to : ∀ {i} n x → CWSphere⇒Sphere {i} n (Sphere⇒CWSphere {i} n x) == x
from-to O _ = idp
from-to {i} (S n) = SuspensionElim.f _ idp idp path
  where
    to = Sphere⇒CWSphere {i} (S n)
    from = CWSphere⇒Sphere {i} (S n)
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
      ap from (glue (lift true , x) ∙ (! (glue (lift false , x))))
        =⟨ ap-∙ from (glue (lift true , x)) (! (glue (lift false , x))) ⟩
      ap from (glue (lift true , x)) ∙ ap from (! (glue (lift false , x)))
        =⟨ ap-! from (glue (lift false , x)) |in-ctx (λ p → ap from (glue (lift true , x)) ∙ p) ⟩
      ap from (glue (lift true , x)) ∙ ! (ap from (glue (lift false , x)))
        =⟨ From.glue-β (lift false , x) |in-ctx ( λ p → ap from (glue (lift true , x)) ∙ ! p) ⟩
      ap from (glue (lift true , x)) ∙ idp
        =⟨ ∙-unit-r $ ap from (glue (lift true , x)) ⟩
      ap from (glue (lift true , x))
        =⟨ From.glue-β (lift true , x) ⟩
      merid _ x
        =⟨ ! $ ∙'-unit-l $ merid _ x ⟩
      idp ∙' merid _ x
        ∎

Sphere⇒CWSphere-is-equiv : ∀ {i} n → is-equiv (Sphere⇒CWSphere {i} n)
private
  to-from : ∀ {i} n x → Sphere⇒CWSphere {i} n (CWSphere⇒Sphere {i} n x) == x
Sphere⇒CWSphere-is-equiv {i} n = is-eq _ (CWSphere⇒Sphere {i} n) (to-from {i} n) (from-to {i} n)

to-from O _ = idp
to-from {i} (S n) = PushoutElim.f to-from-left to-from-right to-from-glue
  where
    to = Sphere⇒CWSphere {i} (S n)
    from = CWSphere⇒Sphere {i} (S n)
    module To = PosToCW i n
    module From = PosFromCW i n

    to-from-left : ∀ b → to (from (left b)) == left b
    to-from-left (lift true) = idp
    to-from-left (lift false) = idp

    to-from-right : ∀ (c : CWSphere {i} n)
      → to (from (right c)) == right c
    to-from-right c =
        glue (lift false , CWSphere⇒Sphere n c)
      ∙ ap right (is-equiv.f-g (Sphere⇒CWSphere-is-equiv n) c)

    to-from-right-to : ∀ (x : Sphere {i} n)
      → to-from-right (Sphere⇒CWSphere n x) == glue (lift false , x)
    to-from-right-to x =
      glue (lift false , CWSphere⇒Sphere n (Sphere⇒CWSphere n x))
        ∙ ap right (is-equiv.f-g (Sphere⇒CWSphere-is-equiv n) (Sphere⇒CWSphere n x))
          =⟨ ! $ is-equiv.adj (Sphere⇒CWSphere-is-equiv n) x
            |in-ctx (λ p → glue (lift false , CWSphere⇒Sphere n (Sphere⇒CWSphere n x)) ∙ ap right p) ⟩
      glue (lift false , CWSphere⇒Sphere n (Sphere⇒CWSphere n x))
        ∙ ap right (ap (Sphere⇒CWSphere n) (is-equiv.g-f (Sphere⇒CWSphere-is-equiv n) x))
          =⟨ ! $ ap-∘ right (Sphere⇒CWSphere n) (is-equiv.g-f (Sphere⇒CWSphere-is-equiv n) x)
            |in-ctx (λ p → glue (lift false , CWSphere⇒Sphere n (Sphere⇒CWSphere n x)) ∙ p) ⟩
      glue (lift false , CWSphere⇒Sphere n (Sphere⇒CWSphere n x))
        ∙ ap (right ∘ Sphere⇒CWSphere n) (is-equiv.g-f (Sphere⇒CWSphere-is-equiv n) x)
          =⟨ htpy-natural-fromcst (λ x → glue (lift false , x)) (is-equiv.g-f (Sphere⇒CWSphere-is-equiv n) x) ⟩
      glue (lift false , x)
          ∎

    to-from-glue : ∀ (bs : Lift Bool × Sphere {i} n)
      → to-from-left (fst bs) == to-from-right (Sphere⇒CWSphere n (snd bs))
          [ (λ x → to (from x) == x) ↓ glue bs ]
    to-from-glue (lift true , x) = ↓-app=idf-in $ ! $
      ap (to ∘ from) (glue (lift true , x)) ∙ to-from-right (Sphere⇒CWSphere n x)
        =⟨ to-from-right-to x |in-ctx (λ p → ap (to ∘ from) (glue (lift true , x)) ∙ p) ⟩
      ap (to ∘ from) (glue (lift true , x)) ∙ glue (lift false , x)
        =⟨ ap-∘ to from (glue (lift true , x)) |in-ctx (λ p → p ∙ glue (lift false , x)) ⟩
      ap to (ap from (glue (lift true , x))) ∙ glue (lift false , x)
        =⟨ From.glue-β (lift true , x) |in-ctx (λ p → ap to p ∙ glue (lift false , x)) ⟩
      ap to (merid _ x) ∙ glue (lift false , x)
        =⟨ To.merid-β x |in-ctx (λ p → p ∙ glue (lift false , x)) ⟩
      (glue (lift true , x) ∙ (! (glue (lift false , x)))) ∙ glue (lift false , x)
        =⟨ ∙-assoc (glue (lift true , x)) (! (glue (lift false , x))) (glue (lift false , x)) ⟩
      glue (lift true , x) ∙ ((! (glue (lift false , x))) ∙ glue (lift false , x))
        =⟨ !-inv-l (glue (lift false , x)) |in-ctx (λ p → glue (lift true , x) ∙ p) ⟩
      glue (lift true , x) ∙ idp
        =⟨ ∙-unit-r (glue (lift true , x)) ⟩
      glue (lift true , x)
        =⟨ ! $ ∙'-unit-l (glue (lift true , x)) ⟩
      idp ∙' glue (lift true , x)
        ∎
    to-from-glue (lift false , x) = ↓-app=idf-in $ ! $
      ap (to ∘ from) (glue (lift false , x)) ∙ to-from-right (Sphere⇒CWSphere n x)
        =⟨ to-from-right-to x |in-ctx (λ p → ap (to ∘ from) (glue (lift false , x)) ∙ p) ⟩
      ap (to ∘ from) (glue (lift false , x)) ∙ glue (lift false , x)
        =⟨ ap-∘ to from (glue (lift false , x)) |in-ctx (λ p → p ∙ glue (lift false , x)) ⟩
      ap to (ap from (glue (lift false , x))) ∙ glue (lift false , x)
        =⟨ From.glue-β (lift false , x) |in-ctx (λ p → ap to p ∙ glue (lift false , x)) ⟩
      glue (lift false , x)
        =⟨ ! $ ∙'-unit-l (glue (lift false , x)) ⟩
      idp ∙' glue (lift false , x)
        ∎

