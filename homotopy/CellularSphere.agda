{-# OPTIONS --without-K --termination-depth=2 #-}

open import HoTT
open import homotopy.CellComplex

module homotopy.CellularSphere where

CWSphere-skeleton : ∀ {i} n → Skeleton {i} n
CWSphere-equiv : ∀ {i} n → ⟦ CWSphere-skeleton {i} n ⟧ ≃ Sphere {i} n

CWSphere-skeleton O = Lift Bool
CWSphere-skeleton (S n) =
  (CWSphere-skeleton n , Lift Bool , <– (CWSphere-equiv n) ∘ snd)

CWSphere-equiv {i} O = ide $ Lift Bool
CWSphere-equiv {i} (S n) = equiv to from to-from from-to
  where
    to-left* : Lift Bool → Sphere {i} (S n)
    to-left* (lift true) = north _
    to-left* (lift false) = south _

    to-right* : ⟦ CWSphere-skeleton {i} n ⟧ → Sphere {i} (S n)
    to-right* _ = south _

    to-glue* : ∀ (bs : Lift Bool × Sphere {i} n)
      → to-left* (fst bs) == to-right* (<– (CWSphere-equiv n) (snd bs))
    to-glue* (lift true , x) = merid _ x
    to-glue* (lift false , _) = idp

    module To = PushoutRec
      {d = attach-span n (<– (CWSphere-equiv n) ∘ snd)}
      to-left* to-right* to-glue*

    to : ⟦ CWSphere-skeleton {i} (S n) ⟧ → Sphere {i} (S n)
    to = To.f

    module From = SuspensionRec _
        {C = ⟦ CWSphere-skeleton {i} (S n) ⟧}
        (left (lift true)) (left (lift false))
        (λ x → glue (lift true , x) ∙ (! (glue (lift false , x))))

    from : Sphere {i} (S n) → ⟦ CWSphere-skeleton {i} (S n) ⟧
    from = From.f

    to-from : ∀ x → to (from x) == x
    to-from = SuspensionElim.f _ idp idp path
      where
        path : ∀ x → idp == idp [ (λ x → to (from x) == x) ↓ merid _ x ]
        path x = ↓-app=idf-in $ ! $
          ap (to ∘ from) (merid _ x) ∙ idp
            =⟨ ∙-unit-r $ ap (to ∘ from) (merid _ x) ⟩
          ap (to ∘ from) (merid _ x)
            =⟨ ap-∘ to from (merid _ x) ⟩
          ap to (ap from (merid _ x))
            =⟨ From.merid-β x |in-ctx ap to ⟩
          ap to (glue (lift true , x) ∙ (! (glue (lift false , x))))
            =⟨ ap-∙ to (glue (lift true , x)) (! (glue (lift false , x))) ⟩
          ap to (glue (lift true , x)) ∙ ap to (! (glue (lift false , x)))
            =⟨ ap-! to (glue (lift false , x)) |in-ctx (λ p → ap to (glue (lift true , x)) ∙ p) ⟩
          ap to (glue (lift true , x)) ∙ ! (ap to (glue (lift false , x)))
            =⟨ To.glue-β (lift false , x) |in-ctx ( λ p → ap to (glue (lift true , x)) ∙ ! p) ⟩
          ap to (glue (lift true , x)) ∙ idp
            =⟨ ∙-unit-r $ ap to (glue (lift true , x)) ⟩
          ap to (glue (lift true , x))
            =⟨ To.glue-β (lift true , x) ⟩
          merid _ x
            =⟨ ! $ ∙'-unit-l $ merid _ x ⟩
          idp ∙' merid _ x
            ∎

    from-to : ∀ x → from (to x) == x
    from-to = PushoutElim.f from-to-left* from-to-right* from-to-glue*
      where
        from-to-left* : ∀ b → from (to (left b)) == left b
        from-to-left* (lift true) = idp
        from-to-left* (lift false) = idp

        from-to-right* : ∀ (c : ⟦ CWSphere-skeleton {i} n ⟧)
          → from (to (right c)) == right c
        from-to-right* c =
            glue (lift false , –> (CWSphere-equiv n) c)
          ∙ ap right (<–-inv-l (CWSphere-equiv n) c)

        from-to-right*-inv : ∀ (x : Sphere {i} n)
          → from-to-right* (<– (CWSphere-equiv n) x) == glue (lift false , x)
        from-to-right*-inv x =
          glue (lift false , –> (CWSphere-equiv n) (<– (CWSphere-equiv n) x))
            ∙ ap right (<–-inv-l (CWSphere-equiv n) (<– (CWSphere-equiv n) x))
              =⟨ ! $ <–-inv-adj' (CWSphere-equiv n) x
                |in-ctx (λ p → glue (lift false , –> (CWSphere-equiv n) (<– (CWSphere-equiv n) x)) ∙ ap right p) ⟩
          glue (lift false , –> (CWSphere-equiv n) (<– (CWSphere-equiv n) x))
            ∙ ap right (ap (<– (CWSphere-equiv n)) (<–-inv-r (CWSphere-equiv n) x))
              =⟨ ! $ ap-∘ right (<– (CWSphere-equiv n)) (<–-inv-r (CWSphere-equiv n) x)
                |in-ctx (λ p → glue (lift false , –> (CWSphere-equiv n) (<– (CWSphere-equiv n) x)) ∙ p) ⟩
          glue (lift false , –> (CWSphere-equiv n) (<– (CWSphere-equiv n) x))
            ∙ ap (right ∘ (<– (CWSphere-equiv n))) (<–-inv-r (CWSphere-equiv n) x)
              =⟨ htpy-natural-fromcst (λ x → glue (lift false , x)) (<–-inv-r (CWSphere-equiv n) x) ⟩
          glue (lift false , x)
              ∎

        from-to-glue* : ∀ (bs : Lift Bool × Sphere {i} n)
          → from-to-left* (fst bs) == from-to-right* (<– (CWSphere-equiv n) (snd bs))
              [ (λ x → from (to x) == x) ↓ glue bs ]
        from-to-glue* (lift true , x) = ↓-app=idf-in $ ! $
          ap (from ∘ to) (glue (lift true , x)) ∙ from-to-right* (<– (CWSphere-equiv n) x)
            =⟨ from-to-right*-inv x |in-ctx (λ p → ap (from ∘ to) (glue (lift true , x)) ∙ p) ⟩
          ap (from ∘ to) (glue (lift true , x)) ∙ glue (lift false , x)
            =⟨ ap-∘ from to (glue (lift true , x)) |in-ctx (λ p → p ∙ glue (lift false , x)) ⟩
          ap from (ap to (glue (lift true , x))) ∙ glue (lift false , x)
            =⟨ To.glue-β (lift true , x) |in-ctx (λ p → ap from p ∙ glue (lift false , x)) ⟩
          ap from (merid _ x) ∙ glue (lift false , x)
            =⟨ From.merid-β x |in-ctx (λ p → p ∙ glue (lift false , x)) ⟩
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
        from-to-glue* (lift false , x) = ↓-app=idf-in $ ! $
          ap (from ∘ to) (glue (lift false , x)) ∙ from-to-right* (<– (CWSphere-equiv n) x)
            =⟨ from-to-right*-inv x |in-ctx (λ p → ap (from ∘ to) (glue (lift false , x)) ∙ p) ⟩
          ap (from ∘ to) (glue (lift false , x)) ∙ glue (lift false , x)
            =⟨ ap-∘ from to (glue (lift false , x)) |in-ctx (λ p → p ∙ glue (lift false , x)) ⟩
          ap from (ap to (glue (lift false , x))) ∙ glue (lift false , x)
            =⟨ To.glue-β (lift false , x) |in-ctx (λ p → ap from p ∙ glue (lift false , x)) ⟩
          glue (lift false , x)
            =⟨ ! $ ∙'-unit-l (glue (lift false , x)) ⟩
          idp ∙' glue (lift false , x)
            ∎
