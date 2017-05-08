{-# OPTIONS --without-K --rewriting #-}
open import HoTT

open import stash.modalities.gbm.GbmUtil

module stash.modalities.JoinAdj {i j k}
  (A : Type i) (B : Type j) (C : Type k) where

  private
  
    module From (f : B → C) (γ : A → hfiber cst f)
      = JoinRec (fst ∘ γ) f (λ { (a , b) → app= (snd (γ a)) b })

    from-β : (f : B → C) (γ : A → hfiber cst f)
             (a : A) (b : B) → ap (From.f f γ) (glue (a , b)) == app= (snd (γ a)) b
    from-β f γ a b = From.glue-β f γ (a , b)

    to : (A * B → C) → Σ (B → C) (λ f → A → hfiber cst f)
    to φ = φ ∘ right , (λ a → φ (left a) , λ= (λ b → ap φ (glue (a , b))))

    from : Σ (B → C) (λ f → A → hfiber cst f) → A * B → C
    from (f , γ) = From.f f γ

    abstract

      to-from : (ψ : Σ (B → C) (λ f → A → hfiber cst f)) → to (from ψ) == ψ
      to-from (f , γ) = pair= idp (λ= coh)

        where coh : (a : A) → from (f , γ) (left a) , λ= (λ b → ap (from (f , γ)) (glue (a , b))) == γ a
              coh a = pair= idp (ap λ= (λ= (λ b → from-β f γ a b)) ∙ ! (λ=-η (snd (γ a))))

      from-to : (φ : A * B → C) → from (to φ) == φ
      from-to φ = λ= (Join-elim (λ a → idp) (λ b → idp) (λ ab → ↓-==-in (coh ab)))

        where coh : (ab : A × B) → ap φ (glue ab) == ap (from (to φ)) (glue ab) ∙ idp
              coh (a , b) = ap φ (glue (a , b))
                               =⟨ ! (app=-β (λ b → ap φ (glue (a , b))) b) ⟩
                            app= (λ= (λ b → ap φ (glue (a , b)))) b
                               =⟨ ! (from-β (fst (to φ)) (snd (to φ)) a b) ⟩
                            ap (From.f (fst (to φ)) (snd (to φ))) (glue (a , b))
                               =⟨ ! (∙-unit-r (ap (from (to φ)) (glue (a , b)))) ⟩ 
                            ap (from (to φ)) (glue (a , b)) ∙ idp ∎

  join-adj : (A * B → C) ≃ Σ (B → C) (λ f → A → hfiber cst f)
  join-adj = equiv to from to-from from-to

