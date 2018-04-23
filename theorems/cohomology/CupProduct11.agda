{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import homotopy.EM1HSpace
open import homotopy.Pi2HSusp

module cohomology.CupProduct11 {i} (R : CRing i) where

  open import cohomology.CupProduct01 R

  private
    module R = CRing R
  open R using () renaming (add-group to R₊)
  open EM₁HSpace R.add-ab-group renaming (mult to EM₁-mult)

  open EMExplicit R.add-ab-group

  module CP₁₁ where

    base'' : EM₁ R₊ → Susp (EM₁ R₊)
    base'' _ = north' (EM₁ R₊)

    base' : EM₁ R₊ → EM 2
    base' _ = pt (⊙EM 2)

    [_]₁ : {x y : Susp (EM₁ R₊)} → (x == y) → Trunc 1 (x == y)
    [_]₁ p = [ p ]

    module _ (g : R.El) where

      loop''' : base'' ∼ base''
      loop''' y = merid (cp₀₁ g y) ∙ ! (merid embase)

      loop'' : base' ∼ base'
      loop'' y = <– (Trunc=-equiv [ north' (EM₁ R₊) ] [ north' (EM₁ R₊) ]) [ loop''' y ]₁

      loop' : base' == base'
      loop' = λ= loop''

    infixr 80 _∙ₜ_
    _∙ₜ_ : {x y z : Susp (EM₁ R₊)} → Trunc 1 (x == y) → Trunc 1 (y == z) → Trunc 1 (x == z)
    _∙ₜ_ {x} {y} {z} p q = Trunc=-∙ {A = Susp (EM₁ R₊)} {ta = [ x ]} {tb = [ y ]} {tc = [ z ]} p q

    -- TODO: generalize and move somewhere else
    ∙-∙ₜ : {x y z : Susp (EM₁ R₊)} (p : x == y) (q : y == z)
      → [ p ∙ q ]₁ == [ p ]₁ ∙ₜ [ q ]₁
    ∙-∙ₜ idp q = idp

    module _ (g₁ g₂ : R.El) where

      comp''' : (y : EM₁ R₊) → [ loop''' (R.add g₁ g₂) y ]₁ == [ loop''' g₁ y ]₁ ∙ₜ [ loop''' g₂ y ]₁
      comp''' y =
        [ loop''' (R.add g₁ g₂) y ]₁
          =⟨ ∙-∙ₜ (merid (cp₀₁ (R.add g₁ g₂) y)) (! (merid embase)) ⟩
        [ merid (cp₀₁ (R.add g₁ g₂) y) ]₁ ∙ₜ [ ! (merid embase) ]₁
          =⟨ R.add-comm g₁ g₂ |in-ctx (λ z → [ merid (cp₀₁ z y) ∙ ! (merid embase) ]₁) ⟩
        [ merid (cp₀₁ (R.add g₂ g₁) y) ]₁ ∙ₜ [ ! (merid embase) ]₁
          =⟨ {!cp₀₁-distr-l g₂ g₁ y!} |in-ctx (λ (z : EM₁ R₊) → [ merid z ∙ ! (merid embase) ]₁) ⟩
        [ merid (EM₁-mult (cp₀₁ g₂ y) (cp₀₁ g₁ y)) ]₁ ∙ₜ [ ! (merid embase) ]₁
          =⟨ homomorphism {X = ⊙EM₁ R₊} H-⊙EM₁ (cp₀₁ g₂ y) (cp₀₁ g₁ y) |in-ctx (λ z → z ∙ₜ [ ! (merid embase) ]₁) ⟩
        [ merid (cp₀₁ g₁ y) ∙ ! (merid embase) ∙ merid (cp₀₁ g₂ y) ]₁ ∙ₜ [ ! (merid embase) ]₁
          =⟨ ! (∙-∙ₜ (merid (cp₀₁ g₁ y) ∙ ! (merid embase) ∙ merid (cp₀₁ g₂ y)) (! (merid embase))) ⟩
        [ (merid (cp₀₁ g₁ y) ∙ ! (merid embase) ∙ merid (cp₀₁ g₂ y)) ∙ ! (merid embase) ]₁
          =⟨ ap (λ z → [ z ∙ ! (merid embase) ]₁) (! (∙-assoc (merid (cp₀₁ g₁ y)) (! (merid embase)) (merid (cp₀₁ g₂ y)))) ⟩
        [ ((merid (cp₀₁ g₁ y) ∙ ! (merid embase)) ∙ merid (cp₀₁ g₂ y)) ∙ ! (merid embase) ]₁
          =⟨ ap [_]₁ (∙-assoc (merid (cp₀₁ g₁ y) ∙ ! (merid embase)) (merid (cp₀₁ g₂ y)) (! (merid embase))) ⟩
        [ loop''' g₁ y ∙ loop''' g₂ y ]₁
          =⟨ ∙-∙ₜ (loop''' g₁ y) (loop''' g₂ y) ⟩
        [ loop''' g₁ y ]₁ ∙ₜ [ loop''' g₂ y ]₁ =∎

      comp'' : loop'' (R.add g₁ g₂) ∼ (λ y → loop'' g₁ y ∙ loop'' g₂ y)
      comp'' y =
        loop'' (R.add g₁ g₂) y
          =⟨ ap (<– (Trunc=-equiv [ north' (EM₁ R₊) ] [ north' (EM₁ R₊) ])) (comp''' y) ⟩
        <– (Trunc=-equiv [ north' (EM₁ R₊) ] [ north' (EM₁ R₊) ]) ([ loop''' g₁ y ]₁ ∙ₜ [ loop''' g₂ y ]₁)
          =⟨ Trunc=-∙-comm' {x = [ north' (EM₁ R₊) ]} {y = [ north' (EM₁ R₊) ]} {z = [ north' (EM₁ R₊) ]} [ loop''' g₁ y ]₁ [ loop''' g₂ y ]₁ ⟩
        loop'' g₁ y ∙ loop'' g₂ y =∎

      comp' : loop' (R.add g₁ g₂) == loop' g₁ ∙ loop' g₂
      comp' = ap λ= (λ= comp'') ∙ ! (∙-λ= (loop'' g₁) (loop'' g₂))

  {-
  cp₁₁ : EM₁ R₊ → EM₁ R₊ → EM 2
  cp₁₁ =
    EM₁-rec
      {C = EM₁ R₊ → EM 2}
      -- {{Π-level (λ _ → EM-level 2)}}
      base'
      loop'
      comp'
      {!!}
    where
  -}
