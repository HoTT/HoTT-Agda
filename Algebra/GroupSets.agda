{-# OPTIONS --without-K #-}

open import Base
open import Algebra.Groups

module Algebra.GroupSets {i} (grp : group i) where

  private
    module G = group grp

  -- The right group action with respect to the π¹ ( A , a )
  -- Y should be some set, but that condition is not needed
  -- in the definition.
  record action (Y : Set i) : Set i where
    constructor act[_,_,_]
    field
      _∙_ : Y → G.elems → Y
      right-unit : ∀ y → y ∙ G.e ≡ y
      assoc : ∀ y p₁ p₂ → (y ∙ p₁) ∙ p₂ ≡ y ∙ (p₁ G.∙ p₂)

  {-
  action-eq : ∀ {Y} ⦃ _ : is-set Y ⦄ {act₁ act₂ : action Y}
    → action._∙_ act₁ ≡ action._∙_ act₂ → act₁ ≡ act₂
  action-eq ∙≡ =
  -}

  record gset : Set (suc i) where
    constructor gset[_,_,_]
    field
      elems : Set i
      act : action elems
      set : is-set elems

  gset-eq : ∀ {gs₁ gs₂ : gset} (elems≡ : gset.elems gs₁ ≡ gset.elems gs₂)
    → (∙≡ : transport (λ Y → Y → G.elems → Y) elems≡ (action._∙_ (gset.act gs₁))
          ≡ action._∙_ (gset.act gs₂))
    → gs₁ ≡ gs₂
  gset-eq
    {gset[ ._ , act[ ._ , unit₁ , assoc₁ ] , set₁ ]}
    {gset[ ._ , act[ ._ , unit₂ , assoc₂ ] , set₂ ]}
    (refl Y) (refl ∙) =
      gset[ Y , act[ ∙ , unit₁ , assoc₁ ] , set₁ ]
        ≡⟨ ap (λ unit → gset[ Y , act[ ∙ , unit , assoc₁ ] , set₁ ])
              $ prop-has-all-paths (Π-is-prop λ _ → set₁ _ _) _ _ ⟩
      gset[ Y , act[ ∙ , unit₂ , assoc₁ ] , set₁ ]
        ≡⟨ ap (λ assoc → gset[ Y , act[ ∙ , unit₂ , assoc ] , set₁ ])
              $ prop-has-all-paths (Π-is-prop λ _ → Π-is-prop λ _ → Π-is-prop λ _ → set₁ _ _) _ _ ⟩
      gset[ Y , act[ ∙ , unit₂ , assoc₂ ] , set₁ ]
        ≡⟨ ap (λ set → gset[ Y , act[ ∙ , unit₂ , assoc₂ ] , set ])
              $ prop-has-all-paths is-set-is-prop _ _ ⟩∎
      gset[ Y , act[ ∙ , unit₂ , assoc₂ ] , set₂ ]
        ∎
