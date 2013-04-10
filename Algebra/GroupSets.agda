{-# OPTIONS --without-K #-}

open import Base
open import Algebra.Groups

{-
    The definition of G-sets.  Thanks to Daniel Grayson.
-}

module Algebra.GroupSets {i} (grp : group i) where

  private
    module G = group grp

  -- The right group action with respect to the group [grp].
  -- [Y] should be some set, but that condition is not needed
  -- in the definition.
  record action (Y : Set i) : Set i where
    constructor act[_,_,_]
    field
      _∙_ : Y → G.carrier → Y
      right-unit : ∀ y → y ∙ G.e ≡ y
      assoc : ∀ y p₁ p₂ → (y ∙ p₁) ∙ p₂ ≡ y ∙ (p₁ G.∙ p₂)

  {-
  action-eq : ∀ {Y} ⦃ _ : is-set Y ⦄ {act₁ act₂ : action Y}
    → action._∙_ act₁ ≡ action._∙_ act₂ → act₁ ≡ act₂
  action-eq ∙≡ =
  -}

  -- The definition of a G-set.  A set [carrier] equipped with
  -- a right group action with respect to [grp].
  record gset : Set (suc i) where
    constructor gset[_,_,_]
    field
      carrier : Set i
      act : action carrier
      set : is-set carrier
    open action act public

  -- A convenient tool to compare two G-sets.  Many data are
  -- just props and this function do the coversion for them
  -- for you.  You only need to show the non-trivial parts.
  gset-eq : ∀ {gs₁ gs₂ : gset} (carrier≡ : gset.carrier gs₁ ≡ gset.carrier gs₂)
    → (∙≡ : transport (λ Y → Y → G.carrier → Y) carrier≡ (action._∙_ (gset.act gs₁))
          ≡ action._∙_ (gset.act gs₂))
    → gs₁ ≡ gs₂
  gset-eq
    {gset[  Y , act[  ∙ , unit₁ , assoc₁ ] , set₁ ]}
    {gset[ ._ , act[ ._ , unit₂ , assoc₂ ] , set₂ ]}
    refl refl =
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
