{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.SetQuotient
open import lib.groups.Homomorphisms
open import lib.groups.PropNormalSubgroup

module lib.groups.QuotientGroup where

module QuotientGroup {i j} (G : Group i) {P : Group.El G → Type j}
  (P-induces-normal-subgroup : induces-normal-subgroup G P) where

  private
    module G = Group G
    module P = induces-normal-subgroup P-induces-normal-subgroup
    infix 80 _⊙_
    _⊙_ = G.comp

  rel : Rel G.El j
  rel g₁ g₂ = P (G.comp g₁ (G.inv g₂))

  struct : GroupStructure (SetQuotient rel)
  struct = record {ident = ident; inv = inv; comp = comp;
      unit-l = unit-l; unit-r = unit-r; assoc = assoc;
      inv-l = inv-l; inv-r = inv-r} where
    -- XXX for some reason [record {M}] does not work.
    ident : SetQuotient rel
    ident = q[ G.ident ]

    inv : SetQuotient rel → SetQuotient rel
    inv = SetQuot-rec SetQuotient-level (λ g → q[ G.inv g ])
      (λ {g₁} {g₂} pg₁g₂⁻¹
        → ! $ quot-rel $ transport! (λ g → P (G.inv g₂ ⊙ g))
            (G.inv-inv g₁) $ P.comm g₁ (G.inv g₂) pg₁g₂⁻¹ )

    comp : SetQuotient rel → SetQuotient rel → SetQuotient rel
    comp = SetQuot-rec (→-is-set SetQuotient-level)
      (λ g₁ → SetQuot-rec SetQuotient-level
        (λ g₂ → q[ g₁ ⊙ g₂ ])
        (λ {g₂} {g₂'} pg₂g₂'⁻¹ → quot-rel $ transport P
          ( ap (_⊙ G.inv g₁) (! $ G.assoc g₁ g₂ (G.inv g₂'))
          ∙ G.assoc (g₁ ⊙ g₂) (G.inv g₂') (G.inv g₁)
          ∙ ap ((g₁ ⊙ g₂) ⊙_) (! $ G.inv-comp g₁ g₂'))
          (P.cong g₁ pg₂g₂'⁻¹)))
      (λ {g₁} {g₁'} pg₁g₁'⁻¹ → λ= $ SetQuot-elim
        (λ _ → =-preserves-set SetQuotient-level)
        (λ g₂ → quot-rel $ transport! P
          ( ap ((g₁ ⊙ g₂) ⊙_) (G.inv-comp g₁' g₂)
          ∙ ! (G.assoc (g₁ ⊙ g₂) (G.inv g₂) (G.inv g₁') )
          ∙ ap (_⊙ G.inv g₁')
            ( G.assoc g₁ g₂ (G.inv g₂)
            ∙ ap (g₁ ⊙_) (G.inv-r g₂)
            ∙ G.unit-r g₁))
          pg₁g₁'⁻¹)
        (λ _ → prop-has-all-paths-↓ (SetQuotient-level _ _)))
    abstract
      unit-l : ∀ g → comp ident g == g
      unit-l = SetQuot-elim
        (λ _ → =-preserves-set SetQuotient-level)
        (ap q[_] ∘ G.unit-l)
        (λ _ → prop-has-all-paths-↓ (SetQuotient-level _ _))

      unit-r : ∀ g → comp g ident == g
      unit-r = SetQuot-elim
        (λ _ → =-preserves-set SetQuotient-level)
        (ap q[_] ∘ G.unit-r)
        (λ _ → prop-has-all-paths-↓ (SetQuotient-level _ _))

      assoc : ∀ g₁ g₂ g₃ → comp (comp g₁ g₂) g₃ == comp g₁ (comp g₂ g₃)
      assoc = SetQuot-elim
        (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set SetQuotient-level)
        (λ g₁ → SetQuot-elim
          (λ _ → Π-is-set λ _ → =-preserves-set SetQuotient-level)
          (λ g₂ → SetQuot-elim
            (λ _ → =-preserves-set SetQuotient-level)
            (λ g₃ → ap q[_] $ G.assoc g₁ g₂ g₃)
            (λ _ → prop-has-all-paths-↓ (SetQuotient-level _ _)))
          (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuotient-level _ _)))
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → SetQuotient-level _ _))

      inv-l : ∀ g → comp (inv g) g == ident
      inv-l = SetQuot-elim
        (λ _ → =-preserves-set SetQuotient-level)
        (ap q[_] ∘ G.inv-l)
        (λ _ → prop-has-all-paths-↓ (SetQuotient-level _ _))

      inv-r : ∀ g → comp g (inv g) == ident
      inv-r = SetQuot-elim
        (λ _ → =-preserves-set SetQuotient-level)
        (ap q[_] ∘ G.inv-r)
        (λ _ → prop-has-all-paths-↓ (SetQuotient-level _ _))

  QuotientGroup : Group (lmax i j)
  QuotientGroup = group _ SetQuotient-level struct
