{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.SetQuotient
open import lib.groups.Homomorphism
open import lib.groups.Subgroup
open import lib.groups.SubgroupProp

module lib.groups.QuotientGroup where

module _ {i j} {G : Group i} (P : NormalSubgroupProp G j) where

  private
    module G = Group G
    module P = NormalSubgroupProp P
    infix 80 _⊙_
    _⊙_ = G.comp

  quotient-group-rel : Rel G.El j
  quotient-group-rel g₁ g₂ = P.prop (G.comp g₁ (G.inv g₂))

  quotient-group-struct : GroupStructure (SetQuotient quotient-group-rel)
  quotient-group-struct = record {M} where
    module M where
      ident : SetQuotient quotient-group-rel
      ident = q[ G.ident ]

      inv : SetQuotient quotient-group-rel → SetQuotient quotient-group-rel
      inv = SetQuot-rec SetQuotient-level (λ g → q[ G.inv g ])
        (λ {g₁} {g₂} pg₁g₂⁻¹
          → ! $ quot-rel $ transport! (λ g → P.prop (G.inv g₂ ⊙ g))
              (G.inv-inv g₁) $ P.comm g₁ (G.inv g₂) pg₁g₂⁻¹ )

      comp : SetQuotient quotient-group-rel → SetQuotient quotient-group-rel → SetQuotient quotient-group-rel
      comp = SetQuot-rec (→-is-set SetQuotient-level)
        (λ g₁ → SetQuot-rec SetQuotient-level
          (λ g₂ → q[ g₁ ⊙ g₂ ])
          (λ {g₂} {g₂'} pg₂g₂'⁻¹ → quot-rel $ transport P.prop
            ( ap (_⊙ G.inv g₁) (! $ G.assoc g₁ g₂ (G.inv g₂'))
            ∙ G.assoc (g₁ ⊙ g₂) (G.inv g₂') (G.inv g₁)
            ∙ ap ((g₁ ⊙ g₂) ⊙_) (! $ G.inv-comp g₁ g₂'))
            (P.conj g₁ pg₂g₂'⁻¹)))
        (λ {g₁} {g₁'} pg₁g₁'⁻¹ → λ= $ SetQuot-elim
          (λ _ → =-preserves-set SetQuotient-level)
          (λ g₂ → quot-rel $ transport! P.prop
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
  QuotientGroup = group _ SetQuotient-level quotient-group-struct

module _ {i j} {G : Group i} {P : NormalSubgroupProp G j} where

  q[_]ᴳ : G →ᴳ QuotientGroup P
  q[_]ᴳ = group-hom q[_] λ _ _ → idp

module _ {i j k} {G : Group i}
  (Q : NormalSubgroupProp G j) (P : SubgroupProp G k)
  (prop-respects-quot : NormalSubgroupProp.subgrp-prop Q ⊆ᴳ P) where

  private
    module G = Group G
    module Q = NormalSubgroupProp Q
    module P = SubgroupProp P

  prop-over-quot : SubgroupProp (QuotientGroup Q) k
  prop-over-quot = record {M; comp-inv-r = λ {g₁} {g₂} → M.comp-inv-r' g₁ g₂} where
    module M where
      module QG = Group (QuotientGroup Q)
      private
        abstract
          prop'-rel : ∀ {g₁ g₂} (qg₁g₂⁻¹ : quotient-group-rel Q g₁ g₂)
            → P.prop g₁ == P.prop g₂
          prop'-rel {g₁} {g₂} qg₁g₂⁻¹ = ua $
            equiv (λ pg₁ → transport P.prop
                    ( ap (λ g → G.comp g g₁) (G.inv-comp g₁ (G.inv g₂))
                    ∙ G.assoc (G.inv (G.inv g₂)) (G.inv g₁) g₁
                    ∙ ap2 G.comp (G.inv-inv g₂) (G.inv-l g₁)
                    ∙ G.unit-r g₂)
                    (P.comp (P.inv pg₁g₂⁻¹) pg₁))
                  (λ pg₂ → transport P.prop
                    ( G.assoc g₁ (G.inv g₂) g₂
                    ∙ ap (G.comp g₁) (G.inv-l g₂)
                    ∙ G.unit-r g₁)
                    (P.comp pg₁g₂⁻¹ pg₂))
                  (λ _ → prop-has-all-paths (P.level g₂) _ _)
                  (λ _ → prop-has-all-paths (P.level g₁) _ _)
            where pg₁g₂⁻¹ : P.prop (G.comp g₁ (G.inv g₂))
                  pg₁g₂⁻¹ = prop-respects-quot (G.comp g₁ (G.inv g₂)) qg₁g₂⁻¹

        prop' : Group.El (QuotientGroup Q) → hProp k
        prop' = SetQuot-rec
          (hProp-is-set k)
          (λ g → P.prop g , P.level g)
          (nType=-out ∘ prop'-rel)

      prop : QG.El → Type k
      prop g' = fst (prop' g')

      abstract
        level : ∀ g' → is-prop (prop g')
        level g' = snd (prop' g')

      ident : prop q[ G.ident ]
      ident = P.ident

      abstract
        comp-inv-r' : ∀ g₁' g₂' → prop g₁' → prop g₂' → prop (QG.comp g₁' (QG.inv g₂'))
        comp-inv-r' = SetQuot-elim
          {P = λ g₁' → ∀ g₂' → prop g₁' → prop g₂' → prop (QG.comp g₁' (QG.inv g₂'))}
          (λ g₁' → Π-is-set λ g₂' → →-is-set $ →-is-set $ prop-has-level-S (level (QG.comp g₁' (QG.inv g₂'))))
          (λ g₁ → SetQuot-elim (λ g₂' → →-is-set $ →-is-set $ prop-has-level-S (level (QG.comp q[ g₁ ] (QG.inv g₂'))))
            (λ g₂ pg₁ pg₂ → P.comp-inv-r pg₁ pg₂)
            (λ {_} {g₂} _ → prop-has-all-paths-↓ (→-is-prop $ →-is-prop $ level q[ G.comp g₁ (G.inv g₂) ])))
          (λ {_} {g₁} _ → prop-has-all-paths-↓ (Π-is-prop λ g₂' → →-is-prop $ →-is-prop $ level (QG.comp q[ g₁ ] (QG.inv g₂'))))

  rel-over-sub : NormalSubgroupProp (Subgroup P) j
  rel-over-sub = Q ∘nsubᴳ SG.inject where module SG = Subgroup P

  -- Maybe this is needed at some point.
  -- QuotientGroup rel-over-sub ≃ᴳ Subgroup prop-over-quot
