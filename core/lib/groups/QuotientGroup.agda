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

  quot-group-rel : Rel G.El j
  quot-group-rel g₁ g₂ = P.prop (G.diff g₁ g₂)

  quot-group-struct : GroupStructure (SetQuot quot-group-rel)
  quot-group-struct = record {M} where
    module M where
      ident : SetQuot quot-group-rel
      ident = q[ G.ident ]

      abstract
        inv-rel : ∀ {g₁ g₂ : G.El} (pg₁g₂⁻¹ : P.prop (G.diff g₁ g₂))
          → q[ G.inv g₁ ] == q[ G.inv g₂ ] :> SetQuot quot-group-rel
        inv-rel {g₁} {g₂} pg₁g₂⁻¹ = ! $ quot-rel $
          transport! (λ g → P.prop (G.inv g₂ ⊙ g))
            (G.inv-inv g₁) $ P.comm g₁ (G.inv g₂) pg₁g₂⁻¹

      inv : SetQuot quot-group-rel → SetQuot quot-group-rel
      inv = SetQuot-rec SetQuot-level (λ g → q[ G.inv g ]) inv-rel

      abstract
        comp-rel-r : ∀ g₁ {g₂ g₂' : G.El} (pg₂g₂'⁻¹ : P.prop (G.diff g₂ g₂'))
          → q[ g₁ ⊙ g₂ ] == q[ g₁ ⊙ g₂' ] :> SetQuot quot-group-rel
        comp-rel-r g₁ {g₂} {g₂'} pg₂g₂'⁻¹ = quot-rel $ transport P.prop
          ( ap (_⊙ G.inv g₁) (! $ G.assoc g₁ g₂ (G.inv g₂'))
          ∙ G.assoc (g₁ ⊙ g₂) (G.inv g₂') (G.inv g₁)
          ∙ ap ((g₁ ⊙ g₂) ⊙_) (! $ G.inv-comp g₁ g₂'))
          (P.conj g₁ pg₂g₂'⁻¹)

      comp' : G.El → SetQuot quot-group-rel → SetQuot quot-group-rel
      comp' g₁ = SetQuot-rec SetQuot-level (λ g₂ → q[ g₁ ⊙ g₂ ]) (comp-rel-r g₁)

      abstract
        comp-rel-l : ∀ {g₁ g₁' : G.El} (pg₁g₁'⁻¹ : P.prop (G.diff g₁ g₁')) g₂
          → q[ g₁ ⊙ g₂ ] == q[ g₁' ⊙ g₂ ] :> SetQuot quot-group-rel
        comp-rel-l {g₁} {g₁'} pg₁g₁'⁻¹ g₂ = quot-rel $ transport! P.prop
            ( ap ((g₁ ⊙ g₂) ⊙_) (G.inv-comp g₁' g₂)
            ∙ ! (G.assoc (g₁ ⊙ g₂) (G.inv g₂) (G.inv g₁') )
            ∙ ap (_⊙ G.inv g₁')
              ( G.assoc g₁ g₂ (G.inv g₂)
              ∙ ap (g₁ ⊙_) (G.inv-r g₂)
              ∙ G.unit-r g₁))
            pg₁g₁'⁻¹

        comp'-rel : ∀ {g₁ g₁' : G.El} (pg₁g₁'⁻¹ : P.prop (G.diff g₁ g₁'))
          → comp' g₁ == comp' g₁'
        comp'-rel pg₁g₁'⁻¹ = λ= $ SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (comp-rel-l pg₁g₁'⁻¹)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

      comp : SetQuot quot-group-rel → SetQuot quot-group-rel → SetQuot quot-group-rel
      comp = SetQuot-rec (→-is-set SetQuot-level) comp' comp'-rel

      abstract
        unit-l : ∀ g → comp ident g == g
        unit-l = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (ap q[_] ∘ G.unit-l)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

        unit-r : ∀ g → comp g ident == g
        unit-r = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (ap q[_] ∘ G.unit-r)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

        assoc : ∀ g₁ g₂ g₃ → comp (comp g₁ g₂) g₃ == comp g₁ (comp g₂ g₃)
        assoc = SetQuot-elim
          (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set SetQuot-level)
          (λ g₁ → SetQuot-elim
            (λ _ → Π-is-set λ _ → =-preserves-set SetQuot-level)
            (λ g₂ → SetQuot-elim
              (λ _ → =-preserves-set SetQuot-level)
              (λ g₃ → ap q[_] $ G.assoc g₁ g₂ g₃)
              (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _)))
            (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuot-level _ _)))
          (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → SetQuot-level _ _))

      inv-l : ∀ g → comp (inv g) g == ident
      inv-l = SetQuot-elim
        (λ _ → =-preserves-set SetQuot-level)
        (ap q[_] ∘ G.inv-l)
        (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

      inv-r : ∀ g → comp g (inv g) == ident
      inv-r = SetQuot-elim
        (λ _ → =-preserves-set SetQuot-level)
        (ap q[_] ∘ G.inv-r)
        (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

  QuotGroup : Group (lmax i j)
  QuotGroup = group _ SetQuot-level quot-group-struct

{- helper functions -}
module _ {i j} {G : Group i} {P : NormalSubgroupProp G j} where
  private
    module G = Group G
    module P = NormalSubgroupProp P
    infix 80 _⊙_
    _⊙_ = G.comp

  q[_]ᴳ : G →ᴳ QuotGroup P
  q[_]ᴳ = group-hom q[_] λ _ _ → idp

  quot-relᴳ = λ {g₁} {g₂} → quot-rel {R = quot-group-rel P} {a₁ = g₁} {a₂ = g₂}

  private
    abstract
      quot-group-rel-is-refl : is-refl (quot-group-rel P)
      quot-group-rel-is-refl g = transport! P.prop (G.inv-r g) P.ident

      quot-group-rel-is-sym : is-sym (quot-group-rel P)
      quot-group-rel-is-sym {g₁} {g₂} pg₁g₂⁻¹ =
        transport P.prop (G.inv-comp g₁ (G.inv g₂) ∙ ap (_⊙ G.inv g₁) (G.inv-inv g₂)) (P.inv pg₁g₂⁻¹)

      quot-group-rel-is-trans : is-trans (quot-group-rel P)
      quot-group-rel-is-trans {g₁} {g₂} {g₃} pg₁g₂⁻¹ pg₂g₃⁻¹ =
        transport P.prop
          ( G.assoc g₁ (G.inv g₂) (g₂ ⊙ G.inv g₃)
          ∙ ap (g₁ ⊙_) ( ! (G.assoc (G.inv g₂) g₂ (G.inv g₃))
                       ∙ ap (_⊙ G.inv g₃) (G.inv-l g₂)
                       ∙ G.unit-l (G.inv g₃)))
          (P.comp pg₁g₂⁻¹ pg₂g₃⁻¹)

  quot-relᴳ-equiv : {g₁ g₂ : G.El} → P.prop (g₁ ⊙ G.inv g₂) ≃ (q[ g₁ ] == q[ g₂ ])
  quot-relᴳ-equiv = quot-rel-equiv {R = quot-group-rel P} (P.level _)
    quot-group-rel-is-refl
    quot-group-rel-is-sym
    quot-group-rel-is-trans

module QuotGroup {i j} {G : Group i} (P : NormalSubgroupProp G j) where
  npropᴳ : NormalSubgroupProp G j
  npropᴳ = P
  module P = NormalSubgroupProp npropᴳ
    using (propᴳ; prop)

  grp : Group (lmax i j)
  grp = QuotGroup P
  open Group grp public

module Coker {i j} {G : Group i} {H : Group j}
  (H-is-abelian : is-abelian H) (φ : G →ᴳ H)
  = QuotGroup (sub-abelian-normal H-is-abelian (im-propᴳ φ))

module _ {i j k} {G : Group i}
  (P : SubgroupProp G j) (Q : NormalSubgroupProp G k) where

  quot-of-sub : NormalSubgroupProp (Subgroup P) k
  quot-of-sub = Q ∘nsubᴳ Subgroup.inject P

{- interactions between quotients and subgroups (work in progress) -}
{- So far not used.

-- QuotGroup rel-over-sub ≃ᴳ Subgroup prop-over-quot

module _ {i j k} {G : Group i}
  (Q : NormalSubgroupProp G j) (P : SubgroupProp G k)
  (prop-respects-quot : NormalSubgroupProp.subgrp-prop Q ⊆ᴳ P) where

  private
    module G = Group G
    module Q = NormalSubgroupProp Q
    module P = SubgroupProp P

  prop-over-quot : SubgroupProp (QuotGroup Q) k
  prop-over-quot = record {M; diff = λ {g₁} {g₂} → M.diff' g₁ g₂} where
    module M where
      module QG = Group (QuotGroup Q)
      private
        abstract
          prop'-rel : ∀ {g₁ g₂} (qg₁g₂⁻¹ : quot-group-rel Q g₁ g₂)
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
            where pg₁g₂⁻¹ : P.prop (G.diff g₁ g₂)
                  pg₁g₂⁻¹ = prop-respects-quot (G.diff g₁ g₂) qg₁g₂⁻¹

        prop' : Group.El (QuotGroup Q) → hProp k
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
        diff' : ∀ g₁' g₂' → prop g₁' → prop g₂' → prop (QG.diff g₁' g₂')
        diff' = SetQuot-elim
          {P = λ g₁' → ∀ g₂' → prop g₁' → prop g₂' → prop (QG.diff g₁' g₂')}
          (λ g₁' → Π-is-set λ g₂' → →-is-set $ →-is-set $ raise-level -1 (level (QG.diff g₁' g₂')))
          (λ g₁ → SetQuot-elim (λ g₂' → →-is-set $ →-is-set $ raise-level -1 (level (QG.diff q[ g₁ ] g₂')))
            (λ g₂ pg₁ pg₂ → P.diff pg₁ pg₂)
            (λ {_} {g₂} _ → prop-has-all-paths-↓ (→-is-prop $ →-is-prop $ level q[ G.diff g₁ g₂ ])))
          (λ {_} {g₁} _ → prop-has-all-paths-↓ (Π-is-prop λ g₂' → →-is-prop $ →-is-prop $ level (QG.diff q[ g₁ ] g₂')))

-}
