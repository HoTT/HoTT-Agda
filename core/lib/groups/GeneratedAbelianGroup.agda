{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.List
open import lib.types.Pi
open import lib.types.SetQuotient
open import lib.types.Word
open import lib.groups.GeneratedGroup
open import lib.groups.Homomorphism

module lib.groups.GeneratedAbelianGroup {i m} (A : Type i) {R : Rel (Word A) m} where

data AbGroupRel : Word A → Word A → Type (lmax i m) where
  agr-commutes : ∀ l₁ l₂ → AbGroupRel (l₁ ++ l₂) (l₂ ++ l₁)
  agr-rel : ∀ {l₁ l₂} → R l₁ l₂ → AbGroupRel l₁ l₂

GeneratedAbGroup : AbGroup (lmax i m)
GeneratedAbGroup = grp , grp-is-abelian
  where
  grp : Group (lmax i m)
  grp = GeneratedGroup A AbGroupRel
  module grp = Group grp
  grp-is-abelian : is-abelian grp
  grp-is-abelian =
    QuotWord-elim {P = λ a → ∀ b → grp.comp a b == grp.comp b a}
      (λ la →
        QuotWord-elim {P = λ b → grp.comp qw[ la ] b == grp.comp b qw[ la ]}
          (λ lb → quot-rel (qwr-rel (agr-commutes la lb)))
          (λ _ → prop-has-all-paths-↓))
      (λ _ → prop-has-all-paths-↓ {{Π-level ⟨⟩}})

module GeneratedAbGroup = AbGroup GeneratedAbGroup

{- Freeness (universal properties) -}

module _ {j} (G : AbGroup j) where

  private
    module G = AbGroup G

  R-legal-to-AbGroupRel-legal : LegalFunction {A = A} {R} G.grp → LegalFunction {A = A} {AbGroupRel} G.grp
  R-legal-to-AbGroupRel-legal lf =
    record { f = lf.f; legality = legality }
    where
    module lf = LegalFunction lf
    legality : is-legal {A = A} {AbGroupRel} G.grp lf.f
    legality (agr-commutes l₁ l₂) =
      Word-extendᴳ G.grp lf.f (l₁ ++ l₂)
        =⟨ Word-extendᴳ-++ G.grp lf.f l₁ l₂ ⟩
      G.comp (Word-extendᴳ G.grp lf.f l₁) (Word-extendᴳ G.grp lf.f l₂)
        =⟨ G.comm (Word-extendᴳ G.grp lf.f l₁) (Word-extendᴳ G.grp lf.f l₂) ⟩
      G.comp (Word-extendᴳ G.grp lf.f l₂) (Word-extendᴳ G.grp lf.f l₁)
        =⟨ ! (Word-extendᴳ-++ G.grp lf.f l₂ l₁) ⟩
      Word-extendᴳ G.grp lf.f (l₂ ++ l₁) =∎
    legality (agr-rel r) = lf.legality r

  AbGroupRel-legal-to-R-legal : LegalFunction {A = A} {AbGroupRel} G.grp → LegalFunction {A = A} {R} G.grp
  AbGroupRel-legal-to-R-legal lf =
    record { f = lf.f; legality = legality }
    where
    module lf = LegalFunction lf
    legality : is-legal {A = A} {R} G.grp lf.f
    legality r = lf.legality (agr-rel r)

  legal-functions-equiv : LegalFunction {A = A} {R} G.grp ≃ LegalFunction {A = A} {AbGroupRel} G.grp
  legal-functions-equiv =
    equiv R-legal-to-AbGroupRel-legal
          AbGroupRel-legal-to-R-legal
          (λ lf → LegalFunction= _ idp)
          (λ lf → LegalFunction= _ idp)

  GeneratedAbGroup-extend-equiv : LegalFunction {A = A} {R} G.grp ≃ (GeneratedAbGroup.grp →ᴳ G.grp)
  GeneratedAbGroup-extend-equiv =
    GeneratedGroup-extend-equiv G.grp ∘e legal-functions-equiv

  GeneratedAbGroup-extend : LegalFunction {A = A} {R} G.grp → (GeneratedAbGroup.grp →ᴳ G.grp)
  GeneratedAbGroup-extend = –> GeneratedAbGroup-extend-equiv
