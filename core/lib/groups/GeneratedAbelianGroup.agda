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

module lib.groups.GeneratedAbelianGroup {i} {m} where

module GeneratedAbelianGroup (A : Type i) (R : Rel (Word A) m) where

  data AbGroupRel : Word A → Word A → Type (lmax i m) where
    agr-commutes : ∀ l₁ l₂ → AbGroupRel (l₁ ++ l₂) (l₂ ++ l₁)
    agr-rel : ∀ {l₁ l₂} → R l₁ l₂ → AbGroupRel l₁ l₂

  private
    module Gen = GeneratedGroup A AbGroupRel
  open Gen hiding (module HomomorphismEquiv) public

  agr-reverse : (w : Word A) → QuotWordRel (reverse w) w
  agr-reverse nil = qwr-refl idp
  agr-reverse (x :: w) =
    reverse w ++ (x :: nil)
      qwr⟨ qwr-rel (agr-commutes (reverse w) (x :: nil)) ⟩
    x :: reverse w
      qwr⟨ qwr-cong-r (x :: nil) (agr-reverse w) ⟩
    x :: w qwr∎

  GenAbGroup : AbGroup (lmax i m)
  GenAbGroup = grp , grp-is-abelian
    where
    grp : Group (lmax i m)
    grp = GenGroup
    module grp = Group grp
    grp-is-abelian : is-abelian grp
    grp-is-abelian =
      QuotWord-elim {P = λ a → ∀ b → grp.comp a b == grp.comp b a}
        (λ la →
          QuotWord-elim {P = λ b → grp.comp qw[ la ] b == grp.comp b qw[ la ]}
            (λ lb → quot-rel (qwr-rel (agr-commutes la lb)))
            (λ _ → prop-has-all-paths-↓))
        (λ _ → prop-has-all-paths-↓ {{Π-level ⟨⟩}})

  module GenAbGroup = AbGroup GenAbGroup

  {- Universal Properties -}
  module HomomorphismEquiv {j} (G : AbGroup j) where

    private
      module G = AbGroup G
      module R-RFs = RelationRespectingFunctions A R G.grp
      module AbGroupRel-RFs = RelationRespectingFunctions A AbGroupRel G.grp

    open R-RFs public

    private
      legal-functions-equiv : R-RFs.RelationRespectingFunction
                            ≃ AbGroupRel-RFs.RelationRespectingFunction
      legal-functions-equiv =
        equiv to from
              (λ lf → AbGroupRel-RFs.RelationRespectingFunction= idp)
              (λ lf → R-RFs.RelationRespectingFunction= idp)
        where
        to : R-RFs.RelationRespectingFunction → AbGroupRel-RFs.RelationRespectingFunction
        to (R-RFs.rel-res-fun f respects-R) =
          AbGroupRel-RFs.rel-res-fun f respects-AbGroupRel
          where
          respects-AbGroupRel : AbGroupRel-RFs.respects-rel f
          respects-AbGroupRel (agr-commutes l₁ l₂) =
            Word-extendᴳ G.grp f (l₁ ++ l₂)
              =⟨ Word-extendᴳ-++ G.grp f l₁ l₂ ⟩
            G.comp (Word-extendᴳ G.grp f l₁) (Word-extendᴳ G.grp f l₂)
              =⟨ G.comm (Word-extendᴳ G.grp f l₁) (Word-extendᴳ G.grp f l₂) ⟩
            G.comp (Word-extendᴳ G.grp f l₂) (Word-extendᴳ G.grp f l₁)
              =⟨ ! (Word-extendᴳ-++ G.grp f l₂ l₁) ⟩
            Word-extendᴳ G.grp f (l₂ ++ l₁) =∎
          respects-AbGroupRel (agr-rel r) = respects-R r
        from : AbGroupRel-RFs.RelationRespectingFunction → R-RFs.RelationRespectingFunction
        from (AbGroupRel-RFs.rel-res-fun f respects-AbGroupRel) =
          R-RFs.rel-res-fun f respects-R
          where
          respects-R : R-RFs.respects-rel f
          respects-R r = respects-AbGroupRel (agr-rel r)

    extend-equiv : R-RFs.RelationRespectingFunction ≃ (GenAbGroup.grp →ᴳ G.grp)
    extend-equiv =
      Gen.HomomorphismEquiv.extend-equiv G.grp ∘e legal-functions-equiv

    extend : R-RFs.RelationRespectingFunction → (GenAbGroup.grp →ᴳ G.grp)
    extend = –> extend-equiv
