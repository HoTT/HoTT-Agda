{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Empty
open import lib.types.Group
open import lib.types.Word
open import lib.groups.GeneratedGroup
open import lib.groups.Homomorphism

module lib.groups.FreeGroup {i} (A : Type i) where

EmptyRel : Word A → Word A → Type lzero
EmptyRel _ _ = Empty

-- open module FreeGroupM = lib.groups.GeneratedGroup A EmptyRel

FreeQuotWordRel : Rel (Word A) i
FreeQuotWordRel = QuotWordRel {A = A} {R = EmptyRel}

FreeGroup : Group i
FreeGroup = GeneratedGroup A EmptyRel

FreeQuotWord : Type i
FreeQuotWord = QuotWord A EmptyRel

-- freeness

module _ {j} (G : Group j) where

  private
    module G = Group G

  every-function-is-legal : ∀ (f : A → G.El) → LegalFunction {A = A} {R = EmptyRel} G
  every-function-is-legal f =
    record { f = f; legality = λ {_} {_} () }

  every-function-is-legal-equiv : (A → G.El) ≃ LegalFunction {A = A} {R = EmptyRel} G
  every-function-is-legal-equiv =
    equiv every-function-is-legal
          LegalFunction.f
          (λ lf → LegalFunction= G idp)
          (λ f → idp)

  FreeGroup-extend-equiv : (A → G.El) ≃ (FreeGroup →ᴳ G)
  FreeGroup-extend-equiv =
    GeneratedGroup-extend-equiv G ∘e every-function-is-legal-equiv

  FreeGroup-extend : (A → G.El) → (FreeGroup →ᴳ G)
  FreeGroup-extend = –> FreeGroup-extend-equiv
