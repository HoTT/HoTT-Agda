{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities
import stash.modalities.gbm.Pushout

module stash.modalities.gbm.Surjectivity {ℓ} (M : Modality ℓ) where

  open Modality M

  module _ {A : Type ℓ} {B : Type ℓ} (Q : A → B → Type ℓ) where

    open import stash.modalities.gbm.PushoutMono
    open import stash.modalities.gbm.PullbackSplit
    open import homotopy.PushoutSplit

    private

      A' : Type ℓ
      A' = Σ A (λ a → Trunc (S ⟨-2⟩) (Σ B (λ b → Q a b)))

      Q' : A' → B → Type ℓ
      Q' (a , _) b = Q a b

      module W = stash.modalities.gbm.Pushout Q
      module W' = stash.modalities.gbm.Pushout Q'
      W  = W.BMPushout
      W' = W'.BMPushout
      
      Z = (Σ A λ a → Σ B λ b → Q a b)
      Z' = (Σ A' λ a → Σ B λ b → Q (fst a) b)

      Z-to-Z' : Z → Z'
      Z-to-Z' (a , b , q) = (a , [ b , q ]) , b , q

      Z'-to-Z : Z' → Z
      Z'-to-Z ((a , e) , b , q) = a , b , q

      postulate
        Z-to-Z'-equiv : is-equiv Z-to-Z'

      --
      --  The following two cospans are clearly equivalent
      --  in view of the equivalence between Z and Z'
      --
      --   span₀ : A <--- Z ----> B
      --   span₁ : A <--- Z' ---> B
      --
      
      span₀ = span A B Z fst (fst ∘ snd)
      span₁ = span A B Z' (fst ∘ fst) (fst ∘ snd)

      W'' = Pushout span₁

      W-equiv-W'' : W ≃ W''
      W-equiv-W'' = Pushout-emap span-eqv

        where span-eqv : SpanEquiv span₀ span₁
              span-eqv = (span-map (idf A) (idf B) Z-to-Z'
                           (comm-sqr (λ a → idp))
                           (comm-sqr (λ b → idp))) ,
                           ( idf-is-equiv A
                           , idf-is-equiv B
                           , Z-to-Z'-equiv)


      X = Pushout (span A W' A' fst left)
      
      --
      --  Now apply the PushoutLSplit lemma to the following diagram:
      --
      --    Z' ---------> B   
      --    |             |   
      --    |             |
      --    v             v
      --    A' ---------> W'
      --    |             |
      --    |             |
      --    v             v
      --    A ----------> W'' ≃ W ≃ X
      --
      
      W''-equiv-X : W'' ≃ X
      W''-equiv-X = PS.split-equiv

        where module PS = PushoutLSplit {A = A'} {B = A} {C = B} {D = Z'} fst fst (fst ∘ snd)

      --
      --  Now we switch gears and take pullbacks.  We
      --  have the following diagram:
      --
      -- U'' ≃  U' ≃ U ---------> B  
      --             |            |
      --             |            |
      --             v            v
      --        A' ≃ V ---------> W'  outer = cospan₀
      --             |            |
      --             |  cospan₂   |
      --             v            v
      --             A ---------> X ≃ W''

      -- cospan₀ = cospan A B X left (right ∘ W'.bmright)
      -- cospan₁ = cospan A B W'' left right
      -- cospan₂ = cospan A W' X left right

      V = Pullback (cospan A W' X left right)

      U = Pullback (cospan A B X left (right ∘ W'.bmright))
      U' = Pullback (cospan A B W'' left right)
      U'' = Pullback (cospan V B W' Pullback.b right)
      
      U≃U'' : U ≃ U''
      U≃U'' = PBSplit.split-equiv

        where module PBSplit = PullbackLSplit {A = W'} {B = B} {C = A} {D = X} right right left

      --
      --  The map A' --> A is a mono.  Hence by
      --  the PushoutMono lemma we get that it
      --  is also a pullback and consequently 
      --  equivalent to V
      --
      
      V≃A' : V ≃ A'
      V≃A' = (ML.pushout-mono-is-pullback) ⁻¹ ∘e (pullback-decomp-equiv (cospan A W' X left right))
      
        where module ML = MonoLemma
                (span A W' A' fst left)
                (λ b → equiv-preserves-level ((hfiber-fst b) ⁻¹) Trunc-level)

      -- We need this for commutivity below
      V≃A'-coh : (v : V) → Pullback.b v == left (fst V≃A' v)
      V≃A'-coh (pullback a b h) = {!(fst V-equiv-A' (pullback a b h))!}

      --
      --  Now on to the main theorem
      --

      A×WB = Pullback (cospan A B W left right)
      A'×W'B = Pullback (cospan A' B W' left right)

      U''≃A'×W'B : U'' ≃ A'×W'B
      U''≃A'×W'B = Pullback-emap cospan-eqv

        where cospan-eqv : CospanEquiv (cospan V B W' Pullback.b right)
                                       (cospan A' B W' left right)
              cospan-eqv = (cospan-map (fst (V≃A')) (idf B) (idf W')
                                       (comm-sqr V≃A'-coh) 
                                       (comm-sqr (λ b → idp))) ,
                                       snd (V≃A') ,
                                       idf-is-equiv B ,
                                       idf-is-equiv W'
              

      A×WB≃U : A×WB ≃ U
      A×WB≃U = Pullback-emap cospan-eqv

        where cospan-eqv : CospanEquiv (cospan A B W left right) (cospan A B X left (right ∘ W'.bmright))
              cospan-eqv = (cospan-map (idf A) (idf B) (fst (W''-equiv-X ∘e W-equiv-W''))
                                       (comm-sqr (λ a → idp))
                                       (comm-sqr (λ b → idp))) ,
                                       idf-is-equiv A ,
                                       (idf-is-equiv B) ,
                                       (snd (W''-equiv-X ∘e W-equiv-W''))

      pullback-equiv : A×WB ≃ A'×W'B
      pullback-equiv = A×WB ≃⟨ A×WB≃U ⟩
                       U ≃⟨ U≃U'' ⟩ 
                       U'' ≃⟨ U''≃A'×W'B ⟩ 
                       A'×W'B ≃∎
      
