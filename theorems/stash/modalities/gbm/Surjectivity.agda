{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities
import stash.modalities.gbm.Pushout

module stash.modalities.gbm.Surjectivity {ℓ} (M : Modality ℓ) where

  open Modality M
  
  Relation : Type ℓ → Type ℓ → Type (lsucc ℓ)
  Relation A B = A → B → Type ℓ

  BM-Relation : {A : Type ℓ} {B : Type ℓ} (R : Relation A B) → Type ℓ
  BM-Relation {A} {B} Q =
    {a₀ : A} {b₀ : B} (q₀ : Q a₀ b₀)
    {a₁ : A} (q₁ : Q a₁ b₀)
    {b₁ : B} (q₂ : Q a₀ b₁) → 
    is-◯-connected (((a₀ , q₀) == (a₁ , q₁)) * ((b₀ , q₀) == (b₁ , q₂)))

  prop-lemma : {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
               (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
               x₀ == x₁ [ (fst ∘ P) ↓ p ]
  prop-lemma P idp x₀ x₁ = prop-has-all-paths (snd (P _)) x₀ x₁              

  pths-ovr-is-prop : {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
                     (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
                     is-prop (x₀ == x₁ [ (fst ∘ P) ↓ p ])
  pths-ovr-is-prop P idp x₀ x₁ = =-preserves-level (snd (P _))                             
  
  module _ {A : Type ℓ} {B : Type ℓ} (Q : Relation A B) where

    --
    --  Right, so to finish the theorem, you need to show two things:
    --
    --  1) The implication below, so that you can apply the theorem
    --     with the new hypothesis on the restricted fibration
    --
    --  2) That the space a' == b' ≃ a == b
    --

    private

      A' : Type ℓ
      A' = Σ A λ a → Trunc -1 (Σ B λ b → Q a b)

    RestrictionOf : Relation A' B
    RestrictionOf (a , _) b = Q a b

    private
      Q' = RestrictionOf
      
    claim₀ : (a₀ a₁ : A') → (a₀ == a₁) ≃ (fst a₀ == fst a₁)
    claim₀ a₀ a₁ = Subtype=-econv ((λ a → Trunc -1 (Σ B λ b → Q a b)), λ a → Trunc-level) a₀ a₁ ⁻¹

    next-claim : {a₀ a₁ : A'} {b : B} (q₀ : Q' a₀ b) (q₁ : Q' a₁ b) (p : a₀ == a₁)
                 → (q₀ == q₁ [ (λ a → Q' a b) ↓ p ]) ≃ (q₀ == q₁ [ (λ a → Q a b) ↓ fst= p ])
    next-claim q₀ q₁ idp = ide (q₀ == q₁)                 

    thm : BM-Relation Q → BM-Relation Q'
    thm H {a₀} {b₀} q₀ {a₁} q₁ {b₁} q₂ = equiv-preserves-◯-conn claim₂ (H {fst a₀} {b₀} q₀ {fst a₁} q₁ {b₁} q₂)

      where claim₁ : (a₀ , q₀ == a₁ , q₁) ≃ (fst a₀ , q₀ == fst a₁ , q₁)
            claim₁ = (=Σ-econv (fst a₀ , q₀) (fst a₁ , q₁))
              ∘e (Σ-emap-l (λ p → q₀ == q₁ [ (λ a → Q a b₀) ↓ p ]) (claim₀ a₀ a₁))
              ∘e Σ-emap-r (next-claim q₀ q₁) 
              ∘e (=Σ-econv (a₀ , q₀) (a₁ , q₁)) ⁻¹

            claim₂ : ((fst a₀ , q₀ == fst a₁ , q₁) * (b₀ , q₀ == b₁ , q₂)) ≃
                     ((a₀ , q₀ == a₁ , q₁) * (b₀ , q₀ == b₁ , q₂))
            claim₂ = *-emap (claim₁ ⁻¹) (ide _)                            

    open import stash.modalities.gbm.PushoutMono
    open import stash.modalities.gbm.PullbackSplit
    open import homotopy.PushoutSplit

    private

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
      
      equiv-span₀₁ : SpanEquiv span₀ span₁
      equiv-span₀₁ = (span-map (idf A) (idf B) Z-to-Z'
        (comm-sqr (λ a → idp))
        (comm-sqr (λ b → idp))) ,
          ( idf-is-equiv A
          , idf-is-equiv B
          , Z-to-Z'-equiv)

      equiv-pushout₀₁ : W ≃ W''
      equiv-pushout₀₁ = Pushout-emap equiv-span₀₁

      X = Pushout (span A W' A' fst left)
      
      --
      --  Now apply the PushoutLSplit lemma to the following diagram:
      --
      --    Z' ---------> B   
      --    |             |   
      --    |             |
      --    v             v
      --    A' ---------> W'   outer = span₁
      --    |             |
      --    |   span₂     |
      --    v             v
      --    A ----------> W'' ≃ X ≃ W
      --
      
      po-split-lemma : W'' ≃ X
      po-split-lemma = PS.split-equiv

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

      cospan₀ = cospan A B X left (right ∘ W'.bmright)
      cospan₁ = cospan A B W'' left right
      cospan₂ = cospan A W' X left right

      V = Pullback (cospan A W' X left right)

      U = Pullback cospan₀
      U' = Pullback cospan₁
      U'' = Pullback (cospan V B W' Pullback.b right)
      
      pb-split-lemma : U ≃ U''
      pb-split-lemma = PBSplit.split-equiv

        where module PBSplit = PullbackLSplit {A = W'} {B = B} {C = A} {D = X} right right left
      
      cospan-equiv₀₁ : CospanEquiv cospan₁ cospan₀
      cospan-equiv₀₁ = (cospan-map (idf A) (idf B) (fst (po-split-lemma))
        (comm-sqr (λ a → idp))
        (comm-sqr (λ b → idp))) ,
          idf-is-equiv A ,
          idf-is-equiv B ,
          snd (po-split-lemma)

      U'-equiv-U : U' ≃ U
      U'-equiv-U = Pullback-emap cospan-equiv₀₁

      --
      --  The map A' --> A is a mono.  Hence by
      --  the PushoutMono lemma we get that it
      --  is also a pullback and consequently 
      --  equivalent to V
      --
      
      V-equiv-A' : V ≃ A'
      V-equiv-A' = (ML.pushout-mono-is-pullback) ⁻¹ ∘e (pullback-decomp-equiv cospan₂)
      
        where module ML = MonoLemma
                (span A W' A' fst left)
                (λ b → equiv-preserves-level ((hfiber-fst b) ⁻¹) Trunc-level)

      
      --
      --  Now on to the main theorem
      --

      A×WB = Pullback (cospan A B W left right)
      A'×W'B = Pullback (cospan A' B W' left right)

      U''-equiv-A'×W'B : U'' ≃ A'×W'B
      U''-equiv-A'×W'B = Pullback-emap cospan-eqv

        where cospan-eqv : CospanEquiv (cospan V B W' Pullback.b right)
                                       (cospan A' B W' left right)
              cospan-eqv = (cospan-map (fst (V-equiv-A')) (idf B) (idf W')
                                       (comm-sqr (λ v → {!!})) -- have to show this commutes
                                       (comm-sqr (λ b → idp))) ,
                                       snd (V-equiv-A') ,
                                       idf-is-equiv B ,
                                       idf-is-equiv W'

      A×WB-equiv-U : A×WB ≃ U
      A×WB-equiv-U = Pullback-emap cospan-eqv

        where cospan-eqv : CospanEquiv (cospan A B W left right) cospan₀
              cospan-eqv = (cospan-map (idf A) (idf B) (fst (po-split-lemma ∘e equiv-pushout₀₁))
                                       (comm-sqr (λ a → idp))
                                       (comm-sqr (λ b → idp))) ,
                                       idf-is-equiv A ,
                                       (idf-is-equiv B) ,
                                       (snd (po-split-lemma ∘e equiv-pushout₀₁))

      pullback-equiv : A×WB ≃ A'×W'B
      pullback-equiv = A×WB ≃⟨ A×WB-equiv-U ⟩
                       U ≃⟨ pb-split-lemma ⟩ 
                       U'' ≃⟨ U''-equiv-A'×W'B ⟩ 
                       A'×W'B ≃∎
      
