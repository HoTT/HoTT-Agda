{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma

{-
This file contains various lemmas that rely on lib.types.Paths or
functional extensionality for pointed maps.
-}

module lib.types.Pointed where

{- Pointed maps -}

-- function extensionality for pointed maps
⊙λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  (p : ∀ x → fst f x == fst g x) (α : snd f == snd g [ (λ y → y == snd Y) ↓ p (snd X) ])
  → f == g
⊙λ= {g = g} p α =
  pair= (λ= p) (↓-app=cst-in (↓-idf=cst-out α ∙ ap (_∙ snd g) (! (app=-β p _))))

{-
⊙λ=' : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  (p : ∀ x → fst f x == fst g x) (α : snd f == p (snd X) ∙ snd g)
  → f == g
⊙λ=' p α = ⊙λ= p (↓-idf=cst-in α)
-}

-- associativity of pointed maps
⊙∘-assoc-pt : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {a₁ a₂ : A} (f : A → B) {b : B} (g : B → C) {c : C}
  (p : a₁ == a₂) (q : f a₂ == b) (r : g b == c)
  → ⊙∘-pt (g ∘ f) p (⊙∘-pt g q r) == ⊙∘-pt g (⊙∘-pt f p q) r
⊙∘-assoc-pt _ _ idp _ _ = idp

⊙∘-assoc : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (h : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ((h ⊙∘ g) ⊙∘ f) == (h ⊙∘ (g ⊙∘ f))
⊙∘-assoc (h , hpt) (g , gpt) (f , fpt) = ⊙λ= (λ _ → idp) (⊙∘-assoc-pt g h fpt gpt hpt)

{- Pointed equivalences -}

-- Extracting data from an pointed equivalence
module _ {i j} {X : Ptd i} {Y : Ptd j} (⊙e : X ⊙≃ Y) where

  private
    e : fst X ≃ fst Y
    e = (fst (fst ⊙e) , snd ⊙e)

  ⊙≃-to-≃ = e

  ⊙–>-pt : –> e (snd X) == snd Y
  ⊙–>-pt = snd (fst ⊙e)

  private
    p = ⊙–>-pt

  ⊙–> : X ⊙→ Y
  ⊙–> = fst ⊙e

  ⊙<–-pt : <– e (snd Y) == snd X
  ⊙<–-pt = ap (<– e) (! ⊙–>-pt) ∙ <–-inv-l e (snd X)

  ⊙<– : Y ⊙→ X
  ⊙<– = <– e , ⊙<–-pt

  infix 120 _⊙⁻¹
  _⊙⁻¹ : Y ⊙≃ X
  _⊙⁻¹ = ⊙<– , is-equiv-inverse (snd ⊙e)

  ⊙<–-inv-l : ⊙<– ⊙∘ ⊙–> == ⊙idf _
  ⊙<–-inv-l = ⊙λ= (<–-inv-l e) $ ↓-idf=cst-in $
    ap (<– e) p ∙ ap (<– e) (! p) ∙ <–-inv-l e (snd X)
      =⟨ ! (∙-assoc (ap (<– e) p) (ap (<– e) (! p)) (<–-inv-l e (snd X))) ⟩
    (ap (<– e) p ∙ ap (<– e) (! p)) ∙ <–-inv-l e (snd X)
      =⟨ ∙-ap (<– e) p (! p) ∙ ap (ap (<– e)) (!-inv-r p)
         |in-ctx (λ w → w ∙ <–-inv-l e (snd X)) ⟩
    <–-inv-l e (snd X)
      =⟨ ! (∙-unit-r _) ⟩
    <–-inv-l e (snd X) ∙ idp =∎

  ⊙<–-inv-r : ⊙–> ⊙∘ ⊙<– == ⊙idf _
  ⊙<–-inv-r = ⊙λ= (<–-inv-r e) $ ↓-idf=cst-in $
    ap (–> e) (ap (<– e) (! p) ∙ <–-inv-l e (snd X)) ∙ p
      =⟨ ap-∙ (–> e) (ap (<– e) (! p)) (<–-inv-l e (snd X))
         |in-ctx (λ w → w ∙ p) ⟩
    (ap (–> e) (ap (<– e) (! p)) ∙ ap (–> e) (<–-inv-l e (snd X))) ∙ p
      =⟨ <–-inv-adj e (snd X)
         |in-ctx (λ w → (ap (–> e) (ap (<– e) (! p)) ∙ w) ∙ p) ⟩
    (ap (–> e) (ap (<– e) (! p)) ∙ <–-inv-r e (–> e (snd X))) ∙ p
      =⟨ ∘-ap (–> e) (<– e) (! p)
         |in-ctx (λ w → (w ∙ <–-inv-r e (–> e (snd X))) ∙ p) ⟩
    (ap (–> e ∘ <– e) (! p) ∙ <–-inv-r e (–> e (snd X))) ∙ p
      =⟨ ap (_∙ p) (! (↓-app=idf-out (apd (<–-inv-r e) (! p))))  ⟩
    (<–-inv-r e (snd Y) ∙' (! p)) ∙ p
      =⟨ ∙'=∙ (<–-inv-r e (snd Y)) (! p) |in-ctx _∙ p ⟩
    (<–-inv-r e (snd Y) ∙ (! p)) ∙ p
      =⟨ ∙-assoc (<–-inv-r e (snd Y)) (! p) p ⟩
    <–-inv-r e (snd Y) ∙ (! p ∙ p)
      =⟨ !-inv-l p |in-ctx (<–-inv-r e (snd Y)) ∙_ ⟩
    <–-inv-r e (snd Y) ∙ idp =∎

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} (⊙e : X ⊙≃ Y) where

  post⊙∘-is-equiv : is-equiv (λ (k : Z ⊙→ X) → ⊙–> ⊙e ⊙∘ k)
  post⊙∘-is-equiv = is-eq f g f-g g-f
    where f = ⊙–> ⊙e ⊙∘_
          g = ⊙<– ⊙e ⊙∘_
          f-g = λ k → ! (⊙∘-assoc (⊙–> ⊙e) (⊙<– ⊙e) k) ∙ ap (_⊙∘ k) (⊙<–-inv-r ⊙e) ∙ ⊙∘-unit-l k
          g-f = λ k → ! (⊙∘-assoc (⊙<– ⊙e) (⊙–> ⊙e) k) ∙ ap (_⊙∘ k) (⊙<–-inv-l ⊙e) ∙ ⊙∘-unit-l k

  pre⊙∘-is-equiv : is-equiv (λ (k : Y ⊙→ Z) → k ⊙∘ ⊙–> ⊙e)
  pre⊙∘-is-equiv = is-eq f g f-g g-f
    where f = _⊙∘ ⊙–> ⊙e
          g = _⊙∘ ⊙<– ⊙e
          f-g = λ k → ⊙∘-assoc k (⊙<– ⊙e) (⊙–> ⊙e) ∙ ap (k ⊙∘_) (⊙<–-inv-l ⊙e) ∙ ⊙∘-unit-r k
          g-f = λ k → ⊙∘-assoc k (⊙–> ⊙e) (⊙<– ⊙e) ∙ ap (k ⊙∘_) (⊙<–-inv-r ⊙e) ∙ ⊙∘-unit-r k

  pre⊙∘-equiv : (Y ⊙→ Z) ≃ (X ⊙→ Z)
  pre⊙∘-equiv = _ , pre⊙∘-is-equiv
