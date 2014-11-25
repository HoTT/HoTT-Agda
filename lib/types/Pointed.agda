{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma

module lib.types.Pointed where

Ptd : ∀ i → Type (lsucc i)
Ptd i = Σ (Type i) (λ A → A)

Ptd₀ = Ptd lzero

∙[_,_] : ∀ {i} (A : Type i) (a : A) → Ptd i
∙[_,_] = _,_

_∙→_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
(A , a₀) ∙→ (B , b₀) = ∙[ Σ (A → B) (λ f → f a₀ == b₀) , ((λ _ → b₀), idp) ]

infixr 0 _∙→_

_×ptd_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
(A , a₀) ×ptd (B , b₀) = (A × B , (a₀ , b₀))

ptd-fst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ×ptd Y ∙→ X)
ptd-fst = (fst , idp)

ptd-snd : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ×ptd Y ∙→ Y)
ptd-snd = (snd , idp)

ptd[_,_] = ∙[_,_]
_ptd->_ = _∙→_

infixr 4 _∘ptd_

ptd-idf : ∀ {i} (X : Ptd i) → fst (X ∙→ X)
ptd-idf A = ((λ x → x) , idp)

ptd-cst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ∙→ Y)
ptd-cst {Y = Y} = ((λ x → snd Y) , idp)

_∘ptd_ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : fst (Y ∙→ Z)) (f : fst (X ∙→ Y)) → fst (X ∙→ Z)
(g , gpt) ∘ptd (f , fpt) = (g ∘ f) , (ap g fpt ∙ gpt)

∘ptd-unit-l : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : fst (X ∙→ Y))
  → ptd-idf Y ∘ptd f == f
∘ptd-unit-l (f , idp) = idp

∘ptd-assoc : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (h : fst (Z ∙→ W)) (g : fst (Y ∙→ Z)) (f : fst (X ∙→ Y))
  → ((h ∘ptd g) ∘ptd f) == (h ∘ptd (g ∘ptd f))
∘ptd-assoc (h , hpt) (g , gpt) (f , fpt) = pair= idp (lemma fpt gpt hpt)
  where
  lemma : ∀ {x₁ x₂} (fpt : x₁ == x₂) → ∀ gpt → ∀ hpt →
          ap (h ∘ g) fpt ∙ ap h gpt ∙ hpt == ap h (ap g fpt ∙ gpt) ∙ hpt
  lemma idp gpt hpt = idp

{- Obtaining equality of pointed types from an equivalence -}
ptd-ua : ∀ {i} {A B : Type i} {a₀ : A} {b₀ : B}
  (e : A ≃ B) → –> e a₀ == b₀ → ∙[ A , a₀ ] == ∙[ B , b₀ ]
ptd-ua e p = pair= (ua e) (↓-idf-ua-in e p)

{- ∙→ preserves hlevel -}
∙→-level : ∀ {i j} {X : Ptd i} {Y : Ptd j} {n : ℕ₋₂}
  → has-level n (fst Y) → has-level n (fst (X ∙→ Y))
∙→-level pY = Σ-level (Π-level (λ _ → pY)) (λ _ → =-preserves-level _ pY)

{- function extensionality for pointed functions -}
ptd-λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : fst (X ∙→ Y)}
  (p : ∀ x → fst f x == fst g x) (α : snd f == p (snd X) ∙ snd g)
  → f == g
ptd-λ= {g = g} p α =
  pair= (λ= p) (↓-app=cst-in (α ∙ ap (λ w → w ∙ snd g) (! (app=-β p _))))

{- Obtaining pointed maps from an pointed equivalence -}
module _ {i j} {X : Ptd i} {Y : Ptd j} (e : fst X ≃ fst Y)
  (p : –> e (snd X) == snd Y) where

  ∙–> : fst (X ∙→ Y)
  ∙–> = (–> e , p)

  ∙<– : fst (Y ∙→ X)
  ∙<– = (<– e , ap (<– e) (! p) ∙ <–-inv-l e (snd X))
