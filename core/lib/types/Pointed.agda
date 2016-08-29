{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma

module lib.types.Pointed where

Ptd : ∀ i → Type (lsucc i)
Ptd i = Σ (Type i) (λ A → A)

Ptd₀ = Ptd lzero

⊙[_,_] : ∀ {i} (A : Type i) (a : A) → Ptd i
⊙[_,_] = _,_

{-
Pointed maps.

Note that [A ⊙→ B] will be pointed as well.
-}

infixr 0 _⊙→_
_⊙→_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
(A , a₀) ⊙→ (B , b₀) = ⊙[ Σ (A → B) (λ f → f a₀ == b₀) , ((λ _ → b₀), idp) ]

⊙idf : ∀ {i} (X : Ptd i) → fst (X ⊙→ X)
⊙idf X = ((λ x → x) , idp)

⊙cst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙→ Y)
⊙cst {Y = Y} = ((λ x → snd Y) , idp)

infixr 80 _⊙∘_
_⊙∘_ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y)) → fst (X ⊙→ Z)
(g , gpt) ⊙∘ (f , fpt) = (g ∘ f) , (ap g fpt ∙ gpt)

⊙∘-unit-l : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : fst (X ⊙→ Y))
  → ⊙idf Y ⊙∘ f == f
⊙∘-unit-l (f , idp) = idp

⊙∘-unit-r : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : fst (X ⊙→ Y))
  → f ⊙∘ ⊙idf X == f
⊙∘-unit-r f = idp

⊙∘-assoc : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (h : fst (Z ⊙→ W)) (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
  → ((h ⊙∘ g) ⊙∘ f) == (h ⊙∘ (g ⊙∘ f))
⊙∘-assoc (h , hpt) (g , gpt) (f , fpt) = pair= idp (lemma fpt gpt hpt)
  where
  lemma : ∀ {x₁ x₂} (fpt : x₁ == x₂) → ∀ gpt → ∀ hpt →
          ap (h ∘ g) fpt ∙ ap h gpt ∙ hpt == ap h (ap g fpt ∙ gpt) ∙ hpt
  lemma idp gpt hpt = idp

-- [⊙→] preserves hlevel
⊙→-level : ∀ {i j} {X : Ptd i} {Y : Ptd j} {n : ℕ₋₂}
  → has-level n (fst Y) → has-level n (fst (X ⊙→ Y))
⊙→-level pY = Σ-level (Π-level (λ _ → pY)) (λ _ → =-preserves-level _ pY)

-- function extensionality for pointed functions
⊙λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : fst (X ⊙→ Y)}
  (p : ∀ x → fst f x == fst g x) (α : snd f == p (snd X) ∙ snd g)
  → f == g
⊙λ= {g = g} p α =
  pair= (λ= p) (↓-app=cst-in (α ∙ ap (λ w → w ∙ snd g) (! (app=-β p _))))

{-
Pointed equivalences
-}

infix 30 _⊙≃_
_⊙≃_ : ∀ {i j} → Ptd i → Ptd j → Type (lmax i j)
X ⊙≃ Y = Σ (fst (X ⊙→ Y)) (λ {(f , _) → is-equiv f})

≃-to-⊙≃ : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  (e : fst X ≃ fst Y) (p : –> e (snd X) == snd Y)
  → X ⊙≃ Y
≃-to-⊙≃ (f , ie) p = ((f , p) , ie)

⊙ide : ∀ {i} (X : Ptd i) → (X ⊙≃ X)
⊙ide X = ⊙idf X , idf-is-equiv (fst X)

infixr 80 _⊙∘e_
_⊙∘e_ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙≃ Z) (f : X ⊙≃ Y) → X ⊙≃ Z
(g , g-eq) ⊙∘e (f , f-eq) = (g ⊙∘ f , g-eq ∘ise f-eq)

infix 15 _⊙≃∎
infixr 10 _⊙≃⟨_⟩_

_⊙≃⟨_⟩_ : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k}
  → X ⊙≃ Y → Y ⊙≃ Z → X ⊙≃ Z
X ⊙≃⟨ u ⟩ v = v ⊙∘e u

_⊙≃∎ : ∀ {i} (X : Ptd i) → X ⊙≃ X
_⊙≃∎ = ⊙ide

-- Extracting data from an pointed equivalence
module _ {i j} {X : Ptd i} {Y : Ptd j} (⊙e : X ⊙≃ Y) where

  private
    e : fst X ≃ fst Y
    e = (fst (fst ⊙e) , snd ⊙e)

    p = snd (fst ⊙e)

  ⊙≃-to-≃ = e

  ⊙–> : fst (X ⊙→ Y)
  ⊙–> = fst ⊙e

  ⊙<– : fst (Y ⊙→ X)
  ⊙<– = (<– e , ap (<– e) (! p) ∙ <–-inv-l e (snd X))

  infix 120 _⊙⁻¹
  _⊙⁻¹ : Y ⊙≃ X
  _⊙⁻¹ = ⊙<– , is-equiv-inv (snd ⊙e)

  ⊙<–-inv-l : ⊙<– ⊙∘ ⊙–> == ⊙idf _
  ⊙<–-inv-l = ⊙λ= (<–-inv-l e) $
    ap (<– e) p ∙ ap (<– e) (! p) ∙ <–-inv-l e (snd X)
      =⟨ ! (∙-assoc (ap (<– e) p) (ap (<– e) (! p)) (<–-inv-l e (snd X))) ⟩
    (ap (<– e) p ∙ ap (<– e) (! p)) ∙ <–-inv-l e (snd X)
      =⟨ ∙-ap (<– e) p (! p) ∙ ap (ap (<– e)) (!-inv-r p)
         |in-ctx (λ w → w ∙ <–-inv-l e (snd X)) ⟩
    <–-inv-l e (snd X)
      =⟨ ! (∙-unit-r _) ⟩
    <–-inv-l e (snd X) ∙ idp =∎

  ⊙<–-inv-r : ⊙–> ⊙∘ ⊙<– == ⊙idf _
  ⊙<–-inv-r = ⊙λ= (<–-inv-r e) $
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
      =⟨ htpy-lemma (<–-inv-r e) p ⟩
    <–-inv-r e (snd Y)
      =⟨ ! (∙-unit-r _) ⟩
    <–-inv-r e (snd Y) ∙ idp =∎
    where
    htpy-lemma : ∀ {i} {A : Type i} {f : A → A}
      (p : ∀ z → f z == z) {x y : A} (q : x == y)
      → (ap f (! q) ∙ p x) ∙ q == p y
    htpy-lemma p idp = ∙-unit-r _

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} (⊙e : X ⊙≃ Y) where

  post⊙∘-is-equiv : is-equiv (λ (k : fst (Z ⊙→ X)) → ⊙–> ⊙e ⊙∘ k)
  post⊙∘-is-equiv = is-eq f g f-g g-f
    where f = ⊙–> ⊙e ⊙∘_
          g = ⊙<– ⊙e ⊙∘_
          f-g = λ k → ! (⊙∘-assoc (⊙–> ⊙e) (⊙<– ⊙e) k) ∙ ap (_⊙∘ k) (⊙<–-inv-r ⊙e) ∙ ⊙∘-unit-l k
          g-f = λ k → ! (⊙∘-assoc (⊙<– ⊙e) (⊙–> ⊙e) k) ∙ ap (_⊙∘ k) (⊙<–-inv-l ⊙e) ∙ ⊙∘-unit-l k

  pre⊙∘-is-equiv : is-equiv (λ (k : fst (Y ⊙→ Z)) → k ⊙∘ ⊙–> ⊙e)
  pre⊙∘-is-equiv = is-eq f g f-g g-f
    where f = _⊙∘ ⊙–> ⊙e
          g = _⊙∘ ⊙<– ⊙e
          f-g = λ k → ⊙∘-assoc k (⊙<– ⊙e) (⊙–> ⊙e) ∙ ap (k ⊙∘_) (⊙<–-inv-l ⊙e) ∙ ⊙∘-unit-r k
          g-f = λ k → ⊙∘-assoc k (⊙–> ⊙e) (⊙<– ⊙e) ∙ ap (k ⊙∘_) (⊙<–-inv-r ⊙e) ∙ ⊙∘-unit-r k

  pre⊙∘-equiv : fst (Y ⊙→ Z) ≃ fst (X ⊙→ Z)
  pre⊙∘-equiv = _ , pre⊙∘-is-equiv

-- [ua] for pointed types
⊙ua : ∀ {i} {X Y : Ptd i} → X ⊙≃ Y → X == Y
⊙ua ((f , p) , ie) = pair= (ua (f , ie)) (↓-idf-ua-in (f , ie) p)

{-
Pointed Σ
-}

⊙Σ : ∀ {i j} (X : Ptd i) → (fst X → Ptd j) → Ptd (lmax i j)
⊙Σ (A , a₀) Y = ⊙[ Σ A (fst ∘ Y) , (a₀ , snd (Y a₀)) ]

infixr 80 _⊙×_
_⊙×_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙× Y = ⊙Σ X (λ _ → Y)

-- XXX Do we really need two versions of [⊙fst]?
⊙fstᵈ : ∀ {i j} {X : Ptd i} (Y : fst X → Ptd j) → fst (⊙Σ X Y ⊙→ X)
⊙fstᵈ Y = (fst , idp)

⊙fst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙× Y ⊙→ X)
⊙fst = ⊙fstᵈ _

⊙snd : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙× Y ⊙→ Y)
⊙snd = (snd , idp)

⊙diag : ∀ {i} {X : Ptd i} → fst (X ⊙→ X ⊙× X)
⊙diag = ((λ x → (x , x)) , idp)

⊙fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → fst (X ⊙→ Y) → fst (X ⊙→ Z) → fst (X ⊙→ Y ⊙× Z)
⊙fanout (f , fpt) (g , gpt) = fanout f g , pair×= fpt gpt

⊙fst-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Y)) (g : fst (X ⊙→ Z))
  → ⊙fst ⊙∘ ⊙fanout f g == f
⊙fst-fanout (f , idp) (g , idp) = idp

⊙snd-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Y)) (g : fst (X ⊙→ Z))
  → ⊙snd ⊙∘ ⊙fanout f g == g
⊙snd-fanout (f , idp) (g , idp) = idp

⊙fanout-pre∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : fst (Y ⊙→ Z)) (g : fst (Y ⊙→ W)) (h : fst (X ⊙→ Y))
  → ⊙fanout f g ⊙∘ h == ⊙fanout (f ⊙∘ h) (g ⊙∘ h)
⊙fanout-pre∘ (f , idp) (g , idp) (h , idp) = idp

⊙×-fmap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → fst (X ⊙→ X') → fst (Y ⊙→ Y') → fst (X ⊙× Y ⊙→ X' ⊙× Y')
⊙×-fmap (f , fpt) (g , gpt) = ×-fmap f g , pair×= fpt gpt

⊙×-emap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → X ⊙≃ X' → Y ⊙≃ Y' → X ⊙× Y ⊙≃ X' ⊙× Y'
⊙×-emap (F , F-ise) (G , G-ise) = ⊙×-fmap F G , ×-isemap F-ise G-ise
