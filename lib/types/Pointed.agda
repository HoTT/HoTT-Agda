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

_⊙→_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
(A , a₀) ⊙→ (B , b₀) = ⊙[ Σ (A → B) (λ f → f a₀ == b₀) , ((λ _ → b₀), idp) ]

infixr 0 _⊙→_

infixr 4 _⊙∘_

⊙idf : ∀ {i} (X : Ptd i) → fst (X ⊙→ X)
⊙idf A = ((λ x → x) , idp)

⊙cst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙→ Y)
⊙cst {Y = Y} = ((λ x → snd Y) , idp)

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

⊙Σ : ∀ {i j} (X : Ptd i) → (fst X → Ptd j) → Ptd (lmax i j)
⊙Σ (A , a₀) Y = ⊙[ Σ A (fst ∘ Y) , (a₀ , snd (Y a₀)) ]

_⊙×_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙× Y = ⊙Σ X (λ _ → Y)

⊙fst : ∀ {i j} {X : Ptd i} {Y : fst X → Ptd j} → fst (⊙Σ X Y ⊙→ X)
⊙fst = (fst , idp)

⊙snd : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙× Y ⊙→ Y)
⊙snd = (snd , idp)

⊙diag : ∀ {i} {X : Ptd i} → fst (X ⊙→ X ⊙× X)
⊙diag = ((λ x → (x , x)) , idp)

⊙×-in : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → fst (X ⊙→ Y) → fst (X ⊙→ Z) → fst (X ⊙→ Y ⊙× Z)
⊙×-in (f , fpt) (g , gpt) = (λ x → (f x , g x)) , ap2 _,_ fpt gpt

⊙fst-⊙×-in : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Y)) (g : fst (X ⊙→ Z))
  → ⊙fst ⊙∘ ⊙×-in f g == f
⊙fst-⊙×-in (f , idp) (g , idp) = idp

⊙snd-⊙×-in : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Y)) (g : fst (X ⊙→ Z))
  → ⊙snd ⊙∘ ⊙×-in f g == g
⊙snd-⊙×-in (f , idp) (g , idp) = idp

⊙×-in-pre∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : fst (Y ⊙→ Z)) (g : fst (Y ⊙→ W)) (h : fst (X ⊙→ Y))
  → ⊙×-in f g ⊙∘ h == ⊙×-in (f ⊙∘ h) (g ⊙∘ h)
⊙×-in-pre∘ (f , idp) (g , idp) (h , idp) = idp

pair⊙→ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  → fst (X ⊙→ Y) → fst (Z ⊙→ W)
  → fst ((X ⊙× Z) ⊙→ (Y ⊙× W))
pair⊙→ (f , fpt) (g , gpt) =
  ((λ {(x , z) → (f x , g z)}) , pair×= fpt gpt)

{- Obtaining equality of pointed types from an equivalence -}
⊙ua : ∀ {i} {A B : Type i} {a₀ : A} {b₀ : B}
  (e : A ≃ B) → –> e a₀ == b₀ → ⊙[ A , a₀ ] == ⊙[ B , b₀ ]
⊙ua e p = pair= (ua e) (↓-idf-ua-in e p)

{- ⊙→ preserves hlevel -}
⊙→-level : ∀ {i j} {X : Ptd i} {Y : Ptd j} {n : ℕ₋₂}
  → has-level n (fst Y) → has-level n (fst (X ⊙→ Y))
⊙→-level pY = Σ-level (Π-level (λ _ → pY)) (λ _ → =-preserves-level _ pY)

{- function extensionality for pointed functions -}
⊙λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : fst (X ⊙→ Y)}
  (p : ∀ x → fst f x == fst g x) (α : snd f == p (snd X) ∙ snd g)
  → f == g
⊙λ= {g = g} p α =
  pair= (λ= p) (↓-app=cst-in (α ∙ ap (λ w → w ∙ snd g) (! (app=-β p _))))

{- Obtaining pointed maps from an pointed equivalence -}
module _ {i j} {X : Ptd i} {Y : Ptd j} (e : fst X ≃ fst Y)
  (p : –> e (snd X) == snd Y) where

  ⊙–> : fst (X ⊙→ Y)
  ⊙–> = (–> e , p)

  ⊙<– : fst (Y ⊙→ X)
  ⊙<– = (<– e , ap (<– e) (! p) ∙ <–-inv-l e (snd X))

  ⊙<–-inv-l : ⊙<– ⊙∘ ⊙–> == ⊙idf _
  ⊙<–-inv-l = ⊙λ= (<–-inv-l e) $
    ap (<– e) p ∙ ap (<– e) (! p) ∙ <–-inv-l e (snd X)
      =⟨ ! (∙-assoc (ap (<– e) p) (ap (<– e) (! p)) (<–-inv-l e (snd X))) ⟩
    (ap (<– e) p ∙ ap (<– e) (! p)) ∙ <–-inv-l e (snd X)
      =⟨ ∙-ap (<– e) p (! p) ∙ ap (ap (<– e)) (!-inv-r p)
         |in-ctx (λ w → w ∙ <–-inv-l e (snd X)) ⟩
    <–-inv-l e (snd X)
      =⟨ ! (∙-unit-r _) ⟩
    <–-inv-l e (snd X) ∙ idp ∎

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
    <–-inv-r e (snd Y) ∙ idp ∎
    where
    htpy-lemma : ∀ {i} {A : Type i} {f : A → A}
      (p : ∀ z → f z == z) {x y : A} (q : x == y)
      → (ap f (! q) ∙ p x) ∙ q == p y
    htpy-lemma p idp = ∙-unit-r _
