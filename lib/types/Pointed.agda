{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Suspension
open import lib.types.Truncation

module lib.types.Pointed where

Ptd : ∀ i → Type (lsucc i)
Ptd i = Σ (Type i) (λ A → A)

∙[_,_] : ∀ {i} (A : Type i) (a : A) → Ptd i
∙[_,_] = _,_

_∙→_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
(A , a₀) ∙→ (B , b₀) = ∙[ Σ (A → B) (λ f → f a₀ == b₀) , ((λ _ → b₀), idp) ]

ptd[_,_] = ∙[_,_]
_ptd->_ = _∙→_

infixr 2 _∘ptd_

_∘ptd_ : ∀ {i j k} {A : Ptd i} {B : Ptd j} {C : Ptd k}
  (g : fst (B ∙→ C)) (f : fst (A ∙→ B)) → fst (A ∙→ C)
(g , gpt) ∘ptd (f , fpt) = (g ∘ f) , (ap g fpt ∙ gpt)

∘ptd-assoc : ∀ {i j k l} {A : Ptd i} {B : Ptd j} {C : Ptd k} {D : Ptd l}
  (h : fst (C ∙→ D)) (g : fst (B ∙→ C)) (f : fst (A ∙→ B))
  → ((h ∘ptd g) ∘ptd f) == (h ∘ptd (g ∘ptd f))
∘ptd-assoc (h , hpt) (g , gpt) (f , fpt) = pair= idp (lemma fpt gpt hpt)
  where 
  lemma : ∀ {x} {y} (fpt : x == y) → ∀ gpt → ∀ hpt →
          ap (h ∘ g) fpt ∙ ap h gpt ∙ hpt == ap h (ap g fpt ∙ gpt) ∙ hpt
  lemma idp gpt hpt = idp
    -- ap (h ∘ g) fpt ∙ ap h gpt ∙ hpt
    --   =⟨ ap-∘ h g fpt |in-ctx (λ w → w ∙ ap h gpt ∙ hpt) ⟩
    -- ap h (ap g fpt) ∙ ap h gpt ∙ hpt
    --   =⟨ ! (∙-assoc (ap h (ap g fpt)) (ap h gpt) hpt) ⟩
    -- (ap h (ap g fpt) ∙ ap h gpt) ∙ hpt
    --   =⟨ ∙-ap h (ap g fpt) gpt |in-ctx (λ w → w ∙ hpt) ⟩
    -- ap h (ap g fpt ∙ gpt) ∙ hpt ∎

{- Pointed versions of existing types -}
module _ {i} where

  Ptd-Susp : Ptd i → Ptd i
  Ptd-Susp (A , _) = ∙[ Suspension A , north A ]

  Ptd-Trunc : ℕ₋₂ → Ptd i → Ptd i
  Ptd-Trunc n (A , a) = ∙[ Trunc n A , [ a ] ]

{- Equality of pointed types from an equivalence -}
ptd-ua : ∀ {i} {A B : Type i} {a₀ : A} {b₀ : B}
  (e : A ≃ B) → –> e a₀ == b₀ → ∙[ A , a₀ ] == ∙[ B , b₀ ]
ptd-ua e p = pair= (ua e) (↓-idf-ua-in e p)

