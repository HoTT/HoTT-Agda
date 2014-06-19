{-# OPTIONS --without-K #-}

open import HoTT

{- Useful lemmas for computing the effect of transporting 
 (a) a function A → B along an equivalence B ≃ C 
 (b) a pointed function X ∙→ Y along a basepoint-preserving equivalence X ≃ Y 
-}

module cohomology.CodomainOverEquiv {i} {j} where

module _ {A : Type i} {B C : Type j} (f : A → B) (g : A → C) (e : B ≃ C) where

  codomain-over-equiv : (∀ a → –> e (f a) == g a)
    → f == g [ (λ D → (A → D)) ↓ ua e ]
  codomain-over-equiv p = ↓-cst→app-in $ λ a → ↓-idf-ua-in e (p a)

{- Some lemmas for the pointed case. Are any of these generally useful? -}
private
  ↓-cst2-ap↓ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : A → Type k}
    {D : A → Type l} (f : {a : A} → B a → D a)
    {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    (r : u == v [ B ↓ p ])
    → ↓-cst2-in p q (ap↓ f r) == ap↓ f (↓-cst2-in p q r)
  ↓-cst2-ap↓ f idp idp idp = idp

  ap↓-↓-cst→app : ∀ {i j k} {A : Type i} {B : Type j}
    {C : A → B → Type k} {x x' : A} {p : x == x'}
    {u : (b : B) → C x b} {u' : (b : B) → C x' b}
    (α : (b : B) → u b == u' b [ (λ x → C x b) ↓ p ]) (b₀ : B)
    → ap↓ (λ f → f b₀) (↓-cst→app-in α) == α b₀
  ap↓-↓-cst→app {p = idp} = app=-β

  ap-snd-is-↓-cst2-in : ∀ {i j} {A : Type i} {B : A → Type j}
    {x y : A} (p : x == y)
    {u : B x} {v : B y} (q : u == v [ B ↓ p ])
    → apd snd (pair= p q) == ↓-cst2-in p q q
  ap-snd-is-↓-cst2-in idp idp = idp

abstract
  codomain-over-ptd-equiv : {X : Ptd i} {Y Z : Ptd j}
    (f : fst (X ∙→ Y)) (g : fst (X ∙→ Z))
    (e : fst Y ≃ fst Z) (p : –> e (snd Y) == snd Z) 
    (q : ∀ x → –> e (fst f x) == fst g x)
    (α :  q (snd X) ∙' snd g == ap (–> e) (snd f) ∙ p)
    → f == g [ (λ W → fst (X ∙→ W)) ↓ ptd-ua e p ]
  codomain-over-ptd-equiv {X = X} (f , idp) (g , idp) e p q α = ↓-Σ-in
    (↓-cst2-in (ua e) (↓-idf-ua-in e p)
               (codomain-over-equiv f g e q))
    (↓-=-in $ lemma 
      snd (λ r → r (snd X))
      (pair= (ua e) (↓-idf-ua-in e p))
      (↓-cst2-in (ua e) (↓-idf-ua-in e p) (codomain-over-equiv f g e q))
      idp idp $
        idp ◃ apd snd (pair= (ua e) (↓-idf-ua-in e p))
          =⟨ idp◃ _ ⟩
        apd snd (pair= (ua e) (↓-idf-ua-in e p))
          =⟨ ap-snd-is-↓-cst2-in (ua e) (↓-idf-ua-in e p) ⟩
        ↓-cst2-in (ua e) (↓-idf-ua-in e p) (↓-idf-ua-in e p)
          =⟨ ! α |in-ctx (λ w → 
               ↓-cst2-in (ua e) (↓-idf-ua-in e p) (↓-idf-ua-in e w)) ⟩
        ↓-cst2-in (ua e) (↓-idf-ua-in e p) (↓-idf-ua-in e (q (snd X)))
          =⟨ ! (ap↓-↓-cst→app (↓-idf-ua-in e ∘ q) (snd X))
             |in-ctx (λ w → ↓-cst2-in (ua e) (↓-idf-ua-in e p) w) ⟩
        ↓-cst2-in (ua e) (↓-idf-ua-in e p)
                  (ap↓ (λ r → r (snd X)) (codomain-over-equiv f g e q))
          =⟨ ↓-cst2-ap↓ (λ r → r (snd X)) (ua e) (↓-idf-ua-in e p)
                        (codomain-over-equiv f g e q) ⟩
        ap↓ (λ r → r (snd X)) (↓-cst2-in (ua e) (↓-idf-ua-in e p)
                                         (codomain-over-equiv f g e q))
          =⟨ ! (▹idp _) ⟩
        ap↓ (λ r → r (snd X)) (↓-cst2-in (ua e) (↓-idf-ua-in e p)
                              (codomain-over-equiv f g e q))
        ▹ idp ∎)
    where
    lemma : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
      (f : Π A C) (g : {a : A} → B a → C a)
      {a₁ a₂ : A} (p : a₁ == a₂)
      {b₁ : B a₁} {b₂ : B a₂} (q : b₁ == b₂ [ B ↓ p ])
      (r : g b₁ == f a₁) (s : g b₂ == f a₂)
      → r ◃ apd f p == ap↓ g q ▹ s
      → r ◃ apd (f ∘ fst) (pair= p q) == apd (g ∘ snd) (pair= p q) ▹ s
    lemma f g idp idp r s α = α
