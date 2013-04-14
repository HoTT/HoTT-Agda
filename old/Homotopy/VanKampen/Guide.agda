{-# OPTIONS --without-K #-}

open import Base

module Homotopy.VanKampen.Guide where

open import Homotopy.Truncation
open import Homotopy.Connected

record legend i (city : Set i) : Set (suc i) where
  constructor leg_,_,_
  field
    name : Set i
    loc : name → city
    all-listed : ∀ c → [ hfiber loc c ]

id-legend : ∀ {i} (A : Set i) → legend i A
id-legend A = leg A , id A , λ x → proj $ x , refl

private
  module Book {i} {city : Set i} {l : legend i city} where
    open legend l

    private
      data #guide : Set i where
        #point : name → #guide

    guide : Set i
    guide = #guide

    point : name → guide
    point = #point

    postulate  -- HIT
      route : ∀ n₁ n₂ → loc n₁ ≡ loc n₂ → point n₁ ≡ point n₂

    guide-rec : ∀ {l} (P : guide → Set l)
      (point* : (n : name) → P (point n))
      (route* : ∀ n₁ n₂ (p : loc n₁ ≡ loc n₂)
        → transport P (route n₁ n₂ p) (point* n₁) ≡ point* n₂)
      → (x : guide) → P x
    guide-rec P point* route* (#point n) = point* n

    postulate  -- HIT
      guide-β-route : ∀ {l} (P : guide → Set l)
        (point* : (n : name) → P (point n))
        (route* : ∀ n₁ n₂ (p : loc n₁ ≡ loc n₂)
          → transport P (route n₁ n₂ p) (point* n₁) ≡ point* n₂)
        n₁ n₂ (p : loc n₁ ≡ loc n₂)
        → apd (guide-rec {l} P point* route*) (route n₁ n₂ p)
        ≡ route* n₁ n₂ p

    guide-rec-nondep : ∀ {l} (P : Set l) (point* : name → P)
      (route* : ∀ n₁ n₂ → loc n₁ ≡ loc n₂ → point* n₁ ≡ point* n₂)
      → (guide → P)
    guide-rec-nondep P point* route* (#point n) = point* n

    postulate  -- HIT
      guide-β-route-nondep : ∀ {l} (P : Set l) (point* : name → P)
        (route* : ∀ n₁ n₂ → loc n₁ ≡ loc n₂ → point* n₁ ≡ point* n₂)
        n₁ n₂ (p : loc n₁ ≡ loc n₂)
        → ap (guide-rec-nondep P point* route*) (route n₁ n₂ p)
        ≡ route* n₁ n₂ p

open Book public hiding (guide)

module _ {i} {city : Set i} (l : legend i city) where
  open legend l

  guide : Set i
  guide = Book.guide {i} {city} {l}

  visit : guide → city
  visit = guide-rec-nondep city loc (λ _ _ p → p)

  visit-β-route : ∀ n₁ n₂ (p : loc n₁ ≡ loc n₂) → ap visit (route n₁ n₂ p) ≡ p
  visit-β-route = guide-β-route-nondep city loc (λ _ _ p → p)

  private
    drawn-as-one : ∀ c → is-contr (π₀ $ hfiber visit c)
    drawn-as-one c = []-extend-nondep
      ⦃ is-connected-is-prop ⟨0⟩ ⦄
      ( λ {(n₁ , p₁) → proj (point n₁ , p₁) , π₀-extend
        ⦃ λ _ → ≡-is-set $ π₀-is-set $ hfiber visit c ⦄
        ( uncurry $ guide-rec
          (λ x → ∀ p₂ → proj (x , p₂) ≡ proj (point n₁ , p₁))
          (λ n₂ p₂ → ap proj let p₃ = p₂ ∘ ! p₁ in
            Σ-eq (route n₂ n₁ p₃) $
              transport (λ x → visit x ≡ c) (route n₂ n₁ p₃) p₂
                ≡⟨ trans-app≡cst visit c (route n₂ n₁ p₃) p₂ ⟩
              ! (ap visit (route n₂ n₁ p₃)) ∘ p₂
                ≡⟨ ap (λ x → ! x ∘ p₂) $ visit-β-route n₂ n₁ p₃ ⟩
              ! (p₂ ∘ ! p₁) ∘ p₂
                ≡⟨ ap (λ x → x ∘ p₂) $ opposite-concat p₂ (! p₁) ⟩
              (! (! p₁) ∘ ! p₂) ∘ p₂
                ≡⟨ concat-assoc (! (! p₁)) (! p₂) p₂ ⟩
              ! (! p₁) ∘ (! p₂ ∘ p₂)
                ≡⟨ ap (λ x → ! (! p₁) ∘ x) $ opposite-left-inverse p₂ ⟩
              ! (! p₁) ∘ refl
                ≡⟨ refl-right-unit $ ! (! p₁) ⟩
              ! (! p₁)
                ≡⟨ opposite-opposite p₁ ⟩∎
              p₁
                ∎)
          (λ _ _ _ → funext λ _ → prop-has-all-paths (π₀-is-set _ _ _) _ _))})
      (all-listed c)

  private
    visit-fiber-rec′ : ∀ {j} (P : city → Set j)
      (h₀-point : ∀ n → P (loc n))
      (h₁-route : ∀ n₁ n₂ r → transport P r (h₀-point n₁) ≡ h₀-point n₂)
      → (∀ c → hfiber visit c → P c)
    visit-fiber-rec′ P h₀-p h₁-r c (pt , p₁) =
      transport P p₁ $ guide-rec (P ◯ visit) h₀-p
        (λ n₁ n₂ r →
            transport (P ◯ visit) (route n₁ n₂ r) (h₀-p n₁)
              ≡⟨ ! $ trans-ap P visit (route n₁ n₂ r) $ h₀-p n₁ ⟩
            transport P (ap visit $ route n₁ n₂ r) (h₀-p n₁)
              ≡⟨ ap (λ x → transport P x $ h₀-p n₁) $ visit-β-route n₁ n₂ r ⟩
            transport P r (h₀-p n₁)
              ≡⟨ h₁-r n₁ n₂ r ⟩∎
            h₀-p n₂
              ∎) pt

  visit-fiber-rec : ∀ {j} (P : city → Set j)
    ⦃ _ : ∀ (c : city) → is-set $ P c ⦄
    (h₀-point : ∀ n → P (loc n))
    (h₁-route : ∀ n₁ n₂ r → transport P r (h₀-point n₁) ≡ h₀-point n₂)
    → (∀ c → P c)
  visit-fiber-rec P ⦃ P-is-set ⦄ h₀-p h₁-r c =
    π₀-extend-nondep ⦃ P-is-set c ⦄
    (visit-fiber-rec′ P h₀-p h₁-r c)
    (π₁ $ drawn-as-one c)

  visit-fiber-β-loc : ∀ {j} (P : city → Set j)
    ⦃ P-is-set : ∀ (c : city) → is-set $ P c ⦄
    (h₀-p : ∀ n → P (loc n))
    (h₁-r : ∀ n₁ n₂ r → transport P r (h₀-p n₁) ≡ h₀-p n₂)
    → ∀ n → visit-fiber-rec P ⦃ P-is-set ⦄ h₀-p h₁-r (loc n) ≡ h₀-p n
  visit-fiber-β-loc P ⦃ P-is-set ⦄ h₀-p h₁-r n =
    visit-fiber-rec P ⦃ P-is-set ⦄ h₀-p h₁-r (loc n)
      ≡⟨ ap (π₀-extend-nondep ⦃ P-is-set $ loc n ⦄ (visit-fiber-rec′ P h₀-p h₁-r $ loc n))
            $ ! $ π₂ (drawn-as-one $ loc n) (proj $ point n , refl) ⟩∎
    h₀-p n
      ∎

  private
    loc-fiber-rec′ : ∀ {j} (P : city → Set j)
      (h₀-point : ∀ n → P (loc n))
      → (∀ c → hfiber loc c → P c)
    loc-fiber-rec′ P h₀-p c (n , p) = transport P p (h₀-p n)

  loc-fiber-rec : ∀ {j} (P : city → Set j)
    ⦃ _ : ∀ c → is-prop $ P c ⦄
    (h₀-point : ∀ n → P (loc n))
    → (∀ c → P c)
  loc-fiber-rec P ⦃ P-is-prop ⦄ h₀-p c = []-extend-nondep ⦃ P-is-prop c ⦄
    (loc-fiber-rec′ P h₀-p c) (all-listed c)

  loc-fiber-β-loc : ∀ {j} (P : city → Set j)
    ⦃ P-is-prop : ∀ (c : city) → is-prop $ P c ⦄
    (h₀-p : ∀ n → P (loc n))
    → ∀ n → loc-fiber-rec P ⦃ P-is-prop ⦄ h₀-p (loc n) ≡ h₀-p n
  loc-fiber-β-loc P ⦃ P-is-prop ⦄ h₀-p n =
    loc-fiber-rec P ⦃ P-is-prop ⦄ h₀-p (loc n)
      ≡⟨ ap ([]-extend-nondep ⦃ P-is-prop $ loc n ⦄ (loc-fiber-rec′ P h₀-p $ loc n))
            $ prop-has-all-paths []-is-prop (all-listed $ loc n) $ proj $ n , refl ⟩∎
    h₀-p n
      ∎

-- Did I preserve the computational contents for identity legend?
private
  module IdTest {i} {city : Set i} where
    open legend (id-legend city)

    visit-fiber-β-id : ∀ {j} (P : city → Set j)
      ⦃ P-is-set : ∀ (c : city) → is-set $ P c ⦄
      (h₀-p : ∀ n → P n)
      (h₁-r : ∀ n₁ n₂ r → transport P r (h₀-p n₁) ≡ h₀-p n₂)
      → ∀ n → visit-fiber-rec (id-legend city) P ⦃ P-is-set ⦄ h₀-p h₁-r n ≡ h₀-p n
    visit-fiber-β-id P ⦃ P-is-set ⦄ h₀-p h₁-r n = refl

    loc-fiber-β-id : ∀ {j} (P : city → Set j)
      ⦃ P-is-prop : ∀ (c : city) → is-prop $ P c ⦄
      (h₀-p : ∀ n → P n)
      → ∀ n → loc-fiber-rec (id-legend city) P ⦃ P-is-prop ⦄ h₀-p n ≡ h₀-p n
    loc-fiber-β-id P ⦃ P-is-prop ⦄ h₀-p n = refl
