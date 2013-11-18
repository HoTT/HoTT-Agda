{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation
open import Integers

-- Formalization of 0-truncated groups
module Algebra.Groups where

-- A pregroup is a group whose carrier is not a required to be a set (but
-- without higher coherences)

record pregroup i : Set (suc i) where
  -- constructor pregroup
  field
    -- Stuff
    carrier : Set i  -- \|

    -- Structure
    _∙_ : carrier → carrier → carrier  -- \.
    e : carrier
    _′ : carrier → carrier  -- \'

    -- Properties
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    right-unit : ∀ x → x ∙ e ≡ x
    left-unit : ∀ x → e ∙ x ≡ x
    right-inverse : ∀ x → x ∙ (x ′) ≡ e
    left-inverse : ∀ x → (x ′) ∙ x ≡ e

record group i : Set (suc i) where
  -- constructor group
  field
    pre : pregroup i
  open pregroup pre
  field
    set : is-set carrier
  open pregroup pre public

-- Group structure on [unit]
unit-group : ∀ {i} → group i
unit-group {i} = record
  { pre = record
    { carrier = unit
    ; _∙_ = λ _ _ → tt
    ; e = tt
    ; _′ = λ _ → tt
    ; assoc = λ _ _ _ → refl
    ; right-unit = λ _ → refl
    ; left-unit = λ _ → refl
    ; right-inverse = λ _ → refl
    ; left-inverse = λ _ → refl
    }
  ; set = unit-is-set
  }

postulate  -- Tedious because I have a terrible definition of groups
  unit-group-unique : ∀ {i} (G : group i) →
    let open group G in (c : is-contr carrier) → G ≡ unit-group

unit-group-unique' : ∀ {i} (G : group i) →
  let open group G in (c : is-contr carrier) → G ≡ unit-group
unit-group-unique' G (center , contr) = {!!}

-- Every pregroup can be truncated to a group
π₀-pregroup : ∀ {i} → pregroup i → group i
π₀-pregroup pre = record
  { pre = record
    { carrier = carrier₀
    ; _∙_ = _•₀_
    ; e = e₀
    ; _′ = _′₀
    ; assoc = assoc₀
    ; right-unit = right-unit₀
    ; left-unit = left-unit₀
    ; right-inverse = right-inverse₀
    ; left-inverse = left-inverse₀
    }
  ; set = carrier₀-is-set
  } where

    open pregroup pre

    carrier₀ : Set _
    carrier₀ = π₀ carrier

    carrier₀-is-set : is-set carrier₀
    carrier₀-is-set = π₀-is-set carrier

    _•₀_ : carrier₀ → carrier₀ → carrier₀
    _•₀_ = π₀-extend-nondep ⦃ →-is-set $ carrier₀-is-set ⦄
              (λ x → π₀-extend-nondep ⦃ carrier₀-is-set ⦄
                (λ y → proj (x ∙ y)))

    e₀ : π₀ carrier
    e₀ = proj e

    _′₀ : carrier₀ → carrier₀
    _′₀ = π₀-extend-nondep ⦃ carrier₀-is-set ⦄ (λ x → proj (x ′))

    abstract
      assoc₀ : ∀ x y z → (x •₀ y) •₀ z ≡ x •₀ (y •₀ z)
      assoc₀ =
        (π₀-extend ⦃ λ _ → Π-is-set λ _ → Π-is-set λ _ → ≡-is-set carrier₀-is-set ⦄
          (λ x → π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set carrier₀-is-set ⦄
            (λ y → π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
              (λ z → ap proj (assoc x y z)))))

    abstract
      right-unit₀ : ∀ x → x •₀ e₀ ≡ x
      right-unit₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ right-unit))

    abstract
      left-unit₀ : ∀ x → e₀ •₀ x ≡ x
      left-unit₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ left-unit))

    abstract
      right-inverse₀ : ∀ x → x •₀ (x ′₀) ≡ e₀
      right-inverse₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ right-inverse))

    abstract
      left-inverse₀ : ∀ x → (x ′₀) •₀ x ≡ e₀
      left-inverse₀ =
        (π₀-extend ⦃ λ _ → ≡-is-set carrier₀-is-set ⦄
          (ap proj ◯ left-inverse))

-- Not used

is-group-morphism : ∀ {i j} (G : group i) (H : group j)
                  → let open group in (f : carrier G → carrier H)
                  → Set (max i j)
is-group-morphism G H f = let open group in
    ∀ x y → f (_∙_ G x y) ≡ _∙_ H (f x) (f y)

group-iso : ∀ {i j} → (G : group i) (H : group j) → Set (max i j)
group-iso G H = let open group in
  Σ (carrier G → carrier H) (λ f → (is-equiv f × is-group-morphism G H f))

Σ-group : ∀ i → Set (suc i)
Σ-group  i = Σ (Set i) (λ A →
             Σ (A → A → A) (λ m →
             Σ A           (λ e →
             Σ (A → A)     (λ inv →
             (∀ x y z → m (m x y) z ≡ m x (m y z))
             × (∀ x → m x e ≡ x)
             × (∀ x → m e x ≡ x)
             × (∀ x → m x (inv x) ≡ e)
             × (∀ x → m (inv x) x ≡ e)
             × is-set A))))

group-to-Σ : ∀ {i} → group i ≃ Σ-group i
group-to-Σ {i} = (there , (iso-is-eq there back inv₁ inv₂)) where
  there : group i → Σ-group i
  there G = 
    let open group G in
    carrier ,
    (_∙_    ,
    (e      ,
    (_′     ,
    (assoc , (right-unit , (left-unit , (right-inverse , (left-inverse , set))))))))

  back : Σ-group i → group i
  back (car , (m , (e , (inv , (assoc , (ru , (lu , (ri , (li , set))))))))) = record {
    pre = record {
            carrier = car;
            _∙_ = m;
            e = e;
            _′ = inv;
            assoc = assoc;
            right-unit = ru;
            left-unit = lu;
            right-inverse = ri;
            left-inverse = li };
    set = set
    }

  inv₁ : ∀ (G : Σ-group i) → there (back G) ≡ G
  inv₁ G = refl

  inv₂ : ∀ (G : group i) → back (there G) ≡ G
  inv₂ G = refl

group-iso-is-eq : ∀ {i} {G H : group i} → group-iso G H → G ≡ H
group-iso-is-eq {i} {G = G} {H = H} (f , (eq , hom)) = {!!} where
  G' : Σ-group i
  G' = group-to-Σ ☆ G

  H' : Σ-group i
  H' = group-to-Σ ☆ H

  eq-sethood-proofs : let open group H in (s t : is-set carrier) → s ≡ t
  eq-sethood-proofs s t = π₂ contr s ∘ ! (π₂ contr t) where
    open group H
    contr : Σ (is-set carrier) (λ p → ∀ q → q ≡ p)
    contr = inhab-prop-is-contr set is-set-is-prop

  inhab-prop-contr : ∀ {i} {A : Set i} → is-prop A → A → ((x y : A) → x ≡ y)
  inhab-prop-contr {A = A} prop a x y = π₂ contr x ∘ ! (π₂ contr y) where
    contr : Σ A (λ c → ∀ z → z ≡ c)
    contr = inhab-prop-is-contr a prop

  trust-me : ∀ {i} {A : Set i} → A
  trust-me = ?

  eq-as-Σ : G' ≡ H'
  eq-as-Σ = Σ-eq (eq-to-path (f , eq)) (
            Σ-eq (funext (λ x → funext (λ y → {!!}))) (
            Σ-eq (trust-me ) (
            Σ-eq (trust-me ) (
            Σ-eq (trust-me ) (
            Σ-eq (trust-me ) (
            Σ-eq (trust-me ) (
            Σ-eq (trust-me ) (Σ-eq (inhab-prop-contr ? ? ? ?) (eq-sethood-proofs _ _)))))))))

-- is-group-morphism : ∀ {i j} (A : Group i) (B : Group j)
-- (f : ∣ g A ∣ → ∣ g B ∣)
--   → Set (max i j)
-- is-group-morphism A B f =
--   (x y : ∣ g A ∣) → f (_∙_ (g A) x y) ≡ _∙_ (g B) (f x) (f y)

-- _≈_ : ∀ {i j} (A : Group i) (B : Group j) → Set (max i j)
-- A ≈ B = Σ (∣ g A ∣ → ∣ g B ∣) (λ f → is-equiv f × is-group-morphism A B f)
