{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.NType

module lib.Equivalences where

record is-equiv {i j} {A : Type i} {B : Type j} (f : A → B) : Type (max i j)
  where
  field
    g : B → A
    f-g : (b : B) → f (g b) == b
    g-f : (a : A) → g (f a) == a
    adj : (a : A) → ap f (g-f a) == f-g (f a)

is-eq : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  (g : B → A) (f-g : (b : B) → f (g b) == b)
  (g-f : (a : A) → g (f a) == a) → is-equiv f
is-eq {A = A} {B = B} f g f-g g-f =
  record {g = g; f-g = f-g'; g-f = g-f; adj = adj} where
    f-g' : (b : B) → f (g b) == b
    f-g' b = ! (ap (f ∘ g) (f-g b)) ∙ ap f (g-f (g b)) ∙ f-g b

    postulate  -- TODO
      adj : (a : A) → ap f (g-f a) == f-g' (f a)
--    adj a = {!!}

_≃_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A ≃ B = Σ (A → B) is-equiv

Equiv = _≃_

equiv : ∀ {i j} {A : Type i} {B : Type j}
  (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
  (g-f : (a : A) → g (f a) == a) → A ≃ B
equiv f g f-g g-f = (f , is-eq f g f-g g-f)

postulate  -- TODO
  is-equiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
    → is-prop (is-equiv f)

–> : ∀ {i} {j} {A : Type i} {B : Type j} (e : A ≃ B) → (A → B)
–> e = fst e

<– : ∀ {i} {j} {A : Type i} {B : Type j} (e : A ≃ B) → (B → A)
<– e = is-equiv.g (snd e)

<–-inv-l : ∀ {i} {j} {A : Type i} {B : Type j} (e : A ≃ B) (a : A)
  → (<– e (–> e a) == a)
<–-inv-l e a = is-equiv.g-f (snd e) a

<–-inv-r : ∀ {i} {j} {A : Type i} {B : Type j} (e : A ≃ B) (b : B)
  → (–> e (<– e b) == b)
<–-inv-r e b = is-equiv.f-g (snd e) b

-- Equivalences are injective
equiv-inj : ∀ {i} {j} {A : Type i} {B : Type j} (e : A ≃ B) {x y : A}
  → (–> e x == –> e y → x == y)
equiv-inj e {x} {y} p = let (f , g) = (–> e , <– e) in
  x       =⟨ ! (<–-inv-l e x) ⟩
  g (f x) =⟨ ap g p ⟩
  g (f y) =⟨ <–-inv-l e y ⟩
  y ∎

_⁻¹ : ∀ {i j} {A : Type i} {B : Type j} → (A ≃ B) → (B ≃ A)
e ⁻¹ = equiv (<– e) (–> e) (<–-inv-l e) (<–-inv-r e)

_∘e_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → B ≃ C → A ≃ B → A ≃ C
e1 ∘e e2 = equiv (–> e1 ∘ –> e2) (<– e2 ∘ <– e1)
  (λ c → –> e1 (–> e2 (<– e2 (<– e1 c)))
                   =⟨ <–-inv-r e2 (<– e1 c) |in-ctx (–> e1) ⟩
         –> e1 (<– e1 c)  =⟨ <–-inv-r e1 c ⟩
         c ∎)
  (λ a → <– e2 (<– e1 (–> e1 (–> e2 a)))
                   =⟨ <–-inv-l e1 (–> e2 a) |in-ctx (<– e2) ⟩
         <– e2 (–> e2 a)  =⟨ <–-inv-l e2 a ⟩
         a ∎)

-- Any contractible type is equivalent to the unit type
contr-equiv-Unit : ∀ {i j} {A : Type i} → (is-contr A → A ≃ Lift {j = j} ⊤)
contr-equiv-Unit e = equiv (λ _ → lift tt) (λ _ → fst e) (λ _ → idp) (λ a → snd e a)


-- An equivalence induces an equivalence on the path spaces
-- The proofs here can probably be simplified
module _ {i j} {A : Type i} {B : Type j} (e : A ≃ B) where

  private
    ap-is-inj : {x y : A} (p : –> e x == –> e y) → x == y
    ap-is-inj p = equiv-inj e p

    abstract
      left-inverse : {x y : A} (p : x == y) → ap-is-inj (ap (–> e) p) == p
      left-inverse idp =
        ! (<–-inv-l e _) ∙ <–-inv-l e _ ∙ idp
                  =⟨ ∙-unit-r (<–-inv-l e _) |in-ctx (λ u → ! (<–-inv-l e _) ∙ u)  ⟩
        ! (<–-inv-l e _) ∙ <–-inv-l e _ =⟨ !-inv-l (<–-inv-l e _) ⟩
        idp ∎

      postulate
       right-inverse : {x y : A} (p : –> e x == –> e y)
        → ap (–> e) (ap-is-inj p) == p
--      right-inverse p = {!!}
        -- ap-∙ (–> e) (! (inverse-left-inverse e x)) _
        -- ∙ (ap (λ u → u ∙ ap (–> e) (ap (inverse e) p
        --           ∙ inverse-left-inverse e y))
        --        (ap-opposite (–> e) (inverse-left-inverse e x))
        --   ∙ move!-right-on-left (ap (–> e) (inverse-left-inverse e x)) _ p
        --     (ap-concat (–> e) (ap (inverse e) p) (inverse-left-inverse e y)
        --     ∙ (ap (λ u → u ∙ ap (–> e) (inverse-left-inverse e y))
        --            (compose-ap (–> e) (inverse e) p)
        --     ∙ (whisker-left (ap (–> e ◯ inverse e) p)
        --                     (! (inverse-triangle e y))
        --     ∙ (homotopy-naturality-toid (–> e ◯ inverse e)
        --                                 (inverse-right-inverse e)
        --                                 p
        --     ∙ whisker-right p (inverse-triangle e x))))))

  equiv-ap : (x y : A) → (x == y) ≃ (–> e x == –> e y)
  equiv-ap x y = equiv (ap (–> e)) ap-is-inj right-inverse left-inverse

-- Equivalent types have the same truncation level
equiv-preserves-level : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ₋₂} (f : A ≃ B)
  → (has-level n A → has-level n B)
equiv-preserves-level {n = ⟨-2⟩} (f , e) (x , p) =
  (f x , (λ y → ap f (p _) ∙ <–-inv-r (f , e) y))
equiv-preserves-level {n = S n} f c = λ x y →
   equiv-preserves-level (equiv-ap (f ⁻¹) x y ⁻¹) (c (<– f x) (<– f y))
