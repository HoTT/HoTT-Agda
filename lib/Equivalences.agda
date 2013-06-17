{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
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

    adj : (a : A) → ap f (g-f a) == f-g' (f a)
    adj a = 
      ap f (g-f a)
        =⟨ ! (!-inv-l (ap (f ∘ g) (f-g (f a)))) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
      (! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f a)
        =⟨ ∙-assoc (! (ap (f ∘ g) (f-g (f a)))) (ap (f ∘ g) (f-g (f a))) _ ⟩
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
        =⟨ lemma |in-ctx (λ q → ! (ap (f ∘ g) (f-g (f a))) ∙ q) ⟩
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f (g (f a))) ∙ f-g (f a) ∎ 
      where 
      lemma : ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a) 
           == ap f (g-f (g (f a))) ∙ f-g (f a)
      lemma = 
        ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
          =⟨ htpy-natural-toid f-g (f a) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
        f-g (f (g (f a))) ∙ ap f (g-f a)
          =⟨ ! (ap-idf (ap f (g-f a))) |in-ctx (λ q → f-g (f (g (f a))) ∙ q) ⟩
        f-g (f (g (f a))) ∙ ap (idf B) (ap f (g-f a))
          =⟨ ! (htpy-natural f-g (ap f (g-f a))) ⟩
        ap (f ∘ g) (ap f (g-f a)) ∙ f-g (f a)
          =⟨ ap-∘ f g (ap f (g-f a)) |in-ctx (λ q → q ∙ f-g (f a)) ⟩
        ap f (ap g (ap f (g-f a))) ∙ f-g (f a)
          =⟨ ∘-ap g f (g-f a) ∙ htpy-natural-toid g-f a 
             |in-ctx (λ q → ap f q ∙ f-g (f a)) ⟩
        ap f (g-f (g (f a))) ∙ f-g (f a) ∎

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

      right-inverse : {x y : A} (p : –> e x == –> e y) 
        → ap (–> e) (ap-is-inj p) == p
      right-inverse {x} {y} p = 
        ap f (! (g-f x) ∙ ap g p ∙ (g-f y) ∙ idp)
          =⟨ ∙-unit-r _ |in-ctx (λ q →  ap f (! (g-f x) ∙ ap g p ∙ q)) ⟩
        ap f (! (g-f x) ∙ ap g p ∙ (g-f y))
          =⟨ ap-∙ f (! (g-f x)) (ap g p ∙ (g-f y)) ⟩
        ap f (! (g-f x)) ∙ ap f (ap g p ∙ (g-f y))
          =⟨ ap-∙ f (ap g p) (g-f y) |in-ctx (λ q →  ap f (! (g-f x)) ∙ q) ⟩
        ap f (! (g-f x)) ∙ ap f (ap g p) ∙ ap f (g-f y)
          =⟨ ∘-ap f g p |in-ctx (λ q → ap f (! (g-f x)) ∙ q ∙ ap f (g-f y)) ⟩
        ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ ap f (g-f y)
          =⟨ adj y |in-ctx (λ q →  ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ q) ⟩
        ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
          =⟨ ap-! f (g-f x) |in-ctx (λ q → q ∙ ap (f ∘ g) p ∙ (f-g (f y))) ⟩
        ! (ap f (g-f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
          =⟨ adj x |in-ctx (λ q →  ! q ∙ ap (f ∘ g) p ∙ (f-g (f y))) ⟩
        ! (f-g (f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
          =⟨ htpy-natural f-g p |in-ctx (λ q →  ! (f-g (f x)) ∙ q) ⟩
        ! (f-g (f x)) ∙ (f-g (f x)) ∙ ap (idf B) p
          =⟨ ! (∙-assoc (! (f-g (f x))) (f-g (f x)) (ap (idf B) p))
             ∙ ap (λ q → q ∙ ap (idf B) p) (!-inv-l (f-g (f x))) ∙ ap-idf p ⟩
        p ∎
        where f : A → B; f = –> e; g : B → A; g = <– e
              g-f : ∀ x → (g (f x) == x); g-f = <–-inv-l e 
              f-g : ∀ y → (f (g y) == y); f-g = <–-inv-r e 
              adj : ∀ x → ap f (g-f x) == f-g (f x); adj = is-equiv.adj (snd e)

  equiv-ap : (x y : A) → (x == y) ≃ (–> e x == –> e y)
  equiv-ap x y = equiv (ap (–> e)) ap-is-inj right-inverse left-inverse

-- Equivalent types have the same truncation level
equiv-preserves-level : ∀ {i j} {A : Set i} {B : Set j} {n : ℕ₋₂} (e : A ≃ B)
  → (has-level n A → has-level n B)
equiv-preserves-level {n = ⟨-2⟩} e (x , p) =
  (–> e x , (λ y → ap (–> e) (p _) ∙ <–-inv-r e y))
equiv-preserves-level {n = S n} e c = λ x y →
   equiv-preserves-level (equiv-ap (e ⁻¹) x y ⁻¹) (c (<– e x) (<– e y))
