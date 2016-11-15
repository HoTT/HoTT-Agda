{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.Function

module lib.Equivalence where

{-
We use the half-adjoint definition of equivalences (but this fact should be
invisible to the user of the library). The constructor of the type of
equivalences is [equiv], it takes two maps and the two proofs that the composites
are equal: [equiv to from to-from from-to]

The type of equivalences between two types [A] and [B] can be written either
[A ≃ B] or [Equiv A B].

Given an equivalence [e] : [A ≃ B], you can extract the two maps as follows:
[–> e] : [A → B] and [<– e] : [B → A] (the dash is an en dash)
The proofs that the composites are the identities are [<–-inv-l] and [<–-inv-r].

The identity equivalence on [A] is [ide A], the composition of two equivalences
is [_∘e_] (function composition order) and the inverse of an equivalence is [_⁻¹]
-}

{- These lemmas are here because lib.Path is not available at this point.
   Otherwise they are just combinations of [↓-='-out] and [apd]. -}

private
  htpy-natural : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {f g : A → B}
    (p : ∀ x → (f x == g x)) (q : x == y) → ap f q ∙ p y == p x ∙ ap g q
  htpy-natural p idp = ! (∙-unit-r _)

  htpy-natural-app=idf : ∀ {i} {A : Type i} {f : A → A}
    (p : ∀ (x : A) → f x == x) → (∀ x → ap f (p x) == p (f x))
  htpy-natural-app=idf {f = f} p x = anti-whisker-right (p x) $
    htpy-natural p (p x) ∙ ap (p (f x) ∙_) (ap-idf (p x))


module _ {i} {j} {A : Type i} {B : Type j} where

  record is-equiv (f : A → B) : Type (lmax i j)
    where
    field
      g : B → A
      f-g : (b : B) → f (g b) == b
      g-f : (a : A) → g (f a) == a
      adj : (a : A) → ap f (g-f a) == f-g (f a)

    abstract
      adj' : (b : B) → ap g (f-g b) == g-f (g b)
      adj' b = anti-whisker-left (ap g (f-g (f (g b)))) $ ! $
        ap g (f-g (f (g b))) ∙ g-f (g b)
          =⟨ ! $ htpy-natural-app=idf f-g b |in-ctx (λ p → ap g p ∙ g-f (g b)) ⟩
        ap g (ap (f ∘ g) (f-g b)) ∙ g-f (g b)
          =⟨ ! $ ap-∘ g (f ∘ g) (f-g b) |in-ctx (λ p → p ∙ g-f (g b)) ⟩
        ap (g ∘ f ∘ g) (f-g b) ∙ g-f (g b)
          =⟨ htpy-natural (g-f ∘ g) (f-g b) ⟩
        g-f (g (f (g b))) ∙ ap g (f-g b)
          =⟨ ! $ htpy-natural-app=idf g-f (g b) |in-ctx (λ p → p ∙ ap g (f-g b)) ⟩
        ap (g ∘ f) (g-f (g b)) ∙ ap g (f-g b)
          =⟨ ap-∘ g f (g-f (g b)) |in-ctx (λ p → p ∙ ap g (f-g b)) ⟩
        ap g (ap f (g-f (g b))) ∙ ap g (f-g b)
          =⟨ adj (g b) |in-ctx (λ p → ap g p ∙ ap g (f-g b)) ⟩
        ap g (f-g (f (g b))) ∙ ap g (f-g b)
          =∎


  {-
  In order to prove that something is an equivalence, you have to give an inverse
  and a proof that it’s an inverse (you don’t need the adj part).
  [is-eq] is a very, very bad name.
  -}
  is-eq : (f : A → B)
    (g : B → A) (f-g : (b : B) → f (g b) == b)
    (g-f : (a : A) → g (f a) == a) → is-equiv f
  is-eq f g f-g g-f =
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
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f (g (f a))) ∙ f-g (f a) =∎
      where
      lemma : ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
           == ap f (g-f (g (f a))) ∙ f-g (f a)
      lemma =
        ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
          =⟨ htpy-natural-app=idf f-g (f a) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
        f-g (f (g (f a))) ∙ ap f (g-f a)
          =⟨ ! (ap-idf (ap f (g-f a))) |in-ctx (λ q → f-g (f (g (f a))) ∙ q) ⟩
        f-g (f (g (f a))) ∙ ap (idf B) (ap f (g-f a))
          =⟨ ! (htpy-natural f-g (ap f (g-f a))) ⟩
        ap (f ∘ g) (ap f (g-f a)) ∙ f-g (f a)
          =⟨ ap-∘ f g (ap f (g-f a)) |in-ctx (λ q → q ∙ f-g (f a)) ⟩
        ap f (ap g (ap f (g-f a))) ∙ f-g (f a)
          =⟨ ∘-ap g f (g-f a) ∙ htpy-natural-app=idf g-f a
             |in-ctx (λ q → ap f q ∙ f-g (f a)) ⟩
        ap f (g-f (g (f a))) ∙ f-g (f a) =∎

infix 30 _≃_

_≃_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A ≃ B = Σ (A → B) is-equiv

Equiv = _≃_

module _ {i} {j} {A : Type i} {B : Type j} where

  equiv : (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
          (g-f : (a : A) → g (f a) == a) → A ≃ B
  equiv f g f-g g-f = (f , is-eq f g f-g g-f)

  –> : (e : A ≃ B) → (A → B)
  –> e = fst e

  <– : (e : A ≃ B) → (B → A)
  <– e = is-equiv.g (snd e)

  <–-inv-l : (e : A ≃ B) (a : A)
    → (<– e (–> e a) == a)
  <–-inv-l e a = is-equiv.g-f (snd e) a

  <–-inv-r : (e : A ≃ B) (b : B)
    → (–> e (<– e b) == b)
  <–-inv-r e b = is-equiv.f-g (snd e) b

  <–-inv-adj : (e : A ≃ B) (a : A)
    → ap (–> e) (<–-inv-l e a) == <–-inv-r e (–> e a)
  <–-inv-adj e a = is-equiv.adj (snd e) a

  <–-inv-adj' : (e : A ≃ B) (b : B)
    → ap (<– e) (<–-inv-r e b) == <–-inv-l e (<– e b)
  <–-inv-adj' e b = is-equiv.adj' (snd e) b

  -- Equivalences are "injective"
  –>-is-inj : (e : A ≃ B) → is-inj (–> e)
  –>-is-inj e x y p = ! (<–-inv-l e x) ∙ ap (<– e) p ∙ <–-inv-l e y

  equiv-is-inj : {f : A → B} → is-equiv f → is-inj f
  equiv-is-inj ise = –>-is-inj (_ , ise)

idf-is-equiv : ∀ {i} (A : Type i) → is-equiv (idf A)
idf-is-equiv A = is-eq _ (idf A) (λ _ → idp) (λ _ → idp)

ide : ∀ {i} (A : Type i) → A ≃ A
ide A = equiv (idf A) (idf A) (λ _ → idp) (λ _ → idp)

transport-equiv : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x ≃ B y)
transport-equiv B idp = ide _

infixr 80 _∘e_
infixr 80 _∘ise_

_∘e_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → B ≃ C → A ≃ B → A ≃ C
e1 ∘e e2 = ((–> e1 ∘ –> e2) , record {g = (<– e2 ∘ <– e1);
  f-g = (λ c → ap (–> e1) (<–-inv-r e2 (<– e1 c)) ∙ <–-inv-r e1 c);
  g-f = (λ a → ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a);
  adj = λ a →
      ap (–> e1 ∘ –> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a)
          =⟨ ap-∘ (–> e1) (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a) ⟩
      ap (–> e1) (ap (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a))
          =⟨ ap-∙ (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a))) (<–-inv-l e2 a)  |in-ctx ap (–> e1) ⟩
      ap (–> e1) (ap (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a))) ∙ ap (–> e2) (<–-inv-l e2 a))
          =⟨ ! (ap-∘ (–> e2) (<– e2) (<–-inv-l e1 (–> e2 a))) ∙2 <–-inv-adj e2 a |in-ctx ap (–> e1) ⟩
      ap (–> e1) (ap (–> e2 ∘ <– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-r e2 (–> e2 a))
          =⟨ htpy-natural (<–-inv-r e2) (<–-inv-l e1 (–> e2 a))    |in-ctx ap (–> e1) ⟩
      ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a)) ∙ ap (λ z → z) (<–-inv-l e1 (–> e2 a)))
          =⟨ <–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a)) ∙ₗ ap-idf (<–-inv-l e1 (–> e2 a)) |in-ctx ap (–> e1) ⟩
      ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a)) ∙ <–-inv-l e1 (–> e2 a))
          =⟨ ap-∙ (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) (<–-inv-l e1 (–> e2 a)) ⟩
      ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) ∙ ap (–> e1) (<–-inv-l e1 (–> e2 a))
          =⟨  ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) ∙ₗ (<–-inv-adj e1 (–> e2 a)) ⟩
      ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) ∙ <–-inv-r e1 ((–> e1 ∘ –> e2) a)
          =∎})

_∘ise_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {f : A → B} {g : B → C}
  → is-equiv g → is-equiv f → is-equiv (g ∘ f)
i1 ∘ise i2 = snd ((_ , i1) ∘e (_ , i2))

is-equiv-inverse : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (f-is-equiv : is-equiv f) → is-equiv (is-equiv.g f-is-equiv)
is-equiv-inverse ise = record { g = _ ; f-g = is-equiv.g-f ise ; g-f = is-equiv.f-g ise ; adj = is-equiv.adj' ise }

infix 120 _⁻¹
_⁻¹ : ∀ {i j} {A : Type i} {B : Type j} → (A ≃ B) → (B ≃ A)
(_ , ise) ⁻¹ = (is-equiv.g ise , is-equiv-inverse ise)

{- Equational reasoning for equivalences -}
infix 15 _≃∎
infixr 10 _≃⟨_⟩_

_≃⟨_⟩_ : ∀ {i j k} (A : Type i) {B : Type j} {C : Type k} → A ≃ B → B ≃ C → A ≃ C
A ≃⟨ u ⟩ v = v ∘e u

_≃∎ : ∀ {i} (A : Type i) → A ≃ A
_≃∎ = ide


{- lifting is an equivalence -}
lower-equiv : ∀ {i j} {A : Type i} → Lift {j = j} A ≃ A
lower-equiv = equiv lower lift (λ _ → idp) (λ _ → idp)

{- Any contractible type is equivalent to (all liftings of) the unit type -}
module _ {i} {A : Type i} (h : is-contr A) where
  contr-equiv-Unit : A ≃ Unit
  contr-equiv-Unit = equiv (λ _ → unit) (λ _ → fst h) (λ _ → idp) (snd h)

  contr-equiv-LiftUnit : ∀ {j} → A ≃ Lift {j = j} Unit
  contr-equiv-LiftUnit = lower-equiv ⁻¹ ∘e contr-equiv-Unit


{- An equivalence induces an equivalence on the path spaces -}
module _ {i j} {A : Type i} {B : Type j} where

  private
    abstract
      left-inverse : (e : A ≃ B) {x y : A} (p : x == y)
        → –>-is-inj e _ _ (ap (–> e) p) == p
      left-inverse e idp = !-inv-l (<–-inv-l e _)

      right-inverse : (e : A ≃ B) {x y : A} (p : –> e x == –> e y)
        → ap (–> e) (–>-is-inj e _ _ p) == p
      right-inverse e {x} {y} p =
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
        p =∎
        where f : A → B
              f = fst e

              open is-equiv (snd e)

  ap-is-equiv : {f : A → B} → is-equiv f
    → (x y : A) → is-equiv (ap f :> (x == y → f x == f y))
  ap-is-equiv {f} e x y =
    is-eq (ap f) (equiv-is-inj e _ _) (right-inverse (_ , e)) (left-inverse (_ , e))

  ap-equiv : (e : A ≃ B) (x y : A) → (x == y) ≃ (–> e x == –> e y)
  ap-equiv e x y = _ , ap-is-equiv (snd e) x y


{- Equivalent types have the same truncation level -}
equiv-preserves-level : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} (e : A ≃ B)
  → (has-level n A → has-level n B)
equiv-preserves-level {n = ⟨-2⟩} e (x , p) =
  (–> e x , (λ y → ap (–> e) (p _) ∙ <–-inv-r e y))
equiv-preserves-level {n = S n} e c = λ x y →
   equiv-preserves-level (ap-equiv (e ⁻¹) x y ⁻¹) (c (<– e x) (<– e y))

{- This is a collection of type equivalences involving basic type formers.
   We exclude Empty since Π₁-Empty requires λ=.
-}
module _ {j} {B : Unit → Type j} where
  Σ₁-Unit : Σ Unit B ≃ B unit
  Σ₁-Unit = equiv (λ {(unit , b) → b}) (λ b → (unit , b)) (λ _ → idp) (λ _ → idp)

  Π₁-Unit : Π Unit B ≃ B unit
  Π₁-Unit = equiv (λ f → f unit) (λ b _ → b) (λ _ → idp) (λ _ → idp)

module _ {i} {A : Type i} where
  Σ₂-Unit : Σ A (λ _ → Unit) ≃ A
  Σ₂-Unit = equiv fst (λ a → (a , unit)) (λ _ → idp) (λ _ → idp)

  Π₂-Unit : Π A (λ _ → Unit) ≃ Unit
  Π₂-Unit = equiv (λ _ → unit) (λ _ _ → unit) (λ _ → idp) (λ _ → idp)

module _ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} where
  Σ-assoc : Σ (Σ A B) (uncurry C) ≃ Σ A (λ a → Σ (B a) (C a))
  Σ-assoc = equiv (λ {((a , b) , c) → (a , (b , c))})
                  (λ {(a , (b , c)) → ((a , b) , c)}) (λ _ → idp) (λ _ → idp)

  curry-equiv : Π (Σ A B) (uncurry C) ≃ Π A (λ a → Π (B a) (C a))
  curry-equiv = equiv curry uncurry (λ _ → idp) (λ _ → idp)

  {- The type-theoretic axiom of choice -}
  choice : Π A (λ a → Σ (B a) (λ b → C a b)) ≃ Σ (Π A B) (λ g → Π A (λ a → C a (g a)))
  choice = equiv f g (λ _ → idp) (λ _ → idp)
    where f = λ c → ((λ a → fst (c a)) , (λ a → snd (c a)))
          g = λ d → (λ a → (fst d a , snd d a))

{-
Pointed equivalences
-}

infix 30 _⊙≃_
_⊙≃_ : ∀ {i j} → Ptd i → Ptd j → Type (lmax i j)
X ⊙≃ Y = Σ (X ⊙→ Y) (λ {(f , _) → is-equiv f})

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
