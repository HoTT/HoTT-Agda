{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Empty
open import lib.types.Lift
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Coproduct where

module _ {i j} {A : Type i} {B : Type j} where

  Coprod-elim : ∀ {k} {C : A ⊔ B → Type k}
    → ((a : A) → C (inl a)) → ((b : B) → C (inr b))
    → Π (A ⊔ B) C
  Coprod-elim f g (inl a) = f a
  Coprod-elim f g (inr b) = g b

  ⊔-elim = Coprod-elim

  Coprod-rec : ∀ {k} {C : Type k}
    → (A → C) → (B → C) → (A ⊔ B → C)
  Coprod-rec {C = C} = Coprod-elim {C = λ _ → C}

  ⊔-rec = Coprod-rec

  Coprod= : Coprod A B → Coprod A B → Type (lmax i j)
  Coprod= (inl a₁) (inl a₂) = Lift {j = (lmax i j)} $ a₁ == a₂
  Coprod= (inl a₁) (inr b₂) = Lift Empty
  Coprod= (inr b₁) (inl a₂) = Lift Empty
  Coprod= (inr b₁) (inr b₂) = Lift {j = (lmax i j)} $ b₁ == b₂

  Coprod=-in : {x y : Coprod A B} → (x == y) → Coprod= x y
  Coprod=-in {inl _} idp = lift idp
  Coprod=-in {inr _} idp = lift idp

  Coprod=-out : {x y : Coprod A B} → Coprod= x y → (x == y)
  Coprod=-out {inl _} {inl _} c = ap inl $ lower c
  Coprod=-out {inl _} {inr _} c = Empty-rec $ lower c
  Coprod=-out {inr _} {inl _} c = Empty-rec $ lower c
  Coprod=-out {inr _} {inr _} c = ap inr (lower c)

  Coprod=-in-equiv : (x y : Coprod A B) → (x == y) ≃ Coprod= x y
  Coprod=-in-equiv x y = equiv Coprod=-in Coprod=-out (f-g x y) (g-f x y)
    where f-g : ∀ x' y' → ∀ c → Coprod=-in (Coprod=-out {x'} {y'} c) == c
          f-g (inl a₁) (inl .a₁) (lift idp) = idp
          f-g (inl a₁) (inr b₂) b = Empty-rec $ lower b
          f-g (inr b₁) (inl a₂) b = Empty-rec $ lower b
          f-g (inr b₁) (inr .b₁) (lift idp) = idp

          g-f : ∀ x' y' → ∀ p → Coprod=-out (Coprod=-in {x'} {y'} p) == p
          g-f (inl _) .(inl _) idp = idp
          g-f (inr _) .(inr _) idp = idp

  inl=inl-equiv : (a₁ a₂ : A) → (inl a₁ == inl a₂) ≃ (a₁ == a₂)
  inl=inl-equiv a₁ a₂ = lower-equiv ∘e Coprod=-in-equiv (inl a₁) (inl a₂)

  inr=inr-equiv : (b₁ b₂ : B) → (inr b₁ == inr b₂) ≃ (b₁ == b₂)
  inr=inr-equiv b₁ b₂ = lower-equiv ∘e Coprod=-in-equiv (inr b₁) (inr b₂)

  inl≠inr : (a₁ : A) (b₂ : B) → (inl a₁ ≠ inr b₂)
  inl≠inr a₁ b₂ p = lower $ Coprod=-in p

  inr≠inl : (b₁ : B) (a₂ : A) → (inr b₁ ≠ inl a₂)
  inr≠inl a₁ b₂ p = lower $ Coprod=-in p

  instance
    ⊔-level : ∀ {n} → has-level (S (S n)) A → has-level (S (S n)) B
              → has-level (S (S n)) (Coprod A B)
    ⊔-level {n} pA pB = has-level-make (⊔-level-aux pA pB) where
      
      instance _ = pA; _ = pB

      ⊔-level-aux : has-level (S (S n)) A → has-level (S (S n)) B
              → has-level-aux (S (S n)) (Coprod A B)
      ⊔-level-aux _ _ (inl a₁) (inl a₂) = equiv-preserves-level (inl=inl-equiv a₁ a₂ ⁻¹)
      ⊔-level-aux _ _ (inl a₁) (inr b₂) = has-level-make (λ p → Empty-rec (inl≠inr a₁ b₂ p))
      ⊔-level-aux _ _ (inr b₁) (inl a₂) = has-level-make (λ p → Empty-rec (inr≠inl b₁ a₂ p))
      ⊔-level-aux _ _ (inr b₁) (inr b₂) = equiv-preserves-level ((inr=inr-equiv b₁ b₂)⁻¹)

  Coprod-level = ⊔-level

module _ {i i' j j'} {A : Type i} {A' : Type i'} {B : Type j} {B' : Type j'}
  (f : A → A') (g : B → B') where

  ⊔-fmap : A ⊔ B → A' ⊔ B'
  ⊔-fmap (inl a) = inl (f a)
  ⊔-fmap (inr b) = inr (g b)

infix 80 _⊙⊔_
_⊙⊔_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙⊔ Y = ⊙[ Coprod (de⊙ X) (de⊙ Y) , inl (pt X) ]

_⊔⊙_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊔⊙ Y = ⊙[ Coprod (de⊙ X) (de⊙ Y) , inr (pt Y) ]

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Z) (g : Y ⊙→ Z) where

  ⊙⊔-rec : X ⊙⊔ Y ⊙→ Z
  ⊙⊔-rec = Coprod-rec (fst f) (fst g) , snd f

  ⊔⊙-rec : X ⊔⊙ Y ⊙→ Z
  ⊔⊙-rec = Coprod-rec (fst f) (fst g) , snd g

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  (f : X ⊙→ X') (g : Y ⊙→ Y') where

  ⊙⊔-fmap : X ⊙⊔ Y ⊙→ X' ⊙⊔ Y'
  ⊙⊔-fmap = ⊔-fmap (fst f) (fst g) , ap inl (snd f)

  ⊔⊙-fmap : X ⊔⊙ Y ⊙→ X' ⊔⊙ Y'
  ⊔⊙-fmap = ⊔-fmap (fst f) (fst g) , ap inr (snd g)

codiag : ∀ {i} {A : Type i} → A ⊔ A → A
codiag = Coprod-rec (idf _) (idf _)

⊙codiag : ∀ {i} {X : Ptd i} → X ⊙⊔ X ⊙→ X
⊙codiag = (codiag , idp)

-- A binary sigma is a coproduct
ΣBool-equiv-⊔ : ∀ {i} (Pick : Bool → Type i)
  → Σ Bool Pick ≃ Pick true ⊔ Pick false
ΣBool-equiv-⊔ Pick = equiv into out into-out out-into
  where
  into : Σ _ Pick → Pick true ⊔ Pick false
  into (true , a) = inl a
  into (false , b) = inr b

  out : (Pick true ⊔ Pick false) → Σ _ Pick
  out (inl a) = (true , a)
  out (inr b) = (false , b)

  abstract
    into-out : ∀ c → into (out c) == c
    into-out (inl a) = idp
    into-out (inr b) = idp

    out-into : ∀ s → out (into s) == s
    out-into (true , a) = idp
    out-into (false , b) = idp

module _ {i j k} {A : Type i} {B : Type j} (P : A ⊔ B → Type k) where
  Π₁-⊔-equiv-× : Π (A ⊔ B) P ≃ Π A (P ∘ inl) × Π B (P ∘ inr)
  Π₁-⊔-equiv-× = equiv to from to-from from-to
    where
    to : Π (A ⊔ B) P → Π A (P ∘ inl) × Π B (P ∘ inr)
    to f = (λ a → f (inl a)) , (λ b → f (inr b))

    from : Π A (P ∘ inl) × Π B (P ∘ inr) → Π (A ⊔ B) P
    from (f , g) (inl a) = f a
    from (f , g) (inr b) = g b

    abstract
      to-from : ∀ fg → to (from fg) == fg
      to-from _ = idp

      from-to : ∀ fg → from (to fg) == fg
      from-to fg = λ= λ where (inl _) → idp
                              (inr _) → idp
