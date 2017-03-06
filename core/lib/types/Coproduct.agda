{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Empty
open import lib.types.Lift
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Coproduct where

module _ {i j} {A : Type i} {B : Type j} where

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

  ⊔-level : ∀ {n} → has-level (S (S n)) A → has-level (S (S n)) B
            → has-level (S (S n)) (Coprod A B)
  ⊔-level pA _ (inl a₁) (inl a₂) =
    equiv-preserves-level (inl=inl-equiv a₁ a₂ ⁻¹) (pA a₁ a₂)
  ⊔-level _ _ (inl a₁) (inr b₂) = λ p → Empty-rec (inl≠inr a₁ b₂ p)
  ⊔-level _ _ (inr b₁) (inl a₂) = λ p → Empty-rec (inr≠inl b₁ a₂ p)
  ⊔-level _ pB (inr b₁) (inr b₂) =
    equiv-preserves-level ((inr=inr-equiv b₁ b₂)⁻¹) (pB b₁ b₂)

  Coprod-level = ⊔-level

infix 80 _⊙⊔_
_⊙⊔_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙⊔ Y = ⊙[ Coprod (fst X) (fst Y) , inl (snd X) ]

_⊔⊙_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊔⊙ Y = ⊙[ Coprod (fst X) (fst Y) , inr (snd Y) ]

codiag : ∀ {i} {A : Type i} → A ⊔ A → A
codiag (inl a) = a
codiag (inr a) = a

⊙codiag : ∀ {i} {X : Ptd i} → X ⊙⊔ X ⊙→ X
⊙codiag = (codiag , idp)

-- A binary sigma is a coproduct
ΣBool-equiv-⊔ : ∀ {i} (Pick : Bool → Type i)
  → Σ _ Pick ≃ (Pick true ⊔ Pick false)
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
