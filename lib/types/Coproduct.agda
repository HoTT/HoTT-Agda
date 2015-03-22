{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Empty
open import lib.types.Lift
open import lib.types.Pointed

module lib.types.Coproduct where

module _ {i j} {A : Type i} {B : Type j} where

  ⊔-code : Coprod A B → Coprod A B → Type (lmax i j)
  ⊔-code (inl a₁) (inl a₂) = Lift {j = (lmax i j)} $ a₁ == a₂
  ⊔-code (inl a₁) (inr b₂) = Lift Empty
  ⊔-code (inr b₁) (inl a₂) = Lift Empty
  ⊔-code (inr b₁) (inr b₂) = Lift {j = (lmax i j)} $ b₁ == b₂

  ⊔-encode : {x y : Coprod A B} → (x == y) → ⊔-code x y
  ⊔-encode {inl a₁} {y} p = transport (⊔-code $ inl a₁) p (lift $ idp {a = a₁})
  ⊔-encode {inr b₁} {y} p = transport (⊔-code $ inr b₁) p (lift $ idp {a = b₁})

  ⊔-decode : {x y : Coprod A B} → ⊔-code x y → (x == y)
  ⊔-decode {inl _} {inl _} c = ap inl $ lower c
  ⊔-decode {inl _} {inr _} c = Empty-rec $ lower c
  ⊔-decode {inr _} {inl _} c = Empty-rec $ lower c
  ⊔-decode {inr _} {inr _} c = ap inr (lower c)

  ⊔-code-equiv : (x y : Coprod A B) → (x == y) ≃ ⊔-code x y
  ⊔-code-equiv x y = equiv ⊔-encode ⊔-decode (f-g x y) (g-f x y)
    where f-g : ∀ x' y' → ∀ c → ⊔-encode (⊔-decode {x'} {y'} c) == c
          f-g (inl a₁) (inl .a₁) (lift idp) = idp
          f-g (inl a₁) (inr b₂) b = Empty-rec $ lower b
          f-g (inr b₁) (inl a₂) b = Empty-rec $ lower b
          f-g (inr b₁) (inr .b₁) (lift idp) = idp

          g-f : ∀ x' y' → ∀ p → ⊔-decode (⊔-encode {x'} {y'} p) == p
          g-f (inl _) .(inl _) idp = idp
          g-f (inr _) .(inr _) idp = idp

  inl=inl-equiv : (a₁ a₂ : A) → (inl a₁ == inl a₂) ≃ (a₁ == a₂)
  inl=inl-equiv a₁ a₂ = lift-equiv ∘e ⊔-code-equiv (inl a₁) (inl a₂)

  inr=inr-equiv : (b₁ b₂ : B) → (inr b₁ == inr b₂) ≃ (b₁ == b₂)
  inr=inr-equiv b₁ b₂ = lift-equiv ∘e ⊔-code-equiv (inr b₁) (inr b₂)

  inl≠inr : (a₁ : A) (b₂ : B) → (inl a₁ ≠ inr b₂)
  inl≠inr a₁ b₂ p = lower $ ⊔-encode p

  inr≠inl : (b₁ : B) (a₂ : A) → (inr b₁ ≠ inl a₂)
  inr≠inl a₁ b₂ p = lower $ ⊔-encode p

  ⊔-level : ∀ {n} → has-level (S (S n)) A → has-level (S (S n)) B
            → has-level (S (S n)) (Coprod A B)
  ⊔-level pA _ (inl a₁) (inl a₂) =
    equiv-preserves-level ((inl=inl-equiv a₁ a₂)⁻¹) (pA a₁ a₂)
  ⊔-level _ _ (inl a₁) (inr b₂) = λ p → Empty-rec (inl≠inr a₁ b₂ p)
  ⊔-level _ _ (inr b₁) (inl a₂) = λ p → Empty-rec (inr≠inl b₁ a₂ p)
  ⊔-level _ pB (inr b₁) (inr b₂) =
    equiv-preserves-level ((inr=inr-equiv b₁ b₂)⁻¹) (pB b₁ b₂)

_⊙⊔_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙⊔ Y = ⊙[ Coprod (fst X) (fst Y) , inl (snd X) ]

_⊔⊙_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊔⊙ Y = ⊙[ Coprod (fst X) (fst Y) , inr (snd Y) ]

codiag : ∀ {i} {A : Type i} → A ⊔ A → A
codiag (inl a) = a
codiag (inr a) = a

⊙codiag : ∀ {i} {X : Ptd i} → fst (X ⊙⊔ X ⊙→ X)
⊙codiag = (codiag , idp)

-- A binary sigma is a coproduct
ΣBool-equiv-⊔ : ∀ {i} (Pick : Lift {j = i} Bool → Type i)
  → Σ _ Pick ≃ (Pick (lift true) ⊔ Pick (lift false))
ΣBool-equiv-⊔ Pick = equiv into out into-out out-into
  where
  into : Σ _ Pick → (Pick (lift true) ⊔ Pick (lift false))
  into (lift true , a) = inl a
  into (lift false , b) = inr b

  out : (Pick (lift true) ⊔ Pick (lift false)) → Σ _ Pick
  out (inl a) = (lift true , a)
  out (inr b) = (lift false , b)

  into-out : ∀ c → into (out c) == c
  into-out (inl a) = idp
  into-out (inr b) = idp

  out-into : ∀ s → out (into s) == s
  out-into (lift true , a) = idp
  out-into (lift false , b) = idp
