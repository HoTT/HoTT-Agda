{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import Orthogonality
open import Modalities

module NullifyFamily where

  module _ {ℓ} {I : Type ℓ} (X : I → Type ℓ) (A : Type ℓ) where

    private

      data #NullifyAll : Type ℓ where
        #inj : A → #NullifyAll
        #apex : (i : I) → (X i → #NullifyAll) → #NullifyAll
        
    NullifyAll : Type ℓ 
    NullifyAll = #NullifyAll
      
    inj : A → NullifyAll
    inj = #inj

    apex : (i : I) → (X i → #NullifyAll) → #NullifyAll
    apex = #apex

    postulate
      apex-path : (i : I) (α : X i → NullifyAll) (x : X i) → apex i α == α x
      apex-cst : (i : I) (n : NullifyAll) → apex i (λ _ → n) == n
      apex-adj : (i : I) (n : NullifyAll) → ap (Δ NullifyAll (X i)) (apex-cst i n) == λ= (apex-path i (Δ NullifyAll (X i) n))

    module NullifyAllElim (Q : NullifyAll → Type ℓ) (is-null : ⟦ X ⊥ Q ⟧) (φ : Π A (Q ∘ inj)) where

      f : Π NullifyAll Q
      f (#inj a) = φ a 
      f (#apex i α) = is-equiv.g (is-null i (#apex i α)) α' 

         where α' : X i → Q (#apex i α)
               α' x = transport! Q (apex-path i α x) (f (α x))
  
  module _ {ℓ} {I : Type ℓ} (X : I → Type ℓ) where

    nullify-is-null : (A : Type ℓ) → ⟦ X ⊥ NullifyAll X A ⟧ₗ
    is-equiv.g (nullify-is-null A i) = apex X A i
    is-equiv.f-g (nullify-is-null A i) α = λ= (λ x → apex-path X A i α x)
    is-equiv.g-f (nullify-is-null A i) = apex-cst X A i
    is-equiv.adj (nullify-is-null A i) = apex-adj X A i

    open Modality

    NullifyAllModality : Modality {ℓ}
    P NullifyAllModality A = ⟦ X ⊥ A ⟧ₗ
    P-is-prop NullifyAllModality {A} = Π-level (λ i → is-equiv-is-prop (Δ A (X i)))
    ◯ NullifyAllModality A = NullifyAll X A
    in-◯ NullifyAllModality {A} = nullify-is-null A  
    η NullifyAllModality {A} = inj X A
    ◯-elim NullifyAllModality Q Q-is-null φ = NullifyAllElim.f X _ Q (λ i n → Q-is-null n i) φ
    ◯-elim-β NullifyAllModality Q Q-is-null φ a = idp
    ◯-== NullifyAllModality {A} a₀ a₁ i = is-eq _ squash inv-l inv-r

      where a₀' : NullifyAll X A
            a₀' = apex X A i (λ _ → a₀)
            
            a₁' : NullifyAll X A
            a₁' = apex X A i (λ _ → a₁)

            squash : (X i → a₀ == a₁) → a₀ == a₁
            squash φ = ! (apex-cst X A i a₀) ∙ cyl ∙ apex-cst X A i a₁

              where cyl : a₀' == a₁'
                    cyl = ap (apex X A i) (λ= φ)

            inv-l : (φ : X i → a₀ == a₁) → (λ _ → squash φ) == φ
            inv-l φ = {!!}

            inv-r : (p : a₀ == a₁) → squash (λ _ → p) == p
            inv-r p = {!!}

            -- Main idea is to use this coherence ... (and possibly the other adjoint as well)
            -- apex-adj : (i : I) (n : NullifyAll) → ap (Δ NullifyAll (X i)) (apex-cst i n) == λ= (apex-path i (Δ NullifyAll (X i) n))
