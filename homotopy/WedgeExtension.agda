{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalences2
open import lib.NConnected
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Suspension
open import lib.types.Truncation

module homotopy.WedgeExtension where

module WedgeExt {i j} {A : Type i} {a₀ : A} {B : Type j} {b₀ : B} where

  -- easier to keep track of than a long list of arguments
  record args : Type (lmax (lsucc i) (lsucc j)) where
    field
      n m : ℕ₋₂
      cA : is-connected (S (S n)) A
      cB : is-connected (S (S m)) B
      P : A → B → (S (n +2+ (S m))) -Type (lmax i j)
      f : (a : A) → fst (P a b₀)
      g : (b : B) → fst (P a₀ b)
      p : f a₀ == g b₀

  private
    module _ (r : args) where
      open args r
    
      Q : A → (S n) -Type (lmax i j)
      Q a = ((Σ (∀ b → fst (P a b)) (λ k → (k ∘ cst b₀) == cst (f a)) ,
                conn-elim-general (pointed-conn-out B b₀ cB) 
                                  (P a) (cst (f a))))
  
      l : Π A (fst ∘ Q)
      l = conn-elim (pointed-conn-out A a₀ cA) 
                    Q (λ (_ : Unit) → (g , ap cst (! p)))


  module _ (r : args) where
    open args r

    ext : ∀ a → ∀ b → fst (P a b)
    ext a = fst (l r a)

  module _ {r : args} where
    open args r

    abstract
      β-l : ∀ a → ext r a b₀ == f a
      β-l a = ap (λ t → t unit) (snd (l r a))

    abstract
      β-r-aux : fst (l r a₀) == g
      β-r-aux = fst= (conn-elim-β (pointed-conn-out A a₀ cA)
                                  (Q r) (λ (_ : Unit) → (g , ap cst (! p))) unit)

    abstract
      β-r : ∀ b → ext r a₀ b == g b
      β-r = app= β-r-aux

    abstract
      coh : ! (β-l a₀) ∙ β-r b₀ == p
      coh = 
        ! (β-l a₀) ∙ β-r b₀
          =⟨ ! lemma₂ |in-ctx (λ w → ! w ∙ β-r b₀) ⟩
        ! (β-r b₀ ∙ ! p) ∙ β-r b₀
          =⟨ !-∙ (β-r b₀) (! p) |in-ctx (λ w → w ∙ β-r b₀) ⟩
        (! (! p) ∙ ! (β-r b₀)) ∙ β-r b₀            
          =⟨ !-! p |in-ctx (λ w → (w ∙ ! (β-r b₀)) ∙ β-r b₀)  ⟩
        (p ∙ ! (β-r b₀)) ∙ β-r b₀            
          =⟨ ∙-assoc p (! (β-r b₀)) (β-r b₀) ⟩
        p ∙ ! (β-r b₀) ∙ β-r b₀            
          =⟨ ap (λ w → p ∙ w) (!-inv-l (β-r b₀)) ∙ ∙-unit-r p ⟩
        p ∎
        where
        -- could probably be better organized
        lemma₁ : β-l a₀ == ap (λ s → s unit) (ap cst (! p)) 
                 [ (λ k → k b₀ == f a₀) ↓ β-r-aux ]
        lemma₁ = ap↓ (ap (λ s → s unit)) $
                      snd= (conn-elim-β (pointed-conn-out A a₀ cA)
                           (Q r) (λ (_ : Unit) → (g , ap cst (! p))) unit)

        lemma₂ : β-r b₀ ∙ ! p == β-l a₀
        lemma₂ = ap (λ w → β-r b₀ ∙ w) (! (ap-idf _) ∙ ap-∘ _ _ _) 
                 ∙ (–> (↓-pathto-eqv β-r-aux) lemma₁)
