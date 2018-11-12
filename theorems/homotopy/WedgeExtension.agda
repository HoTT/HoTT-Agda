{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.WedgeExtension
  {i j} {A : Type i} {a₀ : A} {B : Type j} {b₀ : B} where

  -- easier to keep track of than a long list of arguments
  record args : Type (lmax (lsucc i) (lsucc j)) where
    field
      n m : ℕ₋₂
      {{cA}} : is-connected (S n) A
      {{cB}} : is-connected (S m) B
      P : A → B → (n +2+ m) -Type (lmax i j)
      f : (a : A) → fst (P a b₀)
      g : (b : B) → fst (P a₀ b)
      p : f a₀ == g b₀

  module WedgeExt (r : args) where

    private
      module _ (r : args) where
        open args r

        Q : A → n -Type (lmax i j)
        Q a = ((Σ (∀ b → fst (P a b)) (λ k → (k ∘ cst b₀) == cst (f a)) ,
                  conn-extend-general (pointed-conn-out B b₀)
                                      (P a) (cst (f a))))

        l : Π A (fst ∘ Q)
        l = conn-extend (pointed-conn-out A a₀)
                        Q (λ (_ : Unit) → (g , ap cst (! p)))

    open args r

    ext : ∀ a → ∀ b → fst (P a b)
    ext a = fst (l r a)

    abstract
      β-l : ∀ a → ext a b₀ == f a
      β-l a = ap (λ t → t unit) (snd (l r a))

    private
      abstract
        β-r-aux : fst (l r a₀) == g
        β-r-aux = fst= (conn-extend-β
          (pointed-conn-out A a₀)
          (Q r) (λ (_ : Unit) → (g , ap cst (! p))) unit)

    abstract
      β-r : ∀ b → ext a₀ b == g b
      β-r = app= β-r-aux

    abstract
      coh : ! (β-l a₀) ∙ β-r b₀ == p
      coh =
        ! (β-l a₀) ∙ β-r b₀
          =⟨ ! lemma₂ |in-ctx (λ w → ! w ∙ β-r b₀) ⟩
        ! (β-r b₀ ∙ ! p) ∙ β-r b₀
          =⟨ !-∙ (β-r b₀) (! p) |in-ctx (λ w → w ∙ β-r b₀) ⟩
        (! (! p) ∙ ! (β-r b₀)) ∙ β-r b₀
          =⟨ ∙-assoc (! (! p)) (! (β-r b₀)) (β-r b₀) ⟩
        ! (! p) ∙ (! (β-r b₀) ∙ β-r b₀)
          =⟨ ap2 _∙_ (!-! p) (!-inv-l (β-r b₀)) ⟩
        p ∙ idp
          =⟨ ∙-unit-r p ⟩
        p =∎
        where
        lemma₁ : β-l a₀ == ap (λ s → s unit) (ap cst (! p))
                 [ (λ k → k b₀ == f a₀) ↓ β-r-aux ]
        lemma₁ = ap↓ (ap (λ s → s unit)) $
                      snd= (conn-extend-β (pointed-conn-out A a₀)
                           (Q r) (λ (_ : Unit) → (g , ap cst (! p))) unit)

        lemma₂ : β-r b₀ ∙ ! p == β-l a₀
        lemma₂ = ap (λ w → β-r b₀ ∙ w)
                    (! (ap-idf (! p)) ∙ ap-∘ (λ s → s unit) cst (! p))
                 ∙ (! (↓-app=cst-out lemma₁))
