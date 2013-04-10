{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

{-
  An example of using the overkilling covering space library.
-}

module Homotopy.Cover.ExamplePi1Circle where

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation
  open import Spaces.Circle

  {-
      The 1st step: Show that the circle is connected.
  -}
  S¹-is-conn : is-connected ⟨0⟩ S¹
  S¹-is-conn = proj base ,
    τ-extend ⦃ λ _ → ≡-is-set $ π₀-is-set S¹ ⦄
      (S¹-rec (λ x → proj x ≡ proj base) refl
        (prop-has-all-paths (π₀-is-set S¹ _ _) _ _))

  open import Integers
  open import Homotopy.Pointed
  open import Homotopy.Cover.Def S¹
  open import Homotopy.Cover.HomotopyGroupSetIsomorphism (⋆[ S¹ , base ]) S¹-is-conn

  S¹-covering : covering
  S¹-covering = let fiber = S¹-rec-nondep Set ℤ (eq-to-path succ-equiv) in
    cov[ fiber , S¹-rec (is-set ◯ fiber) ℤ-is-set (prop-has-all-paths is-set-is-prop _ _) ]

  open covering S¹-covering

  {-
      The 2nd step : Show that S¹ is contractible.
  -}

  -- One step.
  trans-fiber-!loop : ∀ z → transport fiber (! loop) z ≡ pred z
  trans-fiber-!loop z =
    transport fiber (! loop) z
      ≡⟨ ! $ trans-ap (id _) fiber (! loop) z ⟩
    transport (id _) (ap fiber (! loop)) z
      ≡⟨ ap (λ x → transport (id _) x z) $ ap-opposite fiber loop ⟩
    transport (id _) (! (ap fiber loop)) z
      ≡⟨ ap (λ x → transport (id _) (! x) z) $ S¹-β-loop-nondep Set ℤ (eq-to-path _) ⟩
    transport (id _) (! (eq-to-path succ-equiv)) z
      ≡⟨ trans-id-!eq-to-path _ _ ⟩∎
    pred z
      ∎

  -- The end of this function.  This can save some type annotations.
  loop⁻ⁿ-end : Σ S¹ fiber
  loop⁻ⁿ-end = (base , O)

  -- Climbing up the stairs.
  loop⁻¹ : ∀ z → _≡_ {A = Σ S¹ fiber} (base , z) (base , pred z)
  loop⁻¹ z = Σ-eq (! loop) (trans-fiber-!loop z)

  -- Agda needs us to show the induction order explicitly,
  -- and so there are so many functions.
  loop⁻ⁿ : ∀ z → (base , z) ≡ loop⁻ⁿ-end
  loop⁻ⁿ-pos : ∀ n → (base , pos n) ≡ loop⁻ⁿ-end
  loop⁻ⁿ-neg : ∀ n → (base , neg n) ≡ loop⁻ⁿ-end

  loop⁻ⁿ O = refl
  loop⁻ⁿ (pos _) = loop⁻ⁿ-pos _
  loop⁻ⁿ (neg _) = loop⁻ⁿ-neg _
  loop⁻ⁿ-pos 0 = loop⁻¹ _
  loop⁻ⁿ-pos (S _) = loop⁻¹ _ ∘ loop⁻ⁿ-pos _
  loop⁻ⁿ-neg 0 = ! (loop⁻¹ _)
  loop⁻ⁿ-neg (S _) = ! (loop⁻¹ _) ∘ loop⁻ⁿ-neg _

  private
    -- These are specialized J rules that work for this development only.
    -- I am too lazy to generalize them.

    lemma₁ : ∀ {x₁ x₂} (q : x₁ ≡ x₂) (f : ∀ z → (x₁ , z) ≡ loop⁻ⁿ-end) (z : fiber x₂)
      → transport (λ s → ∀ z → (s , z) ≡ loop⁻ⁿ-end) q f z
      ≡ Σ-eq (! q) refl ∘ f (transport fiber (! q) z)
    lemma₁ refl f z = refl

    lemma₂ : ∀ {b₁} {b₂} (q : b₁ ≡ b₂) p
      → transport (λ z → (base , z) ≡ loop⁻ⁿ-end) (! q) p
      ≡ Σ-eq refl q ∘ p
    lemma₂ refl p = refl

    compose-Σ-eq : ∀ {a₁} {a₂} (p : a₁ ≡ a₂)
      {b₁ : fiber a₁} {b₂} (q : transport fiber p b₁ ≡ b₂)
      → Σ-eq {A = S¹} {P = fiber} p refl ∘ Σ-eq refl q ≡ Σ-eq p q
    compose-Σ-eq refl q = refl

    loop⁻¹-loop⁻ⁿ-pred : ∀ z → loop⁻¹ z ∘ loop⁻ⁿ (pred z) ≡ loop⁻ⁿ z
    loop⁻¹-loop⁻ⁿ-pred O = opposite-right-inverse (loop⁻¹ _)
    loop⁻¹-loop⁻ⁿ-pred (pos O) = refl-right-unit _
    loop⁻¹-loop⁻ⁿ-pred (pos (S _)) = refl
    loop⁻¹-loop⁻ⁿ-pred (neg _) =
      loop⁻¹ _ ∘ (! (loop⁻¹ _) ∘ loop⁻ⁿ-neg _)
        ≡⟨ ! $ concat-assoc (loop⁻¹ _) (! (loop⁻¹ _)) _ ⟩
      (loop⁻¹ _ ∘ ! (loop⁻¹ _)) ∘ loop⁻ⁿ-neg _
        ≡⟨ ap (λ x → x ∘ loop⁻ⁿ-neg _) $ opposite-right-inverse (loop⁻¹ _) ⟩∎
      loop⁻ⁿ-neg _
        ∎

  path : ∀ x z → (x , z) ≡ loop⁻ⁿ-end
  path = S¹-rec (λ s → ∀ z → (s , z) ≡ loop⁻ⁿ-end) loop⁻ⁿ $ funext λ z →
    transport (λ s → ∀ z → (s , z) ≡ loop⁻ⁿ-end) loop loop⁻ⁿ z
        ≡⟨ lemma₁ loop loop⁻ⁿ z ⟩
    Σ-eq (! loop) refl ∘ loop⁻ⁿ (transport fiber (! loop) z)
        ≡⟨ ap (λ x → Σ-eq (! loop) refl ∘ x) $ apd! loop⁻ⁿ (trans-fiber-!loop z) ⟩
    Σ-eq (! loop) refl ∘
      (transport (λ z → (base , z) ≡ loop⁻ⁿ-end) (! $ trans-fiber-!loop z) (loop⁻ⁿ (pred z)))
        ≡⟨ ap (λ x → Σ-eq (! loop) refl ∘ x) $ lemma₂ (trans-fiber-!loop z) (loop⁻ⁿ (pred z)) ⟩
    Σ-eq (! loop) refl ∘ (Σ-eq refl (trans-fiber-!loop z) ∘ loop⁻ⁿ (pred z))
        ≡⟨ ! $ concat-assoc (Σ-eq (! loop) refl) _ _ ⟩
    (Σ-eq (! loop) refl ∘ Σ-eq refl (trans-fiber-!loop z)) ∘ loop⁻ⁿ (pred z)
        ≡⟨ ap (λ x → x ∘ loop⁻ⁿ (pred z)) $ compose-Σ-eq (! loop) (trans-fiber-!loop z) ⟩
    loop⁻¹ z ∘ loop⁻ⁿ (pred z)
        ≡⟨ loop⁻¹-loop⁻ⁿ-pred z ⟩∎
    loop⁻ⁿ z
        ∎

  S¹-covering-is-universal : is-universal S¹-covering
  S¹-covering-is-universal = contr-is-connected ⟨1⟩ $ loop⁻ⁿ-end , uncurry path

  ℤ-π¹S¹-equiv : ℤ ≃ (base ≡₀ base)
  ℤ-π¹S¹-equiv = GiveMeAPoint.fiber-a≃fg S¹-covering S¹-covering-is-universal O
