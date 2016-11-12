{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module experimental.NConnected where

  lemma₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {n : ℕ₋₂}
    → is-connected n A → is-connected (S n) B
    → has-conn-fibers n f
  lemma₁ f cA cB = λ b → Σ-conn cA (λ a → path-conn cB)

  lemma₂ : ∀ {i} {A B C : Type i}
    → (f : A → B) (g : B → C) {n : ℕ₋₂}
    → has-conn-fibers n (g ∘ f)
    → has-conn-fibers (S n) g
    → has-conn-fibers n f
  lemma₂ f g {n} cA cB b =
    equiv-preserves-conn (eqv b idp ⁻¹) (lemma₁-f′ (g b) (b , idp))
      where
        f′ : ∀ c → hfiber (g ∘ f) c → hfiber g c
        f′ c (a , p) = (f a , p)

        -- We first show [∀ b → is-connected n (hfiber (f′ (g b) (b , idp))) ]
        lemma₁-f′ : ∀ c → has-conn-fibers n (f′ c)
        lemma₁-f′ c = lemma₁ (f′ c) (cA c) (cB c)

        -- The remaining shows [hfiber (f′ (g b) (b , idp))]
        -- is the same as [hfiber f b]
        to : ∀ b p → hfiber f b → hfiber (f′ (g b)) (b , p)
        to ._ p (a , idp) = ((a , p) , idp)

        from′ : ∀ b a → f a == b → hfiber f b
        from′ ._ a idp = (a , idp)

        from : ∀ b p → hfiber (f′ (g b)) (b , p) → hfiber f b
        from b p ((a , q) , r) = from′ b a (fst= r)

        from-to : ∀ b p x → from b p (to b p x) == x
        from-to ._ p (a , idp) = idp

        to-from : ∀ b p x → to b p (from b p x) == x
        to-from b p ((a , q) , r) =
            to b p (from b p ((a , q) , r))
              =⟨ pair=-η r |in-ctx (λ r → to b p (from b p ((a , q) , r))) ⟩
            to b p (from b p ((a , q) , pair= (fst= r) (snd= r)))
              =⟨ lemma b p a q (fst= r) (snd= r) ⟩
            ((a , q) , pair= (fst= r) (snd= r))
              =⟨ ! (pair=-η r) |in-ctx (λ r → ((a , q) , r)) ⟩
            ((a , q) , r)
              ∎
          where
            lemma : ∀ b p a (q : g (f a) == g b)
              → (r : f a == b) (s : q == p [ (λ b′ → g b′ == g b) ↓ r ])
              → to b p (from b p ((a , q) , pair= r s)) == ((a , q) , pair= r s)
            lemma ._ ._ a q idp idp = idp

        eqv : ∀ b p → hfiber f b ≃ hfiber (f′ (g b)) (b , p)
        eqv b p = equiv (to b p) (from b p) (to-from b p) (from-to b p)

  lemma₃ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
    → A ≃ Σ B (hfiber f)
  lemma₃ {A = A} {B} f = equiv to from to-from from-to
    where
      to : A → Σ B (hfiber f)
      to a = (f a , (a , idp))

      from : Σ B (hfiber f) → A
      from (_ , (a , p)) = a

      to-from : ∀ s → to (from s) == s
      to-from (._ , (a , idp)) = idp

      from-to : ∀ a → from (to a) == a
      from-to a = idp



{-
∘-conn : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → (f : A → B) → (g : B → C) → {n : ℕ₋₂}
  → has-conn-fibers n f
  → has-conn-fibers n g
  → has-conn-fibers n (g ∘ f)
∘-conn f g {⟨-2⟩} cf cg c = -2-conn _
∘-conn f g {S n } cf cg c =
  Trunc-rec
    {P = is-connected (hfiber (g ∘ f) c)}
    (prop-has-level-S n (is-connected-is-prop n A))
    (λ c )
    (cg c)
-}

{-
  lemma₃-path : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
    → A == Σ B (hfiber f)
  lemma₃-path = λ f → ua (lemma₃ f)
-}
