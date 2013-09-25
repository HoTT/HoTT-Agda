{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.UniversalCoverIsUniversal {i} (A : Type i)
  (A-conn : is-connected ⟨0⟩ A) where

  open Cover

  module _
    (a₁ : A)
    -- And an arbitrary covering.
    {k} (cov : Cover A k)
    (cov-conn : is-connected ⟨0⟩ (Cover.TotalSpace cov))
    (a↑₁ : Fiber cov a₁)
    where

    -- "Curried" covering space. (a : A) → fiber a → Set
    quotient-cover : ∀ a₂ → Cover (Fiber cov a₂) (lmax i k)
    quotient-cover a₂ = record
      { Fiber = -- A base path with a proof that it transports [a↑₁] to [a↑₂]
          λ a↑₂ → Σ (a₁ =₀ a₂) (λ p → cover-trace cov a↑₁ p == a↑₂)
      ; Fiber-level = λ a↑₂ →
          Σ-level Trunc-level (λ p → =-preserves-set $ Fiber-level cov a₂)
      }

    private
      -- A lemma that should be moved to the basic library.
      ↓-cst×app-in : ∀ {i j k} {A : Type i}
        {B : Type j} {C : A → B → Type k}
        {a₁ a₂ : A} (p : a₁ == a₂)
        {b₁ b₂ : B} (q : b₁ == b₂)
        {c₁ : C a₁ b₁}{c₂ : C a₂ b₂}
        → c₁ == c₂ [ uncurry C ↓ pair×= p q ]
        → (b₁ , c₁) == (b₂ , c₂) [ (λ x → Σ B (C x)) ↓ p ]
      ↓-cst×app-in idp idp idp = idp

      -- One-to-many relationship between the base paths
      -- and points in the cover.

      to : ∀ {a₂} → TotalSpace (quotient-cover a₂) → a₁ =₀ a₂
      to (_ , (p , _)) = p

      from : ∀ {a₂} → a₁ =₀ a₂ → TotalSpace (quotient-cover a₂)
      from {a₂} p = cover-trace cov a↑₁ p , (p , idp)

      to-from : ∀ {a₂} (p : a₁ =₀ a₂) → to (from p) == p
      to-from p = idp

      from-to : ∀ {a₂} (a↑ : TotalSpace (quotient-cover a₂)) → from (to a↑) == a↑
      from-to {a₂} (a↑ , (p , cert)) =
        (cover-trace cov a↑₁ p , (p , idp))
          =⟨ pair= cert (↓-cst×app-in cert idp lemma) ⟩
        (a↑ , (p , cert))
          ∎
        where
          lemma :
            idp == cert
            [ (λ a↑p → cover-trace cov a↑₁ (snd a↑p) == (fst a↑p))
            ↓ pair×= cert idp ]
          lemma = ↓-='-in $
            fst×= (pair×= cert idp)
              =⟨ fst×=-β cert idp ⟩
            cert
              =⟨ ! $ ∙'-unit-l cert ⟩
            idp ∙' cert
              =⟨ idp ⟩
            ap (cover-trace cov a↑₁) (idp :> (p == p)) ∙' cert
              =⟨ ap (λ q → ap (cover-trace cov a↑₁) (q :> (p == p)) ∙' cert) $ ! $ snd×=-β cert idp ⟩
            ap (cover-trace cov a↑₁) (snd×= (pair×= cert (idp :> (p == p)))) ∙' cert
              =⟨ ap (λ p → p ∙' cert) $ ! $ ap-∘ (cover-trace cov a↑₁) snd (pair×= cert idp) ⟩
            ap (cover-trace cov a↑₁ ∘ snd) (pair×= cert (idp :> (p == p))) ∙' cert
              ∎

    weak-inital : ∀ a₂ → TotalSpace (quotient-cover a₂) ≃ (a₁ =₀ a₂)
    weak-inital a₂ = to , is-eq _ from to-from from-to

    module Uniqueness
      (cover′ : ∀ a₂ → Cover (Fiber cov a₂) (lmax i k))
      --(a↑₁ : Fiber cov a₁)
      (weak-inital′ : ∀ a₂ → TotalSpace (cover′ a₂) ≃ (a₁ =₀ a₂))
      (preserves-a↑₁ : fst (<– (weak-inital′ a₁) idp₀) == a↑₁)
      where

      private
        fst-match′ : ∀ {a₂} (p : a₁ =₀ a₂)
          → fst (<– (weak-inital a₂) p) == fst (<– (weak-inital′ a₂) p)
        fst-match′ {a₂} = Trunc-elim
          (λ p → =-preserves-set $ Fiber-is-set cov a₂)
          lemma where
            lemma : ∀ {a₂} (p : a₁ == a₂)
              → fst (<– (weak-inital a₂) [ p ]) == fst (<– (weak-inital′ a₂) [ p ])
            lemma idp = ! preserves-a↑₁

        total-equiv : ∀ a₂ → TotalSpace (quotient-cover a₂) ≃ TotalSpace (cover′ a₂)
        total-equiv a₂ = (weak-inital′ a₂) ⁻¹ ∘e weak-inital a₂

        fst-match : ∀ a₂ {a⇑₂} {a⇑₂′} (q : a⇑₂ == a⇑₂′ [ (λ X → X) ↓ ua (total-equiv a₂) ])
          → fst a⇑₂ == fst a⇑₂′
        fst-match a₂ {a⇑₂} {a⇑₂′} q =
          fst a⇑₂
            =⟨ ap fst $ ! $ <–-inv-l (weak-inital a₂) a⇑₂ ⟩
          fst (<– (weak-inital a₂) (–> (weak-inital a₂) a⇑₂))
            =⟨ fst-match′ (–> (weak-inital a₂) a⇑₂) ⟩
          fst (<– (weak-inital′ a₂) (–> (weak-inital a₂) a⇑₂))
            =⟨ ap fst $ ↓-idf-ua-out (total-equiv a₂) q ⟩
          fst a⇑₂′
            ∎
  
        fst-equiv : ∀ a₂ → fst == fst [ (λ C → C → Fiber cov a₂) ↓ ua (total-equiv a₂) ]
        fst-equiv a₂ = ↓-app→cst-in (fst-match a₂)

        Fiber-equiv : ∀ a₂ a↑₂ → Fiber (quotient-cover a₂) a↑₂ ≃ Fiber (cover′ a₂) a↑₂
        Fiber-equiv a₂ a↑₂ = hfiber-fst a↑₂
          ∘e lemma a₂ a↑₂ (ua $ total-equiv a₂) (fst-equiv a₂)
          ∘e (hfiber-fst a↑₂) ⁻¹
          where
            lemma : ∀ a₂ a↑₂ {l} {C₁ C₂ : Type l} (C= : C₁ == C₂)
              {f₁} {f₂} → (f₁ == f₂ [ (λ C → C → Fiber cov a₂) ↓ C= ])
              → hfiber f₁ a↑₂ ≃ hfiber f₂ a↑₂
            lemma a₂ a↑₂ idp idp = ide _

      theorem : quotient-cover == cover′
      theorem = λ= λ a₂ → cover= (Fiber-equiv a₂)
