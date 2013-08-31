{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.RibbonCover

module homotopy.CoverClassification {i} (A : Type i)
  (A-conn : is-connected ⟨0⟩ A) where

  open Cover

  module _ where
  -- private
    π1A = λ a → fundamental-group ∙[ A , a ]

  gset-to-cover : ∀ {j} a₁ → Gset (π1A a₁) j → Cover A (lmax i j)
  gset-to-cover a₁ gs = Ribbon-cover (A , a₁) gs

  module _ where
    cover-trace* : ∀ {j} (cov : Cover A j) {a₁ a₂}
      → Cover.Fiber cov a₁ → a₁ =₀ a₂
      → Cover.Fiber cov a₂
    cover-trace* cov a↑ p =
      transport₀ (Fiber cov) (Fiber-is-set cov _) p a↑

    abstract
      cover-trace*-idp₀ : ∀ {j} (cov : Cover A j) {a₁}
        → (a↑ : Cover.Fiber cov a₁)
        → cover-trace* cov a↑ idp₀ == a↑
      cover-trace*-idp₀ cov a↑ = idp

      cover-paste* : ∀ {j} (cov : Cover A j) {a₁ a₂}
        → (a↑ : Cover.Fiber cov a₁)
        → (loop : a₁ =₀ a₁)
        → (p : a₁ =₀ a₂)
        → cover-trace* cov (cover-trace* cov a↑ loop) p
        == cover-trace* cov a↑ (loop ∙₀ p)
      cover-paste* cov a↑ loop p = ! $ trans₀-∙₀ (λ {a} → Fiber-is-set cov a) loop p a↑

  cover-to-gset-struct : ∀ {j} (cov : Cover A j) (a₁ : A)
    → GsetStructure (π1A a₁) (Fiber cov a₁) (Fiber-is-set cov a₁)
  cover-to-gset-struct cov a₁ = record
    { act = cover-trace* cov
    ; unit-r = cover-trace*-idp₀ cov
    ; assoc = cover-paste* cov
    }

  cover-to-gset : ∀ {j} → Cover A j → (a : A) → Gset (π1A a) j
  cover-to-gset cov a₁ = record
    { El = Fiber cov a₁
    ; El-level = Fiber-level cov a₁
    ; gset-struct = cover-to-gset-struct cov a₁
    }

  -- This is derivable from connectedness condition.
  module _ where
    abstract
      [base-path] : ∀ {a₁ a₂ : A} → Trunc ⟨-1⟩ (a₁ == a₂)
      [base-path] {a₁} {a₂} =
        –> (Trunc=-equiv [ a₁ ] [ a₂ ]) (contr-has-all-paths A-conn [ a₁ ] [ a₂ ])

  -- Part 1: Show that the synthesized cover (ribbon) is fiberwisely
  --         equivalent to the original fiber.
  private
    module _ {j} (cov : Cover A j) where

      -- Suppose that we get the path, we can compute the ribbon easily.
      fiber+path-to-ribbon : ∀ {a₁ a₂} (a↑ : Fiber cov a₂) (p : a₁ == a₂)
        → Ribbon (A , a₁) (cover-to-gset cov a₁) a₂
      fiber+path-to-ribbon {a₂} a↑ p =
        trace (cover-trace* cov a↑ [ ! p ]) [ p ]

      abstract
        -- Our construction is "constant" with respect to paths.
        fiber+path-to-ribbon-is-path-irrelevant :
          ∀ {a₁ a₂} (a↑ : Fiber cov a₂) (p₁ p₂ : a₁ == a₂)
          → fiber+path-to-ribbon a↑ p₁ == fiber+path-to-ribbon a↑ p₂
        fiber+path-to-ribbon-is-path-irrelevant a↑ p idp =
          trace (cover-trace* cov a↑ [ ! p ]) [ p ]
            =⟨ paste a↑ [ ! p ] [ p ] ⟩
          trace a↑ [ ! p ∙ p ]
            =⟨ ap (trace a↑) $ !₀-inv-l [ p ] ⟩
          trace a↑ idp₀
            ∎

      open import homotopy.ConstantToSetFactorization

      fiber+path₋₁-to-ribbon : ∀ {a₁ a₂} (a↑ : Cover.Fiber cov a₂)
        → Trunc ⟨-1⟩ (a₁ == a₂) → Ribbon (A , a₁) (cover-to-gset cov a₁) a₂
      fiber+path₋₁-to-ribbon a↑ = cst-extend
        Ribbon-is-set
        (fiber+path-to-ribbon a↑)
        (fiber+path-to-ribbon-is-path-irrelevant a↑)

  -- So the conversion from fiber to ribbon is done.
  fiber-to-ribbon : ∀ {j} (cov : Cover A j)
    → {a₁ a₂ : A} (a↑ : Cover.Fiber cov a₂)
    → Ribbon (A , a₁) (cover-to-gset cov a₁) a₂
  fiber-to-ribbon cov a↑ = fiber+path₋₁-to-ribbon cov a↑ [base-path]

  -- The other direction is easy.
  ribbon-to-fiber : ∀ {j} (cov : Cover A j) {a₁ a₂}
    → Ribbon (A , a₁) (cover-to-gset cov a₁) a₂ → Cover.Fiber cov a₂
  ribbon-to-fiber cov {a₁}{a₂} r =
    Ribbon-rec (Fiber-is-set cov a₂) (cover-trace* cov) (cover-paste* cov) r

  private
    -- Some routine computations.
    abstract
      ribbon-to-fiber-to-ribbon : ∀ {j} (cov : Cover A j) {a₁ a₂}
        → (r : Ribbon (A , a₁) (cover-to-gset cov a₁) a₂)
        → fiber-to-ribbon cov (ribbon-to-fiber cov r) == r
      ribbon-to-fiber-to-ribbon cov {a₁}{a₂} = Ribbon-elim
        {P = λ r → fiber-to-ribbon cov (ribbon-to-fiber cov r) == r}
        (λ {_} → =-preserves-set Ribbon-is-set)
        (λ a↑ p → Trunc-elim
          -- All ugly things will go away when bp = proj bp′
          (λ bp → Ribbon-is-set
                    (fiber+path₋₁-to-ribbon cov (cover-trace* cov a↑ p) bp)
                    (trace a↑ p))
          (lemma a↑ p)
          [base-path])
        (λ _ _ _ → prop-has-all-paths-↓ (Ribbon-is-set _ _))
        where
          abstract
            lemma : ∀ {a₂} (a↑ : Cover.Fiber cov a₁) (p : a₁ =₀ a₂) (bp : a₁ == a₂)
              → trace {gs = cover-to-gset cov a₁}
                  (cover-trace* cov (cover-trace* cov a↑ p) [ ! bp ]) [ bp ]
              == trace a↑ p
            lemma a↑ p idp =
              trace (cover-trace* cov a↑ p) idp₀
                =⟨ paste a↑ p idp₀ ⟩
              trace a↑ (p ∙₀ idp₀)
                =⟨ ap (trace a↑) $ ∙₀-unit-r p ⟩
              trace a↑ p
                ∎

      fiber-to-ribbon-to-fiber : ∀ {j} (cov : Cover A j) {a₁ a₂}
        → (a↑ : Cover.Fiber cov a₂)
        → ribbon-to-fiber cov (fiber-to-ribbon cov {a₁} a↑) == a↑
      fiber-to-ribbon-to-fiber cov {a₁}{a₂} a↑ = Trunc-elim
        -- All ugly things will go away when bp = proj bp′
        (λ bp → Cover.Fiber-is-set cov a₂
                  (ribbon-to-fiber cov
                    (fiber+path₋₁-to-ribbon cov a↑ bp))
                  a↑)
        (lemma a↑)
        [base-path]
        where
          abstract
            lemma : ∀ {a₂} (a↑ : Cover.Fiber cov a₂) (bp : a₁ == a₂)
              → cover-trace* cov (cover-trace* cov a↑ [ ! bp ]) [ bp ]
              == a↑
            lemma a↑ idp = idp

  cover-to-gset-to-cover : ∀ {j} (cov : Cover A (lmax i j)) a₁
    → gset-to-cover a₁ (cover-to-gset cov a₁) == cov
  cover-to-gset-to-cover cov a₁ = cover= λ _ →
    ribbon-to-fiber cov , is-eq
      (ribbon-to-fiber cov)
      (fiber-to-ribbon cov)
      (fiber-to-ribbon-to-fiber cov)
      (ribbon-to-fiber-to-ribbon cov)

  -- The second direction : gset -> covering -> gset

  -- Part 2.1: The fiber over the point a is the carrier.
  ribbon-a₁-to-El : ∀ {j} {a₁} {gs : Gset (π1A a₁) j}
    → Ribbon (A , a₁) gs a₁ → Gset.El gs
  ribbon-a₁-to-El {j} {a₁} {gs} = let open Gset gs in
    Ribbon-rec El-level act assoc

  ribbon-a₁-to-El-equiv : ∀ {j} {a₁} {gs : Gset (π1A a₁) j}
    → Ribbon (A , a₁) gs a₁ ≃ Gset.El gs
  ribbon-a₁-to-El-equiv {j} {a₁} {gs} = let open Gset gs in
    ribbon-a₁-to-El , is-eq _
      (λ r → trace r idp₀)
      (λ a↑ → unit-r a↑)
      (Ribbon-elim
        {P = λ r → trace (ribbon-a₁-to-El r) idp₀ == r}
        (=-preserves-set Ribbon-is-set)
        (λ y p →
          trace (act y p) idp₀
            =⟨ paste y p idp₀ ⟩
          trace y (p ∙₀ idp₀)
            =⟨ ap (trace y) $ ∙₀-unit-r p ⟩
          trace y p
            ∎)
        (λ _ _ _ → prop-has-all-paths-↓ (Ribbon-is-set _ _)))

  gset-to-cover-to-gset : ∀ {j} a₁ (gs : Gset (π1A a₁) (lmax i j))
    → cover-to-gset (gset-to-cover a₁ gs) a₁ == gs
  gset-to-cover-to-gset a₁ gs =
    gset=
      ribbon-a₁-to-El-equiv
      (λ {x₁}{x₂} x= → Trunc-elim (λ _ → =-preserves-set $ Gset.El-is-set gs) λ g →
        ribbon-a₁-to-El (transport (Ribbon (A , a₁) gs) g x₁)
          =⟨ ap (λ x → ribbon-a₁-to-El (transport (Ribbon (A , a₁) gs) g x))
                $ ! $ <–-inv-l ribbon-a₁-to-El-equiv x₁ ⟩
        ribbon-a₁-to-El (transport (Ribbon (A , a₁) gs) g (trace (ribbon-a₁-to-El x₁) idp₀))
          =⟨ ap (λ x → ribbon-a₁-to-El (transport (Ribbon (A , a₁) gs) g (trace x idp₀))) x= ⟩
        ribbon-a₁-to-El (transport (Ribbon (A , a₁) gs) g (trace x₂ idp₀))
          =⟨ ap ribbon-a₁-to-El $ trans-trace g x₂ idp₀ ⟩
        Gset.act gs x₂ [ g ]
          ∎)

  -- Finally...
  gset-to-cover-equiv : ∀ {j} (a : A)
    → Gset (π1A a) (lmax i j) ≃ Cover A (lmax i j)
  gset-to-cover-equiv {j} a =
    gset-to-cover a , is-eq
      _
      (λ c → cover-to-gset c a)
      (λ c → cover-to-gset-to-cover {lmax i j} c a)
      (gset-to-cover-to-gset {lmax i j} a)
