{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.ConstantToSetExtendsToProp as ConstExt
open import homotopy.RibbonCover

module homotopy.CoverClassification {i} (X : Ptd i)
  (A-conn : is-connected 0 (fst X)) where

  open Cover

  private
    A : Type i
    A = fst X
    a₁ : A
    a₁ = snd X

  -- A covering space constructed from a G-set.
  gset-to-cover : ∀ {j} → Gset (πS 0 X) j → Cover A (lmax i j)
  gset-to-cover gs = Ribbon-cover X gs

  -- Covering spaces to G-sets.
  cover-to-gset-struct : ∀ {j} (cov : Cover A j)
    → GsetStructure (πS 0 X) (Fiber cov a₁) (Fiber-is-set cov a₁)
  cover-to-gset-struct cov = record
    { act = cover-trace cov
    ; unit-r = cover-trace-idp₀ cov
    ; assoc = cover-paste cov
    }

  cover-to-gset : ∀ {j} → Cover A j → Gset (πS 0 X) j
  cover-to-gset cov = record
    { El = Fiber cov a₁
    ; El-level = Fiber-level cov a₁
    ; gset-struct = cover-to-gset-struct cov
    }

  -- This is derivable from connectedness condition.
  module _ where
    abstract
      [base-path] : ∀ {a₂ : A} → Trunc -1 (a₁ == a₂)
      [base-path] {a₂} =
        –> (Trunc=-equiv [ a₁ ] [ a₂ ]) (contr-has-all-paths A-conn [ a₁ ] [ a₂ ])

  -- Part 1: Show that the synthesized cover (ribbon) is fiberwisely
  --         equivalent to the original fiber.
  private
    module _ {j} (cov : Cover A j) where

      -- Suppose that we get the path, we can compute the ribbon easily.
      fiber+path-to-ribbon : ∀ {a₂} (a↑ : Fiber cov a₂) (p : a₁ == a₂)
        → Ribbon X (cover-to-gset cov) a₂
      fiber+path-to-ribbon {a₂} a↑ p =
        trace (cover-trace cov a↑ [ ! p ]) [ p ]

      abstract
        -- Our construction is "constant" with respect to paths.
        fiber+path-to-ribbon-is-path-irrelevant :
          ∀ {a₂} (a↑ : Fiber cov a₂) (p₁ p₂ : a₁ == a₂)
          → fiber+path-to-ribbon a↑ p₁ == fiber+path-to-ribbon a↑ p₂
        fiber+path-to-ribbon-is-path-irrelevant a↑ p idp =
          trace (cover-trace cov a↑ [ ! p ]) [ p ]
            =⟨ paste a↑ [ ! p ] [ p ] ⟩
          trace a↑ [ ! p ∙ p ]
            =⟨ !₀-inv-l [ p ] |in-ctx trace a↑ ⟩
          trace a↑ idp₀
            ∎

      module FiberAndPathToRibbon {a₂} (a↑ : Fiber cov a₂)
        = ConstExt Ribbon-is-set
          (fiber+path-to-ribbon a↑)
          (fiber+path-to-ribbon-is-path-irrelevant a↑)

      fiber+path₋₁-to-ribbon : ∀ {a₂} (a↑ : Cover.Fiber cov a₂)
        → Trunc -1 (a₁ == a₂) → Ribbon X (cover-to-gset cov) a₂
      fiber+path₋₁-to-ribbon a↑ = FiberAndPathToRibbon.cst-extend a↑

  -- So the conversion from fiber to ribbon is done.
  fiber-to-ribbon : ∀ {j} (cov : Cover A j)
    → {a₂ : A} (a↑ : Cover.Fiber cov a₂)
    → Ribbon X (cover-to-gset cov) a₂
  fiber-to-ribbon cov a↑ = fiber+path₋₁-to-ribbon cov a↑ [base-path]

  -- The other direction is easy.
  ribbon-to-fiber : ∀ {j} (cov : Cover A j) {a₂}
    → Ribbon X (cover-to-gset cov) a₂ → Cover.Fiber cov a₂
  ribbon-to-fiber cov {a₂} r =
    Ribbon-rec (Fiber-is-set cov a₂) (cover-trace cov) (cover-paste cov) r

  private
    -- Some routine computations.
    abstract
      ribbon-to-fiber-to-ribbon : ∀ {j} (cov : Cover A j) {a₂}
        → (r : Ribbon X (cover-to-gset cov) a₂)
        → fiber-to-ribbon cov (ribbon-to-fiber cov r) == r
      ribbon-to-fiber-to-ribbon cov {a₂} = Ribbon-elim
        {P = λ r → fiber-to-ribbon cov (ribbon-to-fiber cov r) == r}
        (λ _ → =-preserves-set Ribbon-is-set)
        (λ a↑ p → Trunc-elim
          -- All ugly things will go away when bp = proj bp′
          (λ bp → Ribbon-is-set
                    (fiber+path₋₁-to-ribbon cov (cover-trace cov a↑ p) bp)
                    (trace a↑ p))
          (lemma a↑ p)
          [base-path])
        (λ _ _ _ → prop-has-all-paths-↓ (Ribbon-is-set _ _))
        where
          abstract
            lemma : ∀ {a₂} (a↑ : Cover.Fiber cov a₁) (p : a₁ =₀ a₂) (bp : a₁ == a₂)
              → trace {X = X} {gs = cover-to-gset cov}
                  (cover-trace cov (cover-trace cov a↑ p) [ ! bp ]) [ bp ]
              == trace {X = X} {gs = cover-to-gset cov} a↑ p
            lemma a↑ p idp =
              trace (cover-trace cov a↑ p) idp₀
                =⟨ paste a↑ p idp₀ ⟩
              trace a↑ (p ∙₀ idp₀)
                =⟨ ap (trace a↑) $ ∙₀-unit-r p ⟩
              trace a↑ p
                ∎

      fiber-to-ribbon-to-fiber : ∀ {j} (cov : Cover A j) {a₂}
        → (a↑ : Cover.Fiber cov a₂)
        → ribbon-to-fiber cov (fiber-to-ribbon cov {a₂} a↑) == a↑
      fiber-to-ribbon-to-fiber cov {a₂} a↑ = Trunc-elim
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
              → cover-trace cov (cover-trace cov a↑ [ ! bp ]) [ bp ]
              == a↑
            lemma a↑ idp = idp

  cover-to-gset-to-cover : ∀ {j} (cov : Cover A (lmax i j))
    → gset-to-cover (cover-to-gset cov) == cov
  cover-to-gset-to-cover cov = cover= λ _ →
    ribbon-to-fiber cov , is-eq
      (ribbon-to-fiber cov)
      (fiber-to-ribbon cov)
      (fiber-to-ribbon-to-fiber cov)
      (ribbon-to-fiber-to-ribbon cov)

  -- The second direction : gset -> covering -> gset

  -- Part 2.1: The fiber over the point a is the carrier.
  ribbon-a₁-to-El : ∀ {j} {gs : Gset (πS 0 X) j}
    → Ribbon X gs a₁ → Gset.El gs
  ribbon-a₁-to-El {j} {gs} = let open Gset gs in
    Ribbon-rec El-level act assoc

  ribbon-a₁-to-El-equiv : ∀ {j} {gs : Gset (πS 0 X) j}
    → Ribbon X gs a₁ ≃ Gset.El gs
  ribbon-a₁-to-El-equiv {j} {gs} = let open Gset gs in
    ribbon-a₁-to-El , is-eq _
      (λ r → trace r idp₀)
      (λ a↑ → unit-r a↑)
      (Ribbon-elim
        {P = λ r → trace (ribbon-a₁-to-El r) idp₀ == r}
        (λ _ → =-preserves-set Ribbon-is-set)
        (λ y p →
          trace (act y p) idp₀
            =⟨ paste y p idp₀ ⟩
          trace y (p ∙₀ idp₀)
            =⟨ ap (trace y) $ ∙₀-unit-r p ⟩
          trace y p
            ∎)
        (λ _ _ _ → prop-has-all-paths-↓ (Ribbon-is-set _ _)))

  gset-to-cover-to-gset : ∀ {j} (gs : Gset (πS 0 X) (lmax i j))
    → cover-to-gset (gset-to-cover gs) == gs
  gset-to-cover-to-gset gs =
    gset=
      ribbon-a₁-to-El-equiv
      (λ {x₁}{x₂} x= → Trunc-elim (λ _ → =-preserves-set $ Gset.El-is-set gs) λ g →
        ribbon-a₁-to-El (transport (Ribbon X gs) g x₁)
          =⟨ ap (λ x → ribbon-a₁-to-El (transport (Ribbon X gs) g x))
                $ ! $ <–-inv-l ribbon-a₁-to-El-equiv x₁ ⟩
        ribbon-a₁-to-El (transport (Ribbon X gs) g (trace (ribbon-a₁-to-El x₁) idp₀))
          =⟨ ap (λ x → ribbon-a₁-to-El (transport (Ribbon X gs) g (trace x idp₀))) x= ⟩
        ribbon-a₁-to-El (transport (Ribbon X gs) g (trace x₂ idp₀))
          =⟨ ap ribbon-a₁-to-El $ trans-trace g x₂ idp₀ ⟩
        Gset.act gs x₂ [ g ]
          ∎)

  -- Finally...
  gset-to-cover-equiv : ∀ {j}
    → Gset (πS 0 X) (lmax i j) ≃ Cover A (lmax i j)
  gset-to-cover-equiv {j} =
    gset-to-cover , is-eq
      _
      (λ c → cover-to-gset c)
      (λ c → cover-to-gset-to-cover {lmax i j} c)
      (gset-to-cover-to-gset {lmax i j})
