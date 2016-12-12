{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.AnyUniversalCoverIsPathSet {i} (X : Ptd i) where

private
  a₁ = snd X

path-set-is-universal : is-universal (path-set-cover X)
path-set-is-universal = [ snd X , idp₀ ] ,
  Trunc-elim
    {P = λ xp₀ → [ snd X , idp₀ ] == xp₀}
    (λ xp₀ → =-preserves-level 1 Trunc-level)
    (λ{(x , p₀) → Trunc-elim
      {P = λ p₀ → [ snd X , idp₀ ] == [ x , p₀ ]}
      (λ p₀ → Trunc-level {n = 1} [ snd X , idp₀ ] [ x , p₀ ])
      (λ p → ap [_] $ pair= p (lemma p))
      p₀ })
  where
    lemma : ∀ {x} (p : snd X == x) → idp₀ == [ p ] [ (snd X =₀_) ↓ p ]
    lemma idp = idp

module _ {j} (univ-cov : ⊙UniversalCover X j) where
  private
    module univ-cov = ⊙UniversalCover univ-cov

    -- One-to-one mapping between the universal cover
    -- and the truncated path spaces from one point.

    [path] : ∀ (a⇑₁ a⇑₂ : univ-cov.TotalSpace) → a⇑₁ =₀ a⇑₂
    [path] a⇑₁ a⇑₂ = –> (Trunc=-equiv [ a⇑₁ ] [ a⇑₂ ])
      (contr-has-all-paths univ-cov.is-univ [ a⇑₁ ] [ a⇑₂ ])

    [path]-has-all-paths :
      ∀ {a⇑₁ a⇑₂ : univ-cov.TotalSpace}
      → has-all-paths (a⇑₁ =₀ a⇑₂)
    [path]-has-all-paths {a⇑₁} {a⇑₂} =
      coe (ap has-all-paths $ ua (Trunc=-equiv [ a⇑₁ ] [ a⇑₂ ]))
      $ contr-has-all-paths (raise-level -2 univ-cov.is-univ [ a⇑₁ ] [ a⇑₂ ])

    to : ∀ {a₂} → univ-cov.Fiber a₂ → a₁ =₀ a₂
    to {a₂} a⇑₂ = ap₀ fst ([path] (a₁ , univ-cov.pt) (a₂ , a⇑₂))

    from : ∀ {a₂} → a₁ =₀ a₂ → univ-cov.Fiber a₂
    from p = cover-trace univ-cov.cov univ-cov.pt p

    to-from : ∀ {a₂} (p : a₁ =₀ a₂) → to (from p) == p
    to-from = Trunc-elim
      (λ _ → =-preserves-set Trunc-level)
      (λ p → lemma p)
      where
        lemma : ∀ {a₂} (p : a₁ == a₂) → to (from [ p ]) == [ p ]
        lemma idp =
          ap₀ fst ([path] (a₁ , univ-cov.pt) (a₁ , univ-cov.pt))
            =⟨ ap (ap₀ fst)
                  $ [path]-has-all-paths
                    ([path] (a₁ , univ-cov.pt) (a₁ , univ-cov.pt))
                    (idp₀ :> ((a₁ , univ-cov.pt) =₀ (a₁ , univ-cov.pt))) ⟩
          (idp₀ :> (a₁ =₀ a₁))
            ∎

    from-to : ∀ {a₂} (a⇑₂ : univ-cov.Fiber a₂) → from (to a⇑₂) == a⇑₂
    from-to {a₂} a⇑₂ = Trunc-elim
      (λ p → =-preserves-set
              {x = from (ap₀ fst p)}
              {y = a⇑₂}
              (univ-cov.Fiber-is-set a₂))
      (λ p → to-transp $ snd= p)
      ([path] (a₁ , univ-cov.pt) (a₂ , a⇑₂))

  theorem : ∀ a₂ → univ-cov.Fiber a₂ ≃ (a₁ =₀ a₂)
  theorem a₂ = to , is-eq _ from to-from from-to
