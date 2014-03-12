{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.AnyUniversalCoverIsPathSet {i} (A : Type i)
  (A-conn : is-connected ⟨0⟩ A) where

  open Cover

  module _
    (a₁ : A)
    -- A universal covering (defined as being simply connected).
    {j} (univ-cov : Cover A j)
    (univ-cov-univ : is-universal univ-cov)
    (a⇑₁ : Fiber univ-cov a₁)
    where

    private
      -- One-to-one mapping between the universal cover
      -- and the truncated path spaces from one point.

      [path] : ∀ (a⇑₁ a⇑₂ : TotalSpace univ-cov) → a⇑₁ =₀ a⇑₂
      [path] a⇑₁ a⇑₂ = –> (Trunc=-equiv [ a⇑₁ ] [ a⇑₂ ])
        (contr-has-all-paths univ-cov-univ [ a⇑₁ ] [ a⇑₂ ])

      [path]-has-all-paths :
        ∀ {a⇑₁ a⇑₂ : TotalSpace univ-cov}
        → has-all-paths (a⇑₁ =₀ a⇑₂)
      [path]-has-all-paths {a⇑₁} {a⇑₂} =
        coe (ap has-all-paths $ ua (Trunc=-equiv [ a⇑₁ ] [ a⇑₂ ]))
        $ contr-has-all-paths (raise-level ⟨-2⟩ univ-cov-univ [ a⇑₁ ] [ a⇑₂ ])

      to : ∀ {a₂} → Fiber univ-cov a₂ → a₁ =₀ a₂
      to {a₂} a⇑₂ = ap₀ fst ([path] (a₁ , a⇑₁) (a₂ , a⇑₂))

      from : ∀ {a₂} → a₁ =₀ a₂ → Fiber univ-cov a₂
      from p = cover-trace univ-cov a⇑₁ p

      to-from : ∀ {a₂} (p : a₁ =₀ a₂) → to (from p) == p
      to-from = Trunc-elim
        (λ _ → =-preserves-set Trunc-level)
        (λ p → lemma p)
        where
          lemma : ∀ {a₂} (p : a₁ == a₂) → to (from [ p ]) == [ p ]
          lemma idp =
            ap₀ fst ([path] (a₁ , a⇑₁) (a₁ , a⇑₁))
              =⟨ ap (ap₀ fst)
                    $ [path]-has-all-paths
                      ([path] (a₁ , a⇑₁) (a₁ , a⇑₁))
                      (idp₀ :> ((a₁ , a⇑₁) =₀ (a₁ , a⇑₁))) ⟩
            (idp₀ :> (a₁ =₀ a₁))
              ∎

      from-to : ∀ {a₂} (a⇑₂ : Fiber univ-cov a₂) → from (to a⇑₂) == a⇑₂
      from-to {a₂} a⇑₂ = Trunc-elim
        (λ p → =-preserves-set
                {x = from (ap₀ fst p)}
                {y = a⇑₂}
                (Fiber-level univ-cov a₂))
        (λ p → to-transp $ snd= p)
        ([path] (a₁ , a⇑₁) (a₂ , a⇑₂))

    theorem : ∀ a₂ → Fiber univ-cov a₂ ≃ (a₁ =₀ a₂)
    theorem a₂ = to , is-eq _ from to-from from-to
