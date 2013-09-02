{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.UniversalCoverIsUniversal {i} (A : Type i)
  (A-conn : is-connected ⟨0⟩ A) where

  open Cover

  module _
    (a₁ : A)
    -- A universal covering.
    {j} (univ-cov : Cover A j)
    (univ-cov-univ : is-universal univ-cov)
    (a⇑₁ : Fiber univ-cov a₁)
    -- And an arbitrary covering.
    {k} (cov : Cover A k)
    (cov-conn : is-connected ⟨0⟩ (Cover.TotalSpace cov))
    (a↑₁ : Fiber cov a₁)
    where

    inital-cover : ∀ a₂ → Cover (Fiber cov a₂) (lmax i k)
    inital-cover a₂ = record
      { Fiber = λ a↑₂ → Σ (a₁ =₀ a₂) (λ p → cover-trace cov a↑₁ p == a↑₂)
      ; Fiber-level = λ a↑₂ →
        Σ-level Trunc-level (λ p → =-preserves-set $ Fiber-level cov a₂)
      }

    private
      ↓-cst×app-in : ∀ {i j k} {A : Type i}
        {B : Type j} {C : A → B → Type k}
        {a₁ a₂ : A} (p : a₁ == a₂)
        {b₁ b₂ : B} (q : b₁ == b₂)
        {c₁ : C a₁ b₁}{c₂ : C a₂ b₂}
        → c₁ == c₂ [ uncurry C ↓ pair×= p q ]
        → (b₁ , c₁) == (b₂ , c₂) [ (λ x → Σ B (C x)) ↓ p ]
      ↓-cst×app-in idp idp idp = idp

      module Part1 where

        to : ∀ {a₂} → TotalSpace (inital-cover a₂) → a₁ =₀ a₂
        to (_ , (p , _)) = p

        from : ∀ {a₂} → a₁ =₀ a₂ → TotalSpace (inital-cover a₂)
        from {a₂} p = cover-trace cov a↑₁ p , (p , idp)

        to-from : ∀ {a₂} (p : a₁ =₀ a₂) → to (from p) == p
        to-from p = idp

        from-to : ∀ {a₂} (a↑ : TotalSpace (inital-cover a₂)) → from (to a↑) == a↑
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

      part1 : ∀ a₂ → TotalSpace (inital-cover a₂) ≃ (a₁ =₀ a₂)
      part1 a₂ = let open Part1 in to , is-eq _ from to-from from-to
      
      module Part2 where

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

      part2 : ∀ a₂ → Fiber univ-cov a₂ ≃ (a₁ =₀ a₂)
      part2 a₂ = let open Part2 in to , is-eq _ from to-from from-to

    theorem : ∀ a₂ → TotalSpace (inital-cover a₂) ≃ Fiber univ-cov a₂
    theorem a₂ = (part2 a₂) ⁻¹ ∘e part1 a₂

