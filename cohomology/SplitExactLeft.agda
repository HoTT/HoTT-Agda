{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver

{- Splitting Lemma - Left Split
   Assume an exact sequence:

             φ   ψ
           G → H → K → 0

   where H is abelian. If φ has a left inverse χ, then H == G × K. Over
   this path φ becomes the natural injection and ψ the natural projection.

   The only non-private terms are [iso], [φ-over-iso], and [ψ-over-iso].
-}

module cohomology.SplitExactLeft {i} {G H K : Group i}
  (H-abelian : is-abelian H) (φ : GroupHom G H) (ψ : GroupHom H K) where

private
  module G = Group G
  module H = Group H
  module K = Group K
  module φ = GroupHom φ
  module ψ = GroupHom ψ

module SplitExactLeft
  (ex : ExactSeq (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ K ⟨ cst-hom ⟩→ 0G ⊣|))
  (χ : GroupHom H G) (χ-linv : (g : G.El) → GroupHom.f χ (φ.f g) == g)
  where

  private
    module χ = GroupHom χ

    {- H == Im φ ×G Ker χ -}

    im-part : GroupHom H (Im φ)
    im-part = im-in-hom φ ∘hom χ

    im-part-imφ : (h : H.El) (s : Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h)))
      → GroupHom.f im-part h == (h , s)
    im-part-imφ h s = pair=
      (Trunc-rec (Group.El-level H _ _)
        (λ {(g , p) →
          φ.f (χ.f h)        =⟨ ap (φ.f ∘ χ.f) (! p) ⟩
          φ.f (χ.f (φ.f g))  =⟨ ap φ.f (χ-linv g) ⟩
          φ.f g              =⟨ p ⟩
          h ∎})
        s)
      (prop-has-all-paths-↓ Trunc-level)

    im-part-kerχ :  (h : H.El) (p : χ.f h == G.ident)
      → GroupHom.f im-part h == Group.ident (Im φ)
    im-part-kerχ h p = pair=
      (ap φ.f p ∙ φ.pres-ident)
      (prop-has-all-paths-↓ Trunc-level)


    ker-part : GroupHom H (Ker χ)
    ker-part = ker-hom χ
      (comp-hom H-abelian (idhom H) (inv-hom H H-abelian ∘hom (φ ∘hom χ)))
      (λ h →
        χ.f (H.comp h (H.inv (φ.f (χ.f h))))
          =⟨ χ.pres-comp h (H.inv (φ.f (χ.f h))) ⟩
        G.comp (χ.f h) (χ.f (H.inv (φ.f (χ.f h))))
          =⟨ ! (φ.pres-inv (χ.f h))
             |in-ctx (λ w → G.comp (χ.f h) (χ.f w)) ⟩
        G.comp (χ.f h) (χ.f (φ.f (G.inv (χ.f h))))
          =⟨ χ-linv (G.inv (χ.f h)) |in-ctx (λ w → G.comp (χ.f h) w) ⟩
        G.comp (χ.f h) (G.inv (χ.f h))
          =⟨ G.invr (χ.f h) ⟩
        G.ident ∎)

    ker-part-imφ : (h : H.El) → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h))
      → GroupHom.f ker-part h == Group.ident (Ker χ)
    ker-part-imφ h = Trunc-rec (Group.El-level (Ker χ) _ _) $
      λ {(g , p) → pair=
       (H.comp h (H.inv (φ.f (χ.f h)))
          =⟨ ! p |in-ctx (λ w → H.comp w (H.inv (φ.f (χ.f w)))) ⟩
        H.comp (φ.f g) (H.inv (φ.f (χ.f (φ.f g))))
          =⟨ χ-linv g |in-ctx (λ w → H.comp (φ.f g) (H.inv (φ.f w))) ⟩
        H.comp (φ.f g) (H.inv (φ.f g))
          =⟨ H.invr (φ.f g) ⟩
        H.ident ∎)
       (prop-has-all-paths-↓ (Group.El-level G _ _))}

    ker-part-kerχ : (h : H.El) (p : χ.f h == G.ident)
      → GroupHom.f ker-part h == (h , p)
    ker-part-kerχ h p = pair=
      (H.comp h (H.inv (φ.f (χ.f h)))
         =⟨ p |in-ctx (λ w → H.comp h (H.inv (φ.f w))) ⟩
       H.comp h (H.inv (φ.f G.ident))
         =⟨ φ.pres-ident |in-ctx (λ w → H.comp h (H.inv w)) ⟩
       H.comp h (H.inv H.ident)
         =⟨ group-inv-ident H |in-ctx H.comp h ⟩
       H.comp h H.ident
         =⟨ H.unitr h ⟩
       h ∎)
      (prop-has-all-paths-↓ (Group.El-level G _ _))


    decomp : GroupHom H (Im φ ×G Ker χ)
    decomp = ×-hom im-part ker-part

    decomp-is-equiv : is-equiv (GroupHom.f decomp)
    decomp-is-equiv = is-eq _ dinv decomp-dinv dinv-decomp
      where
      dinv : Group.El (Im φ ×G Ker χ) → H.El
      dinv ((h₁ , _) , (h₂ , _)) = H.comp h₁ h₂

      decomp-dinv : ∀ s → GroupHom.f decomp (dinv s) == s
      decomp-dinv ((h₁ , im) , (h₂ , kr)) = pair×=
        (GroupHom.f im-part (H.comp h₁ h₂)
           =⟨ GroupHom.pres-comp im-part h₁ h₂ ⟩
         Group.comp (Im φ) (GroupHom.f im-part h₁) (GroupHom.f im-part h₂)
           =⟨ im-part-imφ h₁ im
              |in-ctx (λ w → Group.comp (Im φ) w (GroupHom.f im-part h₂)) ⟩
         Group.comp (Im φ) (h₁ , im) (GroupHom.f im-part h₂)
           =⟨ im-part-kerχ h₂ kr
              |in-ctx (λ w → Group.comp (Im φ) (h₁ , im) w) ⟩
         Group.comp (Im φ) (h₁ , im) (Group.ident (Im φ))
           =⟨ Group.unitr (Im φ) (h₁ , im) ⟩
         (h₁ , im) ∎)
        (GroupHom.f ker-part (H.comp h₁ h₂)
           =⟨ GroupHom.pres-comp ker-part h₁ h₂ ⟩
         Group.comp (Ker χ) (GroupHom.f ker-part h₁) (GroupHom.f ker-part h₂)
           =⟨ ker-part-imφ h₁ im
              |in-ctx (λ w → Group.comp (Ker χ) w (GroupHom.f ker-part h₂)) ⟩
         Group.comp (Ker χ) (Group.ident (Ker χ)) (GroupHom.f ker-part h₂)
           =⟨ ker-part-kerχ h₂ kr
              |in-ctx (λ w → Group.comp (Ker χ) (Group.ident (Ker χ)) w) ⟩
         Group.comp (Ker χ) (Group.ident (Ker χ)) (h₂ , kr)
           =⟨ Group.unitl (Ker χ) (h₂ , kr) ⟩
         (h₂ , kr) ∎)

      dinv-decomp : ∀ h → dinv (GroupHom.f decomp h) == h
      dinv-decomp h =
        H.comp (φ.f (χ.f h)) (H.comp h (H.inv (φ.f (χ.f h))))
          =⟨ H-abelian (φ.f (χ.f h)) (H.comp h (H.inv (φ.f (χ.f h)))) ⟩
        H.comp (H.comp h (H.inv (φ.f (χ.f h)))) (φ.f (χ.f h))
          =⟨ H.assoc h (H.inv (φ.f (χ.f h))) (φ.f (χ.f h)) ⟩
        H.comp h (H.comp (H.inv (φ.f (χ.f h))) (φ.f (χ.f h)))
          =⟨ H.invl (φ.f (χ.f h)) |in-ctx (λ w → H.comp h w)  ⟩
        H.comp h H.ident
          =⟨ H.unitr h ⟩
        h ∎

    decomp-equiv : H.El ≃ Group.El (Im φ ×G Ker χ)
    decomp-equiv = (_ , decomp-is-equiv)

    decomp-iso : H == Im φ ×G Ker χ
    decomp-iso = group-iso decomp decomp-is-equiv

    {- K == Ker χ -}

    ψ|kerχ-inj : (h : Group.El (Ker χ))
      → ψ.f (GroupHom.f (ker-inj χ) h) == K.ident → h == Group.ident (Ker χ)
    ψ|kerχ-inj (h , p) q = pair=
      (Trunc-rec (H.El-level _ _)
        (λ {(g , r) →
          ! r ∙ ap φ.f (! (χ-linv g) ∙ ap χ.f r ∙ p) ∙ φ.pres-ident})
        (ktoi (exact-get ex 0) h q))
      (prop-has-all-paths-↓ (G.El-level _ _))

    ψ|kerχ-surj : (k : K.El)
      → Trunc ⟨-1⟩ (Σ (Group.El (Ker χ))
                      (λ h → ψ.f (GroupHom.f (ker-inj χ) h) == k))
    ψ|kerχ-surj k = Trunc-fmap
      (λ {(h , p) → (GroupHom.f ker-part h ,
         ψ.f (H.comp h (H.inv (φ.f (χ.f h))))
           =⟨ ψ.pres-comp h (H.inv (φ.f (χ.f h))) ⟩
         K.comp (ψ.f h) (ψ.f (H.inv (φ.f (χ.f h))))
           =⟨ ψ.pres-inv (φ.f (χ.f h))
              |in-ctx (λ k → K.comp (ψ.f h) k) ⟩
         K.comp (ψ.f h) (K.inv (ψ.f (φ.f (χ.f h))))
           =⟨ itok (exact-get ex 0) (φ.f (χ.f h)) [ χ.f h , idp ]
              |in-ctx (λ k → K.comp (ψ.f h) (K.inv k)) ⟩
         K.comp (ψ.f h) (K.inv K.ident)
           =⟨ group-inv-ident K |in-ctx (λ k → K.comp (ψ.f h) k) ⟩
         K.comp (ψ.f h) K.ident
           =⟨ K.unitr (ψ.f h) ⟩
         ψ.f h
           =⟨ p ⟩
         k ∎)})
      (ktoi (exact-get ex 1) k idp)

    ψ|kerχ-is-equiv : is-equiv (GroupHom.f (ψ ∘hom (ker-inj χ)))
    ψ|kerχ-is-equiv = surj-inj-is-equiv (ψ ∘hom (ker-inj χ))
      (zero-kernel-injective (ψ ∘hom (ker-inj χ)) ψ|kerχ-inj)
      ψ|kerχ-surj

    Kerχ-iso-K : Ker χ == K
    Kerχ-iso-K = group-iso (ψ ∘hom (ker-inj χ)) ψ|kerχ-is-equiv

    {- G == Im φ -}

    im-in-φ-is-equiv : is-equiv (GroupHom.f (im-in-hom φ))
    im-in-φ-is-equiv = surj-inj-is-equiv (im-in-hom φ) inj (im-in-surj φ)
      where
      inj = zero-kernel-injective (im-in-hom φ)
        (λ g p → ! (χ-linv g) ∙ ap (χ.f ∘ fst) p ∙ χ.pres-ident)

    G-iso-Imφ : G == Im φ
    G-iso-Imφ = group-iso (im-in-hom φ) im-in-φ-is-equiv

  {- H == G ×G K -}

  iso : H == G ×G K
  iso = decomp-iso ∙ ap2 _×G_ (! G-iso-Imφ) Kerχ-iso-K

  private
    decomp-φ = ×-hom (im-in-hom φ) (cst-hom {G = G} {H = Ker χ})

    φ-over-decomp : φ == decomp-φ [ (λ J → GroupHom G J) ↓ decomp-iso ]
    φ-over-decomp = codomain-over-iso _ _ _ _ $
                      codomain-over-equiv φ.f _ ▹ lemma
      where
      lemma : GroupHom.f decomp ∘ φ.f == GroupHom.f decomp-φ
      lemma = λ= $ λ g → pair×=
        (im-part-imφ (φ.f g) [ g , idp ])
        (ker-part-imφ (φ.f g) [ g , idp ])

    ψ-dinv : GroupHom (Im φ ×G Ker χ) K
    ψ-dinv = ψ ∘hom ×-sum-hom H-abelian (im-inj φ) (ker-inj χ)

    ψ-over-decomp : ψ == ψ-dinv [ (λ J → GroupHom J K) ↓ decomp-iso ]
    ψ-over-decomp = domain-over-iso _ _ _ _ $ domain!-over-equiv ψ.f _

    id-over-G-iso : idhom _ == im-in-hom φ [ (λ J → GroupHom G J) ↓ G-iso-Imφ ]
    id-over-G-iso = codomain-over-iso _ _ _ _ $ codomain-over-equiv (idf _) _

    φ-over-G-iso : φ == im-inj φ [ (λ J → GroupHom J H) ↓ G-iso-Imφ ]
    φ-over-G-iso = domain-over-iso _ _ _ _ $
                     domain-over-equiv (GroupHom.f (im-inj φ)) _

    ψ|kerχ-over-K-iso :
      ψ ∘hom ker-inj χ == idhom K [ (λ J → GroupHom J K) ↓ Kerχ-iso-K ]
    ψ|kerχ-over-K-iso = domain-over-iso _ _ _ _ $ domain-over-equiv (idf _) _

    φ-over-G-K-isos : decomp-φ == ×G-inl
      [ (λ J → GroupHom G J) ↓ ap2 _×G_ (! G-iso-Imφ) Kerχ-iso-K ]
    φ-over-G-K-isos = ↓-ap2-in _ _×G_ $ transport
      (λ q → decomp-φ == ×G-inl [ (GroupHom G ∘ uncurry _×G_) ↓ q ])
      (! (pair×=-split-l (! G-iso-Imφ) (Kerχ-iso-K)))
      (l ∙ᵈ r)
      where
      l : decomp-φ == ×-hom (idhom G) (cst-hom {G = G} {H = Ker χ})
          [ (λ {(J₁ , J₂) → GroupHom G (J₁ ×G J₂)})
            ↓ ap (λ J → J , Ker χ) (! G-iso-Imφ) ]
      l = ↓-ap-in _ (λ J → J , Ker χ)
            (ap↓ (λ θ → ×-hom θ (cst-hom {G = G} {H = Ker χ}))
              (!ᵈ id-over-G-iso))

      r : ×-hom (idhom G) (cst-hom {G = G} {H = Ker χ}) == ×G-inl
          [ (λ {(J₁ , J₂) → GroupHom G (J₁ ×G J₂)})
            ↓ ap (λ J → G , J) Kerχ-iso-K ]
      r = ↓-ap-in _ (λ J → G , J)
            (apd (λ J → ×-hom (idhom G) (cst-hom {G = G} {H = J}))
              Kerχ-iso-K)

    ψ-over-G-K-isos : ψ-dinv == (×G-snd {G = G})
      [ (λ J → GroupHom J K) ↓ ap2 _×G_ (! G-iso-Imφ) Kerχ-iso-K ]
    ψ-over-G-K-isos = ↓-ap2-in _ _×G_ $ transport
      (λ q → ψ-dinv == (×G-snd {G = G})
        [ (λ {(J₁ , J₂) → GroupHom (J₁ ×G J₂) K}) ↓ q ])
      (! (pair×=-split-l (! G-iso-Imφ) (Kerχ-iso-K)))
      (l ∙ᵈ (m ◃ r))
      where
      l : ψ-dinv == ψ ∘hom ×-sum-hom H-abelian φ (ker-inj χ)
          [ (λ {(J₁ , J₂) → GroupHom (J₁ ×G J₂) K})
            ↓ ap (λ J → J , Ker χ) (! G-iso-Imφ) ]
      l = ↓-ap-in _ (λ J → J , Ker χ)
        (ap↓ (λ θ → ψ ∘hom ×-sum-hom H-abelian θ (ker-inj χ))
          (!ᵈ φ-over-G-iso))

      m : ψ ∘hom ×-sum-hom H-abelian φ (ker-inj χ)
        == (ψ ∘hom (ker-inj χ)) ∘hom (×G-snd {G = G})
      m = hom= _ _ (λ= (λ {(g , (h , _)) →
        ψ.f (H.comp (φ.f g) h)
          =⟨ ψ.pres-comp (φ.f g) h ⟩
        K.comp (ψ.f (φ.f g)) (ψ.f h)
          =⟨ itok (exact-get ex 0) (φ.f g) [ g , idp ]
             |in-ctx (λ k → K.comp k (ψ.f h)) ⟩
        K.comp K.ident (ψ.f h)
          =⟨ K.unitl (ψ.f h) ⟩
        ψ.f h ∎}))

      r : (ψ ∘hom (ker-inj χ)) ∘hom (×G-snd {G = G}) == (×G-snd {G = G})
          [ (λ {(J₁ , J₂) → GroupHom (J₁ ×G J₂) K})
            ↓ (ap (λ J → G , J) Kerχ-iso-K) ]
      r = ↓-ap-in _ (λ J → G , J)
            (ap↓ (λ θ → θ ∘hom ×G-snd {G = G}) ψ|kerχ-over-K-iso)

  φ-over-iso : φ == ×G-inl [ (λ J → GroupHom G J) ↓ iso ]
  φ-over-iso = φ-over-decomp ∙ᵈ φ-over-G-K-isos

  ψ-over-iso : ψ == (×G-snd {G = G}) [ (λ J → GroupHom J K) ↓ iso ]
  ψ-over-iso = ψ-over-decomp ∙ᵈ ψ-over-G-K-isos
