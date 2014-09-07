{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver

{- Splitting Lemma - Right Split
   Assume an exact sequence:

             φ   ψ
       0 → G → H → K

   where H is abelian. If ψ has a right inverse χ, then H == G × K. Over
   this path φ becomes the natural injection and ψ the natural projection.

   The only non-private terms are [iso], [φ-over-iso], and [ψ-over-iso].
-}

module cohomology.SplitExactRight {i} {L G H K : Group i}
  (H-abelian : is-abelian H) (φ : GroupHom G H) (ψ : GroupHom H K) where

private
  module G = Group G
  module H = Group H
  module K = Group K
  module φ = GroupHom φ
  module ψ = GroupHom ψ

module SplitExactRight
  (ex : ExactSeq (L ⟨ cst-hom ⟩→ G ⟨ φ ⟩→ H ⟨ ψ ⟩→ K ⊣|))
  (χ : GroupHom K H) (χ-rinv : (k : K.El) → ψ.f (GroupHom.f χ k) == k)
  where

  private
    module χ = GroupHom χ

    {- H == Ker ψ × Im χ -}

    ker-part : GroupHom H (Ker ψ)
    ker-part = ker-hom ψ
      (comp-hom H-abelian (idhom H) (inv-hom H H-abelian ∘hom (χ ∘hom ψ)))
      (λ h →
        ψ.f (H.comp h (H.inv (χ.f (ψ.f h))))
          =⟨ ψ.pres-comp h (H.inv (χ.f (ψ.f h))) ⟩
        K.comp (ψ.f h) (ψ.f (H.inv (χ.f (ψ.f h))))
          =⟨ ! (χ.pres-inv (ψ.f h))
             |in-ctx (λ w → K.comp (ψ.f h) (ψ.f w)) ⟩
        K.comp (ψ.f h) (ψ.f (χ.f (K.inv (ψ.f h))))
          =⟨ χ-rinv (K.inv (ψ.f h)) |in-ctx (λ w → K.comp (ψ.f h) w) ⟩
        K.comp (ψ.f h) (K.inv (ψ.f h))
          =⟨ K.invr (ψ.f h) ⟩
        K.ident ∎)

    ker-part-kerψ : (h : H.El) (p : ψ.f h == K.ident)
      → GroupHom.f ker-part h == (h , p)
    ker-part-kerψ h p = pair=
      (H.comp h (H.inv (χ.f (ψ.f h)))
         =⟨ p |in-ctx (λ w → H.comp h (H.inv (χ.f w))) ⟩
       H.comp h (H.inv (χ.f K.ident))
         =⟨ χ.pres-ident |in-ctx (λ w → H.comp h (H.inv w)) ⟩
       H.comp h (H.inv H.ident)
         =⟨ group-inv-ident H |in-ctx H.comp h ⟩
       H.comp h H.ident
         =⟨ H.unitr h ⟩
       h ∎)
      (prop-has-all-paths-↓ (K.El-level _ _))

    ker-part-imχ : (h : H.El) → Trunc ⟨-1⟩ (Σ K.El (λ k → χ.f k == h))
      → GroupHom.f ker-part h == Group.ident (Ker ψ)
    ker-part-imχ h = Trunc-rec (Group.El-level (Ker ψ) _ _) $
      (λ {(k , p) → pair=
        (H.comp h (H.inv (χ.f (ψ.f h)))
           =⟨ ! p |in-ctx (λ w → H.comp w (H.inv (χ.f (ψ.f w)))) ⟩
         H.comp (χ.f k) (H.inv (χ.f (ψ.f (χ.f k))))
           =⟨ χ-rinv k |in-ctx (λ w → H.comp (χ.f k) (H.inv (χ.f w))) ⟩
         H.comp (χ.f k) (H.inv (χ.f k))
           =⟨ H.invr (χ.f k) ⟩
         H.ident ∎)
        (prop-has-all-paths-↓ (K.El-level _ _))})


    im-part : GroupHom H (Im χ)
    im-part = im-in-hom χ ∘hom ψ

    im-part-kerψ : (h : H.El) → ψ.f h == K.ident
      → GroupHom.f im-part h == Group.ident (Im χ)
    im-part-kerψ h p = pair=
      (ap χ.f p ∙ χ.pres-ident)
      (prop-has-all-paths-↓ Trunc-level)

    im-part-imχ : (h : H.El) (s : Trunc ⟨-1⟩ (Σ K.El (λ k → χ.f k == h)))
      → GroupHom.f im-part h == (h , s)
    im-part-imχ h s = pair=
      (Trunc-rec (Group.El-level H _ _)
        (λ {(k , p) →
          χ.f (ψ.f h)        =⟨ ! p |in-ctx (χ.f ∘ ψ.f) ⟩
          χ.f (ψ.f (χ.f k))  =⟨ χ-rinv k |in-ctx χ.f ⟩
          χ.f k              =⟨ p ⟩
          h ∎})
        s)
      (prop-has-all-paths-↓ Trunc-level)

    decomp : GroupHom H (Ker ψ ×G Im χ)
    decomp = ×-hom ker-part im-part

    decomp-is-equiv : is-equiv (GroupHom.f decomp)
    decomp-is-equiv = is-eq _ dinv decomp-dinv dinv-decomp
      where
      dinv : Group.El (Ker ψ ×G Im χ) → H.El
      dinv ((h₁ , _) , (h₂ , _)) = H.comp h₁ h₂

      decomp-dinv : ∀ s → GroupHom.f decomp (dinv s) == s
      decomp-dinv ((h₁ , kr) , (h₂ , im)) = pair×=
        (GroupHom.f ker-part (H.comp h₁ h₂)
           =⟨ GroupHom.pres-comp ker-part h₁ h₂ ⟩
         Group.comp (Ker ψ) (GroupHom.f ker-part h₁) (GroupHom.f ker-part h₂)
           =⟨ ker-part-kerψ h₁ kr
              |in-ctx (λ w → Group.comp (Ker ψ) w (GroupHom.f ker-part h₂)) ⟩
         Group.comp (Ker ψ) (h₁ , kr) (GroupHom.f ker-part h₂)
           =⟨ ker-part-imχ h₂ im
              |in-ctx (λ w → Group.comp (Ker ψ) (h₁ , kr) w) ⟩
         Group.comp (Ker ψ) (h₁ , kr) (Group.ident (Ker ψ))
           =⟨ Group.unitr (Ker ψ) (h₁ , kr) ⟩
         (h₁ , kr) ∎)
        (GroupHom.f im-part (H.comp h₁ h₂)
           =⟨ GroupHom.pres-comp im-part h₁ h₂ ⟩
         Group.comp (Im χ) (GroupHom.f im-part h₁) (GroupHom.f im-part h₂)
           =⟨ im-part-kerψ h₁ kr
              |in-ctx (λ w → Group.comp (Im χ) w (GroupHom.f im-part h₂)) ⟩
         Group.comp (Im χ) (Group.ident (Im χ)) (GroupHom.f im-part h₂)
           =⟨ im-part-imχ h₂ im
              |in-ctx (λ w → Group.comp (Im χ) (Group.ident (Im χ)) w) ⟩
         Group.comp (Im χ) (Group.ident (Im χ)) (h₂ , im)
           =⟨ Group.unitl (Im χ) (h₂ , im) ⟩
         (h₂ , im) ∎)

      dinv-decomp : ∀ h → dinv (GroupHom.f decomp h) == h
      dinv-decomp h =
        H.comp (H.comp h (H.inv (χ.f (ψ.f h)))) (χ.f (ψ.f h))
          =⟨ H.assoc h (H.inv (χ.f (ψ.f h))) (χ.f (ψ.f h)) ⟩
        H.comp h (H.comp (H.inv (χ.f (ψ.f h))) (χ.f (ψ.f h)))
          =⟨ H.invl (χ.f (ψ.f h)) |in-ctx H.comp h ⟩
        H.comp h H.ident
          =⟨ H.unitr h ⟩
        h ∎

    decomp-equiv : H.El ≃ Group.El (Ker ψ ×G Im χ)
    decomp-equiv = (_ , decomp-is-equiv)

    decomp-iso : H == Ker ψ ×G Im χ
    decomp-iso = group-iso decomp decomp-is-equiv

    {- G == Ker ψ -}

    ker-in-φ : GroupHom G (Ker ψ)
    ker-in-φ = ker-hom ψ φ (λ g → itok (exact-get ex 1) (φ.f g) [ g , idp ])

    ker-in-φ-is-equiv : is-equiv (GroupHom.f ker-in-φ)
    ker-in-φ-is-equiv = surj-inj-is-equiv ker-in-φ inj surj
      where
      inj = zero-kernel-injective ker-in-φ
        (λ g p → Trunc-rec (G.El-level _ _)
          (λ {(_ , q) → ! q}) (ktoi (exact-get ex 0) g (ap fst p)))

      surj = λ {(h , p) → Trunc-fmap
        (λ {(g , q) → (g , pair= q (prop-has-all-paths-↓ (K.El-level _ _)))})
        (ktoi (exact-get ex 1) h p)}

    G-iso-Kerψ : G == Ker ψ
    G-iso-Kerψ = group-iso ker-in-φ ker-in-φ-is-equiv

    {- K == Im χ -}

    im-in-χ-is-equiv : is-equiv (GroupHom.f (im-in-hom χ))
    im-in-χ-is-equiv = surj-inj-is-equiv (im-in-hom χ) inj (im-in-surj χ)
      where
      inj = zero-kernel-injective (im-in-hom χ)
        (λ k p → ! (χ-rinv k) ∙ ap ψ.f (ap fst p) ∙ ψ.pres-ident)

    K-iso-Imχ : K == Im χ
    K-iso-Imχ = group-iso (im-in-hom χ) im-in-χ-is-equiv

  {- H == G ×G K -}

  iso : H == G ×G K
  iso = decomp-iso ∙ ap2 _×G_ (! G-iso-Kerψ) (! K-iso-Imχ)

  private

    decomp-φ = ×-hom ker-in-φ (cst-hom {G = G} {H = Im χ})
    ψ-dinv = ψ ∘hom ×-sum-hom H-abelian (ker-inj ψ) (im-inj χ)

    φ-over-decomp : φ == decomp-φ [ (λ J → GroupHom G J) ↓ decomp-iso ]
    φ-over-decomp = codomain-over-iso _ _ _ _ $
                      codomain-over-equiv φ.f _ ▹ lemma
      where
      lemma : GroupHom.f decomp ∘ φ.f == GroupHom.f decomp-φ
      lemma = λ= (λ g → pair×=
        (ker-part-kerψ (φ.f g) (itok (exact-get ex 1) (φ.f g) [ g , idp ]))
        (im-part-kerψ (φ.f g) (itok (exact-get ex 1) (φ.f g) [ g , idp ])))

    ψ-over-decomp : ψ == ψ-dinv [ (λ J → GroupHom J K) ↓ decomp-iso ]
    ψ-over-decomp = domain-over-iso _ _ _ _  $ domain!-over-equiv ψ.f _

    id-over-G-iso : idhom _ == ker-in-φ [ (λ J → GroupHom G J) ↓ G-iso-Kerψ ]
    id-over-G-iso = codomain-over-iso _ _ _ _ $
                      codomain-over-equiv (idf _) _

    φ-over-G-iso : φ == ker-inj ψ [ (λ J → GroupHom J H) ↓ G-iso-Kerψ ]
    φ-over-G-iso = domain-over-iso _ _ _ _ $
                     domain-over-equiv (GroupHom.f (ker-inj ψ)) _

    ψ|imχ-over-K-iso : idhom K == ψ ∘hom im-inj χ
      [ (λ J → GroupHom J K) ↓ K-iso-Imχ ]
    ψ|imχ-over-K-iso = domain-over-iso _ _ _ _ $
                         domain!-over-equiv (idf _) _ ▹ lemma
      where
      lemma : <– (_ , im-in-χ-is-equiv) == ψ.f ∘ GroupHom.f (im-inj χ)
      lemma = λ= (λ {(h , s) →
        Trunc-elim {P = λ s' → <– (_ , im-in-χ-is-equiv) (h , s') == ψ.f h}
          (λ _ → K.El-level _ _) (λ {(k , p) → ! (χ-rinv k) ∙ ap ψ.f p}) s})

    φ-over-G-K-isos : decomp-φ == ×G-inl
      [ (λ J → GroupHom G J) ↓ ap2 _×G_ (! G-iso-Kerψ) (! K-iso-Imχ) ]
    φ-over-G-K-isos = ↓-ap2-in _ _×G_ $ transport
      (λ q → decomp-φ == ×G-inl [ (GroupHom G ∘ uncurry _×G_) ↓ q ])
      (! (pair×=-split-l (! G-iso-Kerψ) (! K-iso-Imχ)))
      (l ∙ᵈ r)
      where
      l : decomp-φ == ×-hom (idhom G) (cst-hom {G = G} {H = Im χ})
        [ (λ {(J₁ , J₂) → GroupHom G (J₁ ×G J₂)})
          ↓ ap (λ J → J , Im χ) (! G-iso-Kerψ) ]
      l = ↓-ap-in _ (λ J → J , Im χ)
            (ap↓ (λ θ → ×-hom θ (cst-hom {G = G} {H = Im χ}))
              (!ᵈ id-over-G-iso))

      r : ×-hom (idhom G) (cst-hom {H = Im χ}) == ×G-inl
        [ (λ {(J₁ , J₂) → GroupHom G (J₁ ×G J₂)})
          ↓ ap (λ J → G , J) (! K-iso-Imχ) ]
      r = ↓-ap-in _ (λ J → G , J)
            (apd (λ J → ×-hom (idhom G)
              (cst-hom {G = G} {H = J})) (! K-iso-Imχ))

    ψ-over-G-K-isos : ψ-dinv == ×G-snd {G = G}
      [ (λ J → GroupHom J K) ↓ ap2 _×G_ (! G-iso-Kerψ) (! K-iso-Imχ) ]
    ψ-over-G-K-isos = ↓-ap2-in _ _×G_ $ transport
      (λ q → ψ-dinv == (×G-snd {G = G})
        [ (λ {(J₁ , J₂) → GroupHom (J₁ ×G J₂) K}) ↓ q ])
      (! (pair×=-split-l (! G-iso-Kerψ) (! K-iso-Imχ)))
      (l ∙ᵈ (m ◃ r))
      where
      l : ψ-dinv == ψ ∘hom ×-sum-hom H-abelian φ (im-inj χ)
          [ (λ {(J₁ , J₂) → GroupHom (J₁ ×G J₂) K})
            ↓ ap (λ J → J , Im χ) (! G-iso-Kerψ) ]
      l = ↓-ap-in _ (λ J → J , Im χ)
        (ap↓ (λ θ → ψ ∘hom ×-sum-hom H-abelian θ (im-inj χ))
          (!ᵈ φ-over-G-iso))

      m : ψ ∘hom ×-sum-hom H-abelian φ (im-inj χ)
          == (ψ ∘hom im-inj χ) ∘hom ×G-snd {G = G}
      m = hom= _ _ $ λ= $ (λ {(g , (h , _)) →
        ψ.f (H.comp (φ.f g) h)
          =⟨ ψ.pres-comp (φ.f g) h ⟩
        K.comp (ψ.f (φ.f g)) (ψ.f h)
          =⟨ itok (exact-get ex 1) (φ.f g) [ g , idp ]
             |in-ctx (λ w → K.comp w (ψ.f h))  ⟩
        K.comp K.ident (ψ.f h)
          =⟨ K.unitl (ψ.f h) ⟩
        ψ.f h ∎})

      r : (ψ ∘hom im-inj χ) ∘hom ×G-snd {G = G} == ×G-snd {G = G}
          [ (λ {(J₁ , J₂) → GroupHom (J₁ ×G J₂) K})
            ↓ (ap (λ J → G , J) (! K-iso-Imχ)) ]
      r = ↓-ap-in _ (λ J → G , J)
            (ap↓ (λ θ → θ ∘hom ×G-snd {G = G}) (!ᵈ ψ|imχ-over-K-iso))

  φ-over-iso : φ == ×G-inl [ (λ J → GroupHom G J) ↓ iso ]
  φ-over-iso = φ-over-decomp ∙ᵈ φ-over-G-K-isos

  ψ-over-iso : ψ == (×G-snd {G = G}) [ (λ J → GroupHom J K) ↓ iso ]
  ψ-over-iso = ψ-over-decomp ∙ᵈ ψ-over-G-K-isos
