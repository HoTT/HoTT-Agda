{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.KernelSndImageInl {i j k}
  (G : Group i) {H : Group j} {K : Group k}
  -- the argument [φ-snd], which is intended to be [φ ∘ᴳ ×-snd],
  -- gives the possibility of making the second part
  -- (the proof of being a group homomorphism) abstract.
  (φ : H →ᴳ K) (φ-snd : G ×ᴳ H →ᴳ K)
  (φ-snd-β : ∀ x → GroupHom.f φ-snd x == GroupHom.f φ (snd x))
  (G×H-is-abelian : is-abelian (G ×ᴳ H))
  where

  open import groups.KernelImage
    φ-snd (×ᴳ-inl {G = G} {H = H}) G×H-is-abelian

  private
    module G = Group G
    module H = Group H

  Ker-φ-snd-quot-Im-inl : Ker φ ≃ᴳ Ker/Im
  Ker-φ-snd-quot-Im-inl = to-hom , is-eq to from to-from from-to where
    to : Ker.El φ → Ker/Im.El
    to (h , h-in-ker) = q[ (G.ident , h) , lemma ]
      where abstract lemma = φ-snd-β (G.ident , h) ∙ h-in-ker

    abstract
      to-pres-comp : ∀ k₁ k₂ → to (Ker.comp φ k₁ k₂) == Ker/Im.comp (to k₁) (to k₂)
      to-pres-comp _ _ = ap q[_] $ Ker.El=-out φ-snd $
        pair×= (! (G.unit-l G.ident)) idp

    to-hom : Ker φ →ᴳ Ker/Im
    to-hom = group-hom to to-pres-comp

    abstract
      from' : Ker.El φ-snd → Ker.El φ
      from' ((g , h) , h-in-ker) = h , ! (φ-snd-β (g , h)) ∙ h-in-ker

      from-rel : ∀ {gh₁ gh₂} → ker/im-rel gh₁ gh₂ → from' gh₁ == from' gh₂
      from-rel {gh₁} {gh₂} = Trunc-rec (Ker.El-is-set φ _ _)
        (λ{(g , inl-g=h₁h₂⁻¹) → Ker.El=-out φ
          (H.zero-diff-same (snd (fst gh₁)) (snd (fst gh₂)) (! (snd×= inl-g=h₁h₂⁻¹)))})

    from : Ker/Im.El → Ker.El φ
    from = SetQuot-rec (Ker.El-is-set φ) from' from-rel

    abstract
      to-from : ∀ g → to (from g) == g
      to-from = SetQuot-elim
        {P = λ g → to (from g) == g}
        (λ _ → =-preserves-set Ker/Im.El-is-set)
        (λ{((g , h) , h-in-ker) → quot-rel
          [ G.inv g , ap2 _,_ (! (G.unit-l (G.inv g))) (! (H.inv-r h)) ]})
        (λ _ → prop-has-all-paths-↓ (Ker/Im.El-is-set _ _))

      from-to : ∀ g → from (to g) == g
      from-to _ = Ker.El=-out φ idp
