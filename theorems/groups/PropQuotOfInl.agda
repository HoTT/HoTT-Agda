{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.PropQuotOfInl {i j k}
  (G : Group i) {H : Group j} {K : Group k}
  (G-×-H-is-abelian : is-abelian (G ×ᴳ H)) (φ : H →ᴳ K) where

  private
    module G = Group G
    module H = Group H

    φ-snd : G ×ᴳ H →ᴳ K
    φ-snd = φ ∘ᴳ ×ᴳ-snd {G = G} {H = H}

  module Ker/Im = QuotGroup
    (quot-of-sub
      (ker-propᴳ φ-snd)
      (im-npropᴳ (×ᴳ-inl {G = G} {H = H}) G-×-H-is-abelian))

  Ker-inl-quot-Im-φ-snd : Ker.grp φ ≃ᴳ Ker/Im.grp
  Ker-inl-quot-Im-φ-snd = to-hom , is-eq _ from to-from from-to where
    to : Ker.El φ → Ker/Im.El
    to (h , h-in-ker) = q[ (G.ident , h) , h-in-ker ]

    abstract
      to-pres-comp : ∀ k₁ k₂ → to (Ker.comp φ k₁ k₂) == Ker/Im.comp (to k₁) (to k₂)
      to-pres-comp _ _ = ap q[_] $ Subtype=-out (Ker.subEl-prop φ-snd) $
        pair×= (! (G.unit-l G.ident)) idp

    to-hom : Ker.grp φ →ᴳ Ker/Im.grp
    to-hom = group-hom to to-pres-comp

    abstract
      from' : Ker.El φ-snd → Ker.El φ
      from' ((g , h) , h-in-ker) = h , h-in-ker

      from-rel : {gh₁ gh₂ : Ker.El φ-snd}
        (inl-g=gh₁gh₂⁻¹ : SubgroupProp.prop (im-propᴳ (×ᴳ-inl {G = G} {H = H})) (fst (Ker.diff φ-snd gh₁ gh₂)))
        → from' gh₁ == from' gh₂
      from-rel {gh₁} {gh₂} = Trunc-rec (Ker.El-is-set φ _ _)
        (λ{(g , inl-g=h₁h₂⁻¹) → Subtype=-out (Ker.subEl-prop φ)
          (H.zero-diff-same (snd (fst gh₁)) (snd (fst gh₂)) (! (snd×= inl-g=h₁h₂⁻¹)))})

    from : Ker/Im.El → Ker.El φ
    from = SetQuot-rec (Ker.El-is-set φ) from' from-rel

    abstract
      to-from : ∀ g → to (from g) == g
      to-from = SetQuot-elim
        {P = λ g → to (from g) == g}
        (λ _ → =-preserves-set Ker/Im.El-is-set)
        (λ{((g , h) , h-in-ker) → quot-relᴳ {P = Ker/Im.npropᴳ}
          {g₁ = (G.ident , h) , h-in-ker} {g₂ = (g , h) , h-in-ker}
          [ G.inv g , ap2 _,_ (! (G.unit-l (G.inv g))) (! (H.inv-r h)) ]})
        (λ _ → prop-has-all-paths-↓ (Ker/Im.El-is-set _ _))

      from-to : ∀ g → from (to g) == g
      from-to _ = idp
