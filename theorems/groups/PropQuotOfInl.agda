{-# OPTIONS --without-K #-}

open import HoTT

module groups.PropQuotOfInl {i j k}
  (G : Group i) {H : Group j} {K : Group k}
  (G-×-H-is-abelian : is-abelian (G ×ᴳ H)) (φ : H →ᴳ K) where

  private
    module G = Group G
    module H = Group H

    φ-snd : G ×ᴳ H →ᴳ K
    φ-snd = φ ∘ᴳ ×ᴳ-snd {G = G} {H = H}

  module CokerInl = Coker G-×-H-is-abelian (×ᴳ-inl {G = G} {H = H})

  Ker-inl-quot-Im-φ-snd :
    Ker.grp φ ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ φ-snd) CokerInl.npropᴳ)
  Ker-inl-quot-Im-φ-snd = to-hom , is-eq _ from to-from from-to where
    module Ker/Im = QuotGroup (quot-of-sub (ker-propᴳ φ-snd) CokerInl.npropᴳ)

    to-hom : Ker.grp φ →ᴳ Ker/Im.grp
    to-hom = group-hom (λ{(h , h-in-ker) → q[ (G.ident , h) , h-in-ker ]})
      (λ _ _ → ap q[_] $ Subtype=-out (Ker.subEl-prop φ-snd) (pair×= (! (G.unit-l G.ident)) idp))

    to : Ker.El φ → Ker/Im.El
    to = GroupHom.f to-hom

    from : Ker/Im.El → Ker.El φ
    from = SetQuot-rec (Ker.El-is-set φ)
      (λ{((g , h) , h-in-ker) → (h , h-in-ker)})
      (λ {gh₁} {gh₂} → Trunc-rec (Ker.El-is-set φ _ _)
        (λ{(g , inl-g=h₁h₂⁻¹) → Subtype=-out
          (Ker.subEl-prop φ) (H.zero-diff-same (snd (fst gh₁)) (snd (fst gh₂)) (! (snd×= inl-g=h₁h₂⁻¹)))}))

    abstract
      to-from : ∀ g → to (from g) == g
      to-from = SetQuot-elim (λ _ → =-preserves-set Ker/Im.El-is-set)
        (λ{((g , h) , h-in-ker) → quot-relᴳ {P = Ker/Im.npropᴳ}
          {g₁ = (G.ident , h) , h-in-ker} {g₂ = (g , h) , h-in-ker}
          [ G.inv g , ap2 _,_ (! (G.unit-l (G.inv g))) (! (H.inv-r h)) ]})
        (λ _ → prop-has-all-paths-↓ (Ker/Im.El-is-set _ _))

      from-to : ∀ g → from (to g) == g
      from-to _ = idp
