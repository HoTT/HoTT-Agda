{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.ProductRepr {i j}
  {G : Group (lmax i j)} {H₁ : Group i} {H₂ : Group j}
  (i₁ : H₁ →ᴳ G) (i₂ : H₂ →ᴳ G) (j₁ : G →ᴳ H₁) (j₂ : G →ᴳ H₂)
  (p₁ : ∀ h₁ → GroupHom.f j₁ (GroupHom.f i₁ h₁) == h₁)
  (p₂ : ∀ h₂ → GroupHom.f j₂ (GroupHom.f i₂ h₂) == h₂)
  (ex₁ : is-exact i₁ j₂) (ex₂ : is-exact i₂ j₁) where

  {- Given the following commutative diagram of homomorphisms,

         H₁  i₁  i₂  H₂
            ↘     ↙
      id ↓     G     ↓ id
             ↙   ↘
         H₁ j₁   j₂  H₂

   - assuming i₁,j₂ and i₂,j₁ are exact sequences,
   - there exists an isomorphism G == H₁ × H₂ such that i₁,i₂ correspond
   - to the natural injections and j₁,j₂ correspond to the natural
   - projections. -}

  private
    module G = Group G
    module H₁ = Group H₁
    module H₂ = Group H₂
    module i₁ = GroupHom i₁
    module i₂ = GroupHom i₂
    module j₁ = GroupHom j₁
    module j₂ = GroupHom j₂

  fanout-has-trivial-ker : has-trivial-kerᴳ (×ᴳ-fanout j₁ j₂)
  fanout-has-trivial-ker g q = Trunc-rec (G.El-level _ _)
      (lemma g (fst×= q))
      (ker-sub-im ex₁ g (snd×= q))
    where
    lemma : ∀ g → j₁.f g == H₁.ident
      → hfiber i₁.f g → g == G.ident
    lemma ._ r (h , idp) =
      ap i₁.f (! (p₁ h) ∙ r) ∙ i₁.pres-ident

  β₁ : (h₁ : H₁.El) (h₂ : H₂.El)
    → j₁.f (G.comp (i₁.f h₁) (i₂.f h₂)) == h₁
  β₁ h₁ h₂ =
    j₁.pres-comp (i₁.f h₁) (i₂.f h₂)
    ∙ ap2 H₁.comp (p₁ h₁) (im-sub-ker ex₂ _ [ h₂ , idp ])
    ∙ H₁.unit-r h₁

  β₂ : (h₁ : H₁.El) (h₂ : H₂.El)
    → j₂.f (G.comp (i₁.f h₁) (i₂.f h₂)) == h₂
  β₂ h₁ h₂ =
    j₂.pres-comp (i₁.f h₁) (i₂.f h₂)
    ∙ ap2 H₂.comp (im-sub-ker ex₁ _ [ h₁ , idp ]) (p₂ h₂)
    ∙ H₂.unit-l h₂

  iso : G ≃ᴳ (H₁ ×ᴳ H₂)
  iso = surjᴳ-and-injᴳ-iso (×ᴳ-fanout j₁ j₂)
    (λ {(h₁ , h₂) → [ G.comp (i₁.f h₁) (i₂.f h₂) ,
                      pair×= (β₁ h₁ h₂) (β₂ h₁ h₂) ]})
    (has-trivial-ker-is-injᴳ (×ᴳ-fanout j₁ j₂) fanout-has-trivial-ker)

  j₁-fst-comm-sqr : CommSquareᴳ j₁ ×ᴳ-fst (–>ᴳ iso) (idhom _)
  j₁-fst-comm-sqr = comm-sqrᴳ λ _ → idp

  j₂-snd-comm-sqr : CommSquareᴳ j₂ (×ᴳ-snd {G = H₁}) (–>ᴳ iso) (idhom _)
  j₂-snd-comm-sqr = comm-sqrᴳ λ _ → idp

  abstract
    i₁-inl-comm-sqr : CommSquareᴳ i₁ ×ᴳ-inl (idhom _) (–>ᴳ iso)
    i₁-inl-comm-sqr = comm-sqrᴳ λ h₁ →
      pair×= (p₁ h₁) (im-sub-ker ex₁ _ [ h₁ , idp ])

    i₂-inr-comm-sqr : CommSquareᴳ i₂ ×ᴳ-inr (idhom _) (–>ᴳ iso)
    i₂-inr-comm-sqr = comm-sqrᴳ λ h₂ →
      pair×= (im-sub-ker ex₂ _ [ h₂ , idp ]) (p₂ h₂)

  {- Given additionally maps

            i₀    j₀
         K –––→ G ––→ L

   - such that j₀∘i₀ = 0, we have j₀(i₁(j₁(i₀ k)))⁻¹ = j₀(i₂(j₂(i₀ k))).
   - (This is called the hexagon lemma in Eilenberg & Steenrod's book.
   - The hexagon is not visible in this presentation.)
   -}

  module HexagonLemma {k l}
    {K : Group k} {L : Group l}
    (i₀ : K →ᴳ G) (j₀ : G →ᴳ L)
    (ex₀ : ∀ g → GroupHom.f j₀ (GroupHom.f i₀ g) == Group.ident L)
    where

    abstract
      decomp : ∀ g → G.comp (i₁.f (j₁.f g)) (i₂.f (j₂.f g)) == g
      decomp g = <– (ap-equiv (GroupIso.f-equiv iso) _ g) $
        GroupIso.f iso (G.comp (i₁.f (j₁.f g)) (i₂.f (j₂.f g)))
          =⟨ GroupIso.pres-comp iso (i₁.f (j₁.f g)) (i₂.f (j₂.f g)) ⟩
        Group.comp (H₁ ×ᴳ H₂) (GroupIso.f iso (i₁.f (j₁.f g))) (GroupIso.f iso (i₂.f (j₂.f g)))
          =⟨ ap2 (Group.comp (H₁ ×ᴳ H₂))
              ((i₁-inl-comm-sqr □$ᴳ j₁.f g) ∙ ap (_, H₂.ident) (j₁-fst-comm-sqr □$ᴳ g))
              ((i₂-inr-comm-sqr □$ᴳ j₂.f g) ∙ ap (H₁.ident ,_) (j₂-snd-comm-sqr □$ᴳ g)) ⟩
        (H₁.comp (fst (GroupIso.f iso g)) H₁.ident , H₂.comp H₂.ident (snd (GroupIso.f iso g)))
          =⟨ pair×= (H₁.unit-r (fst (GroupIso.f iso g))) (H₂.unit-l (snd (GroupIso.f iso g))) ⟩
        (fst (GroupIso.f iso g) , snd (GroupIso.f iso g))
          =⟨ idp ⟩
        GroupIso.f iso g
          =∎

      cancel : ∀ k →
        Group.comp L (GroupHom.f (j₀ ∘ᴳ i₁ ∘ᴳ j₁ ∘ᴳ i₀) k)
                     (GroupHom.f (j₀ ∘ᴳ i₂ ∘ᴳ j₂ ∘ᴳ i₀) k)
        == Group.ident L
      cancel k = ! (GroupHom.pres-comp j₀ _ _)
               ∙ ap (GroupHom.f j₀) (decomp (GroupHom.f i₀ k))
               ∙ ex₀ k

      inv₁ : ∀ k → Group.inv L (GroupHom.f (j₀ ∘ᴳ i₁ ∘ᴳ j₁ ∘ᴳ i₀) k)
                == GroupHom.f (j₀ ∘ᴳ i₂ ∘ᴳ j₂ ∘ᴳ i₀) k
      inv₁ k = Group.inv-unique-r L _ _ (cancel k)

      inv₂ : ∀ k → Group.inv L (GroupHom.f (j₀ ∘ᴳ i₂ ∘ᴳ j₂ ∘ᴳ i₀) k)
                == GroupHom.f (j₀ ∘ᴳ i₁ ∘ᴳ j₁ ∘ᴳ i₀) k
      inv₂ k = Group.inv-unique-l L _ _ (cancel k)
