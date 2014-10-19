{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver

module cohomology.ProductRepr where

{- Given the following commutative diagram of homomorphisms,

       H₁  i₁  i₂  H₂
          ↘     ↙
    id ↓     G     ↓ id
           ↙   ↘
       H₁ j₁   j₂  H₂

 - there exists an isomorphism G == H₁ × H₂ such that i₁,i₂ correspond
 - to the natural injections and j₁,j₂ correspond to the natural
 - projections.

 -   G == H₁ × H₂, such that i₁,i₂ correspond to the natural injections,
 -   G == K₁ × K₂, such that j₁,j₂ correspond to the natural projections.
 -}

module ProductRepr {i j}
  {G : Group (lmax i j)} {H₁ : Group i} {H₂ : Group j}
  (i₁ : GroupHom H₁ G) (i₂ : GroupHom H₂ G)
  (j₁ : GroupHom G H₁) (j₂ : GroupHom G H₂)
  (p₁ : ∀ h₁ → GroupHom.f j₁ (GroupHom.f i₁ h₁) == h₁)
  (p₂ : ∀ h₂ → GroupHom.f j₂ (GroupHom.f i₂ h₂) == h₂)
  (ex₁ : is-exact (GroupHom.ptd-f i₁) (GroupHom.ptd-f j₂))
  (ex₂ : is-exact (GroupHom.ptd-f i₂) (GroupHom.ptd-f j₁))
  where

  zero-ker : (g : Group.El G)
    → GroupHom.f (×-hom j₁ j₂) g == Group.ident (H₁ ×G H₂)
    → g == Group.ident G
  zero-ker g q = Trunc-rec (Group.El-level G _ _)
      (lemma g (fst×= q))
      (ktoi ex₁ g (snd×= q))
    where
    lemma : (g : Group.El G) (r : GroupHom.f j₁ g == Group.ident H₁)
      → Σ (Group.El H₁) (λ h → GroupHom.f i₁ h == g)
      → g == Group.ident G
    lemma ._ r (h , idp) =
      ap (GroupHom.f i₁) (! (p₁ h) ∙ r) ∙ GroupHom.pres-ident i₁

  β₁ : (h₁ : Group.El H₁) (h₂ : Group.El H₂)
    → GroupHom.f j₁ (Group.comp G (GroupHom.f i₁ h₁) (GroupHom.f i₂ h₂)) == h₁
  β₁ h₁ h₂ =
    GroupHom.pres-comp j₁ (GroupHom.f i₁ h₁) (GroupHom.f i₂ h₂)
    ∙ ap2 (Group.comp H₁) (p₁ h₁) (itok ex₂ _ [ h₂ , idp ])
    ∙ Group.unitr H₁ h₁

  β₂ : (h₁ : Group.El H₁) (h₂ : Group.El H₂)
    → GroupHom.f j₂ (Group.comp G (GroupHom.f i₁ h₁) (GroupHom.f i₂ h₂)) == h₂
  β₂ h₁ h₂ =
    GroupHom.pres-comp j₂ (GroupHom.f i₁ h₁) (GroupHom.f i₂ h₂)
    ∙ ap2 (Group.comp H₂) (itok ex₁ _ [ h₁ , idp ]) (p₂ h₂)
    ∙ Group.unitl H₂ h₂

  iso : G == H₁ ×G H₂
  iso = surj-inj-iso (×-hom j₁ j₂)
    (zero-kernel-injective (×-hom j₁ j₂) zero-ker)
    (λ {(h₁ , h₂) → [ Group.comp G (GroupHom.f i₁ h₁) (GroupHom.f i₂ h₂) ,
                      pair×= (β₁ h₁ h₂) (β₂ h₁ h₂) ]})

  fst-over : j₁ == ×G-fst [ (λ U → GroupHom U H₁) ↓ iso ]
  fst-over = domain-over-iso _ _ _ _ $ domain-over-equiv fst _

  snd-over : j₂ == ×G-snd {G = H₁} [ (λ U → GroupHom U H₂) ↓ iso ]
  snd-over = domain-over-iso _ _ _ _ $ domain-over-equiv snd _

  inl-over : i₁ == ×G-inl [ (λ V → GroupHom H₁ V) ↓ iso ]
  inl-over = codomain-over-iso _ _ _ _ $
    codomain-over-equiv (GroupHom.f i₁) _
    ▹ λ= (λ h₁ → pair×= (p₁ h₁) (itok ex₁ _ [ h₁ , idp ]))

  inr-over : i₂ == ×G-inr {G = H₁} [ (λ V → GroupHom H₂ V) ↓ iso ]
  inr-over = codomain-over-iso _ _ _ _ $
    codomain-over-equiv (GroupHom.f i₂) _
    ▹ λ= (λ h₂ → pair×= (itok ex₂ _ [ h₂ , idp ]) (p₂ h₂))


  module HexagonLemma {k l}
    {K : Group k} {L : Group l}
    (i₀ : GroupHom K G) (j₀ : GroupHom G L)
    (ex₀ : ∀ g → GroupHom.f j₀ (GroupHom.f i₀ g) == Group.ident L)
    where

    decomp : ∀ g → Group.comp G (GroupHom.f i₁ (GroupHom.f j₁ g))
                                (GroupHom.f i₂ (GroupHom.f j₂ g))
                   == g
    decomp = transport
      (λ {(G' , i₁' , i₂' , j₁' , j₂') → ∀ g →
         Group.comp G' (GroupHom.f i₁' (GroupHom.f j₁' g))
                       (GroupHom.f i₂' (GroupHom.f j₂' g))
         == g})
      (! (pair= iso (↓-×-in inl-over (↓-×-in inr-over
                                             (↓-×-in fst-over snd-over)))))
      (λ {(h₁ , h₂) → pair×= (Group.unitr H₁ h₁) (Group.unitl H₂ h₂)})

    cancel : ∀ k →
      Group.comp L (GroupHom.f (j₀ ∘hom i₁ ∘hom j₁ ∘hom i₀) k)
                   (GroupHom.f (j₀ ∘hom i₂ ∘hom j₂ ∘hom i₀) k)
      == Group.ident L
    cancel k = ! (GroupHom.pres-comp j₀ _ _)
             ∙ ap (GroupHom.f j₀) (decomp (GroupHom.f i₀ k))
             ∙ ex₀ k

    inv₁ : ∀ k → Group.inv L (GroupHom.f (j₀ ∘hom i₁ ∘hom j₁ ∘hom i₀) k)
              == GroupHom.f (j₀ ∘hom i₂ ∘hom j₂ ∘hom i₀) k
    inv₁ k = group-inv-unique-r L _ _ (cancel k)

    inv₂ : ∀ k → Group.inv L (GroupHom.f (j₀ ∘hom i₂ ∘hom j₂ ∘hom i₀) k)
              == GroupHom.f (j₀ ∘hom i₁ ∘hom j₁ ∘hom i₀) k
    inv₂ k = group-inv-unique-l L _ _ (cancel k)
