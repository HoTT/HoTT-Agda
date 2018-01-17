{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Pointed

module groups.Int where

ℤ→ᴳ-η : ∀ {i} {G : Group i} (φ : ℤ-group →ᴳ G)
  → GroupHom.f φ ∼ Group.exp G (GroupHom.f φ 1)
ℤ→ᴳ-η φ (pos 0) = GroupHom.pres-ident φ
ℤ→ᴳ-η φ (pos 1) = idp
ℤ→ᴳ-η {G = G} φ (pos (S (S n))) =
    GroupHom.pres-comp φ 1 (pos (S n))
  ∙ ap (Group.comp G (GroupHom.f φ 1)) (ℤ→ᴳ-η φ (pos (S n)))
  ∙ ! (Group.exp-+ G (GroupHom.f φ 1) 1 (pos (S n)))
ℤ→ᴳ-η φ (negsucc 0) = GroupHom.pres-inv φ 1
ℤ→ᴳ-η {G = G} φ (negsucc (S n)) =
    GroupHom.pres-comp φ -1 (negsucc n)
  ∙ ap2 (Group.comp G) (GroupHom.pres-inv φ 1) (ℤ→ᴳ-η φ (negsucc n))
  ∙ ! (Group.exp-+ G (GroupHom.f φ 1) -1 (negsucc n))

ℤ-idf-η : ∀ i → i == Group.exp ℤ-group 1 i
ℤ-idf-η = ℤ→ᴳ-η (idhom _)

ℤ→ᴳ-unicity : ∀ {i} {G : Group i}
  → (φ ψ : ℤ-group →ᴳ G)
  → GroupHom.f φ 1 == GroupHom.f ψ 1
  → GroupHom.f φ ∼ GroupHom.f ψ
ℤ→ᴳ-unicity {G = G} φ ψ p i =
  ℤ→ᴳ-η φ i ∙ ap (λ g₁ → Group.exp G g₁ i) p ∙ ! (ℤ→ᴳ-η ψ i)

ℤ→ᴳ-equiv-idf : ∀ {i} (G : Group i) → (ℤ-group →ᴳ G) ≃ Group.El G
ℤ→ᴳ-equiv-idf G = equiv (λ φ → GroupHom.f φ 1) (exp-hom G)
  (λ _ → idp) (λ φ → group-hom= $ λ= $ ! ∘ ℤ→ᴳ-η φ)
  where open Group G

ℤ→ᴳ-iso-idf : ∀ {i} (G : AbGroup i) → hom-group ℤ-group G ≃ᴳ AbGroup.grp G
ℤ→ᴳ-iso-idf G = ≃-to-≃ᴳ (ℤ→ᴳ-equiv-idf (AbGroup.grp G)) (λ _ _ → idp)

ℤ-⊙group : ⊙Group₀
ℤ-⊙group = ⊙[ ℤ-group , 1 ]ᴳ

abstract
  ℤ-is-infinite-cyclic : is-infinite-cyclic ℤ-⊙group
  ℤ-is-infinite-cyclic = is-eq
    (Group.exp ℤ-group 1)
    (idf ℤ)
    (! ∘ ℤ-idf-η)
    (! ∘ ℤ-idf-η)

  {- favonia: not sure how useful this is. we'll see -}
  iso-ℤ-implies-endo-infinite-cyclic : ∀ {i} (G : AbGroup i)
    → AbGroup.grp G ≃ᴳ ℤ-group
    → is-infinite-cyclic ⊙[ hom-group (AbGroup.grp G) G , idhom _ ]ᴳ
  iso-ℤ-implies-endo-infinite-cyclic G G-iso-ℤ =
    isomorphism-preserves'-infinite-cyclic
      ((hom-group (AbGroup.grp G) G
        ≃ᴳ⟨ pre∘ᴳ-iso G (G-iso-ℤ ⁻¹ᴳ) ⟩
      hom-group ℤ-group G
        ≃ᴳ⟨ post∘ᴳ-iso ℤ-group G ℤ-abgroup G-iso-ℤ ⟩
      hom-group ℤ-group ℤ-abgroup
        ≃ᴳ⟨ ℤ→ᴳ-iso-idf ℤ-abgroup ⟩
      ℤ-group
        ≃ᴳ∎) ,
      GroupIso.f-g G-iso-ℤ 1)
      ℤ-is-infinite-cyclic

  infinite-cyclic-hom-is-equiv : ∀ {i j} {⊙G : ⊙Group i} {⊙H : ⊙Group j}
    → (φ : ⊙G ⊙→ᴳ ⊙H)
    → is-infinite-cyclic ⊙G
    → is-infinite-cyclic ⊙H
    → is-equiv (GroupHom.f (fst φ))
  infinite-cyclic-hom-is-equiv {⊙G = ⊙G} {⊙H = ⊙H} φ G-iic H-iic =
    ∼-preserves-equiv
      (λ g →
        ⊙Group.exp ⊙H (ptᴳ ⊙H) (is-equiv.g G-iic g)
          =⟨ ℤ→ᴳ-unicity (fst (⊙exp-hom ⊙H)) (fst φ ∘ᴳ fst (⊙exp-hom ⊙G)) (! (snd φ)) (is-equiv.g G-iic g) ⟩
        GroupHom.f (fst φ ∘ᴳ fst (⊙exp-hom ⊙G)) (is-equiv.g G-iic g)
          =⟨ ap (GroupHom.f (fst φ)) $ is-equiv.f-g G-iic g ⟩
        GroupHom.f (fst φ) g
          =∎)
      (H-iic ∘ise is-equiv-inverse G-iic)
