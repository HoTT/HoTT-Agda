{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Pointed

module groups.Int where

abstract
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

ℤ-is-infinite-cyclic : is-infinite-cyclic ℤ-⊙group
ℤ-is-infinite-cyclic = is-eq
  (Group.exp ℤ-group 1)
  (idf ℤ)
  (! ∘ ℤ-idf-η)
  (! ∘ ℤ-idf-η)
