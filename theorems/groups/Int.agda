{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Pointed

module groups.Int where

ℤ-exp-η : ∀ i → i == Group.exp ℤ-group 1 i
ℤ-exp-η (pos 0) = idp
ℤ-exp-η (pos 1) = idp
ℤ-exp-η (pos (S (S n))) = ap succ (ℤ-exp-η (pos (S n)))
ℤ-exp-η (negsucc 0) = idp
ℤ-exp-η (negsucc (S n)) = ap pred (ℤ-exp-η (negsucc n))

hom-from-ℤ-unicity : ∀ {i} {G : Group i}
  → (φ ψ : ℤ-group →ᴳ G)
  → GroupHom.f φ 1 == GroupHom.f ψ 1
  → GroupHom.f φ ∼ GroupHom.f ψ
hom-from-ℤ-unicity {G = G} φ ψ p g =
  φ.f g
    =⟨ ap φ.f (ℤ-exp-η g) ⟩
  φ.f (ℤᴳ.exp 1 g)
    =⟨ φ.pres-exp 1 g ⟩
  G.exp (φ.f 1) g
    =⟨ ap (λ x → G.exp x g) p ⟩
  G.exp (ψ.f 1) g
    =⟨ ! $ ψ.pres-exp 1 g ⟩
  ψ.f (ℤᴳ.exp 1 g)
    =⟨ ! $ ap ψ.f (ℤ-exp-η g) ⟩
  ψ.f g
    =∎
  where
    module φ = GroupHom φ
    module ψ = GroupHom ψ
    module G = Group G
    module ℤᴳ = Group ℤ-group

ℤ-⊙group : ⊙Group₀
ℤ-⊙group = ⊙[ ℤ-group , 1 ]ᴳ

abstract
  ℤ-is-infinite-cyclic : is-infinite-cyclic ℤ-⊙group
  ℤ-is-infinite-cyclic = is-eq
    (Group.exp ℤ-group 1)
    (idf ℤ)
    (! ∘ ℤ-exp-η)
    (! ∘ ℤ-exp-η)

isomorphism-preserves-infinite-cyclic : ∀ {i j}
  → {⊙G : ⊙Group i} {⊙H : ⊙Group j} → ⊙G ⊙≃ᴳ ⊙H
  → is-infinite-cyclic ⊙G
  → is-infinite-cyclic ⊙H
isomorphism-preserves-infinite-cyclic
  {⊙G = ⊙[ G , g ]ᴳ} {⊙H = ⊙[ H , h ]ᴳ} (iso , pres-pt) ⊙G-iic =
  is-eq _ (is-equiv.g ⊙G-iic ∘ GroupIso.g iso) to-from from-to
  where
    lemma : Group.exp H h ∼ GroupIso.f iso ∘ Group.exp G g
    lemma i = ! $
      GroupIso.f iso (Group.exp G g i)
        =⟨ GroupIso.pres-exp iso g i ⟩
      Group.exp H (GroupIso.f iso g) i
        =⟨ ap (λ x → Group.exp H x i) pres-pt ⟩
      Group.exp H h i
        =∎

    abstract
      to-from : ∀ x → Group.exp H h (is-equiv.g ⊙G-iic (GroupIso.g iso x)) == x
      to-from x =
        Group.exp H h (is-equiv.g ⊙G-iic (GroupIso.g iso x))
          =⟨ lemma (is-equiv.g ⊙G-iic (GroupIso.g iso x)) ⟩
        GroupIso.f iso (Group.exp G g (is-equiv.g ⊙G-iic (GroupIso.g iso x)))
          =⟨ ap (GroupIso.f iso) (is-equiv.f-g ⊙G-iic (GroupIso.g iso x)) ⟩
        GroupIso.f iso (GroupIso.g iso x)
          =⟨ GroupIso.f-g iso x ⟩
        x
          =∎

      from-to : ∀ i → is-equiv.g ⊙G-iic (GroupIso.g iso (Group.exp H h i)) == i
      from-to i =
        is-equiv.g ⊙G-iic (GroupIso.g iso (Group.exp H h i))
          =⟨ ap (is-equiv.g ⊙G-iic ∘ GroupIso.g iso) (lemma i) ⟩
        is-equiv.g ⊙G-iic (GroupIso.g iso (GroupIso.f iso (Group.exp G g i)))
          =⟨ ap (is-equiv.g ⊙G-iic) (GroupIso.g-f iso (Group.exp G g i)) ⟩
        is-equiv.g ⊙G-iic (Group.exp G g i)
          =⟨ is-equiv.g-f ⊙G-iic i ⟩
        i
          =∎
