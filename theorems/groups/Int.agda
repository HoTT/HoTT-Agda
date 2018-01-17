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
