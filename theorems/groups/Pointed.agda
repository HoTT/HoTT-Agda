{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.Pointed where

infix 60 ⊙[_,_]ᴳˢ ⊙[_,_]ᴳ

record ⊙GroupStructure {i : ULevel} (GEl : Type i) : Type (lsucc i) where
  constructor ⊙[_,_]ᴳˢ
  field
    de⊙ᴳˢ : GroupStructure GEl
    ptᴳˢ : GEl
open ⊙GroupStructure

record ⊙Group (i : ULevel) : Type (lsucc i) where
  constructor ⊙[_,_]ᴳ
  field
    de⊙ᴳ : Group i
    ptᴳ : Group.El de⊙ᴳ
open ⊙Group

⊙Group₀ = ⊙Group lzero

infix 0 _⊙→ᴳ_
_⊙→ᴳ_ : ∀ {i j} → ⊙Group i → ⊙Group j → Type (lmax i j)
⊙G ⊙→ᴳ ⊙H = Σ (de⊙ᴳ ⊙G →ᴳ de⊙ᴳ ⊙H) (λ φ → GroupHom.f φ (ptᴳ ⊙G) == ptᴳ ⊙H)

infix 30 _⊙≃ᴳ_
_⊙≃ᴳ_ : ∀ {i j} → ⊙Group i → ⊙Group j → Type (lmax i j)
⊙G ⊙≃ᴳ ⊙H = Σ (de⊙ᴳ ⊙G ≃ᴳ de⊙ᴳ ⊙H) (λ φ → GroupIso.f φ (ptᴳ ⊙G) == ptᴳ ⊙H)

infixl 120 _⊙⁻¹ᴳ
_⊙⁻¹ᴳ : ∀ {i j} {⊙G : ⊙Group i} {⊙H : ⊙Group j} → ⊙G ⊙≃ᴳ ⊙H → ⊙H ⊙≃ᴳ ⊙G
_⊙⁻¹ᴳ (iso , iic) = iso ⁻¹ᴳ , ! (equiv-adj (GroupIso.f-equiv iso) iic)

is-struct-infinite-cyclic : ∀ {i} {El : Type i} → ⊙GroupStructure El → Type i
is-struct-infinite-cyclic ⊙[ G , g ]ᴳˢ = is-equiv (GroupStructure.exp G g)

is-infinite-cyclic : ∀ {i} → ⊙Group i → Type i
is-infinite-cyclic ⊙[ G , g ]ᴳ =
  is-struct-infinite-cyclic ⊙[ Group.group-struct G , g ]ᴳˢ

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

isomorphism-preserves'-infinite-cyclic : ∀ {i j}
  → {⊙G : ⊙Group i} {⊙H : ⊙Group j} → ⊙G ⊙≃ᴳ ⊙H
  → is-infinite-cyclic ⊙H
  → is-infinite-cyclic ⊙G
isomorphism-preserves'-infinite-cyclic iso iic =
  isomorphism-preserves-infinite-cyclic (iso ⊙⁻¹ᴳ) iic
