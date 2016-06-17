{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Choice
open import cohomology.FunctionOver

module cohomology.Theory where

-- [i] for the universe level of the group
record CohomologyTheory i : Type (lsucc i) where
  field
    C : ℤ → Ptd i → Group i

  CEl : ℤ → Ptd i → Type i
  CEl n X = Group.El (C n X)

  Cid : (n : ℤ) (X : Ptd i) → CEl n X
  Cid n X = GroupStructure.ident (Group.group-struct (C n X))

  ⊙CEl : ℤ → Ptd i → Ptd i
  ⊙CEl n X = ⊙[ CEl n X , Cid n X ]

  field
    CF-hom : (n : ℤ) {X Y : Ptd i} → fst (X ⊙→ Y) → (C n Y →ᴳ C n X)

    CF-ident : (n : ℤ) {X : Ptd i}
      → CF-hom n {X} {X} (⊙idf X) == idhom (C n X)
    CF-comp : (n : ℤ) {X Y Z : Ptd i} (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → CF-hom n (g ⊙∘ f) == CF-hom n f ∘ᴳ CF-hom n g

  CF : (n : ℤ) {X Y : Ptd i} → fst (X ⊙→ Y) → CEl n Y → CEl n X
  CF n f = GroupHom.f (CF-hom n f)

  field
    C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)

    C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X

    C-SuspF : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → fst (C-Susp n X) ∘ᴳ CF-hom (succ n) (⊙susp-fmap f)
        == CF-hom n f ∘ᴳ fst (C-Susp n Y)

    C-exact : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → is-exact (CF-hom n (⊙cfcod' f)) (CF-hom n f)

    C-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
      → ((W : I → Type i) → has-choice 0 I W)
      → is-equiv (GroupHom.f (Πᴳ-hom-in (CF-hom n ∘ ⊙bwin {X = Z})))

  {- Alternate form of suspension axiom naturality -}
  C-Susp-↓ : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
    → CF-hom (succ n) (⊙susp-fmap f) == CF-hom n f
      [ uncurry _→ᴳ_ ↓ pair×= (group-ua (C-Susp n Y)) (group-ua (C-Susp n X)) ]
  C-Susp-↓ n f =
    hom-over-isos $ function-over-equivs _ _ $ ap GroupHom.f (C-SuspF n f)

record OrdinaryTheory i : Type (lsucc i) where
  constructor ordinary-theory
  field
    cohomology-theory : CohomologyTheory i
  open CohomologyTheory cohomology-theory public
  field
    C-dimension : (n : ℤ) → n ≠ 0 → C n (⊙Lift ⊙S⁰) == 0ᴳ
