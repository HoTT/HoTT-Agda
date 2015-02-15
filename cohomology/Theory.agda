{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Choice

module cohomology.Theory where

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

  CF : (n : ℤ) {X Y : Ptd i} → fst (X ⊙→ Y) → fst (⊙CEl n Y ⊙→ ⊙CEl n X)
  CF n f = GroupHom.⊙f (CF-hom n f)

  field
    C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)

    C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) == C n X

    C-exact : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → is-exact (CF n (⊙cfcod f)) (CF n f)

    C-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
      → ((W : I → Type i) → has-choice ⟨0⟩ I W)
      → C n (⊙BigWedge Z) == Πᴳ I (C n ∘ Z)

  {- A quick useful special case of C-additive:
     C n (X ∨ Y) == C n X × C n Y -}
  C-binary-additive : (n : ℤ) (X Y : Ptd i)
    → C n (X ⊙∨ Y) == C n X ×ᴳ C n Y
  C-binary-additive n X Y =
    ap (C n) (! (BigWedge-Bool-⊙path Pick))
    ∙ C-additive n _ (λ _ → Bool-has-choice)
    ∙ Πᴳ-Bool-is-×ᴳ (C n ∘ Pick)
    where
    Pick : Lift {j = i} Bool → Ptd i
    Pick (lift true) = X
    Pick (lift false) = Y

record OrdinaryTheory i : Type (lsucc i) where
  constructor ordinary-theory
  field
    cohomology-theory : CohomologyTheory i
  open CohomologyTheory cohomology-theory public
  field
    C-dimension : (n : ℤ) → n ≠ O → C n (⊙Sphere O) == 0ᴳ
