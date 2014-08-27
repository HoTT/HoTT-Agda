{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Choice

module cohomology.OrdinaryTheory where

record OrdinaryTheory i : Type (lsucc i) where
  field
    C : ℤ → Ptd i → Group i

  CEl : ℤ → Ptd i → Type i
  CEl n X = Group.El (C n X)

  Cid : (n : ℤ) (X : Ptd i) → CEl n X
  Cid n X = GroupStructure.ident (Group.group-struct (C n X))

  Ptd-CEl : ℤ → Ptd i → Ptd i
  Ptd-CEl n X = ∙[ CEl n X , Cid n X ]

  field
    CF-hom : (n : ℤ) {X Y : Ptd i} → fst (X ∙→ Y) → GroupHom (C n Y) (C n X)

    CF-ident : (n : ℤ) {X : Ptd i}
      → CF-hom n {X} {X} (ptd-idf X) == idhom (C n X)
    CF-comp : (n : ℤ) {X Y Z : Ptd i} (g : fst (Y ∙→ Z)) (f : fst (X ∙→ Y))
      → CF-hom n (g ∘ptd f) == CF-hom n f ∘hom CF-hom n g

  CF : (n : ℤ) {X Y : Ptd i} → fst (X ∙→ Y) → fst (Ptd-CEl n Y ∙→ Ptd-CEl n X)
  CF n f = GroupHom.ptd-f (CF-hom n f)

  field
    C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)

    C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (Ptd-Susp X) == C n X

    C-exact : (n : ℤ) {X Y : Ptd i} (f : fst (X ∙→ Y))
      → is-exact (CF n (ptd-cfcod f)) (CF n f)

    C-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
      → ((W : I → Type i) → (∀ i → has-level (ℤ-to-ℕ₋₂ n) (W i))
                                 → has-choice ⟨0⟩ I W)
      → C n (Ptd-BigWedge Z) == ΠG I (C n ∘ Z)

    C-dimension : (n : ℤ) → n ≠ O → C n (Ptd-Sphere O) == 0G

  {- A quick useful special case of C-additive:
     C n (X ∨ Y) == C n X × C n Y -}
  C-binary-additive : (n : ℤ) (X Y : Ptd i)
    → C n (Ptd-Wedge X Y) == C n X ×G C n Y
  C-binary-additive n X Y =
    ap (C n) (! (BigWedge-Bool-ptd-path Pick))
    ∙ C-additive n _ (λ _ _ → Bool-has-choice)
    ∙ ΠG-Bool-is-×G (C n ∘ Pick)
    where
    Pick : Lift {j = i} Bool → Ptd i
    Pick (lift true) = X
    Pick (lift false) = Y
