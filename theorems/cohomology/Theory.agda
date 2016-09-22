{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Choice
open import homotopy.FunctionOver

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
    -- XXX Should be [C-fmap]
    CF-hom : (n : ℤ) {X Y : Ptd i} → fst (X ⊙→ Y) → (C n Y →ᴳ C n X)

    -- XXX Should be [C-fmap-id]
    CF-ident : (n : ℤ) {X : Ptd i}
      → CF-hom n {X} {X} (⊙idf X) == idhom (C n X)

    -- XXX Should be [C-fmap-∘]
    CF-comp : (n : ℤ) {X Y Z : Ptd i} (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → CF-hom n (g ⊙∘ f) == CF-hom n f ∘ᴳ CF-hom n g

  -- XXX Do we need this?
  -- XXX Should be [C-fmap'] or something like that
  CF : (n : ℤ) {X Y : Ptd i} → fst (X ⊙→ Y) → CEl n Y → CEl n X
  CF n f = GroupHom.f (CF-hom n f)

  C-emap' : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → Group.El (C n Y) ≃ Group.El (C n X)
  C-emap' n ⊙eq = equiv (CF n (⊙–> ⊙eq)) (CF n (⊙<– ⊙eq))
    (app= $ ap GroupHom.f $ ! (CF-comp n (⊙<– ⊙eq) (⊙–> ⊙eq)) ∙ ap (CF-hom n) (⊙<–-inv-l ⊙eq) ∙ CF-ident n)
    (app= $ ap GroupHom.f $ ! (CF-comp n (⊙–> ⊙eq) (⊙<– ⊙eq)) ∙ ap (CF-hom n) (⊙<–-inv-r ⊙eq) ∙ CF-ident n)

  C-emap : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → C n Y ≃ᴳ C n X
  C-emap n ⊙eq = ≃-to-≃ᴳ (C-emap' n ⊙eq) (GroupHom.pres-comp (CF-hom n (⊙–> ⊙eq))) 

  field
    C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)

    C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X

    -- XXX Should be [C-Susp-nat]
    C-SuspF : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → fst (C-Susp n X) ∘ᴳ CF-hom (succ n) (⊙Susp-fmap f)
        == CF-hom n f ∘ᴳ fst (C-Susp n Y)

    C-exact : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → is-exact (CF-hom n (⊙cfcod' f)) (CF-hom n f)

    C-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
      → ((W : I → Type i) → has-choice 0 I W)
      → is-equiv (GroupHom.f (Πᴳ-fanout (CF-hom n ∘ ⊙bwin {X = Z})))

  {- Alternate form of suspension axiom naturality -}
  C-Susp-↓ : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
    → CF-hom (succ n) (⊙Susp-fmap f) == CF-hom n f
      [ uncurry _→ᴳ_ ↓ pair×= (uaᴳ (C-Susp n Y)) (uaᴳ (C-Susp n X)) ]
  C-Susp-↓ n f =
    hom-over-isos $ function-over-equivs _ _ $ ap GroupHom.f (C-SuspF n f)

record OrdinaryTheory i : Type (lsucc i) where
  constructor ordinary-theory
  field
    cohomology-theory : CohomologyTheory i
  open CohomologyTheory cohomology-theory public
  field
    C-dimension : (n : ℤ) → n ≠ 0 → C n (⊙Lift ⊙S⁰) ≃ᴳ 0ᴳ
