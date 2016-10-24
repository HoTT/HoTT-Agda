{-# OPTIONS --without-K #-}

open import HoTT
open import groups.HomSequence

module cohomology.Theory where

-- [i] for the universe level of the group
record CohomologyTheory i : Type (lsucc i) where
  {- functorial parts -}
  field
    C : ℤ → Ptd i → Group i

    C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)

  CEl : ℤ → Ptd i → Type i
  CEl n X = Group.El (C n X)

  Cident : (n : ℤ) (X : Ptd i) → CEl n X
  Cident n X = Group.ident (C n X)

  ⊙CEl : ℤ → Ptd i → Ptd i
  ⊙CEl n X = ⊙[ CEl n X , Cident n X ]

  {- functorial parts -}
  field
    C-fmap : (n : ℤ) {X Y : Ptd i} → X ⊙→ Y → (C n Y →ᴳ C n X)

  CEl-fmap : (n : ℤ) {X Y : Ptd i} → X ⊙→ Y → (CEl n Y → CEl n X)
  CEl-fmap n f = GroupHom.f (C-fmap n f)

  field
    C-fmap-idf : (n : ℤ) {X : Ptd i}
      → ∀ x → CEl-fmap n {X} {X} (⊙idf X) x == x

    C-fmap-∘ : (n : ℤ) {X Y Z : Ptd i} (g : Y ⊙→ Z) (f : X ⊙→ Y)
      → ∀ x → CEl-fmap n (g ⊙∘ f) x == CEl-fmap n f (CEl-fmap n g x)

  ∘-C-fmap : (n : ℤ) {X Y Z : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ Z)
    → ∀ x → CEl-fmap n f (CEl-fmap n g x) == CEl-fmap n (g ⊙∘ f) x
  ∘-C-fmap n f g x = ! (C-fmap-∘ n g f x) 

  CEl-fmap-idf = C-fmap-idf
  CEl-fmap-∘ = C-fmap-∘
  ∘-CEl-fmap = ∘-C-fmap

  -- FIXME The proofs of roundtrips should be made abstract once
  -- Agda 2.5.2 is officially out.
  CEl-emap : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → Group.El (C n Y) ≃ Group.El (C n X)
  CEl-emap n ⊙eq = equiv (CEl-fmap n (⊙–> ⊙eq)) (CEl-fmap n (⊙<– ⊙eq))
    (λ x → ! (CEl-fmap-∘ n (⊙<– ⊙eq) (⊙–> ⊙eq) x) ∙ ap (λ f → CEl-fmap n f x) (⊙<–-inv-l ⊙eq) ∙ CEl-fmap-idf n x)
    (λ x → ! (CEl-fmap-∘ n (⊙–> ⊙eq) (⊙<– ⊙eq) x) ∙ ap (λ f → CEl-fmap n f x) (⊙<–-inv-r ⊙eq) ∙ CEl-fmap-idf n x)

  CEl-isemap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y) → is-equiv (fst f) → is-equiv (CEl-fmap n f)
  CEl-isemap n f f-ise = snd (CEl-emap n (f , f-ise))

  C-emap : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → C n Y ≃ᴳ C n X
  C-emap n ⊙eq = ≃-to-≃ᴳ (CEl-emap n ⊙eq) (GroupHom.pres-comp (C-fmap n (⊙–> ⊙eq)))

  C-isemap = CEl-isemap

  field
    C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X

  CEl-Susp : (n : ℤ) (X : Ptd i) → CEl (succ n) (⊙Susp X) ≃ CEl n X
  CEl-Susp n X = GroupIso.f-equiv (C-Susp n X)

  field
    -- This naming is stretching the convention
    C-Susp-fmap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
      → CommSquareᴳ (C-fmap (succ n) (⊙Susp-fmap f)) (C-fmap n f)
          (GroupIso.f-hom (C-Susp n Y)) (GroupIso.f-hom (C-Susp n X))

  CEl-Susp-fmap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
    → CommSquare (CEl-fmap (succ n) (⊙Susp-fmap f)) (CEl-fmap n f)
        (GroupIso.f (C-Susp n Y)) (GroupIso.f (C-Susp n X))
  CEl-Susp-fmap n f = comm-sqr λ y' → C-Susp-fmap n f □$ᴳ y'

  field
    C-exact : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
      → is-exact (C-fmap n (⊙cfcod' f)) (C-fmap n f)

  C-additive-hom : (n : ℤ) {I : Type i} (Z : I → Ptd i)
    → C n (⊙BigWedge Z) →ᴳ Πᴳ I (λ i → C n (Z i))
  C-additive-hom n Z = Πᴳ-fanout (C-fmap n ∘ ⊙bwin {X = Z})

  field
    C-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
      → has-choice 0 I i
      → is-equiv (GroupHom.f (C-additive-hom n Z))

  C-additive-iso : (n : ℤ) {I : Type i} (Z : I → Ptd i)
    → has-choice 0 I i
    → C n (⊙BigWedge Z) ≃ᴳ Πᴳ I (λ i → C n (Z i))
  C-additive-iso n Z ac = C-additive-hom n Z , C-additive n Z ac

record OrdinaryTheory i : Type (lsucc i) where
  constructor ordinary-theory
  field
    cohomology-theory : CohomologyTheory i
  open CohomologyTheory cohomology-theory public
  field
    C-dimension : {n : ℤ} → n ≠ 0 → is-trivialᴳ (C n (⊙Lift ⊙S⁰))
