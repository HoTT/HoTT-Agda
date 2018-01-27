{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.HomSequence

module cohomology.Theory where

-- [i] for the universe level of the group
record CohomologyTheory i : Type (lsucc i) where
  {- functorial parts -}
  field
    C : ℤ → Ptd i → Group i

    C-is-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)

  C-abgroup : ℤ → Ptd i → AbGroup i
  C-abgroup n X = C n X , C-is-abelian n X

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

  field
    C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X

  CEl-Susp : (n : ℤ) (X : Ptd i) → CEl (succ n) (⊙Susp X) ≃ CEl n X
  CEl-Susp n X = GroupIso.f-equiv (C-Susp n X)

  field
    -- This naming is stretching the convention
    C-Susp-fmap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
      → CommSquareᴳ (C-fmap (succ n) (⊙Susp-fmap f)) (C-fmap n f)
          (GroupIso.f-hom (C-Susp n Y)) (GroupIso.f-hom (C-Susp n X))

  C-Susp-fmap-cse : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
    → CommSquareEquivᴳ (C-fmap (succ n) (⊙Susp-fmap f)) (C-fmap n f)
        (GroupIso.f-hom (C-Susp n Y)) (GroupIso.f-hom (C-Susp n X))
  C-Susp-fmap-cse n {X} {Y} f = C-Susp-fmap n f , GroupIso.f-is-equiv (C-Susp n Y) , GroupIso.f-is-equiv (C-Susp n X)

  C-Susp-fmap' : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
    → CommSquareᴳ (C-fmap n f) (C-fmap (succ n) (⊙Susp-fmap f))
        (GroupIso.g-hom (C-Susp n Y)) (GroupIso.g-hom (C-Susp n X))
  C-Susp-fmap' n f = fst (CommSquareEquivᴳ-inverse-v (C-Susp-fmap-cse n f))

  CEl-Susp-fmap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
    → CommSquare (CEl-fmap (succ n) (⊙Susp-fmap f)) (CEl-fmap n f)
        (GroupIso.f (C-Susp n Y)) (GroupIso.f (C-Susp n X))
  CEl-Susp-fmap n f = comm-sqr λ y' → C-Susp-fmap n f □$ᴳ y'

  field
    C-exact : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
      → is-exact (C-fmap n (⊙cfcod' f)) (C-fmap n f)

  C-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
    → C n (⊙BigWedge Z) →ᴳ Πᴳ I (λ i → C n (Z i))
  C-additive n Z = Πᴳ-fanout (C-fmap n ∘ ⊙bwin {X = Z})

  CEl-additive : (n : ℤ) {I : Type i} (Z : I → Ptd i)
    → CEl n (⊙BigWedge Z) → Π I (λ i → CEl n (Z i))
  CEl-additive n Z = GroupHom.f (C-additive n Z)

  field
    C-additive-is-equiv : (n : ℤ) {I : Type i} (Z : I → Ptd i)
      → has-choice 0 I i
      → is-equiv (CEl-additive n Z)

  C-additive-iso : (n : ℤ) {I : Type i} (Z : I → Ptd i)
    → has-choice 0 I i
    → C n (⊙BigWedge Z) ≃ᴳ Πᴳ I (λ i → C n (Z i))
  C-additive-iso n Z ac = C-additive n Z , C-additive-is-equiv n Z ac

  C2 : ℤ → Group i
  C2 n = C n (⊙Lift ⊙Bool)

  C2-is-abelian : (n : ℤ) → is-abelian (C2 n)
  C2-is-abelian n = C-is-abelian n (⊙Lift ⊙Bool)

  C2-abgroup : ℤ → AbGroup i
  C2-abgroup n = C-abgroup n (⊙Lift ⊙Bool)

  -- XXX This is put here due to the limitation of the current Agda.
  -- See issue #434.
  abstract
    ∘-C-fmap : (n : ℤ) {X Y Z : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ Z)
      → ∀ x → CEl-fmap n f (CEl-fmap n g x) == CEl-fmap n (g ⊙∘ f) x
    ∘-C-fmap n f g x = ! (C-fmap-∘ n g f x)

  CEl-fmap-idf = C-fmap-idf
  CEl-fmap-∘ = C-fmap-∘
  ∘-CEl-fmap = ∘-C-fmap

  CEl-emap : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → Group.El (C n Y) ≃ Group.El (C n X)
  CEl-emap n ⊙eq = equiv (CEl-fmap n (⊙–> ⊙eq)) (CEl-fmap n (⊙<– ⊙eq)) to-from from-to where
    abstract
      to-from = λ x → ! (CEl-fmap-∘ n (⊙<– ⊙eq) (⊙–> ⊙eq) x)
                    ∙ ap (λ f → CEl-fmap n f x) (⊙λ= (⊙<–-inv-l ⊙eq))
                    ∙ CEl-fmap-idf n x
      from-to = λ x → ! (CEl-fmap-∘ n (⊙–> ⊙eq) (⊙<– ⊙eq) x)
                    ∙ ap (λ f → CEl-fmap n f x) (⊙λ= (⊙<–-inv-r ⊙eq))
                    ∙ CEl-fmap-idf n x

  abstract
    CEl-isemap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y) → is-equiv (fst f) → is-equiv (CEl-fmap n f)
    CEl-isemap n f f-ise = snd (CEl-emap n (f , f-ise))

  C-emap : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → C n Y ≃ᴳ C n X
  C-emap n ⊙eq = ≃-to-≃ᴳ (CEl-emap n ⊙eq) lemma
    where abstract lemma = GroupHom.pres-comp (C-fmap n (⊙–> ⊙eq))

  C-isemap = CEl-isemap

  {- Cohomology groups are independent of basepoint, and the action of
   - the cohomology is independent of the basepoint-preservation path -}

  C-base-indep : (n : ℤ) {A : Type i} (a₀ a₁ : A)
    → C n ⊙[ A , a₀ ] ≃ᴳ C n ⊙[ A , a₁ ]
  C-base-indep n a₀ a₁ =
    C-Susp n ⊙[ _ , a₁ ] ∘eᴳ (C-Susp n ⊙[ _ , a₀ ])⁻¹ᴳ

  private
    abstract
      CEl-fmap-base-indep' : (n : ℤ) {X Y : Ptd i}
        (f : de⊙ X → de⊙ Y) (p₁ p₂ : f (pt X) == pt Y)
        → ∀ y → CEl-fmap n (f , p₁) y == CEl-fmap n (f , p₂) y
      CEl-fmap-base-indep' n {X} {Y} f p₁ p₂ y =
        CEl-fmap n (f , p₁) y
          =⟨ ! $ <–-inv-r (CEl-Susp n Y) y |in-ctx CEl-fmap n (f , p₁) ⟩
        CEl-fmap n (f , p₁) (–> (CEl-Susp n Y) (<– (CEl-Susp n Y) y))
          =⟨ ! $ commutes (CEl-Susp-fmap n (f , p₁)) (<– (CEl-Susp n Y) y) ⟩
        –> (CEl-Susp n X) (CEl-fmap (succ n) (Susp-fmap f , idp) (<– (CEl-Susp n Y) y))
          =⟨ commutes (CEl-Susp-fmap n (f , p₂)) (<– (CEl-Susp n Y) y) ⟩
        CEl-fmap n (f , p₂) (–> (CEl-Susp n Y) (<– (CEl-Susp n Y) y))
          =⟨ <–-inv-r (CEl-Susp n Y) y |in-ctx CEl-fmap n (f , p₂) ⟩
        CEl-fmap n (f , p₂) y
          =∎

  abstract
    -- FIXME is there a better name?
    CEl-fmap-base-indep : (n : ℤ) {X Y : Ptd i} {f g : X ⊙→ Y}
      → (∀ x → fst f x == fst g x)
      → (∀ y → CEl-fmap n f y == CEl-fmap n g y)
    CEl-fmap-base-indep n h y = CEl-fmap-base-indep' n _ _ _ _
                              ∙ ap (λ f → CEl-fmap n f y) (⊙λ=' h (↓-idf=cst-in' idp))
  C-fmap-base-indep = CEl-fmap-base-indep

  {- cohomology of the unit -}
  abstract
    C-Unit : ∀ n → is-trivialᴳ (C n (⊙Lift {j = i} ⊙Unit))
    C-Unit n x =
      x
        =⟨ ! (CEl-fmap-idf n x) ⟩
      CEl-fmap n (⊙idf _) x
        =⟨ CEl-fmap-base-indep n (λ _ → idp) x ⟩
      CEl-fmap n (⊙cst ⊙∘ ⊙cfcod' (⊙idf _)) x
        =⟨ CEl-fmap-∘ n ⊙cst (⊙cfcod' (⊙idf _)) x ⟩
      CEl-fmap n (⊙cfcod' (⊙idf _)) (CEl-fmap n ⊙cst x)
        =⟨ ! (CEl-fmap-idf n (CEl-fmap n (⊙cfcod' (⊙idf _)) (CEl-fmap n ⊙cst x))) ⟩
      CEl-fmap n (⊙idf _) (CEl-fmap n (⊙cfcod' (⊙idf _)) (CEl-fmap n ⊙cst x))
        =⟨ im-sub-ker (C-exact n (⊙idf _)) _ [ CEl-fmap n ⊙cst x , idp ] ⟩
      Cident n (⊙Lift {j = i} ⊙Unit)
        =∎

  {- more functoriality -}
  abstract
    C-fmap-cst : (n : ℤ) {X Y : Ptd i} → ∀ y → CEl-fmap n (⊙cst {X = X} {Y = Y}) y == Cident n X
    C-fmap-cst n {X} {Y} y =
      CEl-fmap n (⊙cst {X = ⊙LU} ⊙∘ ⊙cst {X = X}) y
        =⟨ CEl-fmap-∘ n ⊙cst ⊙cst y ⟩
      CEl-fmap n (⊙cst {X = X}) (CEl-fmap n (⊙cst {X = ⊙LU}) y)
        =⟨ C-Unit n (CEl-fmap n (⊙cst {X = ⊙LU}) y)
           |in-ctx CEl-fmap n (⊙cst {X = X} {Y = ⊙LU}) ⟩
      CEl-fmap n (⊙cst {X = X}) (Cident n ⊙LU)
        =⟨ GroupHom.pres-ident (C-fmap n (⊙cst {X = X} {Y = ⊙LU})) ⟩
      Cident n X ∎
      where
      ⊙LU = ⊙Lift {j = i} ⊙Unit

    C-fmap-const : (n : ℤ) {X Y : Ptd i} {f : X ⊙→ Y}
      → (∀ x → fst f x == pt Y)
      → ∀ y → CEl-fmap n f y == Cident n X
    C-fmap-const n f-is-const y =
      CEl-fmap-base-indep n f-is-const y ∙ C-fmap-cst n y

    -- FIXME Is there a better name?
    C-fmap-inverse : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ X)
      → (∀ x → fst g (fst f x) == x)
      → (∀ x → CEl-fmap n f (CEl-fmap n g x) == x)
    C-fmap-inverse n f g p x = ! (CEl-fmap-∘ n g f x) ∙ CEl-fmap-base-indep n p x ∙ C-fmap-idf n x

  CEl-fmap-cst = C-fmap-cst
  CEl-fmap-const = C-fmap-const
  CEl-fmap-inverse = C-fmap-inverse

record OrdinaryTheory i : Type (lsucc i) where
  constructor ordinary-theory
  field
    -- XXX This should be cohomology-thy
    cohomology-theory : CohomologyTheory i
  open CohomologyTheory cohomology-theory public
  field
    C-dimension : {n : ℤ} → n ≠ 0 → is-trivialᴳ (C2 n)
