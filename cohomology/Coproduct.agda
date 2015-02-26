{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.SplitExactRight
open import cohomology.Theory

module cohomology.Coproduct {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT
open import cohomology.Functor CT
open import cohomology.BaseIndependence CT

{- Cⁿ(X ⊔ Y) == Cⁿ(X ∨ Y) × Cⁿ(S⁰). The proof is by constructing a
 - splitting exact sequence

         0 → Cⁿ(X ∨ Y) → Cⁿ(X ⊔ Y) → Cⁿ(S⁰)

 - by defining a map [select : S⁰ → X ⊔ Y] such that
   [Cofiber select == X ∨ Y] and [select] has a left inverse. -}

module CofSelect (X Y : Ptd i) where

  select : Sphere {i} 0 → fst (X ⊙⊔ Y)
  select (lift true) = inl (snd X)
  select (lift false) = inr (snd Y)

  ⊙select : fst (⊙Sphere {i} 0 ⊙→ X ⊙⊔ Y)
  ⊙select = (select , idp)

  module Into = CofiberRec select {C = X ∨ Y}
    (winl (snd X))
    add-wglue
    (λ {(lift true) → idp; (lift false) → wglue})

  module Out = WedgeRec {X = X} {Y = Y} {C = Cofiber select}
    (λ x → cfcod _ (inl x))
    (λ y → cfcod _ (inr y))
    (! (cfglue _ (lift true)) ∙ cfglue _ (lift false))

  into = Into.f
  out = Out.f

  into-out : ∀ w → into (out w) == w
  into-out = Wedge-elim
    (λ x → idp)
    (λ y → idp)
    (↓-∘=idf-in into out $
      ap into (ap out wglue)
        =⟨ ap (ap into) Out.glue-β ⟩
      ap into (! (cfglue _ (lift true)) ∙ cfglue _ (lift false))
        =⟨ ap-∙ into (! (cfglue _ (lift true))) (cfglue _ (lift false)) ⟩
      ap into (! (cfglue _ (lift true))) ∙ ap into (cfglue _ (lift false))
        =⟨ ap-! into (cfglue _ (lift true)) ∙ ap ! (Into.glue-β (lift true))
           |in-ctx (λ w → w ∙ ap into (cfglue _ (lift false))) ⟩
      ap into (cfglue _ (lift false))
        =⟨ Into.glue-β (lift false) ⟩
      wglue ∎)

  out-into : ∀ κ → out (into κ) == κ
  out-into = Cofiber-elim _
    (! (cfglue _ (lift true)))
    (λ {(inl x) → idp; (inr y) → idp})
    (λ {(lift true) → ↓-∘=idf-from-square out into $
          ap (ap out) (Into.glue-β (lift true)) ∙v⊡ bl-square _;
        (lift false) → ↓-∘=idf-from-square out into $
          (ap (ap out) (Into.glue-β (lift false)) ∙ Out.glue-β)
          ∙v⊡ lt-square (! (cfglue _ (lift true))) ⊡h vid-square})

  eq : Cofiber select ≃ X ∨ Y
  eq = equiv into out into-out out-into

  ⊙path : ⊙Cof ⊙select == X ⊙∨ Y
  ⊙path = ⊙ua eq idp

  cfcod-over : cfcod select == add-wglue
               [ (λ U → fst (X ⊙⊔ Y) → fst U) ↓ ⊙path ]
  cfcod-over = ↓-cst2-in _ _ $ codomain-over-equiv _ _

  ext-glue-cst : ext-glue {s = cofiber-span select} == cst (north _)
  ext-glue-cst = λ= $ Cofiber-elim _
    idp
    (λ {(inl _) → ! (merid _ (lift true));
        (inr _) → ! (merid _ (lift false))})
    (λ {(lift true) → ↓-='-from-square $
          ExtGlue.glue-β (lift true)
          ∙v⊡ tr-square (merid _ (lift true))
          ⊡v∙ ! (ap-cst (north _) (glue (lift true)));
        (lift false) → ↓-='-from-square $
          ExtGlue.glue-β (lift false)
          ∙v⊡ tr-square (merid _ (lift false))
          ⊡v∙ ! (ap-cst (north _) (glue (lift false)))})

  ext-over : ext-glue == cst (north _) [ (λ U → fst U → Sphere 1) ↓ ⊙path ]
  ext-over = ↓-cst2-in _ _ $ ext-glue-cst ◃ domain-over-equiv _ _

module C⊔ (n : ℤ) (m : ℕ) (X Y : Ptd i) where

  private

    open CofSelect X Y

    seq : HomSequence _ _
    seq =
      C n (⊙Sphere 1) ⟨ cst-hom ⟩→
      C n (X ⊙∨ Y)    ⟨ CF-hom n ⊙add-wglue ⟩→
      C n (X ⊙⊔ Y)    ⟨ CF-hom n ⊙select ⟩→
      C n (⊙Sphere 0) ⊣|

    eseq : is-exact-seq seq
    eseq = exact-build seq
      (transport (λ {(φ , ψ) → is-exact ψ φ})
        (pair×= (CF-base-indep n _ _ _) (CF-base-indep n _ _ _ ∙ CF-cst n))
        (transport {A = Σ _ (λ {(U , g , h) → (g (inl (snd X)) == snd U)
                                          × (h (snd U) == north _)})}
          (λ {((_ , g , h) , (p , q)) →
            is-exact (CF-hom n (h , q)) (CF-hom n (g , p))})
          (pair= (pair= ⊙path (↓-×-in cfcod-over ext-over))
                 (↓-×-in (from-transp _ _ idp) (from-transp _ _ idp)))
          (transport {A = Σ _ (λ {(U , g) → g (cfbase _) == snd U})}
            (λ {((_ , g) , p) →
              is-exact (CF-hom n (g , p)) (CF-hom n (⊙cfcod ⊙select))})
            (pair= (pair= (Cof².space-path ⊙select) (Cof².cfcod²-over ⊙select))
                   (from-transp _ _ idp))
            (C-exact n (⊙cfcod ⊙select)))))
      (transport (λ φ → is-exact φ (CF-hom n ⊙select))
        (CF-base-indep n _ _ _)
        (transport {A = Σ _ (λ {(U , g) → g (inl (snd X)) == snd U})}
          (λ {((_ , g) , p) → is-exact (CF-hom n (g , p)) (CF-hom n ⊙select)})
          (pair= (pair= ⊙path cfcod-over) (from-transp _ _ idp))
          (C-exact n ⊙select)))

    deselect : fst (X ⊙⊔ Y) → Sphere {i} 0
    deselect (inl _) = lift true
    deselect (inr _) = lift false

    ⊙deselect : fst (X ⊙⊔ Y ⊙→ ⊙Sphere {i} 0)
    ⊙deselect = (deselect , idp)

    deselect-select : (s : Sphere 0) → deselect (select s) == s
    deselect-select (lift true) = idp
    deselect-select (lift false) = idp

    module SER = SplitExactRight (C-abelian n _)
      (CF-hom n ⊙add-wglue) (CF-hom n ⊙select)
      eseq
      (CF-hom n ⊙deselect)
      (app= $ ap GroupHom.f $ CF-inverse n ⊙select ⊙deselect deselect-select)

    path : C n (X ⊙⊔ Y) == C n (X ⊙∨ Y) ×ᴳ C n (⊙Sphere 0)
    path = SER.iso

    add-wglue-over :
      CF-hom n ⊙add-wglue == ×ᴳ-inl [ (λ G → GroupHom (C n (X ⊙∨ Y)) G) ↓ path ]
    add-wglue-over = SER.φ-over-iso
