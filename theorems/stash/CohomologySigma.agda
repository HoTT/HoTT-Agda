{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CofiberSequence
open import groups.SplitExactRight
open import cohomology.Theory

module cohomology.Sigma {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT
open import cohomology.Functor CT
open import cohomology.BaseIndependence CT

{- Cⁿ(Σx:X.Y) = Cⁿ(⋁x:X.Y) × Cⁿ(X). The proof is by constructing a
 - splitting exact sequence

       0 → Cⁿ(⋁x:X.Y) → Cⁿ(Σx:X.Y) → Cⁿ(X)

 - by observing that the map [select : x ↦ (x, snd Yₓ)] has a left inverse
 - and satisfies [Cofiber select == ⋁x:X.Y. -}

module CofSelect (X : Ptd i) (Y : fst X → Ptd i) where

  select : fst X → fst (⊙Σ X Y)
  select x = (x , snd (Y x))

  ⊙select : X ⊙→ ⊙Σ X Y
  ⊙select = (select , idp)

  ⊙Σbwin : ⊙Σ X Y ⊙→ ⊙BigWedge Y
  ⊙Σbwin = (uncurry bwin , ! (bwglue (snd X)))

  eq : Cofiber select ≃ BigWedge Y
  eq = equiv Into.f Out.f into-out out-into
    where
    module Into = CofiberRec select {C = BigWedge Y}
      bwbase (uncurry bwin) bwglue

    module Out = BigWedgeRec {X = Y} {C = Cofiber select}
      (cfbase _) (curry (cfcod _)) (cfglue _)

    into-out : ∀ w → Into.f (Out.f w) == w
    into-out = BigWedge-elim
      idp (λ _ _ → idp)
      (↓-∘=idf-in' Into.f Out.f ∘ λ x →
        ap (ap Into.f) (Out.glue-β x) ∙ Into.glue-β x)

    out-into : ∀ c → Out.f (Into.f c) == c
    out-into = Cofiber-elim select
      idp (λ _ → idp)
      (↓-∘=idf-in' Out.f Into.f ∘ λ x →
        ap (ap Out.f) (Into.glue-β x) ∙ Out.glue-β x)

  ⊙path : ⊙Cofiber ⊙select == ⊙BigWedge Y
  ⊙path = ⊙ua eq idp

  cfcod-over : cfcod _ == uncurry bwin [ (λ U → fst (⊙Σ X Y) → fst U) ↓ ⊙path ]
  cfcod-over = ↓-cst2-in _ _ $ codomain-over-equiv _ _

  extract-glue-cst : extract-glue {s = cofiber-span select} == cst (north _)
  extract-glue-cst = λ= $ Cofiber-elim _
    idp
    (λ {(x , y) → ! (merid _ x)})
    (↓-='-from-square ∘ λ x →
      ExtGlue.glue-β x ∙v⊡
        tr-square (merid _ x)
      ⊡v∙ ! (ap-cst (north _) (cfglue _ x)))

  ext-over : extract-glue == cst (north _)
             [ (λ U → fst U → fst (⊙Susp X)) ↓ ⊙path ]
  ext-over = ↓-cst2-in _ _ $ extract-glue-cst ◃ domain-over-equiv _ _


module CΣ (n : ℤ) (X : Ptd i) (Y : fst X → Ptd i) where

  open CofSelect X Y

  private
    seq : HomSequence _ _
    seq =
      C n (⊙Susp X)     ⟨ cst-hom ⟩→
      C n (⊙BigWedge Y) ⟨ CF-hom n ⊙Σbwin ⟩→
      C n (⊙Σ X Y)      ⟨ CF-hom n ⊙select ⟩→
      C n X             ⊣|

    eseq : is-exact-seq seq
    eseq = exact-build seq
      (transport (λ {(φ , ψ) → is-exact ψ φ})
        (pair×= (CF-base-indep n _ _ _) (CF-base-indep n _ _ _ ∙ CF-cst n))
        (transport {A = Σ _ (λ {(U , g , h) → (g (snd (⊙Σ X Y)) == snd U)
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
        (transport {A = Σ _ (λ {(U , g) → g (snd (⊙Σ X Y)) == snd U})}
          (λ {((_ , g) , p) → is-exact (CF-hom n (g , p)) (CF-hom n ⊙select)})
          (pair= (pair= ⊙path cfcod-over) (from-transp _ _ idp))
          (C-exact n ⊙select)))

    module SER = SplitExactRight (C-is-abelian n _)
      (CF-hom n ⊙Σbwin) (CF-hom n ⊙select)
      eseq
      (CF-hom n (⊙dfst Y))
      (app= $ ap GroupHom.f $ CF-inverse n ⊙select (⊙dfst Y) (λ _ → idp))

  path : C n (⊙Σ X Y) == C n (⊙BigWedge Y) ×ᴳ C n X
  path = SER.iso

  ⊙Σbwin-over : CF-hom n ⊙Σbwin == ×ᴳ-inl
                [ (λ G → GroupHom (C n (⊙BigWedge Y)) G) ↓ path ]
  ⊙Σbwin-over = SER.φ-over-iso

  ⊙select-over : CF-hom n ⊙select == ×ᴳ-snd {G = C n (⊙BigWedge Y)}
                 [ (λ G → GroupHom G (C n X)) ↓ path ]
  ⊙select-over = SER.ψ-over-iso

  open CofSelect public using (select; ⊙select; ⊙Σbwin)


module C⊔ (n : ℤ) (X Y : Ptd i) where

  private
    T : Sphere {i} 0 → Ptd i
    T (lift true) = X
    T (lift false) = Y

  path : C n (X ⊙⊔ Y) == C n (X ⊙∨ Y) ×ᴳ C n (⊙Sphere 0)
  path = ap (C n) (! (⊙ua (ΣBool-equiv-⊔ (fst ∘ T)) idp))
         ∙ CΣ.path n (⊙Sphere 0) T
         ∙ ap (λ Z → C n Z ×ᴳ C n (⊙Sphere 0)) (BigWedge-Bool-⊙path T)
