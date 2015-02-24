{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.MayerVietoris
open import cohomology.SplitExactRight
open import cohomology.Theory

module cohomology.Coproduct {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT
open import cohomology.Functor CT

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

  cfcod-over : ⊙cfcod ⊙select == ⊙add-wglue
               [ (λ U → fst (X ⊙⊔ Y ⊙→ U)) ↓ ⊙path ]
  cfcod-over = codomain-over-⊙equiv _ _ _ ▹ pair= idp lemma
    where
    lemma : ap into (! (cfglue _ (lift true))) ∙ idp == idp
    lemma = ∙-unit-r _ ∙ ap-! into (cfglue _ (lift true))
            ∙ ap ! (Into.glue-β (lift true))

  ext-glue-cst :
    ⊙ext-glue == ⊙cst {X = ⊙Cof ⊙select} {Y = ⊙Sphere 1}
  ext-glue-cst = ⊙λ=
    (Cofiber-elim _
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
            ⊡v∙ ! (ap-cst (north _) (glue (lift false)))}))
    idp

  ext-over : ⊙ext-glue == ⊙cst
             [ (λ U → fst (U ⊙→ ⊙Sphere 1)) ↓ ⊙path ]
  ext-over = ext-glue-cst ◃ domain-over-⊙equiv _ _ _

module C⊔ (n : ℤ) (m : ℕ) (X Y : Ptd i) where

  private

    open CofSelect X Y

    seq : {G : Group i} (φ : GroupHom (C n (X ⊙⊔ Y)) G)
      → HomSequence _ _
    seq {G} φ =
      C n (⊙Sphere 1) ⟨ cst-hom ⟩→
      C n (X ⊙∨ Y)    ⟨ CF-hom n ⊙add-wglue ⟩→
      C n (X ⊙⊔ Y)    ⟨ φ ⟩→ -- CF-hom n (⊙susp^-fmap m ⊙select)
      G ⊣|

    eseq : is-exact-seq (seq (CF-hom n ⊙select))
    eseq = exact-build (seq (CF-hom n ⊙select))
      (transport
        (λ g → is-exact g (CF n ⊙add-wglue))
        (ap GroupHom.⊙f (CF-cst n))
        (transport
          (λ {(_ , g , h) → is-exact (CF n h) (CF n g)})
          (pair= ⊙path (↓-×-in cfcod-over ext-over))
          (transport
            (λ {(_ , g) → is-exact (CF n g) (CF n (⊙cfcod ⊙select))})
            (pair= (Cof².space-path ⊙select) (Cof².cfcod²-over ⊙select))
            (C-exact n (⊙cfcod ⊙select)))))
      (transport
        (λ {(_ , g) → is-exact (CF n g) (CF n ⊙select)})
        (pair= ⊙path cfcod-over)
        (C-exact n ⊙select))

    deselect : fst (X ⊙⊔ Y) → Sphere {i} 0
    deselect (inl _) = lift true
    deselect (inr _) = lift false

    ⊙deselect : fst (X ⊙⊔ Y ⊙→ ⊙Sphere {i} 0)
    ⊙deselect = (deselect , idp)

    deselect-select : ⊙deselect ⊙∘ ⊙select == ⊙idf _
    deselect-select = ⊙λ= (λ {(lift true) → idp; (lift false) → idp}) idp

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
