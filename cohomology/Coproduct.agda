{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.ExactPairIso
open import cohomology.FunctionOver
open import cohomology.MayerVietoris
open import cohomology.SplitExactRight
open import cohomology.OrdinaryTheory

module cohomology.Coproduct {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.ConstantFunction OT
open import cohomology.Functor OT
open import cohomology.Sn OT

{- Cₙ(X ⊔ Y) == Cₙ(X ∨ Y) × Cₙ(S⁰). The proof is by constructing a
 - splitting exact sequence

         0 → Cₙ(X ∨ Y) → Cₙ(X ⊔ Y) → C(S⁰)

 - such by defining a map [select : S⁰ → X ⊔ Y] such that
   [Cofiber select == X ∨ Y] and [select] has a left inverse. -}

module CofSelect (X Y : Ptd i) where

  select : Sphere {i} 0 → fst (X ∙⊔ Y)
  select (lift true) = inl (snd X)
  select (lift false) = inr (snd Y)

  ptd-select : fst (Ptd-Sphere {i} 0 ∙→ X ∙⊔ Y)
  ptd-select = (select , idp)

  module Into = CofiberRec select {C = Wedge X Y}
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

  eq : Cofiber select ≃ Wedge X Y
  eq = equiv into out into-out out-into

  ptd-path : Ptd-Cof ptd-select == Ptd-Wedge X Y
  ptd-path = ptd-ua eq idp

  cfcod-over : ptd-cfcod ptd-select == ptd-add-wglue
               [ (λ U → fst (X ∙⊔ Y ∙→ U)) ↓ ptd-path ]
  cfcod-over = codomain-over-ptd-equiv _ _ _ ▹ pair= idp lemma
    where
    lemma : ap into (! (cfglue _ (lift true))) ∙ idp == idp
    lemma = ∙-unit-r _ ∙ ap-! into (cfglue _ (lift true))
            ∙ ap ! (Into.glue-β (lift true))

  ext-glue-cst :
    ptd-ext-glue == ptd-cst {X = Ptd-Cof ptd-select} {Y = Ptd-Sphere 1}
  ext-glue-cst = ptd-λ=
    (Cofiber-elim _
      idp
      (λ {(inl _) → ! (merid _ (lift true));
          (inr _) → ! (merid _ (lift false))})
      (λ {(lift true) → ↓-='-from-square $
            ExtGlue.glue-β (lift true)
            ∙v⊡ ur-square (merid _ (lift true))
            ⊡v∙ ! (ap-cst (north _) (glue (lift true)));
          (lift false) → ↓-='-from-square $
            ExtGlue.glue-β (lift false)
            ∙v⊡ ur-square (merid _ (lift false))
            ⊡v∙ ! (ap-cst (north _) (glue (lift false)))}))
    idp

  ext-over : ptd-ext-glue == ptd-cst
             [ (λ U → fst (U ∙→ Ptd-Sphere 1)) ↓ ptd-path ]
  ext-over = ext-glue-cst ◃ domain-over-ptd-equiv _ _ _

module C⊔ (n : ℤ) (m : ℕ) (X Y : Ptd i) where

  open CofSelect X Y

  ed : {G : Group i} (φ : GroupHom (C n (Ptd-Susp^ m (X ∙⊔ Y))) G)
    → ExactDiag _ _
  ed {G} φ =
    C n (Ptd-Susp^ m (Ptd-Sphere 1))
      ⟨ cst-hom ⟩→
    C n (Ptd-Susp^ m (Ptd-Wedge X Y))
      ⟨ CF-hom n (ptd-susp^-fmap m ptd-add-wglue) ⟩→
    C n (Ptd-Susp^ m (X ∙⊔ Y))
      ⟨ φ ⟩→ -- CF-hom n (ptd-susp^-fmap m ptd-select)
    G ⊣| -- C n (Ptd-Susp^ m (Ptd-Sphere 0))

  es : ExactSeq (ed (CF-hom n (ptd-susp^-fmap m ptd-select)))
  es = exact-build (ed (CF-hom n (ptd-susp^-fmap m ptd-select)))
    (transport
      (λ g → is-exact g (CF n (ptd-susp^-fmap m ptd-add-wglue)))
      (ap (CF n) (ptd-susp^-fmap-cst m) ∙ ap GroupHom.ptd-f (CF-cst n))
      (transport
        (λ {(_ , g , h) → is-exact (CF n (ptd-susp^-fmap m h))
                                   (CF n (ptd-susp^-fmap m g))})
        (pair= ptd-path (↓-×-in cfcod-over ext-over))
        (transport
          (λ {(_ , g , h) → is-exact (CF n h) (CF n g)})
          (suspend^-cof= m (ptd-cfcod ptd-select) (ptd-ext-glue)
            (pair= (Cof².space-path ptd-select) (Cof².cfcod²-over ptd-select)))
          (C-exact n (ptd-susp^-fmap m (ptd-cfcod ptd-select))))))
    (transport
      (λ {(_ , g) → is-exact (CF n (ptd-susp^-fmap m g))
                             (CF n (ptd-susp^-fmap m ptd-select))})
      (pair= ptd-path cfcod-over)
      (transport
        (λ {(_ , g , h) → is-exact (CF n h) (CF n g)})
        (suspend^-cof= m ptd-select _ idp)
        (C-exact n (ptd-susp^-fmap m ptd-select))))

  module Nonzero (neq : n ≠ ℕ-to-ℤ m) where

    iso : C n (Ptd-Susp^ m (Ptd-Wedge X Y)) == C n (Ptd-Susp^ m (X ∙⊔ Y))
    iso = exact-pair-iso $
      transport (λ {(G , φ) → ExactSeq (ed {G} φ)})
        (pair= (ap (C n) (Ptd-Susp^-+ m O
                          ∙ ap (λ k → Ptd-Susp^ k (Ptd-Sphere 0)) (+-unit-r m))
                ∙ C-Sphere-≠ n m neq)
               (prop-has-all-paths-↓
                  {B = λ G → GroupHom (C n (Ptd-Susp^ m (X ∙⊔ Y))) G}
                  (contr-is-prop 0G-hom-in-level)))
        es

    add-wglue-over :
      idhom _ == CF-hom n (ptd-susp^-fmap m ptd-add-wglue)
      [ (λ G → GroupHom (C n (Ptd-Susp^ m (Ptd-Wedge X Y))) G) ↓ iso ]
    add-wglue-over = codomain-over-iso _ _ _ _ $ codomain-over-equiv _ _

  module Any where

    deselect : fst (X ∙⊔ Y) → Sphere {i} 0
    deselect (inl _) = lift true
    deselect (inr _) = lift false

    ptd-deselect : fst (X ∙⊔ Y ∙→ Ptd-Sphere {i} 0)
    ptd-deselect = (deselect , idp)

    deselect-select : ptd-deselect ∘ptd ptd-select == ptd-idf _
    deselect-select = ptd-λ= (λ {(lift true) → idp; (lift false) → idp}) idp

    module SER = SplitExactRight (C-abelian n _)
      (CF-hom n (ptd-susp^-fmap m ptd-add-wglue))
      (CF-hom n (ptd-susp^-fmap m ptd-select))
      es
      (CF-hom n (ptd-susp^-fmap m ptd-deselect))
      (app= $ ap GroupHom.f $ CF-inverse n
        (ptd-susp^-fmap m ptd-select)
        (ptd-susp^-fmap m ptd-deselect)
        (! (ptd-susp^-fmap-∘ m ptd-deselect ptd-select)
         ∙ ap (ptd-susp^-fmap m) deselect-select
         ∙ ptd-susp^-fmap-idf m _))

    iso : C n (Ptd-Susp^ m (X ∙⊔ Y))
        == C n (Ptd-Susp^ m (Ptd-Wedge X Y))
           ×G C n (Ptd-Susp^ m (Ptd-Sphere 0))
    iso = SER.iso

    add-wglue-over :
      CF-hom n (ptd-susp^-fmap m ptd-add-wglue) == ×G-inl
      [ (λ G → GroupHom (C n (Ptd-Susp^ m (Ptd-Wedge X Y))) G) ↓ iso ]
    add-wglue-over = SER.φ-over-iso
