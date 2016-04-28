{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.PtdAdjoint
open import homotopy.SuspAdjointLoop
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.MayerVietoris
open import cohomology.Theory

{- Standard Mayer-Vietoris exact sequence (algebraic) derived from
 - the result in cohomology.MayerVietoris (topological).
 - This is a whole bunch of algebra which is not very interesting.
 -}

module cohomology.MayerVietorisExact {i} (CT : CohomologyTheory i)
  (n : ℤ) (ps : ⊙Span {i} {i} {i}) where

open MayerVietorisFunctions ps
module MV = MayerVietoris ps
open ⊙Span ps

open CohomologyTheory CT
open import cohomology.BaseIndependence CT
open import cohomology.Functor CT
open import cohomology.InverseInSusp CT
open import cohomology.LongExactSequence CT n ⊙reglue
open import cohomology.Wedge CT

mayer-vietoris-seq : HomSequence _ _
mayer-vietoris-seq =
  C n (⊙Pushout ps)
    ⟨ ×ᴳ-hom-in (CF-hom n (⊙left ps)) (CF-hom n (⊙right ps)) ⟩→
  C n X ×ᴳ C n Y
    ⟨ ×ᴳ-sum-hom (C-abelian _ _) (CF-hom n f)
                 (inv-hom _ (C-abelian _ _) ∘ᴳ (CF-hom n g)) ⟩→
  C n Z
    ⟨ CF-hom (succ n) ⊙ext-glue ∘ᴳ fst ((C-Susp n Z)⁻¹ᴳ) ⟩→
  C (succ n) (⊙Pushout ps)
    ⟨ ×ᴳ-hom-in (CF-hom _ (⊙left ps)) (CF-hom _ (⊙right ps)) ⟩→
  C (succ n) X ×ᴳ C (succ n) Y ⊣|

mayer-vietoris-exact : is-exact-seq mayer-vietoris-seq
mayer-vietoris-exact =
  transport (λ {(r , s) → is-exact-seq s})
    (pair= _ $ sequence= _ _ $
      idp
        ∥⟨ ↓-over-×-in _→ᴳ_ idp (CWedge.⊙wedge-rec-over n X Y _ _) ⟩∥
      CWedge.path n X Y
        ∥⟨ ↓-over-×-in' _→ᴳ_
             (ap↓ (λ φ → φ ∘ᴳ fst (C-Susp n (X ⊙∨ Y) ⁻¹ᴳ))
                  (CF-↓cod= (succ n) MV.ext-over)
              ∙ᵈ codomain-over-iso {χ = diff'} (codomain-over-equiv _ _))
             (CWedge.wedge-hom-η n X Y _
              ▹ ap2 (×ᴳ-sum-hom (C-abelian n Z)) inl-lemma inr-lemma) ⟩∥
      ap (C (succ n)) MV.⊙path ∙ group-ua (C-Susp n Z)
        ∥⟨ ↓-over-×-in _→ᴳ_
            (CF-↓dom= (succ n) MV.cfcod-over
             ∙ᵈ domain-over-iso
                  (! (ap (λ h → CF _ ⊙ext-glue ∘ h)
                     (λ= (is-equiv.g-f (snd (C-Susp n Z)))))
                   ◃ domain-over-equiv _ _))
            idp                                              ⟩∥
      idp
        ∥⟨ ↓-over-×-in _→ᴳ_ idp (CWedge.⊙wedge-rec-over (succ n) X Y _ _) ⟩∥
      CWedge.path (succ n) X Y ∥⊣|)
    long-cofiber-exact
  where
  {- shorthand -}
  diff' = fst (C-Susp n Z) ∘ᴳ CF-hom (succ n) MV.⊙mv-diff
                           ∘ᴳ fst (C-Susp n (X ⊙∨ Y) ⁻¹ᴳ)

  {- Variations on suspension axiom naturality -}
  natural-lemma₁ : {X Y : Ptd i} (n : ℤ) (f : fst (X ⊙→ Y))
    → (fst (C-Susp n X) ∘ᴳ CF-hom _ (⊙susp-fmap f)) ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ)
      == CF-hom n f
  natural-lemma₁ {X} {Y} n f =
    ap (λ φ → φ ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ)) (C-SuspF n f)
    ∙ hom= _ _ (λ= (ap (CF n f) ∘ is-equiv.f-g (snd (C-Susp n Y))))

  natural-lemma₂ : {X Y : Ptd i} (n : ℤ) (f : fst (X ⊙→ Y))
    → CF-hom _ (⊙susp-fmap f) ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ)
      == fst (C-Susp n X ⁻¹ᴳ) ∘ᴳ CF-hom n f
  natural-lemma₂ {X} {Y} n f =
    hom= _ _ (λ= (! ∘ is-equiv.g-f (snd (C-Susp n X))
                    ∘ CF _ (⊙susp-fmap f)
                    ∘ GroupHom.f (fst (C-Susp n Y ⁻¹ᴳ))))
    ∙ ap (λ φ → fst (C-Susp n X ⁻¹ᴳ) ∘ᴳ φ) (natural-lemma₁ n f)

  {- Associativity lemmas -}
  assoc-lemma : ∀ {i} {G H K L J : Group i}
    (φ : L →ᴳ J) (ψ : K →ᴳ L) (χ : H →ᴳ K) (ξ : G →ᴳ H)
    → (φ ∘ᴳ ψ) ∘ᴳ χ ∘ᴳ ξ == φ ∘ᴳ ((ψ ∘ᴳ χ) ∘ᴳ ξ)
  assoc-lemma _ _ _ _ = hom= _ _ idp

  assoc-lemma₂ : ∀ {i} {G H K L J : Group i}
    (φ : L →ᴳ J) (ψ : K →ᴳ L) (χ : H →ᴳ K) (ξ : G →ᴳ H)
    → (φ ∘ᴳ ψ ∘ᴳ χ) ∘ᴳ ξ == φ ∘ᴳ ψ ∘ᴳ χ ∘ᴳ ξ
  assoc-lemma₂ _ _ _ _ = hom= _ _ idp

  inl-lemma : diff' ∘ᴳ CF-hom n (⊙projl X Y) == CF-hom n f
  inl-lemma =
    assoc-lemma₂
      (fst (C-Susp n Z)) (CF-hom (succ n) MV.⊙mv-diff)
      (fst (C-Susp n (X ⊙∨ Y) ⁻¹ᴳ)) (CF-hom n (⊙projl X Y))
    ∙ ap (λ φ → fst (C-Susp n Z) ∘ᴳ CF-hom (succ n) MV.⊙mv-diff ∘ᴳ φ)
         (! (natural-lemma₂ n (⊙projl X Y)))
    ∙ ! (assoc-lemma₂
           (fst (C-Susp n Z)) (CF-hom _ MV.⊙mv-diff)
           (CF-hom _ (⊙susp-fmap (⊙projl X Y)))
           (fst (C-Susp n X ⁻¹ᴳ)))
    ∙ ap (λ φ → (fst (C-Susp n Z) ∘ᴳ φ) ∘ᴳ fst (C-Susp n X ⁻¹ᴳ))
         (! (CF-comp _ (⊙susp-fmap (⊙projl X Y)) MV.⊙mv-diff))
    ∙ ap (λ φ → (fst (C-Susp n Z) ∘ᴳ φ) ∘ᴳ fst (C-Susp n X ⁻¹ᴳ))
         (CF-λ= (succ n) projl-mv-diff)
    ∙ natural-lemma₁ n f
    where
    {- Compute the left projection of mv-diff -}
    projl-mv-diff : (σz : fst (⊙Susp Z))
      → susp-fmap (projl X Y) (MV.mv-diff σz)
        == susp-fmap (fst f) σz
    projl-mv-diff = Suspension-elim _ idp (merid _ (snd X)) $
      ↓-='-from-square ∘ λ z →
        (ap-∘ (susp-fmap (projl X Y)) MV.mv-diff (merid _ z)
         ∙ ap (ap (susp-fmap (projl X Y))) (MV.MVDiff.glue-β z)
         ∙ ap-∙ (susp-fmap (projl X Y))
                (merid _ (winl (fst f z))) (! (merid _ (winr (fst g z))))
         ∙ (SuspFmap.glue-β (projl X Y) (winl (fst f z))
            ∙2 (ap-! (susp-fmap _) (merid _ (winr (fst g z)))
                ∙ ap ! (SuspFmap.glue-β (projl X Y) (winr (fst g z))))))
        ∙v⊡ (vid-square {p = merid _ (fst f z)}
             ⊡h rt-square (merid _ (snd X)))
        ⊡v∙ (∙-unit-r _ ∙ ! (SuspFmap.glue-β (fst f) z))

  inr-lemma : diff' ∘ᴳ CF-hom n (⊙projr X Y)
                           == inv-hom _ (C-abelian n Z) ∘ᴳ CF-hom n g
  inr-lemma =
    assoc-lemma₂
      (fst (C-Susp n Z)) (CF-hom (succ n) MV.⊙mv-diff)
      (fst (C-Susp n (X ⊙∨ Y) ⁻¹ᴳ)) (CF-hom n (⊙projr X Y))
    ∙ ap (λ φ → fst (C-Susp n Z) ∘ᴳ CF-hom (succ n) MV.⊙mv-diff ∘ᴳ φ)
         (! (natural-lemma₂ n (⊙projr X Y)))
    ∙ ! (assoc-lemma₂
           (fst (C-Susp n Z)) (CF-hom _ MV.⊙mv-diff)
           (CF-hom _ (⊙susp-fmap (⊙projr X Y)))
           (fst (C-Susp n Y ⁻¹ᴳ)))
    ∙ ap (λ φ → (fst (C-Susp n Z) ∘ᴳ φ) ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ))
         (! (CF-comp _ (⊙susp-fmap (⊙projr X Y)) MV.⊙mv-diff))
    ∙ ∘ᴳ-assoc (fst (C-Susp n Z))
        (CF-hom _ (⊙susp-fmap (⊙projr X Y) ⊙∘ MV.⊙mv-diff))
        (fst (C-Susp n Y ⁻¹ᴳ))
    ∙ ap (λ φ → fst (C-Susp n Z) ∘ᴳ φ ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ))
         (CF-λ= (succ n) projr-mv-diff)
    ∙ ap (λ φ → fst (C-Susp n Z) ∘ᴳ φ ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ))
         (CF-comp _ (⊙susp-fmap g) (⊙flip-susp Z))
    ∙ ! (assoc-lemma (fst (C-Susp n Z)) (CF-hom _ (⊙flip-susp Z))
                     (CF-hom _ (⊙susp-fmap g)) (fst (C-Susp n Y ⁻¹ᴳ)))
    ∙ ap (λ φ → (fst (C-Susp n Z) ∘ᴳ φ)
                ∘ᴳ CF-hom _ (⊙susp-fmap g) ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ))
         (C-flip-susp-is-inv (succ n))
    ∙ ap (λ φ → φ ∘ᴳ CF-hom _ (⊙susp-fmap g) ∘ᴳ fst (C-Susp n Y ⁻¹ᴳ))
         (inv-hom-natural (C-abelian _ _) (C-abelian _ _)
           (fst (C-Susp n Z)))
    ∙ assoc-lemma (inv-hom _ (C-abelian n Z)) (fst (C-Susp n Z))
                  (CF-hom _ (⊙susp-fmap g)) (fst (C-Susp n Y ⁻¹ᴳ))
    ∙ ap (λ φ → inv-hom _ (C-abelian n Z) ∘ᴳ φ) (natural-lemma₁ n g)
    where
    {- Compute the right projection of mv-diff -}
    projr-mv-diff : (σz : fst (⊙Susp Z))
      → susp-fmap (projr X Y) (MV.mv-diff σz)
        == susp-fmap (fst g) (flip-susp σz)
    projr-mv-diff = Suspension-elim _ (merid _ (snd Y)) idp $
      ↓-='-from-square ∘ λ z →
        (ap-∘ (susp-fmap (projr X Y)) MV.mv-diff (merid _ z)
         ∙ ap (ap (susp-fmap (projr X Y))) (MV.MVDiff.glue-β z)
         ∙ ap-∙ (susp-fmap (projr X Y))
             (merid _ (winl (fst f z))) (! (merid _ (winr (fst g z))))
         ∙ (SuspFmap.glue-β (projr X Y) (winl (fst f z))
            ∙2 (ap-! (susp-fmap (projr X Y))
                  (merid _ (winr (fst g z)))
                ∙ ap ! (SuspFmap.glue-β (projr X Y) (winr (fst g z))))))
        ∙v⊡ ((lt-square (merid _ (snd Y))
             ⊡h vid-square {p = ! (merid _ (fst g z))}))
        ⊡v∙ ! (ap-∘ (susp-fmap (fst g)) flip-susp (merid _ z)
               ∙ ap (ap (susp-fmap (fst g))) (FlipSusp.glue-β z)
               ∙ ap-! (susp-fmap (fst g)) (merid _ z)
               ∙ ap ! (SuspFmap.glue-β (fst g) z))
