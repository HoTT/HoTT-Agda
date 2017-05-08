{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Exactness
open import cohomology.Theory

{- Finite additivity is provable (and in a stronger form) without using
 - the additivity axiom. We have

         Cⁿ(X ∨ Y) == Cⁿ(X) × Cⁿ(Y)

 - and over this path
 -   ∙ Cⁿ(winl) corresponds to fst : Cⁿ(X) × Cⁿ(Y) → Cⁿ(X),
 -   ∙ Cⁿ(winr) corresponds to snd : Cⁿ(X) × Cⁿ(Y) → Cⁿ(Y),
 -   ∙ Cⁿ(Wedge-rec winl* winr* wglue*) : Cⁿ(Z) → Cⁿ(X ∨ Y)
       corresponds to Cⁿ(winl*) × Cⁿ(winr*).
 -   ∙ Cⁿ(f) : Cⁿ(X ∨ Y) → Cⁿ(Z)
       corresponds to Cⁿ(projl ∘ f) + Cⁿ(projr ∘ f) : Cⁿ(X) × Cⁿ(Y) → Cⁿ(Z)
 -}

module cohomology.Wedge {i} (CT : CohomologyTheory i)
  (n : ℤ) (X Y : Ptd i) where

  open import homotopy.WedgeCofiber X Y

  open CohomologyTheory CT
  open import cohomology.PtdMapSequence CT

  private
    abstract
      βl : ∀ x → CEl-fmap n ⊙winl (CEl-fmap n (⊙projl {X = X} {Y}) x) == x
      βl = CEl-fmap-inverse n ⊙winl ⊙projl λ _ → idp

      βr : ∀ y → CEl-fmap n ⊙winr (CEl-fmap n (⊙projr {X = X} {Y}) y) == y
      βr = CEl-fmap-inverse n ⊙winr ⊙projr λ _ → idp

      C-projr-C-winl-is-exact : is-exact (C-fmap n (⊙projr {X = X} {Y})) (C-fmap n ⊙winl)
      C-projr-C-winl-is-exact = equiv-preserves'-exact
        (C-comm-square n cfcod-winl-projr-comm-sqr)
        (C-comm-square n $ comm-sqr λ _ → idp)
        (snd (C-emap n CofWinl.⊙eq))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-exact n ⊙winl)

      C-projl-C-winr-is-exact : is-exact (C-fmap n (⊙projl {X = X} {Y})) (C-fmap n ⊙winr)
      C-projl-C-winr-is-exact = equiv-preserves'-exact
        (C-comm-square n cfcod-winr-projl-comm-sqr)
        (C-comm-square n $ comm-sqr λ _ → idp)
        (snd (C-emap n CofWinr.⊙eq))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-isemap n (⊙idf _) (idf-is-equiv _))
        (C-exact n ⊙winr)

  import groups.ProductRepr
    (C-fmap n (⊙projl {X = X} {Y})) (C-fmap n ⊙projr)
    (C-fmap n ⊙winl) (C-fmap n ⊙winr) βl βr
    C-projl-C-winr-is-exact
    C-projr-C-winl-is-exact as PR

  C-Wedge : C n (X ⊙∨ Y) ≃ᴳ C n X ×ᴳ C n Y
  C-Wedge = PR.iso

  C-projl-inl-comm-sqr : CommSquareᴳ (C-fmap n ⊙projl)
    ×ᴳ-inl (idhom _) (–>ᴳ C-Wedge)
  C-projl-inl-comm-sqr = PR.i₁-inl-comm-sqr

  C-projr-inr-comm-sqr : CommSquareᴳ (C-fmap n ⊙projr)
    ×ᴳ-inr (idhom _) (–>ᴳ C-Wedge)
  C-projr-inr-comm-sqr = PR.i₂-inr-comm-sqr

  abstract
    C-Wedge-rec-comm-sqr : ∀ {Z : Ptd i} (winl* : X ⊙→ Z) (winr* : Y ⊙→ Z)
      → CommSquareᴳ
          (C-fmap n (⊙Wedge-rec winl* winr*))
          (×ᴳ-fanout (C-fmap n winl*) (C-fmap n winr*))
          (idhom _) (–>ᴳ C-Wedge)
    C-Wedge-rec-comm-sqr winl* winr* = comm-sqrᴳ λ z → pair×=
      ( ∘-CEl-fmap n ⊙winl (⊙Wedge-rec winl* winr*) z
      ∙ CEl-fmap-base-indep n (λ _ → idp) z)
      ( ∘-CEl-fmap n ⊙winr (⊙Wedge-rec winl* winr*) z
      ∙ CEl-fmap-base-indep n (λ _ → idp) z)

    C-Wedge-rec-comm-sqr' : ∀ {Z : Ptd i} (winl* : X ⊙→ Z) (winr* : Y ⊙→ Z)
      → CommSquareᴳ
          (×ᴳ-fanout (C-fmap n winl*) (C-fmap n winr*))
          (C-fmap n (⊙Wedge-rec winl* winr*))
          (idhom _) (<–ᴳ C-Wedge)
    C-Wedge-rec-comm-sqr' winl* winr* = comm-sqrᴳ λ z →
      ! (ap (GroupIso.g C-Wedge) (C-Wedge-rec-comm-sqr winl* winr* □$ᴳ z))
      ∙ GroupIso.g-f C-Wedge (CEl-fmap n (⊙Wedge-rec winl* winr*) z)

    Wedge-hom-η-comm-sqr : {Z : Ptd i} (φ : C n (⊙Wedge X Y) →ᴳ C n Z)
      → CommSquareᴳ φ
          (×ᴳ-fanin (C-is-abelian n _) (φ ∘ᴳ C-fmap n ⊙projl)
                                       (φ ∘ᴳ C-fmap n ⊙projr))
          (–>ᴳ C-Wedge) (idhom _)
    Wedge-hom-η-comm-sqr φ = comm-sqrᴳ λ x∨y →
        ap (GroupHom.f φ) (! (GroupIso.g-f C-Wedge x∨y))
      ∙ ! (×ᴳ-fanin-pre∘ (C-is-abelian n _) (C-is-abelian n _)
             φ (C-fmap n ⊙projl) (C-fmap n ⊙projr) _)

    Wedge-hom-η-comm-sqr' : {Z : Ptd i} (φ : C n (⊙Wedge X Y) →ᴳ C n Z)
      → CommSquareᴳ
          (×ᴳ-fanin (C-is-abelian n _) (φ ∘ᴳ C-fmap n ⊙projl)
                                       (φ ∘ᴳ C-fmap n ⊙projr))
          φ (<–ᴳ C-Wedge) (idhom _)
    Wedge-hom-η-comm-sqr' {Z} φ = comm-sqrᴳ λ z →
      ×ᴳ-fanin-pre∘ (C-is-abelian n _) (C-is-abelian n _)
        φ (C-fmap n ⊙projl) (C-fmap n ⊙projr) _

    Wedge-in-comm-sqr : {Z : Ptd i} (f : Z ⊙→ ⊙Wedge X Y)
      → CommSquareᴳ (C-fmap n f)
          (×ᴳ-fanin (C-is-abelian n _) (C-fmap n (⊙projl ⊙∘ f))
                                       (C-fmap n (⊙projr ⊙∘ f)))
          (–>ᴳ C-Wedge) (idhom _)
    Wedge-in-comm-sqr f = comm-sqrᴳ λ x∨y →
        (Wedge-hom-η-comm-sqr (C-fmap n f) □$ᴳ x∨y)
      ∙ ap2 (Group.comp (C n _))
          (∘-C-fmap n f ⊙projl _)
          (∘-C-fmap n f ⊙projr _)

    Wedge-in-comm-sqr' : {Z : Ptd i} (f : Z ⊙→ ⊙Wedge X Y)
      → CommSquareᴳ
          (×ᴳ-fanin (C-is-abelian n _) (C-fmap n (⊙projl ⊙∘ f))
                                       (C-fmap n (⊙projr ⊙∘ f)))
          (C-fmap n f) (<–ᴳ C-Wedge) (idhom _)
    Wedge-in-comm-sqr' f = comm-sqrᴳ λ z →
        ap2 (Group.comp (C n _))
          (C-fmap-∘ n ⊙projl f _)
          (C-fmap-∘ n ⊙projr f _)
      ∙ (Wedge-hom-η-comm-sqr' (C-fmap n f) □$ᴳ z)
