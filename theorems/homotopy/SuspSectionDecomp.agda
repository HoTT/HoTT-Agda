{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.elims.CofPushoutSection

{- If f : X → Y is a section, then ΣY ≃ ΣX ∨ ΣCof(f) -}

module homotopy.SuspSectionDecomp
  {i j} {X : Ptd i} {Y : Ptd j} (⊙f : X ⊙→ Y)
  (g : fst Y → fst X) (inv : ∀ x → g (fst ⊙f x) == x)
  where

module SuspSectionDecomp where

  private
    f = fst ⊙f

  module Into = SuspensionRec {C = fst (⊙Susp X ⊙∨ ⊙Susp (⊙Cof ⊙f))}
    (winl south)
    (winr south)
    (λ y → ! (ap winl (merid (g y))) ∙ wglue ∙ ap winr (merid (cfcod y)))

  into = Into.f

  module OutWinl = SuspensionRec south south
    (λ x → ! (merid (f x)) ∙ merid (snd Y))

  out-winr-glue : fst (⊙Cof ⊙f) → south' (fst Y) == south
  out-winr-glue = CofiberRec.f
    idp
    (λ y → ! (merid (f (g y))) ∙ merid y)
    (λ x → ! $
      ap (λ w → ! (merid (f w)) ∙ merid (f x))
         (inv x)
      ∙ !-inv-l (merid (f x)))

  module OutWinr = SuspensionRec south south out-winr-glue

  out-winl = OutWinl.f
  out-winr = OutWinr.f

  module Out = WedgeRec {X = ⊙Susp X} {Y = ⊙Susp (⊙Cof ⊙f)}
    out-winl out-winr idp

  out = Out.f

  out-into : ∀ σy → out (into σy) == σy
  out-into = Suspension-elim
    (! (merid (snd Y)))
    idp
    (↓-∘=idf-from-square out into ∘ λ y →
      (ap (ap out) (Into.merid-β y)
       ∙ ap-∙ out (! (ap winl (merid (g y))))
                  (wglue ∙ ap winr (merid (cfcod y)))
       ∙ part₁ y
         ∙2 (ap-∙ out wglue (ap winr (merid (cfcod y)))
             ∙ Out.glue-β ∙2 part₂ y))
      ∙v⊡ square-lemma (merid (snd Y)) (merid (f (g y))) (merid y))
    where
    part₁ : (y : fst Y) → ap out (! (ap winl (merid (g y))))
                       == ! (merid (snd Y)) ∙ merid (f (g y))
    part₁ y =
      ap-! out (ap winl (merid (g y)))
      ∙ ap ! (∘-ap out winl (merid (g y)))
      ∙ ap ! (OutWinl.merid-β (g y))
      ∙ !-∙ (! (merid (f (g y)))) (merid (snd Y))
      ∙ ap (λ w → ! (merid (snd Y)) ∙ w)
           (!-! (merid (f (g y))))

    part₂ : (y : fst Y) → ap out (ap winr (merid (cfcod y)))
                       == ! (merid (f (g y))) ∙ merid y
    part₂ y =
      ∘-ap out winr (merid (cfcod y))
      ∙ OutWinr.merid-β (cfcod y)

    square-lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : x == z) (r : x == w)
      → Square (! p) ((! p ∙ q) ∙ ! q ∙ r) r idp
    square-lemma idp idp idp = ids

  into-out : ∀ w → into (out w) == w
  into-out = Wedge-elim
    into-out-winl
    into-out-winr
    (↓-∘=idf-from-square into out $
      ap (ap into) Out.glue-β
      ∙v⊡ glue-square-lemma (! (ap winr (merid cfbase))) wglue)
    where
    {- Three path induction lemmas to simply some squares -}

    winl-square-lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p q : x == y) (s : x == z) (r t u : z == w) (v : x == y)
      → p == q → r == t → r == u
      → Square (! r ∙ ! s) (! (! p ∙ s ∙ t) ∙ ! v ∙ s ∙ u) q (! r ∙ ! s ∙ v)
    winl-square-lemma idp .idp idp idp .idp .idp v idp idp idp =
      ∙-unit-r _ ∙v⊡ rt-square v

    winr-square-lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p q u : x == y) (r t : z == w) (s : z == x)
      → p == q → r == t
      → Square (! p) (! (! r ∙ s ∙ q) ∙ ! t ∙ s ∙ u) u idp
    winr-square-lemma idp .idp u idp .idp idp idp idp = vid-square

    glue-square-lemma : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : z == y)
      → Square (p ∙ ! q) idp q p
    glue-square-lemma idp idp = ids

    into-out-winl : ∀ σx → into (out (winl σx)) == winl σx
    into-out-winl = Suspension-elim
      (! (ap winr (merid cfbase)) ∙ ! wglue)
      (! (ap winr (merid cfbase)) ∙ ! wglue
       ∙ ap winl (merid (g (snd Y))))
      (↓-='-from-square ∘ λ x →
        (ap-∘ into out-winl (merid x)
         ∙ ap (ap into) (OutWinl.merid-β x)
         ∙ ap-∙ into (! (merid (f x))) (merid (snd Y))
         ∙ (ap-! into (merid (f x))
            ∙ ap ! (Into.merid-β (f x)))
           ∙2 Into.merid-β (snd Y))
        ∙v⊡ winl-square-lemma
              (ap winl (merid (g (f x))))
              (ap winl (merid x))
              wglue
              (ap winr (merid cfbase))
              (ap winr (merid (cfcod (f x))))
              (ap winr (merid (cfcod (snd Y))))
              (ap winl (merid (g (snd Y))))
              (ap (ap winl ∘ merid) (inv x))
              (ap (ap winr ∘ merid) (cfglue x))
              (ap (ap winr ∘ merid)
                  (cfglue (snd X) ∙ ap cfcod (snd ⊙f))))

    into-out-winr : ∀ σκ → into (out (winr σκ)) == winr σκ
    into-out-winr = CofPushoutSection.elim {h = λ _ → unit} g inv
      (! (ap winr (merid cfbase)))
      (λ tt → idp)
      (λ tt → transport
        (λ κ → ! (ap winr (merid cfbase)) == idp
               [ (λ σκ → into (out (winr σκ)) == winr σκ) ↓ merid κ ])
        (! (cfglue (snd X)))
        (into-out-winr-coh (f (snd X))))
      into-out-winr-coh
      where
      into-out-winr-coh : (y : fst Y)
        → ! (ap winr (merid cfbase)) == idp
          [ (λ σκ → into (out (winr σκ)) == winr σκ) ↓ merid (cfcod y) ]
      into-out-winr-coh y = ↓-='-from-square $
        (ap-∘ into out-winr (merid (cfcod y))
         ∙ ap (ap into) (OutWinr.merid-β (cfcod y))
         ∙ ap-∙ into (! (merid (f (g y)))) (merid y)
         ∙ (ap-! into (merid (f (g y)))
            ∙ ap ! (Into.merid-β (f (g y))))
           ∙2 Into.merid-β y)
        ∙v⊡ winr-square-lemma
              (ap winr (merid cfbase))
              (ap winr (merid (cfcod (f (g y)))))
              (ap winr (merid (cfcod y)))
              (ap winl (merid (g (f (g y)))))
              (ap winl (merid (g y)))
              wglue
              (ap (ap winr ∘ merid) (cfglue (g y)))
              (ap (ap winl ∘ merid) (inv (g y)))

  eq : fst (⊙Susp Y) ≃ fst (⊙Susp X ⊙∨ ⊙Susp (⊙Cof ⊙f))
  eq = equiv into out into-out out-into
