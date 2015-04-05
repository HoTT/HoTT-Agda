{-# OPTIONS --without-K #-}

open import HoTT
open import lib.cubical.elims.CofPushoutSection

{- If f : X → Y is a section, then ΣY ≃ ΣX ∨ ΣCof(f) -}

module homotopy.SuspSectionDecomp
  {i j} {X : Ptd i} {Y : Ptd j} (⊙f : fst (X ⊙→ Y))
  (g : fst Y → fst X) (inv : ∀ x → g (fst ⊙f x) == x)
  where

module SuspSectionDecomp where

  private
    f = fst ⊙f

  module Into = SuspensionRec (fst Y) {C = fst (⊙Susp X ⊙∨ ⊙Susp (⊙Cof ⊙f))}
    (winl (south _))
    (winr (south _))
    (λ y → ! (ap winl (merid _ (g y))) ∙ wglue ∙ ap winr (merid _ (cfcod _ y)))

  into = Into.f

  module OutWinl = SuspensionRec (fst X)
    (south _) (south _)
    (λ x → ! (merid _ (f x)) ∙ merid _ (snd Y))

  out-winr-glue : fst (⊙Cof ⊙f) → south (fst Y) == south (fst Y)
  out-winr-glue = CofiberRec.f _
    idp
    (λ y → ! (merid _ (f (g y))) ∙ merid _ y)
    (λ x → ! $
      ap (λ w → ! (merid _ (f w)) ∙ merid _ (f x))
         (inv x)
      ∙ !-inv-l (merid _ (f x)))

  module OutWinr = SuspensionRec (fst (⊙Cof ⊙f))
    (south _) (south _) out-winr-glue

  out-winl = OutWinl.f
  out-winr = OutWinr.f

  module Out = WedgeRec {X = ⊙Susp X} {Y = ⊙Susp (⊙Cof ⊙f)}
    out-winl out-winr idp

  out = Out.f

  out-into : ∀ σy → out (into σy) == σy
  out-into = Suspension-elim _
    (! (merid _ (snd Y)))
    idp
    (↓-∘=idf-from-square out into ∘ λ y →
      (ap (ap out) (Into.glue-β y)
       ∙ ap-∙ out (! (ap winl (merid _ (g y))))
                  (wglue ∙ ap winr (merid _ (cfcod _ y)))
       ∙ part₁ y
         ∙2 (ap-∙ out wglue (ap winr (merid _ (cfcod _ y)))
             ∙ Out.glue-β ∙2 part₂ y))
      ∙v⊡ square-lemma (merid _ (snd Y)) (merid _ (f (g y))) (merid _ y))
    where
    part₁ : (y : fst Y) → ap out (! (ap winl (merid _ (g y))))
                       == ! (merid _ (snd Y)) ∙ merid _ (f (g y))
    part₁ y =
      ap-! out (ap winl (merid _ (g y)))
      ∙ ap ! (∘-ap out winl (merid _ (g y)))
      ∙ ap ! (OutWinl.glue-β (g y))
      ∙ !-∙ (! (merid _ (f (g y)))) (merid _ (snd Y))
      ∙ ap (λ w → ! (merid _ (snd Y)) ∙ w)
           (!-! (merid _ (f (g y))))

    part₂ : (y : fst Y) → ap out (ap winr (merid _ (cfcod _ y)))
                       == ! (merid _ (f (g y))) ∙ merid _ y
    part₂ y =
      ∘-ap out winr (merid _ (cfcod _ y))
      ∙ OutWinr.glue-β (cfcod _ y)

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
      ∙v⊡ glue-square-lemma (! (ap winr (merid _ (cfbase _)))) wglue)
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
    into-out-winl = Suspension-elim _
      (! (ap winr (merid _ (cfbase _))) ∙ ! wglue)
      (! (ap winr (merid _ (cfbase _))) ∙ ! wglue
       ∙ ap winl (merid _ (g (snd Y))))
      (↓-='-from-square ∘ λ x →
        (ap-∘ into out-winl (merid _ x)
         ∙ ap (ap into) (OutWinl.glue-β x)
         ∙ ap-∙ into (! (merid _ (f x))) (merid _ (snd Y))
         ∙ (ap-! into (merid _ (f x))
            ∙ ap ! (Into.glue-β (f x)))
           ∙2 Into.glue-β (snd Y))
        ∙v⊡ winl-square-lemma
              (ap winl (merid _ (g (f x))))
              (ap winl (merid _ x))
              wglue
              (ap winr (merid _ (cfbase _)))
              (ap winr (merid _ (cfcod _ (f x))))
              (ap winr (merid _ (cfcod _ (snd Y))))
              (ap winl (merid _ (g (snd Y))))
              (ap (ap winl ∘ merid _) (inv x))
              (ap (ap winr ∘ merid _) (cfglue _ x))
              (ap (ap winr ∘ merid _)
                  (cfglue _ (snd X) ∙ ap (cfcod _) (snd ⊙f))))

    into-out-winr : ∀ σκ → into (out (winr σκ)) == winr σκ
    into-out-winr = CofPushoutSection.path-elim (λ _ → unit) g inv
      (! (ap winr (merid _ (cfbase _))))
      (λ tt → idp)
      (λ tt → transport
        (λ κ → Square (! (ap winr (merid _ (cfbase _))))
                      (ap (into ∘ out ∘ winr) (merid _ κ))
                      (ap winr (merid _ κ))
                      idp)
        (! (cfglue _ (snd X)))
        (into-out-winr-coh (f (snd X))))
      into-out-winr-coh
      where
      into-out-winr-coh : (y : fst Y)
        → Square (! (ap winr (merid _ (cfbase _))))
                 (ap (into ∘ out ∘ winr) (merid _ (cfcod _ y)))
                 (ap winr (merid _ (cfcod _ y)))
                 idp
      into-out-winr-coh y =
        (ap-∘ into out-winr (merid _ (cfcod _ y))
         ∙ ap (ap into) (OutWinr.glue-β (cfcod _ y))
         ∙ ap-∙ into (! (merid _ (f (g y)))) (merid _ y)
         ∙ (ap-! into (merid _ (f (g y)))
            ∙ ap ! (Into.glue-β (f (g y))))
           ∙2 Into.glue-β y)
        ∙v⊡ winr-square-lemma
              (ap winr (merid _ (cfbase _)))
              (ap winr (merid _ (cfcod _ (f (g y)))))
              (ap winr (merid _ (cfcod _ y)))
              (ap winl (merid _ (g (f (g y)))))
              (ap winl (merid _ (g y)))
              wglue
              (ap (ap winr ∘ merid _) (cfglue _ (g y)))
              (ap (ap winl ∘ merid _) (inv (g y)))

  eq : fst (⊙Susp Y) ≃ fst (⊙Susp X ⊙∨ ⊙Susp (⊙Cof ⊙f))
  eq = equiv into out into-out out-into
