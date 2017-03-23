{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.CofPushoutSection

module cohomology.MayerVietoris {i} where

{- Mayer-Vietoris Sequence: Given a span X ←f– Z –g→ Y, the cofiber space
   of the natural map [reglue : X ∨ Y → X ⊔_Z Y] (defined below) is equivalent
   to the suspension of Z. -}

{- Relevant functions -}
module MayerVietorisFunctions (ps : ⊙Span {i} {i} {i}) where

  open ⊙Span ps


  module Reglue = ⊙WedgeRec (⊙left ps) (⊙right ps)

  reglue : X ∨ Y → de⊙ (⊙Pushout ps)
  reglue = Reglue.f

  ⊙reglue : X ⊙∨ Y ⊙→ ⊙Pushout ps
  ⊙reglue = Reglue.⊙f

  module MVDiff = SuspRec {C = Susp (X ∨ Y)}
    north
    north
    (λ z → merid (winl (fst f z)) ∙ ! (merid (winr (fst g z))))

  mv-diff : Susp (de⊙ Z) → Susp (X ∨ Y)
  mv-diff = MVDiff.f

  ⊙mv-diff : ⊙Susp Z ⊙→ ⊙Susp (X ⊙∨ Y)
  ⊙mv-diff = (mv-diff , idp)

{- We use path induction (via [⊙pushout-J]) to assume that the
   basepoint preservation paths of the span maps are [idp]. The module
   [MayerVietorisBase] contains the proof of the theorem for this case. -}
module MayerVietorisBase
  {A B : Type i} (Z : Ptd i) (f : de⊙ Z → A) (g : de⊙ Z → B) where

  X = ⊙[ A , f (pt Z) ]
  Y = ⊙[ B , g (pt Z) ]
  ps = ⊙span X Y Z (f , idp) (g , idp)
  F : Z ⊙→ X
  F = (f , idp)
  G : Z ⊙→ Y
  G = (g , idp)

  open MayerVietorisFunctions ps

  {- Definition of the maps
       into : Cofiber reglue → ΣZ
       out  : ΣZ → Cofiber reglue
   -}

  private
    into-glue-square :
      Square idp idp (ap (extract-glue ∘ reglue) wglue) (merid (pt Z))
    into-glue-square =
      connection ⊡v∙
      ! (ap-∘ extract-glue reglue wglue
         ∙ ap (ap extract-glue) (Reglue.glue-β ∙ !-! (glue (pt Z)))
         ∙ ExtractGlue.glue-β (pt Z))

    module IntoGlue = WedgeElim {P = λ xy → north == extract-glue (reglue xy)}
      (λ _ → idp)
      (λ _ → merid (pt Z))
      (↓-cst=app-from-square into-glue-square)

    into-glue = IntoGlue.f

  module Into = CofiberRec {f = reglue} north extract-glue into-glue

  private
    out-glue-and-square : (z : de⊙ Z)
      → Σ (cfbase' reglue == cfbase' reglue)
          (λ p → Square (cfglue (winl (f z))) p
                   (ap cfcod (glue z)) (cfglue (winr (g z))))
    out-glue-and-square z = fill-square-top _ _ _

    out-glue = fst ∘ out-glue-and-square
    out-square = snd ∘ out-glue-and-square

  module Out = SuspRec {C = Cofiber reglue}
    cfbase
    cfbase
    out-glue

  into = Into.f
  out = Out.f

  abstract
    {- [out] is a right inverse for [into] -}

    private
      into-out-sq : (z : de⊙ Z) →
        Square idp (ap into (ap out (merid z))) (merid z) (merid (pt Z))
      into-out-sq z =
        (ap (ap into) (Out.merid-β z) ∙v⊡
          (! (Into.glue-β (winl (f z)))) ∙h⊡
            ap-square into (out-square z)
          ⊡h∙ (Into.glue-β (winr (g z))))
        ⊡v∙ (∘-ap into cfcod (glue z) ∙ ExtractGlue.glue-β z)

    into-out : ∀ σ → into (out σ) == σ
    into-out = Susp-elim
      idp
      (merid (pt Z))
      (λ z → ↓-∘=idf-from-square into out (into-out-sq z))


    {- [out] is a left inverse for [into] -}

    {- [out] is left inverse on codomain part of cofiber space,
     - i.e. [out (into (cfcod γ)) == cfcod γ] -}

    private
      out-into-cod-square : (z : de⊙ Z) →
        Square (cfglue' reglue (winl (f z)))
               (ap (out ∘ extract-glue {s = ⊙Span-to-Span ps}) (glue z))
               (ap cfcod (glue z)) (cfglue (winr (g z)))
      out-into-cod-square z =
        (ap-∘ out extract-glue (glue z)
          ∙ ap (ap out) (ExtractGlue.glue-β z) ∙ Out.merid-β z)
        ∙v⊡ out-square z

      module OutIntoCod = PushoutElim
        {d = ⊙Span-to-Span ps} {P = λ γ → out (into (cfcod γ)) == cfcod γ}
        (λ x → cfglue (winl x))
        (λ y → cfglue (winr y))
        (λ z → ↓-='-from-square (out-into-cod-square z))

      out-into-cod = OutIntoCod.f

    out-into : ∀ κ → out (into κ) == κ
    out-into = CofPushoutSection.elim
      (λ _ → unit) (λ _ → idp)
      idp
      out-into-cod
      (↓-='-from-square ∘ λ x →
        (ap-∘ out into (cfglue (winl x))
         ∙ ap (ap out) (Into.glue-β (winl x)))
        ∙v⊡ connection
        ⊡v∙ ! (ap-idf (glue (winl x))))
      (↓-='-from-square ∘ λ y →
        (ap-∘ out into (cfglue (winr y))
         ∙ ap (ap out) (Into.glue-β (winr y))
         ∙ Out.merid-β (pt Z)
         ∙ square-top-unique (out-square (pt Z))
             (! (ap-cst cfbase wglue) ∙v⊡
              natural-square cfglue wglue
              ⊡v∙ (ap-∘ cfcod reglue wglue
                   ∙ ap (ap cfcod) (Reglue.glue-β ∙ !-! (glue (pt Z))))))
        ∙v⊡ connection
        ⊡v∙ ! (ap-idf (glue (winr y))))

  {- equivalence and path -}

  eq : Cofiber reglue ≃ Susp (de⊙ Z)
  eq = equiv into out into-out out-into

  ⊙eq : ⊙Cofiber ⊙reglue ⊙≃ ⊙Susp Z
  ⊙eq = ≃-to-⊙≃ eq idp

  {- Transporting [cfcod reglue] over the equivalence -}

  cfcod-comm-sqr : CommSquare (cfcod' reglue) extract-glue (idf _) into
  cfcod-comm-sqr = comm-sqr λ _ → idp

  {- Transporting [extract-glue] over the equivalence. -}

  ext-comm-sqr : CommSquare extract-glue mv-diff into (idf _)
  ext-comm-sqr = comm-sqr $ ! ∘ fn-lemma
    where
    fn-lemma : ∀ κ → mv-diff (into κ) == extract-glue κ
    fn-lemma = CofPushoutSection.elim
      (λ _ → unit) (λ _ → idp)
      idp
      (Pushout-elim
        (λ x → merid (winl x))
        (λ y → merid (winr y))
        (↓-='-from-square ∘ λ z →
          (ap-∘ mv-diff extract-glue (glue z)
           ∙ ap (ap mv-diff) (ExtractGlue.glue-β z)
           ∙ MVDiff.merid-β z)
          ∙v⊡ (lt-square (merid (winl (f z)))
               ⊡h rt-square (merid (winr (g z))))
          ⊡v∙ ! (ap-cst south (glue z))))
      (↓-='-from-square ∘ λ x →
        (ap-∘ mv-diff into (cfglue (winl x))
         ∙ ap (ap mv-diff) (Into.glue-β (winl x)))
        ∙v⊡ connection
        ⊡v∙ ! (ExtractGlue.glue-β (winl x)))
      (↓-='-from-square ∘ λ y →
        (ap-∘ mv-diff into (cfglue (winr y))
         ∙ ap (ap mv-diff) (Into.glue-β (winr y))
         ∙ MVDiff.merid-β (pt Z)
         ∙ ap (λ w → merid w ∙ ! (merid (winr (g (pt Z))))) wglue
         ∙ !-inv-r (merid (winr (g (pt Z)))))
        ∙v⊡ connection
        ⊡v∙ ! (ExtractGlue.glue-β (winr y)))

{- Main results -}
module MayerVietoris (ps : ⊙Span {i} {i} {i}) where

  private
    record Results (ps : ⊙Span {i} {i} {i}) : Type (lsucc i) where
      open ⊙Span ps
      open MayerVietorisFunctions ps public
      field
        ⊙eq : ⊙Cofiber ⊙reglue ⊙≃ ⊙Susp Z
        cfcod-comm-sqr : CommSquare
          (cfcod' reglue) extract-glue
          (idf _) (fst (⊙–> ⊙eq))
        ext-comm-sqr : CommSquare
          extract-glue mv-diff (fst (⊙–> ⊙eq)) (idf _)

    results : Results ps
    results = ⊙pushout-J Results base-results ps
      where
      base-results : ∀ {A} {B} Z (f : de⊙ Z → A) (g : de⊙ Z → B) →
        Results (⊙span _ _ Z (f , idp) (g , idp))
      base-results Z f g = record {
        ⊙eq = ⊙eq;
        cfcod-comm-sqr = cfcod-comm-sqr;
        ext-comm-sqr = ext-comm-sqr}
        where open MayerVietorisBase Z f g

  open Results results public
