{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver
open import homotopy.elims.CofPushoutSection

module cohomology.MayerVietoris {i} where

{- Mayer-Vietoris Sequence: Given a span X ←f– Z –g→ Y, the cofiber space
   of the natural map [reglue : X ∨ Y → X ⊔_Z Y] (defined below) is equivalent
   to the suspension of Z. -}

{- Relevant functions -}
module MayerVietorisFunctions (ps : ⊙Span {i} {i} {i}) where

  open ⊙Span ps


  module Reglue = WedgeRec
    {X = ⊙Span.X ps} {Y = ⊙Span.Y ps} {C = fst (⊙Pushout ps)}
    left right (! (ap left (snd f)) ∙ glue (snd Z) ∙' ap right (snd g))

  reglue : X ∨ Y → fst (⊙Pushout ps)
  reglue = Reglue.f

  ⊙reglue : fst (X ⊙∨ Y ⊙→ ⊙Pushout ps)
  ⊙reglue = (reglue , idp)

  module MVDiff = SuspensionRec (fst Z) {C = Suspension (X ∨ Y)}
    (north _)
    (north _)
    (λ z → merid _ (winl (fst f z)) ∙ ! (merid _ (winr (fst g z))))

  mv-diff : Suspension (fst Z) → Suspension (X ∨ Y)
  mv-diff = MVDiff.f

  ⊙mv-diff : fst (⊙Susp Z ⊙→ ⊙Susp (X ⊙∨ Y))
  ⊙mv-diff = (mv-diff , idp)

{- We use path induction (via [⊙pushout-J]) to assume that the
   basepoint preservation paths of the span maps are [idp]. The module
   [MayerVietorisBase] contains the proof of the theorem for this case. -}
module MayerVietorisBase
  {A B : Type i} (Z : Ptd i) (f : fst Z → A) (g : fst Z → B) where

  X = ⊙[ A , f (snd Z) ]
  Y = ⊙[ B , g (snd Z) ]
  ps = ⊙span X Y Z (f , idp) (g , idp)
  F : fst (Z ⊙→ X)
  F = (f , idp)
  G : fst (Z ⊙→ Y)
  G = (g , idp)

  open MayerVietorisFunctions ps

  {- Definition of the maps
       into : Cofiber reglue → ΣZ
       out  : ΣZ → Cofiber reglue
   -}

  private
    into-glue-square :
      Square idp idp (ap (ext-glue ∘ reglue) wglue) (merid _ (snd Z))
    into-glue-square =
      connection ⊡v∙
      ! (ap-∘ ext-glue reglue wglue ∙ ap (ap ext-glue) Reglue.glue-β
         ∙ ExtGlue.glue-β (snd Z))

    module IntoGlue = WedgeElim {P = λ xy → north _ == ext-glue (reglue xy)}
      (λ _ → idp)
      (λ _ → merid _ (snd Z))
      (↓-cst=app-from-square into-glue-square)

    into-glue = IntoGlue.f

  module Into = CofiberRec reglue (north _) ext-glue into-glue

  private
    out-glue-and-square : (z : fst Z)
      → Σ (cfbase reglue == cfbase reglue)
          (λ p → Square (cfglue _ (winl (f z))) p
                   (ap (cfcod _) (glue z)) (cfglue _ (winr (g z))))
    out-glue-and-square z = fill-square-top _ _ _

    out-glue = fst ∘ out-glue-and-square
    out-square = snd ∘ out-glue-and-square

  module Out = SuspensionRec (fst Z) {C = Cofiber reglue}
    (cfbase _)
    (cfbase _)
    out-glue

  into = Into.f
  out = Out.f


  {- [out] is a right inverse for [into] -}

  private
    into-out-sq : (z : fst Z) →
      Square idp (ap into (ap out (merid _ z))) (merid _ z) (merid _ (snd Z))
    into-out-sq z =
      (ap (ap into) (Out.glue-β z) ∙v⊡
        (! (Into.glue-β (winl (f z)))) ∙h⊡
          ap-square into (out-square z)
        ⊡h∙ (Into.glue-β (winr (g z))))
      ⊡v∙ (∘-ap into (cfcod _) (glue z) ∙ ExtGlue.glue-β z)

  into-out : ∀ σ → into (out σ) == σ
  into-out = Suspension-elim (fst Z)
    idp
    (merid _ (snd Z))
    (λ z → ↓-∘=idf-from-square into out (into-out-sq z))


  {- [out] is a left inverse for [into] -}

  {- [out] is left inverse on codomain part of cofiber space,
   - i.e. [out (into (cfcod _ γ)) == cfcod _ γ] -}

  private
    out-into-cod-square : (z : fst Z) →
      Square (cfglue reglue (winl (f z)))
             (ap (out ∘ ext-glue {s = ⊙span-out ps}) (glue z))
             (ap (cfcod _) (glue z)) (cfglue _ (winr (g z)))
    out-into-cod-square z =
      (ap-∘ out ext-glue (glue z)
        ∙ ap (ap out) (ExtGlue.glue-β z) ∙ Out.glue-β z)
      ∙v⊡ out-square z

    module OutIntoCod = PushoutElim
      {d = ⊙span-out ps} {P = λ γ → out (into (cfcod _ γ)) == cfcod _ γ}
      (λ x → cfglue _ (winl x))
      (λ y → cfglue _ (winr y))
      (λ z → ↓-='-from-square (out-into-cod-square z))

    out-into-cod = OutIntoCod.f

  out-into : ∀ κ → out (into κ) == κ
  out-into = CofPushoutSection.elim reglue
    (λ _ → unit) (λ _ → idp)
    idp
    out-into-cod
    (↓-='-from-square ∘ λ x →
      (ap-∘ out into (cfglue _ (winl x))
       ∙ ap (ap out) (Into.glue-β (winl x)))
      ∙v⊡ connection
      ⊡v∙ ! (ap-idf (glue (winl x))))
    (↓-='-from-square ∘ λ y →
      (ap-∘ out into (cfglue _ (winr y))
       ∙ ap (ap out) (Into.glue-β (winr y))
       ∙ Out.glue-β (snd Z)
       ∙ square-top-unique (out-square (snd Z))
           (! (ap-cst (cfbase _) wglue) ∙v⊡
            natural-square (cfglue _) wglue
            ⊡v∙ (ap-∘ (cfcod _) reglue wglue
                 ∙ ap (ap (cfcod _)) (Reglue.glue-β))))
      ∙v⊡ connection
      ⊡v∙ ! (ap-idf (glue (winr y))))

  {- equivalence and paths -}

  eq : Cofiber reglue ≃ Suspension (fst Z)
  eq = equiv into out into-out out-into

  path : Cofiber reglue == Suspension (fst Z)
  path = ua eq

  ⊙path : ⊙Cof ⊙reglue == ⊙Susp Z
  ⊙path = ⊙ua eq idp

  {- Transporting [cfcod reglue] over the equivalence -}

  cfcod-over : cfcod reglue == ext-glue
              [ (λ W → fst (⊙Pushout ps) → fst W) ↓ ⊙path ]
  cfcod-over = ↓-cst2-in _ _ $ codomain-over-equiv _ _

  {- Transporting [ext-glue] over the equivalence. -}

  ext-over : ext-glue == mv-diff
             [ (λ W → fst W → fst (⊙Susp (X ⊙∨ Y))) ↓ ⊙path ]
  ext-over = ↓-cst2-in _ _ $ λ= fn-lemma ◃ domain-over-equiv _ _
    where
    fn-lemma : ∀ κ → ext-glue κ == mv-diff (into κ)
    fn-lemma = CofPushoutSection.elim reglue
      (λ _ → unit) (λ _ → idp)
      idp
      (Pushout-elim
        (λ x → ! (merid _ (winl x)))
        (λ y → ! (merid _ (winr y)))
        (λ z → ↓-='-from-square $
          ap-cst (south _) (glue z) ∙v⊡
            (bl-square (merid _ (winl (f z))) ⊡h connection)
          ⊡v∙ ! (ap-∘ mv-diff ext-glue (glue z)
                 ∙ ap (ap mv-diff) (ExtGlue.glue-β z)
                 ∙ MVDiff.glue-β z)))
      (↓-='-from-square ∘ λ x →
        ExtGlue.glue-β (winl x)
        ∙v⊡ tr-square (merid _ (winl x))
         ⊡v∙ ! (ap-∘ mv-diff into (cfglue _ (winl x))
                ∙ ap (ap mv-diff) (Into.glue-β (winl x))))
      (↓-='-from-square ∘ λ y →
        ExtGlue.glue-β (winr y)
        ∙v⊡ tr-square (merid _ (winr y))
        ⊡v∙ ! (ap-∘ mv-diff into (cfglue _ (winr y))
              ∙ ap (ap mv-diff) (Into.glue-β (winr y))
              ∙ MVDiff.glue-β (snd Z)
              ∙ ap (λ w → merid _ w ∙ ! (merid _ (winr (g (snd Z)))))
                   wglue
              ∙ !-inv-r (merid _ (winr (g (snd Z))))))

{- Main results -}
module MayerVietoris (ps : ⊙Span {i} {i} {i}) where

  private
    record Results (ps : ⊙Span {i} {i} {i}) : Type (lsucc i) where
      open ⊙Span ps
      open MayerVietorisFunctions ps public
      field
        eq : Cofiber reglue ≃ Suspension (fst Z)
        path : Cofiber reglue == Suspension (fst Z)
        ⊙path : ⊙Cof ⊙reglue == ⊙Susp Z
        cfcod-over : cfcod reglue == ext-glue
                     [ (λ W → fst (⊙Pushout ps) → fst W) ↓ ⊙path ]
        ext-over : ext-glue == mv-diff
                   [ (λ W → fst W → fst (⊙Susp (X ⊙∨ Y))) ↓ ⊙path ]

    results : Results ps
    results = ⊙pushout-J Results base-results ps
      where
      base-results : ∀ {A} {B} Z (f : fst Z → A) (g : fst Z → B) →
        Results (⊙span _ _ Z (f , idp) (g , idp))
      base-results Z f g = record {
        eq = eq;
        path = path;
        ⊙path = ⊙path;
        cfcod-over = cfcod-over;
        ext-over = ext-over}
        where open MayerVietorisBase Z f g

    open Results results public
