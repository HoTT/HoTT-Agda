{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver

module cohomology.MayerVietoris {i} where

{- Mayer-Vietoris Sequence: Given a span X ←f– Z –g→ Y, the cofiber space
   of the natural map [reglue : X ∨ Y → X ⊔_Z Y] (defined below) is equivalent
   to the suspension of Z. -}

{- Relevant functions -}
module MayerVietorisFunctions (ps : Ptd-Span {i} {i} {i}) where

  open Ptd-Span ps


  module Reglue = WedgeRec
    {X = Ptd-Span.X ps} {Y = Ptd-Span.Y ps} {C = fst (Ptd-Pushout ps)}
    left right (! (ap left (snd f)) ∙ glue (snd Z) ∙' ap right (snd g))

  reglue : Wedge X Y → fst (Ptd-Pushout ps)
  reglue = Reglue.f

  ptd-reglue : fst (Ptd-Wedge X Y ∙→ Ptd-Pushout ps)
  ptd-reglue = (reglue , idp)


  module ExtractGlue = PushoutRec {d = ptd-span-out ps} {D = Suspension (fst Z)}
    (λ _ → north _) (λ _ → south _) (merid _)

  extract-glue = ExtractGlue.f

  ptd-extract-glue : fst (Ptd-Pushout ps ∙→ Ptd-Susp Z)
  ptd-extract-glue = (extract-glue , idp)


{- We use path induction (via [ptd-pushout-J]) to assume that the
   basepoint preservation paths of the span maps are [idp]. The module
   [Base] contains the proof of the theorem for this case. -}
module MayerVietorisBase
  {A B : Type i} (Z : Ptd i) (f : fst Z → A) (g : fst Z → B) where

  X = ∙[ A , f (snd Z) ]
  Y = ∙[ B , g (snd Z) ]
  ps = ptd-span X Y Z (f , idp) (g , idp)
  F : fst (Z ∙→ X)
  F = (f , idp)
  G : fst (Z ∙→ Y)
  G = (g , idp)

  open MayerVietorisFunctions ps

  {- Definition of the maps
       into : Cofiber reglue → ΣZ
       out  : ΣZ → Cofiber reglue
   -}

  private
    into-glue-square :
      Square idp idp (ap (extract-glue ∘ reglue) wglue) (merid _ (snd Z))
    into-glue-square =
      connection ⊡v∙
      ! (ap-∘ extract-glue reglue wglue ∙ ap (ap extract-glue) (Reglue.glue-β tt)
         ∙ ExtractGlue.glue-β (snd Z))

    module IntoGlue = WedgeElim {P = λ xy → north _ == extract-glue (reglue xy)}
      (λ _ → idp)
      (λ _ → merid _ (snd Z))
      (↓-cst=app-from-square into-glue-square)

    into-glue = IntoGlue.f

  module Into = CofiberRec reglue (north _) extract-glue into-glue

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
      ⊡v∙ (∘-ap into (cfcod _) (glue z) ∙ ExtractGlue.glue-β z)

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
      Square (cfglue reglue (winl (f z))) (ap (out ∘ extract-glue) (glue z))
             (ap (cfcod _) (glue z)) (cfglue _ (winr (g z)))
    out-into-cod-square z =
      (ap-∘ out extract-glue (glue z)
        ∙ ap (ap out) (ExtractGlue.glue-β z) ∙ Out.glue-β z)
      ∙v⊡ out-square z

    module OutIntoCod = PushoutElim
      {d = ptd-span-out ps} {P = λ γ → out (into (cfcod _ γ)) == cfcod _ γ}
      (λ x → cfglue _ (winl x))
      (λ y → cfglue _ (winr y))
      (λ z → ↓-='-from-square (out-into-cod-square z))

    out-into-cod = OutIntoCod.f

  {- Cube move lemma for the left inverse coherence. This is used to
     build up a right square (in this case starting from a cube filler)  -}
  private
    square-push-rb : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == b} {p₁₋ : a₁₀ == a₁₁}
      (q : a₁₁ == b) (sq : Square p₀₋ p₋₀ p₋₁ (p₁₋ ∙ q))
      → Square p₀₋ p₋₀ (p₋₁ ∙' ! q) p₁₋
    square-push-rb {p₁₋ = idp} idp sq = sq

    cube-lemma : ∀ {i} {A : Type i}
      {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ b₀ b₁ : A}
      {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
      {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
      {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

      {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
      {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
      (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

      {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == b₀ {-a₀₁₁-}}
      {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == b₁ {-a₁₁₁-}}
      {q₀₋ : a₀₁₁ == b₀} {q₋₁ : b₀ == b₁} {q₁₋ : a₁₁₁ == b₁}
      {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ (p₀₋₁ ∙ q₀₋)} -- back
      {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
      {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ q₋₁} -- bottom
      {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ (p₁₋₁ ∙ q₁₋)} -- front
      (sq' : Square q₀₋ p₋₁₁ q₋₁ q₁₋)
      (cu : Cube sq₋₋₀ sq₋₋₁ (square-push-rb q₀₋ sq₀₋₋)
                 sq₋₀₋ (sq₋₁₋ ⊡h' !□h (square-symmetry sq'))
                 (square-push-rb q₁₋ sq₁₋₋))
      → Cube sq₋₋₀ (sq₋₋₁ ⊡v sq') sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    cube-lemma sq₋₋₁ ids cu = cube-lemma' sq₋₋₁ cu
      where
      cube-lemma' : ∀ {i} {A : Type i}
        {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
        {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

        {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
        {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
        (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

        {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
        {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ (p₀₋₁ ∙ idp)} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ (p₁₋₁ ∙ idp)} -- front
        (cu : Cube sq₋₋₀ sq₋₋₁ (square-push-rb idp sq₀₋₋) sq₋₀₋
                   (sq₋₁₋ ⊡h' !□h (square-symmetry vid-square))
                   (square-push-rb idp sq₁₋₋))
        → Cube sq₋₋₀ (sq₋₋₁ ⊡v vid-square) sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
      cube-lemma' ids cu = cu

  {- Proving the coherence term for the left inverse. This means proving
     [(w : Wedge X Y) → Square idp (ap out (ap into (glue w)))
                               (cfglue _ w) (out-into-cod (reglue w))]
  -}

  private
    out-into-sql : (x : fst X) → Square idp (ap out (into-glue (winl x)))
                                        (cfglue _ (winl x)) (cfglue _ (winl x))
    out-into-sql x = connection

    out-into-fill : Σ (Square idp (ap out (glue (snd Z))) idp idp) (λ sq →
      Cube (out-into-sql (snd X)) sq
           (natural-square' (λ _ → idp) wglue)
           (natural-square' (ap out ∘ into-glue) wglue)
           (natural-square' (cfglue _) wglue
             ⊡h' !□h (square-symmetry connection))
           (square-push-rb (cfglue _ (winr (snd Y)))
             (natural-square' (out-into-cod ∘ reglue) wglue)))
    out-into-fill = fill-cube-right _ _ _ _ _


    out-into-fill-square = fst out-into-fill
    out-into-fill-cube = snd out-into-fill

    {- [out-into-fill-square] is chosen so that we can prove
       [out-into-sql == out-into-sqr [ ⋯ ↓ ⋯ ]];
       this is proven by massaging [out-into-fill-cube] into the right shape.
       The trick is that the type of [out-into-fill-square] is independent of
       [y], so we can pick it to give the right result at the basepoint.
    -}
    out-into-sqr : (y : fst Y)
      → Square idp (ap out (into-glue (winr y)))
               (cfglue _ (winr y)) (cfglue _ (winr y))
    out-into-sqr y = out-into-fill-square ⊡v connection

  out-into : ∀ κ → out (into κ) == κ
  out-into = Cofiber-elim reglue
    idp out-into-cod
    (λ w → ↓-∘=idf-from-square out into $
       ap (ap out) (Into.glue-β w) ∙v⊡
         Wedge-elim
           {P = λ w → Square idp (ap out (into-glue w))
                             (cfglue _ w) (out-into-cod (reglue w))}
           out-into-sql
           out-into-sqr
           (cube-to-↓-square $
             cube-lemma out-into-fill-square connection $
               out-into-fill-cube)
           w)

  {- equivalence and paths -}

  eq : Cofiber reglue ≃ Suspension (fst Z)
  eq = equiv into out into-out out-into

  path : Cofiber reglue == Suspension (fst Z)
  path = ua eq

  ptd-path : Ptd-Cof ptd-reglue == Ptd-Susp Z
  ptd-path = ptd-ua eq idp

  {- Transporting [cfcod reglue] over the equivalence -}

  cfcod-over : ptd-cfcod ptd-reglue == ptd-extract-glue
         [ (λ W → fst (Ptd-Pushout ps ∙→ W)) ↓ ptd-path ]
  cfcod-over =
    codomain-over-ptd-equiv (ptd-cfcod ptd-reglue) eq idp ▹ lemma
    where
    lemma : (into , idp) ∘ptd ptd-cfcod ptd-reglue == ptd-extract-glue
    lemma = pair= idp $
      ap into (! (cfglue reglue (winl (snd X)))) ∙ idp
        =⟨ ap-! into (cfglue reglue (winl (snd X))) |in-ctx (λ w → w ∙ idp) ⟩
      ! (ap into (cfglue reglue (winl (snd X)))) ∙ idp
        =⟨ Into.glue-β (winl (snd X)) |in-ctx (λ w → ! w ∙ idp) ⟩
      idp ∎

{- Main results -}
module _ (ps : Ptd-Span {i} {i} {i}) where

  open Ptd-Span ps
  open MayerVietorisFunctions public

  mayer-vietoris-equiv : Cofiber (reglue ps) ≃ Suspension (fst Z)
  mayer-vietoris-equiv = ptd-pushout-J
    (λ ps' → Cofiber (reglue ps') ≃ Suspension (fst (Ptd-Span.Z ps')))
    MayerVietorisBase.eq ps

  mayer-vietoris-path : Cofiber (reglue ps) == Suspension (fst Z)
  mayer-vietoris-path = ua mayer-vietoris-equiv

  mayer-vietoris-ptd-path : Ptd-Cof (ptd-reglue ps) == Ptd-Susp Z
  mayer-vietoris-ptd-path = ptd-pushout-J
    (λ ps' → Ptd-Cof (ptd-reglue ps') == Ptd-Susp (Ptd-Span.Z ps'))
    MayerVietorisBase.ptd-path ps

module _ (ps : Ptd-Span {i} {i} {i}) where

  open Ptd-Span ps

  mayer-vietoris-cfcod-over : ptd-cfcod (ptd-reglue ps) == ptd-extract-glue ps
    [ (λ W → fst (Ptd-Pushout ps ∙→ W)) ↓ mayer-vietoris-ptd-path ps ]
  mayer-vietoris-cfcod-over = ptd-pushout-J
    (λ ps' → ptd-cfcod (ptd-reglue ps') == ptd-extract-glue ps'
      [ (λ W → fst (Ptd-Pushout ps' ∙→ W)) ↓ mayer-vietoris-ptd-path ps' ])
    MayerVietorisBase.cfcod-over ps
