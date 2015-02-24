{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.FunctionOver

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
   [Base] contains the proof of the theorem for this case. -}
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

  {- Cube move lemma for the left inverse coherence. This is used to
     build up a right square (in this case starting from a cube filler)  -}
  private
    square-push-rb : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == b}
      (q : b == a₁₁) (sq : Square p₀₋ p₋₀ p₋₁ (p₁₋ ∙ q))
      → Square p₀₋ p₋₀ (p₋₁ ∙' ! q) p₁₋
    square-push-rb {p₁₋ = idp} idp sq = sq

    right-from-bot-lemma : ∀ {i} {A : Type i}
      {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ b₀ b₁ : A}
      {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
      {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
      {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

      {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
      {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
      (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

      {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == b₀}
      {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == b₁}
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
    right-from-bot-lemma sq₋₋₁ ids cu = right-from-bot-lemma' sq₋₋₁ cu
      where
      right-from-bot-lemma' : ∀ {i} {A : Type i}
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
      right-from-bot-lemma' ids cu = cu

  {- Proving the coherence term for the left inverse. This means proving
     [(w : X ∨ Y) → Square idp (ap out (ap into (glue w)))
                               (cfglue _ w) (out-into-cod (reglue w))]
  -}

  private
    out-into-sql : (x : fst X) → Square idp (ap out (into-glue (winl x)))
                                        (cfglue _ (winl x)) (cfglue _ (winl x))
    out-into-sql x = connection

    out-into-fill : Σ (Square idp (ap out (glue (snd Z))) idp idp) (λ sq →
      Cube (out-into-sql (snd X)) sq
           (natural-square (λ _ → idp) wglue)
           (natural-square (ap out ∘ into-glue) wglue)
           (natural-square (cfglue _) wglue
             ⊡h' !□h (square-symmetry connection))
           (square-push-rb (cfglue _ (winr (snd Y)))
             (natural-square (out-into-cod ∘ reglue) wglue)))
    out-into-fill = fill-cube-right _ _ _ _ _

    {- [fst out-into-fill] is chosen so that we can prove
       [out-into-sql == out-into-sqr [ ⋯ ↓ ⋯ ]];
       this is proven by massaging [out-into-fill-cube] into the right shape.
       The trick is that the type of [out-into-fill-square] is independent of
       [y], so we can pick it to give the right result at the basepoint.
    -}
    out-into-sqr : (y : fst Y)
      → Square idp (ap out (into-glue (winr y)))
               (cfglue _ (winr y)) (cfglue _ (winr y))
    out-into-sqr y = fst out-into-fill ⊡v connection

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
             right-from-bot-lemma (fst out-into-fill) connection $
               (snd out-into-fill))
           w)

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
    where
    lemma : (into , idp) ⊙∘ ⊙cfcod ⊙reglue == ⊙ext-glue
    lemma = pair= idp $
      ap into (! (cfglue reglue (winl (snd X)))) ∙ idp
        =⟨ ap-! into (cfglue reglue (winl (snd X))) |in-ctx (λ w → w ∙ idp) ⟩
      ! (ap into (cfglue reglue (winl (snd X)))) ∙ idp
        =⟨ Into.glue-β (winl (snd X)) |in-ctx (λ w → ! w ∙ idp) ⟩
      idp ∎

  {- Transporting [ext-glue] over the equivalence. Uses the same sort of
   - cube technique as in the proof of [⊙path]. -}

  private
    square-push-rt : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : b == a₁₁}
      (q : a₁₀ == b) (sq : Square p₀₋ p₋₀ p₋₁ (q ∙' p₁₋))
      → Square p₀₋ (p₋₀ ∙' q) p₋₁ p₁₋
    square-push-rt {p₁₋ = idp} idp sq = sq

    right-from-top-lemma : ∀ {i} {A : Type i}
      {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ b₀ b₁ : A}
      {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
      {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
      {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

      {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
      {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
      (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

      {p₀₀₋ : a₀₀₀ == b₀ {-a₀₀₁-}} {p₀₁₋ : a₀₁₀ == a₀₁₁}
      {p₁₀₋ : a₁₀₀ == b₁ {-a₁₀₁-}} {p₁₁₋ : a₁₁₀ == a₁₁₁}
      {q₀₋ : b₀ == a₀₀₁} {q₋₀ : b₀ == b₁} {q₁₋ : b₁ == a₁₀₁}
      {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ (q₀₋ ∙' p₀₋₁)} -- back
      {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ q₋₀} -- top
      {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
      {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ (q₁₋ ∙' p₁₋₁)} -- front
      (sq' : Square q₀₋ q₋₀ p₋₀₁ q₁₋)
      (cu : Cube sq₋₋₀ sq₋₋₁ (square-push-rt q₀₋ sq₀₋₋)
                 (sq₋₀₋ ⊡h' square-symmetry sq') sq₋₁₋
                 (square-push-rt q₁₋ sq₁₋₋))
      → Cube sq₋₋₀ (sq' ⊡v' sq₋₋₁) sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    right-from-top-lemma sq₋₋₁ ids cu = right-from-top-lemma' sq₋₋₁ cu
      where
      right-from-top-lemma' : ∀ {i} {A : Type i}
        {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
        {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

        {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
        {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
        (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

        {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
        {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ (idp ∙' p₀₋₁)} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ (idp ∙' p₁₋₁)} -- front
        (cu : Cube sq₋₋₀ sq₋₋₁ (square-push-rt idp sq₀₋₋)
                   (sq₋₀₋ ⊡h' square-symmetry vid-square) sq₋₁₋
                   (square-push-rt idp sq₁₋₋))
        → Cube sq₋₋₀ (vid-square ⊡v' sq₋₋₁) sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
      right-from-top-lemma' ids cu = cu

  ext-over : ext-glue == mv-diff
             [ (λ W → fst W → fst (⊙Susp (X ⊙∨ Y))) ↓ ⊙path ]
  ext-over = ↓-cst2-in _ _ $ λ= fn-lemma ◃ domain-over-equiv _ _
    where
    fn-lemma : ∀ κ → ext-glue κ == mv-diff (into κ)
    fn-lemma = Cofiber-elim reglue
      idp fn-cod
      (λ w → ↓-='-from-square $
        ExtGlue.glue-β w ∙v⊡
          fn-coh w
        ⊡v∙ ! (ap-∘ mv-diff into (glue w) ∙ ap (ap mv-diff) (Into.glue-β w)))
      where
      fn-cod : (γ : fst (⊙Pushout ps))
        → ext-glue (cfcod reglue γ) == mv-diff (ext-glue γ)
      fn-cod = Pushout-elim
        (λ x → ! (merid _ (winl x)))
        (λ y → ! (merid _ (winr y)))
        (λ z → ↓-='-from-square $
          ap-cst (south _) (glue z) ∙v⊡
            (bl-square (merid _ (winl (f z))) ⊡h connection)
          ⊡v∙ ! (ap-∘ mv-diff ext-glue (glue z)
                 ∙ ap (ap mv-diff) (ExtGlue.glue-β z)
                 ∙ MVDiff.glue-β z))

      fn-fill : Σ (Square idp idp (ap mv-diff (merid _ (snd Z))) idp)
        (λ sq → Cube (tr-square (merid _ (winl (snd X)))) sq
                     (natural-square (λ _ → idp) wglue)
                     (natural-square (merid _) wglue
                       ⊡h' square-symmetry (tr-square (merid _ (winr (snd Y)))))
                     (natural-square (ap mv-diff ∘ into-glue) wglue)
                     (square-push-rt (! (merid _ (winr (snd Y))))
                       (natural-square (fn-cod ∘ reglue) wglue)))
      fn-fill = fill-cube-right _ _ _ _ _

      fn-coh : (w : X ∨ Y)
        → Square idp (merid _ w) (ap mv-diff (into-glue w)) (fn-cod (reglue w))
      fn-coh = Wedge-elim
        (λ x → tr-square (merid _ (winl x)))
          (λ y → tr-square (merid _ (winr y)) ⊡v' (fst fn-fill))
        (cube-to-↓-square $ right-from-top-lemma
          (fst fn-fill)
          (tr-square (merid _ (winr (snd Y))))
          (snd fn-fill))

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
