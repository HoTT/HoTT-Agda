{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.mayer-vietoris.BaseLeftInverse {i j k} {A : Type i}
  {B : Type j} (Z : Ptd k) (f : fst Z → A) (g : fst Z → B) where

open import cohomology.mayer-vietoris.BaseEquivMaps Z f g
open import cohomology.mayer-vietoris.Functions ps
  using (module Reglue; reglue; ptd-reglue)

{- [out] is right inverse on codomain part of cofiber space,
 - i.e. [out (into (cfcod _ γ)) == cfcod _ γ] -}

out-into-cod-square : (z : fst Z) →
  Square (cfglue reglue (winl (f z))) (ap (out ∘ into-cod) (glue z))
         (ap (cfcod _) (glue z)) (cfglue _ (winr (g z)))
out-into-cod-square z =
  (ap-∘ out into-cod (glue z) ∙ ap (ap out) (IntoCod.glue-β z) ∙ Out.glue-β z)
  ∙v⊡ out-square z

module OutIntoCod = PushoutElim
  {d = ptd-span-out ps} {P = λ γ → out (into (cfcod _ γ)) == cfcod _ γ}
  (λ x → cfglue _ (winl x))
  (λ y → cfglue _ (winr y))
  (λ z → ↓-='-from-square (out-into-cod-square z))

out-into-cod = OutIntoCod.f

{- Cube move lemmas for the left inverse coherence. These are used to
   build up a right square (in this case starting from a cube filler  -}
private
  top-lemma : ∀ {i} {A : Type i}
    {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
    {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
    {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
    {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

    {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
    {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
    {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

    {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
    {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
    {q : a₀₀₁ == a₁₀₁}
    {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
    {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ q} -- top
    {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
    {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
    (α : q == p₋₀₁)
    (cu : Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ (sq₋₀₋ ⊡h∙ α) sq₋₁₋ sq₁₋₋)
    → Cube sq₋₋₀ (α ∙v⊡ sq₋₋₁) sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  top-lemma idp cu = cu

private
  square-push-rb : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == b} {p₁₋ : a₁₀ == a₁₁}
    (q : a₁₁ == b) (sq : Square p₀₋ p₋₀ p₋₁ (p₁₋ ∙ q))
    → Square p₀₋ p₋₀ (p₋₁ ∙' ! q) p₁₋
  square-push-rb {p₁₋ = idp} idp sq = sq

  square-pull-rb : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {b : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == b} {p₁₋ : a₁₀ == a₁₁}
    (q : a₁₁ == b) (sq : Square p₀₋ p₋₀ (p₋₁ ∙' ! q) p₁₋)
    → Square p₀₋ p₋₀ p₋₁ (p₁₋ ∙ q)
  square-pull-rb {p₁₋ = idp} idp sq = sq

  bot-lemma' : ∀ {i} {A : Type i}
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
  bot-lemma' ids cu = cu

  bot-lemma : ∀ {i} {A : Type i}
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
  bot-lemma sq₋₋₁ ids cu = bot-lemma' sq₋₋₁ cu

{- Proving the coherence term for the left inverse. This means proving
   [(w : Wedge X Y) → Square idp (ap out (ap into (glue w)))
                             (cfglue _ w) (out-into-cod (reglue w))]
-}

out-into-sql : (x : fst X)
  → Square idp (ap out (ap into (glue (winl x))))
               (cfglue _ (winl x)) (cfglue _ (winl x))
out-into-sql x =
  ap (ap out) (Into.glue-β (winl x)) ∙v⊡ connection2


out-into-fill : Σ (Square idp (ap out (glue (snd Z))) idp idp) (λ sq →
  Cube (out-into-sql (snd X)) sq
       (square-push-rb idp (natural-square' (λ _ → idp) wglue))
       (natural-square' (ap out ∘ ap into ∘ cfglue _) wglue
        ⊡h∙ ap (ap out) (Into.glue-β (winr (snd Y))))
       (natural-square' (cfglue _) wglue ⊡h' !□h (square-symmetry connection2))
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
  → Square idp (ap out (ap into (glue (winr y))))
           (cfglue _ (winr y)) (cfglue _ (winr y))
out-into-sqr y =
  ap (ap out) (Into.glue-β (winr y)) ∙v⊡ out-into-fill-square
  ⊡v connection2

{- Left inverse -}

out-into : ∀ κ → out (into κ) == κ
out-into = Cofiber-elim reglue
  idp out-into-cod
  (↓-∘=idf-from-square out into ∘ Wedge-elim
     {P = λ w → Square idp (ap out (ap into (glue w)))
                       (cfglue _ w) (out-into-cod (reglue w))}
     out-into-sql out-into-sqr
     (cube-to-↓-square $
       top-lemma (ap (ap out) (Into.glue-β (winr (snd Y)))) $
         bot-lemma out-into-fill-square connection2 $
           out-into-fill-cube))
