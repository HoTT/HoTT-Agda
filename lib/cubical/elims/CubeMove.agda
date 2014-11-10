{-# OPTIONS --without-K #-}

open import HoTT

{- Move (parts of) faces of a cube around -}

module lib.cubical.elims.CubeMove where

square-push-rb : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ b : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
  {p₋₁ : a₀₁ == a₁₁} (p₁₋ : a₁₀ == b) (q : b == a₁₁)
  → Square p₀₋ p₋₀ p₋₁ (p₁₋ ∙ q)
  → Square p₀₋ p₋₀ (p₋₁ ∙' ! q) p₁₋
square-push-rb idp idp sq = sq

private
  right-from-front-lemma : ∀ {i} {A : Type i}
    {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
    {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
    {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
    {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

    {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
    {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
    (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

    {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
    {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
    {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
    {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ (p₋₀₁ ∙ idp)} -- top
    {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ (p₋₁₁ ∙ idp)} -- bottom
    {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ (square-push-rb p₋₀₁ idp sq₋₀₋)
           (square-push-rb p₋₁₁ idp sq₋₁₋) (sq₁₋₋ ⊡h' !□h hid-square)
    → Cube sq₋₋₀ (sq₋₋₁ ⊡h hid-square) sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  right-from-front-lemma ids cu = cu

cube-right-from-front : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ b₀ b₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁}
  {p₋₀₁ : a₀₀₁ == b₀} {q₋₀₁ : b₀ == a₁₀₁}
  {r : b₀ == b₁}
  {p₋₁₁ : a₀₁₁ == b₁} {q₋₁₁ : b₁ == a₁₁₁}
  {p₁₋₁ : a₁₀₁ == a₁₁₁}
  (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ r) -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ (p₋₀₁ ∙ q₋₀₁)} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ (p₋₁₁ ∙ q₋₁₁)} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  (sq' : Square r q₋₀₁ q₋₁₁ p₁₋₁)
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ (square-push-rb p₋₀₁ q₋₀₁ sq₋₀₋)
         (square-push-rb p₋₁₁ q₋₁₁ sq₋₁₋) (sq₁₋₋ ⊡h' !□h sq')
  → Cube sq₋₋₀ (sq₋₋₁ ⊡h sq') sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
cube-right-from-front sq₋₋₁ ids cu = right-from-front-lemma sq₋₋₁ cu
