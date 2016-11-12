{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.cubical.Square

module lib.cubical.Cube where

{- Coordinates are yzx, where
     x : left -> right
     y : back -> front
     z : top  -> bottom
 -}

data Cube {i} {A : Type i} {a₀₀₀ : A} :
  {a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  (sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  (sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁) -- back
  (sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁) -- top
  (sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁) -- bottom
  (sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) -- front
  → Type i

  where
  idc : Cube ids ids ids ids ids ids

{- Just transport, but less clutter to use -}
module _ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  where

  cube-shift-left : {sq₋₋₀' : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀}
    → sq₋₋₀ == sq₋₋₀'
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube sq₋₋₀' sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  cube-shift-left idp cu = cu

  cube-shift-right : {sq₋₋₁' : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁}
    → sq₋₋₁ == sq₋₋₁'
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube sq₋₋₀ sq₋₋₁' sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  cube-shift-right idp cu = cu

  cube-shift-back : {sq₀₋₋' : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁}
    → sq₀₋₋ == sq₀₋₋'
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋' sq₋₀₋ sq₋₁₋ sq₁₋₋
  cube-shift-back idp cu = cu

  cube-shift-top : {sq₋₀₋' : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁}
    → sq₋₀₋ == sq₋₀₋'
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋' sq₋₁₋ sq₁₋₋
  cube-shift-top idp cu = cu

  cube-shift-bot : {sq₋₁₋' : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁}
    → sq₋₁₋ == sq₋₁₋'
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋' sq₁₋₋
  cube-shift-bot idp cu = cu

  cube-shift-front : {sq₁₋₋' : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁}
    → sq₁₋₋ == sq₁₋₋'
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋'
  cube-shift-front idp cu = cu

{- A cube where two opposite squares are both [ids] is a square -}
module _ {i} {A : Type i} where

  x-id-cube-in : {a₀ a₁ : A} {p₀₀ p₀₁ p₁₀ p₁₁ : a₀ == a₁}
    {α₀₋ : p₀₀ == p₁₀} {α₁₋ : p₀₁ == p₁₁}
    {α₋₀ : p₀₀ == p₀₁} {α₋₁ : p₁₀ == p₁₁}
    → Square α₀₋ α₋₀ α₋₁ α₁₋
    → Cube ids ids (vert-degen-square α₀₋) (vert-degen-square α₋₀)
           (vert-degen-square α₋₁) (vert-degen-square α₁₋)
  x-id-cube-in {p₀₀ = idp} ids = idc

  y-id-cube-in : {a₀ a₁ : A} {p₀₀ p₀₁ p₁₀ p₁₁ : a₀ == a₁}
    {α₀₋ : p₀₀ == p₁₀} {α₁₋ : p₀₁ == p₁₁}
    {α₋₀ : p₀₀ == p₀₁} {α₋₁ : p₁₀ == p₁₁}
    → Square α₀₋ α₋₀ α₋₁ α₁₋
    → Cube (vert-degen-square α₀₋) (vert-degen-square α₁₋)
           ids (horiz-degen-square α₋₀) (horiz-degen-square α₋₁) ids
  y-id-cube-in {p₀₀ = idp} ids = idc

  z-id-cube-in : {a₀ a₁ : A} {p₀₀ p₁₀ p₀₁ p₁₁ : a₀ == a₁}
    {α₀₋ : p₀₀ == p₁₀} {α₁₋ : p₀₁ == p₁₁}
    {α₋₀ : p₀₀ == p₀₁} {α₋₁ : p₁₀ == p₁₁}
    → Square α₀₋ α₋₀ α₋₁ α₁₋
    → Cube (horiz-degen-square α₀₋) (horiz-degen-square α₁₋)
           (horiz-degen-square α₋₀) ids ids (horiz-degen-square α₋₁)
  z-id-cube-in {p₀₀ = idp} ids = idc

{- Cube fillers -}
module _ {i} {A : Type i} where
  fill-cube-left : {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
    {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
    {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
    -- missing left

    {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
    {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
    (sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁) -- right

    {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
    {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
    (sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁) -- back
    (sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁) -- top
    (sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁) -- bottom
    (sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) -- front
    → Σ (Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀)
        (λ sq₋₋₀ → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋)
  fill-cube-left {p₋₀₀ = p₋₀₀} {p₋₁₀ = p₋₁₀} sq₋₋₁ ids sq₋₀₋ sq₋₁₋ ids =
    (_ ,
     cube-shift-right (vert-degen-square-β sq₋₋₁)
       (cube-shift-top (horiz-degen-square-β sq₋₀₋)
         (cube-shift-bot (horiz-degen-square-β sq₋₁₋)
           cu)))
    where
    fill-sq : Σ (p₋₀₀ == p₋₁₀) (λ α₋₋₀ →
      Square α₋₋₀ (horiz-degen-path sq₋₀₋)
             (horiz-degen-path sq₋₁₋) (vert-degen-path sq₋₋₁))
    fill-sq = fill-square-left _ _ _

    cu : Cube (vert-degen-square (fst fill-sq))
              (vert-degen-square (vert-degen-path sq₋₋₁)) ids
              (horiz-degen-square (horiz-degen-path sq₋₀₋))
              (horiz-degen-square (horiz-degen-path sq₋₁₋)) ids
    cu = y-id-cube-in (snd fill-sq)

  fill-cube-right : {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
    {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
    {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
    (sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀) -- left

    {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
    {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
    -- missing right

    {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
    {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
    (sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁) -- back
    (sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁) -- top
    (sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁) -- bottom
    (sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁) -- front
    → Σ (Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁)
        (λ sq₋₋₁ → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋)
  fill-cube-right sq₋₋₀ {p₋₀₁ = p₋₀₁} {p₋₁₁ = p₋₁₁} ids sq₋₀₋ sq₋₁₋ ids =
    (_ ,
     cube-shift-left (vert-degen-square-β sq₋₋₀)
       (cube-shift-top (horiz-degen-square-β sq₋₀₋)
         (cube-shift-bot (horiz-degen-square-β sq₋₁₋)
           cu)))
    where
    fill-sq : Σ (p₋₀₁ == p₋₁₁) (λ α₋₋₁ →
      Square (vert-degen-path sq₋₋₀) (horiz-degen-path sq₋₀₋)
             (horiz-degen-path sq₋₁₋) α₋₋₁)
    fill-sq = fill-square-right _ _ _

    cu : Cube (vert-degen-square (vert-degen-path sq₋₋₀))
              (vert-degen-square (fst fill-sq)) ids
              (horiz-degen-square (horiz-degen-path sq₋₀₋))
              (horiz-degen-square (horiz-degen-path sq₋₁₋)) ids
    cu = y-id-cube-in (snd fill-sq)


fill-cube-left-unique : ∀ {i} {A : Type i} {a₀₀₀ : A}
  {a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → sq₋₋₀ == fst (fill-cube-left sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋)
fill-cube-left-unique idc = idp

fill-cube-right-unique : ∀ {i} {A : Type i} {a₀₀₀ : A}
  {a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → sq₋₋₁ == fst (fill-cube-right sq₋₋₀ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋)
fill-cube-right-unique idc = idp

{- Paths as degenerate cubes -}
module _ {i} {A : Type i} where

  x-degen-cube : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    {sq₋₋₀ sq₋₋₁ : Square p₀₋ p₋₀ p₋₁ p₁₋}
    → sq₋₋₀ == sq₋₋₁
    → Cube sq₋₋₀ sq₋₋₁ hid-square hid-square hid-square hid-square
  x-degen-cube {sq₋₋₀ = ids} idp = idc

  y-degen-cube : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    {sq₀₋₋ sq₁₋₋ : Square p₀₋ p₋₀ p₋₁ p₁₋}
    → sq₀₋₋ == sq₁₋₋
    → Cube hid-square hid-square sq₀₋₋ vid-square vid-square sq₁₋₋
  y-degen-cube {sq₀₋₋ = ids} idp = idc

  z-degen-cube : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    {sq₋₀₋ sq₋₁₋ : Square p₀₋ p₋₀ p₋₁ p₁₋}
    → sq₋₀₋ == sq₋₁₋
    → Cube vid-square vid-square vid-square sq₋₀₋ sq₋₁₋ vid-square
  z-degen-cube {sq₋₀₋ = ids} idp = idc

  x-degen-cube-out : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    {sq₋₋₀ sq₋₋₁ : Square p₀₋ p₋₀ p₋₁ p₁₋}
    → Cube sq₋₋₀ sq₋₋₁ hid-square hid-square hid-square hid-square
    → sq₋₋₀ == sq₋₋₁
  x-degen-cube-out cu =
    fill-cube-left-unique cu ∙ ! (fill-cube-left-unique (x-degen-cube idp))

{- A pathover between squares can be represented as a cube -}
module _ {i j} {A : Type i} {B : Type j} {b₀₀ b₀₁ b₁₀ b₁₁ : A → B}
  {p₀₋ : (a : A) → b₀₀ a == b₀₁ a} {p₋₀ : (a : A) → b₀₀ a == b₁₀ a}
  {p₋₁ : (a : A) → b₀₁ a == b₁₁ a} {p₁₋ : (a : A) → b₁₀ a == b₁₁ a}
  where

  ↓-square-to-cube :  {x y : A} {q : x == y}
    {u : Square (p₀₋ x) (p₋₀ x) (p₋₁ x) (p₁₋ x)}
    {v : Square (p₀₋ y) (p₋₀ y) (p₋₁ y) (p₁₋ y)}
    → u == v [ (λ z → Square (p₀₋ z) (p₋₀ z) (p₋₁ z) (p₁₋ z)) ↓ q ]
    → Cube u v (natural-square p₀₋ q ) (natural-square p₋₀ q)
           (natural-square p₋₁ q) (natural-square p₁₋ q)
  ↓-square-to-cube {q = idp} r = x-degen-cube r

  cube-to-↓-square : {x y : A} {q : x == y}
    {sqx : Square (p₀₋ x) (p₋₀ x) (p₋₁ x) (p₁₋ x)}
    {sqy : Square (p₀₋ y) (p₋₀ y) (p₋₁ y) (p₁₋ y)}
    → Cube sqx sqy (natural-square p₀₋ q) (natural-square p₋₀ q)
           (natural-square p₋₁ q) (natural-square p₁₋ q)
    → sqx == sqy [ (λ z → Square (p₀₋ z) (p₋₀ z) (p₋₁ z) (p₁₋ z)) ↓ q ]
  cube-to-↓-square {q = idp} cu = x-degen-cube-out cu

module _ {i j} {A : Type i} {B : Type j} {b₀₀ b₀₁ b₁₀ b₁₁ : B}
  {p₀₋ : (a : A) → b₀₀ == b₀₁} {p₋₀ : (a : A) → b₀₀ == b₁₀}
  {p₋₁ : (a : A) → b₀₁ == b₁₁} {p₁₋ : (a : A) → b₁₀ == b₁₁}
  where

  cube-to-disc-square : {x y : A} {q : x == y}
    {sqx : Square (p₀₋ x) (p₋₀ x) (p₋₁ x) (p₁₋ x)}
    {sqy : Square (p₀₋ y) (p₋₀ y) (p₋₁ y) (p₁₋ y)}
    → Cube sqx sqy (natural-square p₀₋ q) (natural-square p₋₀ q)
           (natural-square p₋₁ q) (natural-square p₁₋ q)
    → Square (square-to-disc sqx) (ap (λ z → p₀₋ z ∙ p₋₁ z) q)
             (ap (λ z → p₋₀ z ∙ p₁₋ z) q) (square-to-disc sqy)
  cube-to-disc-square cu =
    ↓-='-to-square (ap↓ square-to-disc (cube-to-↓-square cu))


ap-cube : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → Cube (ap-square f sq₋₋₀) (ap-square f sq₋₋₁) (ap-square f sq₀₋₋)
         (ap-square f sq₋₀₋) (ap-square f sq₋₁₋) (ap-square f sq₁₋₋)
ap-cube f idc = idc

natural-cube : ∀ {i j} {A : Type i} {B : Type j}
  {f₀₀ f₀₁ f₁₀ f₁₁ : A → B}
  {p₀₋ : (a : A) → f₀₀ a == f₀₁ a} {p₋₀ : (a : A) → f₀₀ a == f₁₀ a}
  {p₋₁ : (a : A) → f₀₁ a == f₁₁ a} {p₁₋ : (a : A) → f₁₀ a == f₁₁ a}
  (sq : ∀ a → Square (p₀₋ a) (p₋₀ a) (p₋₁ a) (p₁₋ a))
  {x y : A} (q : x == y)
  → Cube (sq x) (sq y)
         (natural-square p₀₋ q) (natural-square p₋₀ q)
         (natural-square p₋₁ q) (natural-square p₁₋ q)
natural-cube sq idp = x-degen-cube idp

cube-rotate-x→z : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → Cube (square-symmetry sq₀₋₋) (square-symmetry sq₁₋₋)
         (square-symmetry sq₋₀₋) sq₋₋₀ sq₋₋₁ (square-symmetry sq₋₁₋)
cube-rotate-x→z idc = idc

cube-symmetry-x : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → Cube (square-symmetry sq₋₋₀) (square-symmetry sq₋₋₁)
         sq₋₀₋ sq₀₋₋ sq₁₋₋ sq₋₁₋
cube-symmetry-x idc = idc

cube-!-x : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

  {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
  {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
  {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
  {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
  → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
  → Cube sq₋₋₁ sq₋₋₀ (!□h sq₀₋₋) (!□h sq₋₀₋) (!□h sq₋₁₋) (!□h sq₁₋₋)
cube-!-x idc = idc

_∙³x_ : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ a₀₀₂ a₀₁₂ a₁₀₂ a₁₁₂ : A}
  {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
  {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

  {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
  {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- middle

  {p₀₋₂ : a₀₀₂ == a₀₁₂} {p₋₀₂ : a₀₀₂ == a₁₀₂}
  {p₋₁₂ : a₀₁₂ == a₁₁₂} {p₁₋₂ : a₁₀₂ == a₁₁₂}
  {sq₋₋₂ : Square p₀₋₂ p₋₀₂ p₋₁₂ p₁₋₂} -- right

  {p₀₀l : a₀₀₀ == a₀₀₁} {p₀₁l : a₀₁₀ == a₀₁₁}
  {p₁₀l : a₁₀₀ == a₁₀₁} {p₁₁l : a₁₁₀ == a₁₁₁}
  {sq₀₋l : Square p₀₋₀ p₀₀l p₀₁l p₀₋₁} -- backl
  {sq₋₀l : Square p₋₀₀ p₀₀l p₁₀l p₋₀₁} -- topl
  {sq₋₁l : Square p₋₁₀ p₀₁l p₁₁l p₋₁₁} -- bottoml
  {sq₁₋l : Square p₁₋₀ p₁₀l p₁₁l p₁₋₁} -- frontl

  {p₀₀r : a₀₀₁ == a₀₀₂} {p₀₁r : a₀₁₁ == a₀₁₂}
  {p₁₀r : a₁₀₁ == a₁₀₂} {p₁₁r : a₁₁₁ == a₁₁₂}
  {sq₀₋r : Square p₀₋₁ p₀₀r p₀₁r p₀₋₂} -- backr
  {sq₋₀r : Square p₋₀₁ p₀₀r p₁₀r p₋₀₂} -- topr
  {sq₋₁r : Square p₋₁₁ p₀₁r p₁₁r p₋₁₂} -- bottomr
  {sq₁₋r : Square p₁₋₁ p₁₀r p₁₁r p₁₋₂} -- frontr

  → Cube sq₋₋₀ sq₋₋₁ sq₀₋l sq₋₀l sq₋₁l sq₁₋l
  → Cube sq₋₋₁ sq₋₋₂ sq₀₋r sq₋₀r sq₋₁r sq₁₋r
  → Cube sq₋₋₀ sq₋₋₂ (sq₀₋l ⊡h sq₀₋r) (sq₋₀l ⊡h sq₋₀r)
         (sq₋₁l ⊡h sq₋₁r) (sq₁₋l ⊡h sq₁₋r)
idc ∙³x cu = cu

infixr 8 _∙³x_
