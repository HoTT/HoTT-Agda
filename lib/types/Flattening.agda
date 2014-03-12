{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Paths
open import lib.types.Sigma

module lib.types.Flattening {i j k}
  (A : Type i) (B : Type j) (f g : B → A)
  (C : A → Type k) (D : (b : B) → C (f b) ≃ C (g b)) where

{- The base HIT -}

import lib.types.Generic1HIT as Generic1HIT

module W = Generic1HIT A B f g
open W public using (cc; pp)
              renaming (T to W)

module P = W.RecType C D
open P public -- using (↓-pp-in; ↓-pp-out; ↓-pp-β)
              renaming (f to P)

{- The flattened HIT -}

At : Type _
At = Σ A C

Bt : Type _
Bt = Σ B (C ∘ f)

ft : Bt → At
ft (b , d) = (f b , d)

gt : Bt → At
gt (b , d) = (g b , –> (D b) d)

module Wt = Generic1HIT At Bt ft gt
open Wt public using ()
               renaming (T to Wt)

cct = curry Wt.cc
ppt = curry Wt.pp

private
  {- Flattening -}

  module _ where
    paths-flatten :
      (b : B) → (cct (f b) == cct (g b) [ (λ w → (P w → Wt)) ↓ pp b ])
    paths-flatten b =
      ↓-app→cst-in (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))

    module FlattenCurried = W.Elim cct paths-flatten

  flatten-curried : (w : W) → (P w → Wt)
  flatten-curried = FlattenCurried.f 

  flatten : Σ W P → Wt
  flatten (w , x) = flatten-curried w x

  {- Unflattening -}


  unflatten-cc : (ac : At) → Σ W P
  unflatten-cc (a , c) = (cc a , c)

  unflatten-pp : (bd : Bt) → unflatten-cc (ft bd) == unflatten-cc (gt bd)
  unflatten-pp (b , d) = pair= (pp b) (↓-pp-in idp)

  module Unflatten = Wt.Rec unflatten-cc unflatten-pp

  unflatten : Wt → Σ W P
  unflatten = Unflatten.f

  {- First composition -}

  flatten-unflatten : (w : Wt) → flatten (unflatten w) == w
  flatten-unflatten = Wt.elim
    (λ _ → idp)
    (λ bd → let (b , d) = bd in
      ↓-∘=idf-in flatten unflatten
      (ap flatten (ap unflatten (ppt b d))
                 =⟨ Unflatten.pp-β bd |in-ctx ap flatten ⟩
       ap flatten (pair= (pp b) (↓-pp-in idp))
                 =⟨ split-ap2 flatten (pp b) (↓-pp-in idp) ⟩
       ↓-app→cst-out (apd flatten-curried (pp b)) (↓-pp-in idp)
                 =⟨ FlattenCurried.pp-β b
                    |in-ctx (λ u → ↓-app→cst-out u (↓-pp-in idp)) ⟩
       ↓-app→cst-out (paths-flatten b) (↓-pp-in idp)
                 =⟨ idp ⟩
       ↓-app→cst-out (↓-app→cst-in
         (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))) (↓-pp-in idp)
                 =⟨ ↓-app→cst-β (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))
                                (↓-pp-in idp) ⟩
       ppt b d ∙' ap (cct (g b)) (↓-pp-out (↓-pp-in idp))
                 =⟨ ↓-pp-β idp |in-ctx (λ u → ppt b d ∙' ap (cct (g b)) u) ⟩
       ppt b d ∎))

  {- Second composition -}

  unflatten-flatten-curried : (w : W) (x : P w)
    →  unflatten (flatten-curried w x) == (w , x)
  unflatten-flatten-curried = W.elim
    (λ a x → idp)
    (λ b → ↓-Π-in
    (λ q → ↓-∘=idf-in unflatten flatten
      (ap unflatten (ap flatten (pair= (pp b) q))
                 =⟨ split-ap2 flatten (pp b) q |in-ctx ap unflatten ⟩
       ap unflatten (↓-app→cst-out (apd flatten-curried (pp b)) q)
                 =⟨ FlattenCurried.pp-β b
                    |in-ctx (λ u → ap unflatten (↓-app→cst-out u q)) ⟩
       ap unflatten (↓-app→cst-out (paths-flatten b) q)
                 =⟨ idp ⟩
       ap unflatten (↓-app→cst-out (↓-app→cst-in (λ qq → ppt b _ ∙' ap (cct (g b)) (↓-pp-out qq))) q)
                 =⟨ ↓-app→cst-β (λ qq → ppt b _ ∙' ap (cct (g b)) (↓-pp-out qq)) q |in-ctx ap unflatten ⟩
       ap unflatten (ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))
                 =⟨ ap-∙' unflatten (ppt b _) (ap (cct (g b)) (↓-pp-out q)) ⟩
       ap unflatten (ppt b _) ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                 =⟨ Unflatten.pp-β (b , _) |in-ctx (λ u → u ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))) ⟩
       pair= (pp b) (↓-pp-in idp) ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                 =⟨ ∘-ap unflatten (cct (g b)) (↓-pp-out q) |in-ctx (λ u → (pair= (pp b) (↓-pp-in idp) ∙' u)) ⟩
       pair= (pp b) (↓-pp-in idp) ∙' ap (unflatten ∘ cct (g b)) (↓-pp-out q)
                 =⟨ idp ⟩
       pair= (pp b) (↓-pp-in idp) ∙' ap (λ x → (cc (g b), x)) (↓-pp-out q)
                 =⟨ ap-cst,id P (↓-pp-out q) |in-ctx (λ u → pair= (pp b) (↓-pp-in idp) ∙' u) ⟩
       pair= (pp b) (↓-pp-in idp) ∙' pair= idp (↓-pp-out q)
                 =⟨ Σ-∙' (↓-pp-in idp) (↓-pp-out q) ⟩
       pair= (pp b) (↓-pp-in idp ∙'ᵈ ↓-pp-out q)
                 =⟨ to-transp-weird q (coe-pp-β _ _) |in-ctx pair= (pp b) ⟩
       pair= (pp b) q ∎)))

  unflatten-flatten : (wx : Σ W P) → unflatten (flatten wx) == wx
  unflatten-flatten (w , x) = unflatten-flatten-curried w x

{- The equivalence -}

abstract
  flattening-equiv : Σ W P ≃ Wt
  flattening-equiv = equiv flatten unflatten flatten-unflatten unflatten-flatten
