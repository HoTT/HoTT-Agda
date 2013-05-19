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
open W public
  using (cc; pp; pp-β; pp-β')
  renaming (Wg to W; Wg-rec to W-rec; Wg-elim to W-elim)

↓-pp-out = W.↓-pp-out C D
↓-pp-in = W.↓-pp-in C D
↓-pp-β = W.↓-pp-β C D
pp-path = W.pp-path C D

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
open Wt public 
  using ()
  renaming (Wg to Wt; Wg-rec to Wt-rec; Wg-elim to Wt-elim; pp-β' to ppt-β')

cct = curry Wt.cc
ppt = curry Wt.pp

{- The fibration -}

private
  P : W → Type _
  P = W-rec C (ua ∘ D)

{- Flattening -}

-- The family of paths used in the definition of [flatten]
paths-flatten : (b : B) → (cct (f b) == cct (g b) [ (λ w → (P w → Wt)) ↓ pp b ])
paths-flatten b =
  ↓-app→cst-in (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))

flatten-curried : (w : W) → (P w → Wt)
flatten-curried = W-elim cct paths-flatten

flatten : Σ W P → Wt
flatten (w , x) = flatten-curried w x

{- Unflattening -}

unflatten-cc : (ac : At) → Σ W P
unflatten-cc (a , c) = (cc a , c)

unflatten-pp : (bd : Bt) → unflatten-cc (ft bd) == unflatten-cc (gt bd)
unflatten-pp (b , d) = pair= (pp b) (↓-pp-in idp)

unflatten : Wt → Σ W P
unflatten = Wt-rec unflatten-cc unflatten-pp

{- First composition -}

abstract
  flatten-unflatten : (w : Wt) → flatten (unflatten w) == w
  flatten-unflatten =
    Wt-elim
      (λ _ → idp)
      (λ bd → let (b , d) = bd in
        ↓-∘=id-in unflatten flatten
        (ap flatten (ap unflatten (ppt b d))
                   =⟨ ppt-β' unflatten-cc unflatten-pp bd |in-ctx ap flatten ⟩
         ap flatten (pair= (pp b) (↓-pp-in idp))
                   =⟨ split-ap2 flatten (pp b) (↓-pp-in idp) ⟩
         ↓-app→cst-out (apd flatten-curried (pp b)) (↓-pp-in idp)
                   =⟨ pp-β cct paths-flatten b |in-ctx (λ u → ↓-app→cst-out u (↓-pp-in idp)) ⟩
         ↓-app→cst-out (paths-flatten b) (↓-pp-in idp)
                   =⟨ idp ⟩
         ↓-app→cst-out (↓-app→cst-in
           (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))) (↓-pp-in idp)
                   =⟨ ↓-app→cst-β (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q)) (↓-pp-in idp) ⟩
         ppt b d ∙' ap (cct (g b)) (↓-pp-out (↓-pp-in idp))
                   =⟨ ↓-pp-β idp |in-ctx (λ u → ppt b d ∙' ap (cct (g b)) u) ⟩
         ppt b d ∎))

{- Second composition -}

abstract
  unflatten-flatten-curried : (w : W) (x : P w)
    →  unflatten (flatten-curried w x) == (w , x)
  unflatten-flatten-curried =
    W-elim (λ a x → idp)
      (λ b → ↓-Π-in
      (λ q → ↓-∘=id-in flatten unflatten
        (ap unflatten (ap flatten (pair= (pp b) q))
                   =⟨ split-ap2 flatten (pp b) q |in-ctx ap unflatten ⟩
         ap unflatten (↓-app→cst-out (apd flatten-curried (pp b)) q)
                   =⟨ pp-β cct paths-flatten b |in-ctx (λ u → ap unflatten (↓-app→cst-out u q)) ⟩
         ap unflatten (↓-app→cst-out (paths-flatten b) q)
                   =⟨ idp ⟩
         ap unflatten (↓-app→cst-out (↓-app→cst-in (λ qq → ppt b _ ∙' ap (cct (g b)) (↓-pp-out qq))) q)
                   =⟨ ↓-app→cst-β (λ qq → ppt b _ ∙' ap (cct (g b)) (↓-pp-out qq)) q |in-ctx ap unflatten ⟩
         ap unflatten (ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))
                   =⟨ ap-∙' unflatten (ppt b _) (ap (cct (g b)) (↓-pp-out q)) ⟩
         ap unflatten (ppt b _) ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                   =⟨ ppt-β' unflatten-cc unflatten-pp (b , _) |in-ctx (λ u → u ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))) ⟩
         pair= (pp b) (↓-pp-in idp) ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                   =⟨ ∘-ap unflatten (cct (g b)) (↓-pp-out q) |in-ctx (λ u → (pair= (pp b) (↓-pp-in idp) ∙' u)) ⟩
         pair= (pp b) (↓-pp-in idp) ∙' ap (unflatten ∘ cct (g b)) (↓-pp-out q)
                   =⟨ idp ⟩
         pair= (pp b) (↓-pp-in idp) ∙' ap (λ x → (cc (g b), x)) (↓-pp-out q)
                   =⟨ ap-cst,id P (↓-pp-out q) |in-ctx (λ u → pair= (pp b) (↓-pp-in idp) ∙' u) ⟩
         pair= (pp b) (↓-pp-in idp) ∙' pair= idp (↓-pp-out q)
                   =⟨ Σ-∙' (↓-pp-in idp) (↓-pp-out q) ⟩
         pair= (pp b) (↓-pp-in idp ∙'dep ↓-pp-out q)
                   =⟨ to-transp-weird q (pp-path _ _) |in-ctx pair= (pp b) ⟩
         pair= (pp b) q ∎)))

  unflatten-flatten : (wx : Σ W P) → unflatten (flatten wx) == wx
  unflatten-flatten (w , x) = unflatten-flatten-curried w x

{- The equivalence -}

flattening-equiv : Σ W P ≃ Wt
flattening-equiv = equiv flatten unflatten flatten-unflatten unflatten-flatten
