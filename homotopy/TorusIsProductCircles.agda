{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.TorusIsProductCircles where

{- First map -}
to-baseT : S¹ × S¹
to-baseT = (base , base)

to-loopT1 : to-baseT == to-baseT
to-loopT1 = pair=' loop idp

to-loopT2 : to-baseT == to-baseT
to-loopT2 = pair=' idp loop

to-surfT : to-loopT1 ∙ to-loopT2 == to-loopT2 ∙' to-loopT1
to-surfT =
  pair=' loop idp ∙ pair=' idp loop   =⟨ ×-∙ loop idp idp loop ⟩
  pair=' (loop ∙ idp) (idp ∙ loop)    =⟨ ∙-unit-r loop |in-ctx (λ u → pair=' u loop) ⟩
  pair=' loop loop                    =⟨ ! (∙'-unit-l loop) |in-ctx (λ u → pair=' u loop) ⟩
  pair=' (idp ∙' loop) (loop ∙' idp)  =⟨ ! (×-∙' idp loop loop idp) ⟩
  pair=' idp loop ∙' pair=' loop idp ∎

to : Torus → S¹ × S¹
to = Torus-rec to-baseT to-loopT1 to-loopT2 to-surfT

{- Second map -}

from-c-base : S¹ → Torus
from-c-base = S¹-rec baseT loopT2

from-c-loop' : (x : S¹) → from-c-base x == from-c-base x
from-c-loop' = S¹-elim loopT1 (↓-='-in
  (loopT1 ∙ ap from-c-base loop   =⟨ loop-β' baseT loopT2 |in-ctx (λ u → loopT1 ∙ u) ⟩
   loopT1 ∙ loopT2                =⟨ surfT ⟩
   loopT2 ∙' loopT1               =⟨ ! (loop-β' baseT loopT2) |in-ctx (λ u → u ∙' loopT1) ⟩
   ap from-c-base loop ∙' loopT1 ∎))

from-c-loop : from-c-base == from-c-base
from-c-loop = λ= from-c-loop'

from-c : S¹ → (S¹ → Torus)
from-c = S¹-rec from-c-base from-c-loop

from : S¹ × S¹ → Torus
from (x , y) = from-c x y

{- First composition -}

to-from-c-base : (y : S¹) → to (from-c-base y) == (base , y)
to-from-c-base = S¹-elim idp (↓-='-in
  (ap (λ z → (base , z)) loop            =⟨ ap-cst,id _ loop ⟩
   pair=' idp loop                       =⟨ ! (loopT2-β' to-baseT to-loopT1 to-loopT2 to-surfT) ⟩
   ap to loopT2                          =⟨ ! (loop-β' baseT loopT2) |in-ctx ap to ⟩
   ap to (ap from-c-base loop)           =⟨ ! (ap-∘ to from-c-base loop) ⟩
   ap (to ∘ from-c-base) loop ∎))

to-from-c : (x : S¹) (y : S¹) → to (from-c x y) == (x , y)
to-from-c = S¹-elim to-from-c-base (↓-cst→app-in thing)  where
  thing : (y : S¹) → to-from-c-base y == to-from-c-base y [ (λ x → to (from-c x y) == (x , y)) ↓ loop ]
  thing = {!S¹-elim (↓-='-in {!!}) {!!}!}

to-from : (x : S¹ × S¹) → to (from x) == x
to-from (x , y) = to-from-c x y

{- Second composition -}

thing : ap (λ x → from-c x base) loop == loopT1
thing =
  ap ((λ u → u base) ∘ from-c) loop     =⟨ ap-∘ (λ u → u base) from-c loop ⟩
  ap (λ u → u base) (ap from-c loop)    =⟨ loop-β' from-c-base from-c-loop |in-ctx ap (λ u → u base) ⟩
  ap (λ u → u base) (λ= from-c-loop')   =⟨ app=-β from-c-loop' base ⟩
  from-c-loop' base                     =⟨ idp ⟩
  loopT1 ∎

lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A × B → C)
  {x y : A} (p : x == y) {z t : B} (q : z == t)
  → ap f (pair=' p q) == app= (ap (curry f) p) z ∙' ap (curry f y) q
lemma f idp idp = idp

lemma' : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A × B → C)
  {x y : A} (p : x == y) {z t : B} (q : z == t)
  → ap f (pair=' p q) == ap (curry f x) q ∙' app= (ap (curry f) p) t
lemma' f idp idp = idp

from-to-loopT1 : idp == idp [ (λ z → from (to z) == z) ↓ loopT1 ]
from-to-loopT1 = ↓-∘=id-in to from
  (ap from (ap to loopT1)                =⟨ loopT1-β' to-baseT to-loopT1 to-loopT2 to-surfT |in-ctx ap from ⟩
   ap from to-loopT1             =⟨ lemma from loop (idp {a = base}) ⟩
   ap (λ u → u base) (ap from-c loop)    =⟨ loop-β' from-c-base from-c-loop |in-ctx ap (λ u → u base) ⟩
   ap (λ u → u base) (λ= from-c-loop')   =⟨ app=-β from-c-loop' base ⟩
   loopT1 ∎)

from-to-loopT2 : idp == idp [ (λ z → from (to z) == z) ↓ loopT2 ]
from-to-loopT2 = ↓-∘=id-in to from
  (ap from (ap to loopT2)                =⟨ loopT2-β' to-baseT to-loopT1 to-loopT2 to-surfT |in-ctx ap from ⟩
   ap from to-loopT2             =⟨ lemma' from (idp {a = base}) loop ⟩
   ap from-c-base loop    =⟨ loop-β' baseT loopT2 ⟩
   loopT2 ∎)

from-to : (x : Torus) → from (to x) == x
from-to = {!Torus-elim idp from-to-loopT1 from-to-loopT2 {!!}!}
