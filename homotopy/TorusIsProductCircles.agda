{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.TorusIsProductCircles where

surfT' : loopT1 ∙ loopT2 == loopT2 ∙' loopT1
surfT' = surfT ∙ (∙=∙' loopT2 loopT1)

private
  to-surfT : (pair×= loop idp) ∙ (pair×= idp loop)
             == (pair×= idp loop) ∙ (pair×= loop idp)
  to-surfT =
    pair×= loop idp ∙ pair×= idp loop   =⟨ ×-∙ loop idp idp loop ⟩
    pair×= (loop ∙ idp) (idp ∙ loop)    =⟨ ∙-unit-r loop |in-ctx (λ u → pair×= u loop) ⟩
    pair×= loop loop                    =⟨ ! (∙-unit-r loop) |in-ctx (λ u → pair×= loop u) ⟩
    pair×= (idp ∙ loop) (loop ∙ idp)    =⟨ ! (×-∙ idp loop loop idp) ⟩
    pair×= idp loop ∙ pair×= loop idp ∎

module To = TorusRec (base , base) (pair×= loop idp) (pair×= idp loop) to-surfT

{- First map -}
to : Torus → S¹ × S¹
to = To.f 

{- Second map -}

from-c : S¹ → (S¹ → Torus)
from-c = FromC.f module M2 where
  
  module FromCBase = S¹Rec baseT loopT2

  from-c-base : S¹ → Torus
  from-c-base = FromCBase.f

  from-c-loop-loop' : loopT1 ∙ ap from-c-base loop =-= ap from-c-base loop ∙' loopT1
  from-c-loop-loop' = 
    loopT1 ∙ ap from-c-base loop   =⟪ FromCBase.loop-β |in-ctx (λ u → loopT1 ∙ u) ⟫
    loopT1 ∙ loopT2                =⟪ surfT' ⟫
    loopT2 ∙' loopT1               =⟪ ! FromCBase.loop-β |in-ctx (λ u → u ∙' loopT1) ⟫
    ap from-c-base loop ∙' loopT1 ∎∎

  from-c-loop-loop : loopT1 == loopT1 [ (λ x → from-c-base x == from-c-base x) ↓ loop ]
  from-c-loop-loop = ↓-='-in (↯ from-c-loop-loop')

  module FromCLoop = S¹Elim loopT1 from-c-loop-loop
  
  from-c-loop' = FromCLoop.f
  from-c-loop = λ= from-c-loop'

  module FromC = S¹Rec from-c-base from-c-loop

from : S¹ × S¹ → Torus
from (x , y) = from-c x y

open M2

{- First composition -}

thing : (y : S¹) → ap (λ x → from-c x y) loop == from-c-loop' y
thing y =
  ap ((λ u → u y) ∘ from-c) loop   =⟨ ap-∘ (λ u → u y) from-c loop ⟩
  app= (ap from-c loop) y          =⟨ FromC.loop-β |in-ctx (λ u → app= u y)⟩
  app= (λ= from-c-loop') y         =⟨ app=-β from-c-loop' y ⟩
  from-c-loop' y ∎

to-from-c : (x y : S¹) → to (from-c x y) == (x , y)
to-from-c = {!!} --S¹-elim to-from-c-base (↓-cst→app-in to-from-c-loop)
  where

  to-from-c-base-loop' : ap (to ∘ from-c-base) loop =-= ap (λ y → (base , y)) loop
  to-from-c-base-loop' = 
    ap (to ∘ from-c-base) loop    =⟪ ap-∘ to from-c-base loop ⟫
    ap to (ap from-c-base loop)   =⟪ FromCBase.loop-β |in-ctx ap to ⟫
    ap to loopT2                  =⟪ To.loopT2-β ⟫
    pair×= idp loop               =⟪ ! (ap-cst,id _ loop) ⟫
    ap (λ y → (base , y)) loop ∎∎

  to-from-c-base-loop : idp == idp [ (λ z → to (from-c-base z) == (base , z)) ↓ loop ]
  to-from-c-base-loop = ↓-='-in (! (↯ to-from-c-base-loop'))

  module ToFromCBase = S¹Elim idp to-from-c-base-loop

  -- 1!to-from-c-base-loop : idp == idp [ (λ z → to (from-c-base (fst z)) == z) ↓ (pair×= loop idp) ]
  -- 1!to-from-c-base-loop = ↓-='-in (! (↯ 1! to-from-c-base-loop'))

--   module 1!ToFromCBase!1 = S¹Elim idp 1!to-from-c-base-loop

  to-from-c-base : (y : S¹) → to (from-c-base y) == (base , y)
  to-from-c-base = ToFromCBase.f

  thing2 : (y : S¹) → ap to (from-c-loop' y) == to-from-c-base y ∙ pair×= loop idp ∙' (! (to-from-c-base y))
  thing2 = {!S¹-elim To.loopT1-β {!To.loopT1-β!}!}

  to-from-c-loop : (y : S¹) → to-from-c-base y == to-from-c-base y [ (λ x → to (from-c x y) == (x , y)) ↓ loop ]
  to-from-c-loop = {!S¹-elim to-from-c-loop-base ?!}  where

    to-from-c-loop-base2 : ap (λ x → (x , base)) loop =-= ap (λ x → to (from-c x base)) loop
    to-from-c-loop-base2 = 
      ap (λ z → z , base) loop               =⟪ {!ap-id,cst _ loop!} ⟫
      pair×= loop idp                        =⟪ ! To.loopT1-β ⟫
      ap to loopT1                           =⟪ ! (thing base) |in-ctx ap to ⟫
      ap to (ap (λ z → from-c z base) loop)  =⟪ ! (ap-∘ to (λ z → from-c z base) loop) ⟫
      ap (λ z → to (from-c z base)) loop ∎∎

    to-from-c-loop-base : idp == idp [ (λ x → to (from-c x base) == (x , base)) ↓ loop ]
    to-from-c-loop-base = ↓-='-in (↯ to-from-c-loop-base2)
  
    lemma : ↯ to-from-c-loop-base2 == ↯ to-from-c-loop-base2 [ (λ y → to-from-c-base y ∙ ap (λ x → x , y) loop == ap (λ x → to (from-c x y)) loop ∙' to-from-c-base y) ↓ loop ]
    lemma = ↓-=-in (
      (↯ to-from-c-loop-base2) ◃ apd (λ y → ap (λ x → to (from-c x y)) loop ∙' to-from-c-base y) loop  =⟨ {!!} ⟩
      (↯ to-from-c-loop-base2) ◃ ((apd (λ y → ap (λ x → to (from-c x y)) loop) loop) ∙'2 (apd to-from-c-base loop)) =⟨ {!!} ⟩
      ((↯ to-from-c-loop-base2) ◃ (apd (λ y → ap (λ x → to (from-c x y)) loop) loop)) ∙'2 (apd to-from-c-base loop) =⟨ {!!} ⟩
      ((↯ (to-from-c-loop-base2 !1)) ◃ ((apd (λ y → ap to (ap (λ x → from-c x y) loop)) loop) ▹ (↯ to-from-c-loop-base2 #1))) ∙'2 (apd to-from-c-base loop) =⟨ {!!} ⟩
      ((↯ (to-from-c-loop-base2 !2)) ◃ ((apd (λ y → ap to (from-c-loop' y)) loop) ▹ (↯ to-from-c-loop-base2 #2))) ∙'2 (apd to-from-c-base loop) =⟨ {!!} ⟩
      ((↯ (to-from-c-loop-base2 !2)) ◃ ((ap↓ (ap to) (apd from-c-loop' loop)) ▹ (↯ to-from-c-loop-base2 #2))) ∙'2 (apd to-from-c-base loop) =⟨ {!!} ⟩
      ((↯ (to-from-c-loop-base2 !2)) ◃ ((ap↓ (ap to) from-c-loop-loop) ▹ (↯ to-from-c-loop-base2 #2))) ∙'2 (apd to-from-c-base loop) =⟨ {!!} ⟩
      apd (λ y → to-from-c-base y ∙ ap (λ x → x , y) loop) loop ▹ (↯ to-from-c-loop-base2) ∎)


{-
Have: PathOver (λ z → to (from-c-base z) == to (from-c-base z))
      loop (ap (λ x → x , base) loop)
      (ap (λ x → to (from-c x base)) loop)

-}

    -- lemma2 : apd (λ y → ap (λ x → to (from-c x y)) loop) loop == {!!}
    -- lemma2 =
    --   apd (λ y → ap (λ x → to (from-c x y)) loop) loop   =⟨ {!!} ⟩
    --   apd (λ y → ap to (ap (λ x → from-c x y) loop)) loop   =⟨ {!!} ⟩
    --   apd (λ y → ap to (from-c-loop' y)) loop   =⟨ {!!} ⟩
    --   api2 (ap to) (apd from-c-loop' loop)   =⟨ {!!} ⟩
    --   apd (ap to) surfT   =⟨ {!!} ⟩
    --   ? ∎

to-from : (x : S¹ × S¹) → to (from x) == x
to-from (x , y) = to-from-c x y

{- Second composition -}

from-to : (x : Torus) → from (to x) == x
from-to = {!Torus-elim idp from-to-loopT1 from-to-loopT2 {!!}!}
  where

  from-to-loopT1 : idp == idp [ (λ z → from (to z) == z) ↓ loopT1 ]
  from-to-loopT1 = ↓-∘=idf-in from to
    (ap from (ap to loopT1)                =⟨ To.loopT1-β |in-ctx ap from ⟩
    ap from (pair×= loop idp)             =⟨ lemma from loop (idp {a = base}) ⟩
    ap (λ u → u base) (ap from-c loop)    =⟨ FromC.loop-β |in-ctx ap (λ u → u base) ⟩
    ap (λ u → u base) (λ= from-c-loop')   =⟨ app=-β from-c-loop' base ⟩
    loopT1 ∎)  where

      lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A × B → C)
        {x y : A} (p : x == y) {z t : B} (q : z == t)
        → ap f (pair×= p q) == app= (ap (curry f) p) z ∙' ap (curry f y) q
      lemma f idp idp = idp


  from-to-loopT2 : idp == idp [ (λ z → from (to z) == z) ↓ loopT2 ]
  from-to-loopT2 = ↓-∘=idf-in from to
    (ap from (ap to loopT2)                =⟨ To.loopT2-β |in-ctx ap from ⟩
    ap from (pair×= idp loop)             =⟨ lemma' from (idp {a = base}) loop ⟩
    ap from-c-base loop    =⟨ FromCBase.loop-β ⟩
    loopT2 ∎)  where

      lemma' : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A × B → C)
        {x y : A} (p : x == y) {z t : B} (q : z == t)
        → ap f (pair×= p q) == ap (curry f x) q ∙' app= (ap (curry f) p) t
      lemma' f idp idp = idp

-- to-from-c-app-base : (y : S¹) → to (from-c y base) == (y , base)
-- to-from-c-app-base = S¹-elim {!to (from-c base base) == base , base!} {!!}
