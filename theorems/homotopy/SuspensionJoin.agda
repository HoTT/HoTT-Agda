{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.SuspensionJoin {i} (A : Type i) where

{- To -}

false, : A → Bool × A
false, a = false , a

true, : A → Bool × A
true, a = true , a

module To = SuspensionRec {i} A {_} {Bool * A} (left false :> Bool * A) (left true) (λ a → glue (false, a) ∙ ! (glue (true, a)))

to : Suspension A → (Bool * A)
to = To.f

{- From -}

from : Bool * A → Suspension A
from = From.f  module _ where

  from-bool : Bool → Suspension A
  from-bool false = north A
  from-bool true = south A

  from-glue : (c : Bool × A) → from-bool (fst c) == south A
  from-glue (false , a) = merid A a
  from-glue (true , a) = idp

  module From = PushoutRec {d = *-span Bool A} from-bool (λ _ → south A) from-glue

{- ToFrom -}

to-from : (c : Bool * A) → to (from c) == c
to-from = Pushout-elim to-from-left (λ a → glue (true , a)) to-from-glue  where

  to-from-left : (b : Bool) → to (from (left b)) == left b
  to-from-left false = idp
  to-from-left true = idp

  to-from-glue' : (b : Bool) (a : A)
    → ap to (ap from (glue (b , a))) ∙' glue (true , a) == to-from-left b ∙ glue (b , a)
  to-from-glue' true a =
    ap to (ap from (glue (true , a))) ∙' glue (true , a)   =⟨ From.glue-β (true , a) |in-ctx (λ u → ap to u ∙' glue (true , a)) ⟩
    idp ∙' glue (true , a)                                 =⟨ ∙'-unit-l _ ⟩
    glue (true , a) ∎
  to-from-glue' false a =
    ap to (ap from (glue (false , a))) ∙' glue (true , a)   =⟨ From.glue-β (false , a) |in-ctx (λ u → ap to u ∙' glue (true , a)) ⟩
    ap to (merid A a) ∙' glue (true , a)   =⟨ To.glue-β a |in-ctx (λ u → u ∙' glue (true , a)) ⟩
    (glue (false , a) ∙ ! (glue (true , a))) ∙' glue (true , a)   =⟨ coh (glue (false , a)) (glue (true , a)) ⟩
    glue (false , a) ∎  where

    coh : ∀ {i} {A : Type i} {a b c : A} (p : a == b) (q : c == b) → (p ∙ ! q) ∙' q == p
    coh idp idp = idp

  to-from-glue : (c : Bool × A)
    → to-from-left (fst c) == glue (true , snd c) [ (λ z → to (from z) == z) ↓ glue c ]
  to-from-glue c = ↓-∘=idf-in to from (uncurry to-from-glue' c)

{- FromTo -}

from-to : (c : Suspension A) → from (to c) == c
from-to = Suspension-elim A idp idp from-to-merid  where

  from-to-merid' : (a : A) → ap from (ap to (merid A a)) == merid A a
  from-to-merid' a =
    ap from (ap to (merid A a))   =⟨ To.glue-β a |in-ctx ap from ⟩
    ap from (glue (false , a) ∙ ! (glue (true , a)))   =⟨ ap-∙ from (glue (false , a)) (! (glue (true , a))) ⟩
    ap from (glue (false , a)) ∙ ap from (! (glue (true , a)))   =⟨ ap-! from (glue (true , a)) |in-ctx (λ u → ap from (glue (false , a)) ∙ u) ⟩
    ap from (glue (false , a)) ∙ ! (ap from (glue (true , a)))   =⟨ From.glue-β (false , a) |in-ctx (λ u → u ∙ ! (ap from (glue (true , a)))) ⟩
    merid A a ∙ ! (ap from (glue (true , a)))   =⟨ From.glue-β (true , a) |in-ctx (λ u → merid A a ∙ ! u) ⟩
    merid A a ∙ idp   =⟨ ∙-unit-r _ ⟩
    merid A a ∎

  from-to-merid : (a : A) → idp == idp [ (λ z → from (to z) == z) ↓ merid A a ]
  from-to-merid a = ↓-∘=idf-in from to (from-to-merid' a)

{- Conclusion -}

e : Suspension A ≃ (Bool * A)
e = equiv to from to-from from-to

