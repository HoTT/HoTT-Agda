{-# OPTIONS --without-K #-}

open import HoTT

{- Proof that if [A] and [B] are two propositions, then so is [A * B]. -}

module homotopy.PropJoinProp
  {i} (A : Type i) {pA : (a a' : A) → a == a'}
  {j} (B : Type j) {pB : (b b' : B) → b == b'} where

{-
We first prove that [left a == y] for all [a : A] and [y : A * B].
For that we will need the coherence condition [coh1] below.
-}

eq-left : (a : A) (y : A * B) → left a == y
eq-left = EqLeft.f  module M where

  coh1 : {b' : B} {a a' : A} (p : a == a')
    → ap left p ∙ glue (a' , b') == glue (a , b') :> (left a == right b' :> A * B)
  coh1 idp = idp

  module EqLeft (a : A) =
    PushoutElim (λ a' → ap left (pA a a'))
                (λ b' → glue (a , b'))
                (λ {(a' , b') → ↓-cst=idf-in (coh1 (pA a a'))})

open M

{-
Now we prove that [right b == y] for all [b : B] and [y : A * B].
We will again need some coherence condition [coh2].
-}

eq-right : (b : B) (y : A * B) → right b == y
eq-right = EqRight.f  module M' where

  coh2 : {a' : A} {b b' : B} (p : b == b')
    → ! (glue (a' , b)) ∙ glue (a' , b') == ap right p :> (right b == right b' :> A * B)
  coh2 idp = !-inv-l (glue _)

  module EqRight (b : B) =
    PushoutElim (λ a' → ! (glue (a' , b)))
                (λ b' → ap right (pB b b'))
                (λ {(a' , b') → ↓-cst=idf-in (coh2 (pB b b'))})

open M'

{-
Then we prove the missing cases.
For the cases [x == left a'] and [x == right b'] we will need the coherence
conditions [coh3] and [coh4].
For the last case, we need a "2-dimensional" coherence condition [coh²],
relating [coh1], [coh2], [coh3] and [coh4].
-}

eq : (x y : A * B) → x == y
eq = Pushout-elim eq-left eq-right
       (λ {(a , b) → ↓-cst→app-in (Pushout-elim (λ a' → ↓-idf=cst-in (coh3 (pA a a')))
                                                (λ b' → ↓-idf=cst-in (coh4 (pB b b')))
                                                (λ {(a' , b') → ↓-idf=cst-in=↓ (↓-=-in
   (coh3 (pA a a') ◃ apd (λ x → glue (a , b) ∙' eq-right b x) (glue (a' , b'))
          =⟨ apd∙' (λ x → glue (a , b)) (eq-right b) (glue (a' , b')) |in-ctx (λ u → coh3 (pA a a') ◃ u) ⟩
    coh3 (pA a a') ◃ (apd (λ x → glue (a , b)) (glue (a' , b')) ∙'2ᵈ apd (eq-right b) (glue (a' , b')))
          =⟨ EqRight.glue-β b (a' , b') |in-ctx (λ u → coh3 (pA a a') ◃ (apd (λ x → glue (a , b)) (glue (a' , b')) ∙'2ᵈ u)) ⟩
    coh3 (pA a a') ◃ (apd (λ x → glue (a , b)) (glue (a' , b')) ∙'2ᵈ ↓-cst=idf-in {p = glue _} {u = ! (glue _)} (coh2 (pB b b')))
          =⟨ coh² (pA a a') (pB b b') ⟩
    ↓-cst=idf-in (coh1 (pA a a')) ▹ coh4 (pB b b')
          =⟨ ! (EqLeft.glue-β a (a' , b')) |in-ctx (λ u → u ▹ coh4 (pB b b')) ⟩
    apd (eq-left a) (glue (a' , b')) ▹ coh4 (pB b b') ∎))}))})

  where


  coh3 : {b : B} {a a' : A} (p : a == a')
    → ap left p == (glue (a , b) ∙' ! (glue (a' , b))) :> (left a == left a' :> A * B)
  coh3 idp = ! (!-inv-r (glue _)) ∙ ∙=∙' (glue _) (! (glue _))

  coh4 : {a : A} {b b' : B} (p : b == b')
    → glue (a , b') == (glue (a , b) ∙' ap right p) :> (left a == right b' :> A * B)
  coh4 idp = idp

  {- Should go to lib.types.Paths -}
  ↓-idf=cst-in=↓ : ∀ {i} {A : Type i} {a a' : A} {p : a == a'} {a0 a0' : A} {p0 : a0 == a0'} {f : (a : A) → a0 == a} {g : (a : A) → a0' == a}
    {q : f a == p0 ∙' g a } {r : f a' == p0 ∙' g a'}
    → q == r [ (λ a → f a == p0 ∙' g a) ↓ p ]
    → ↓-idf=cst-in q == ↓-idf=cst-in r [ (λ a → f a == g a [ (λ x → x == a) ↓ p0 ]) ↓ p ]
  ↓-idf=cst-in=↓ {p = idp} {p0 = idp} idp = idp

  abstract
    coh² : {a a' : A} {b b' : B} (p : a == a') (q : b == b')
      → coh3 {b = b} p ◃ (apd (λ x → glue (a , b)) (glue (a' , b')) ∙'2ᵈ ↓-cst=idf-in {p = glue (a' , b')} {u = ! (glue (a' , b))} (coh2 q))
        == ↓-cst=idf-in (coh1 p) ▹ coh4 q
    coh² idp idp = aux (glue _)  where

      abstract
        aux : {x y : A * B} (p : x == y) →
              (! (!-inv-r p) ∙ ∙=∙' p (! p))
              ◃
              (apd (λ x → p) p ∙'2ᵈ ↓-cst=idf-in {p = p} {u = ! p} (!-inv-l p))
              == ↓-cst=idf-in idp ▹ idp
        aux idp = idp
