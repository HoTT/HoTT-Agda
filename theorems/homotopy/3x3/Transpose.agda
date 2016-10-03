{-# OPTIONS --without-K #-}

open import homotopy.3x3.Common
open import homotopy.3x3.PushoutPushout

module homotopy.3x3.Transpose where

open M using (Pushout^2)

type-of : ∀ {i} {A : Type i} (u : A) → Type i
type-of {A = A} _ = A

module _ {i} (d : Span^2 {i}) where

  open Span^2 d

  transpose-f : (f : type-of H₁₁ → _) (g : type-of H₃₃ → _) → Span^2
  transpose-f f g = span^2 A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄
                     f₁₀ f₃₀ f₁₂ f₃₂ f₁₄ f₃₄ f₀₁ f₀₃ f₂₁ f₂₃ f₄₁ f₄₃
                     (f H₁₁) H₃₁ H₁₃ (g H₃₃)

  transpose : Span^2
  transpose = span^2 A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄
                     f₁₀ f₃₀ f₁₂ f₃₂ f₁₄ f₃₄ f₀₁ f₀₃ f₂₁ f₂₃ f₄₁ f₄₃
                     (! ∘ H₁₁) H₃₁ H₁₃ (! ∘ H₃₃)

ch1 : ∀ {i j} {A : Type i} {x y : A} {p : x == y} {f g : A → Type j} {a : f x → g x} {b : f y → g y}
  → (a == b [ (λ u → f u → g u) ↓ p ]) → (a == b [ (λ u → fst u → snd u) ↓ pair×= (ap f p) (ap g p)])
ch1 {p = idp} α = α

ch2 : ∀ {i j} {X : Type i} {x y : X} {p : x == y}
  {A B₁ B₂ C : X → Type j}
  {f₁ : (x : X) → A x → B₁ x} {g₁ : (x : X) → B₁ x → C x}
  {f₂ : (x : X) → A x → B₂ x} {g₂ : (x : X) → B₂ x → C x}
  {a : _} {b : _}
  → (a == b [ (λ z → (x : A z) → g₁ z (f₁ z x) == g₂ z (f₂ z x)) ↓ p ])
  → (a == b [ (λ u → (x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x))
            ↓ square=-raw (ap A p) (ap B₁ p) (ap B₂ p) (ap C p) (ch1 (apd f₁ p)) (ch1 (apd f₂ p)) (ch1 (apd g₁ p)) (ch1 (apd g₂ p)) ])
ch2 {p = idp} α = α

ap-span^2=-priv : ∀ {i} {d d' : Span^2 {i}} (p : d == d')
    → ap transpose p == span^2=-raw (ap Span^2.A₀₀ p) (ap Span^2.A₂₀ p) (ap Span^2.A₄₀ p)
                                    (ap Span^2.A₀₂ p) (ap Span^2.A₂₂ p) (ap Span^2.A₄₂ p)
                                    (ap Span^2.A₀₄ p) (ap Span^2.A₂₄ p) (ap Span^2.A₄₄ p)
                                    (ch1 (apd Span^2.f₁₀ p)) (ch1 (apd Span^2.f₃₀ p))
                                    (ch1 (apd Span^2.f₁₂ p)) (ch1 (apd Span^2.f₃₂ p))
                                    (ch1 (apd Span^2.f₁₄ p)) (ch1 (apd Span^2.f₃₄ p))
                                    (ch1 (apd Span^2.f₀₁ p)) (ch1 (apd Span^2.f₀₃ p))
                                    (ch1 (apd Span^2.f₂₁ p)) (ch1 (apd Span^2.f₂₃ p))
                                    (ch1 (apd Span^2.f₄₁ p)) (ch1 (apd Span^2.f₄₃ p))
                                    (ch2 (ap↓ (λ u → ! ∘ u) (apd Span^2.H₁₁ p))) (ch2 (apd Span^2.H₃₁ p))
                                    (ch2 (apd Span^2.H₁₃ p)) (ch2 (ap↓ (λ u → ! ∘ u) (apd Span^2.H₃₃ p)))
ap-span^2=-priv {i} {d} {.d} idp = idp

ap-span^2=-priv2 : ∀ {i}
  {A₀₀ A₀₀' : Type i} (eq-A₀₀ : A₀₀ == A₀₀')
  {A₀₂ A₀₂' : Type i} (eq-A₀₂ : A₀₂ == A₀₂')
  {A₀₄ A₀₄' : Type i} (eq-A₀₄ : A₀₄ == A₀₄')
  {A₂₀ A₂₀' : Type i} (eq-A₂₀ : A₂₀ == A₂₀')
  {A₂₂ A₂₂' : Type i} (eq-A₂₂ : A₂₂ == A₂₂')
  {A₂₄ A₂₄' : Type i} (eq-A₂₄ : A₂₄ == A₂₄')
  {A₄₀ A₄₀' : Type i} (eq-A₄₀ : A₄₀ == A₄₀')
  {A₄₂ A₄₂' : Type i} (eq-A₄₂ : A₄₂ == A₄₂')
  {A₄₄ A₄₄' : Type i} (eq-A₄₄ : A₄₄ == A₄₄')
  {f₀₁ : A₀₂ → A₀₀} {f₀₁' : A₀₂' → A₀₀'} (eq-f₀₁ : f₀₁ == f₀₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A₀₂ eq-A₀₀ ])
  {f₀₃ : A₀₂ → A₀₄} {f₀₃' : A₀₂' → A₀₄'} (eq-f₀₃ : f₀₃ == f₀₃' [ (λ u → fst u → snd u) ↓ pair×= eq-A₀₂ eq-A₀₄ ])
  {f₂₁ : A₂₂ → A₂₀} {f₂₁' : A₂₂' → A₂₀'} (eq-f₂₁ : f₂₁ == f₂₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₂₀ ])
  {f₂₃ : A₂₂ → A₂₄} {f₂₃' : A₂₂' → A₂₄'} (eq-f₂₃ : f₂₃ == f₂₃' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₂₄ ])
  {f₄₁ : A₄₂ → A₄₀} {f₄₁' : A₄₂' → A₄₀'} (eq-f₄₁ : f₄₁ == f₄₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A₄₂ eq-A₄₀ ])
  {f₄₃ : A₄₂ → A₄₄} {f₄₃' : A₄₂' → A₄₄'} (eq-f₄₃ : f₄₃ == f₄₃' [ (λ u → fst u → snd u) ↓ pair×= eq-A₄₂ eq-A₄₄ ])
  {f₁₀ : A₂₀ → A₀₀} {f₁₀' : A₂₀' → A₀₀'} (eq-f₁₀ : f₁₀ == f₁₀' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₀ eq-A₀₀ ])
  {f₃₀ : A₂₀ → A₄₀} {f₃₀' : A₂₀' → A₄₀'} (eq-f₃₀ : f₃₀ == f₃₀' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₀ eq-A₄₀ ])
  {f₁₂ : A₂₂ → A₀₂} {f₁₂' : A₂₂' → A₀₂'} (eq-f₁₂ : f₁₂ == f₁₂' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₀₂ ])
  {f₃₂ : A₂₂ → A₄₂} {f₃₂' : A₂₂' → A₄₂'} (eq-f₃₂ : f₃₂ == f₃₂' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₄₂ ])
  {f₁₄ : A₂₄ → A₀₄} {f₁₄' : A₂₄' → A₀₄'} (eq-f₁₄ : f₁₄ == f₁₄' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₄ eq-A₀₄ ])
  {f₃₄ : A₂₄ → A₄₄} {f₃₄' : A₂₄' → A₄₄'} (eq-f₃₄ : f₃₄ == f₃₄' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₄ eq-A₄₄ ])
  {H₁₁ : (x : A₂₂) → f₁₀ (f₂₁ x) == f₀₁ (f₁₂ x)} {H₁₁' : (x : A₂₂') → f₁₀' (f₂₁' x) == f₀₁' (f₁₂' x)}
  (eq-H₁₁ : H₁₁ == H₁₁' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                        ↓ square=-raw eq-A₂₂ eq-A₂₀ eq-A₀₂ eq-A₀₀ eq-f₂₁ eq-f₁₂ eq-f₁₀ eq-f₀₁ ])
  {H₁₃ : (x : A₂₂) → f₀₃ (f₁₂ x) == f₁₄ (f₂₃ x)} {H₁₃' : (x : A₂₂') → f₀₃' (f₁₂' x) == f₁₄' (f₂₃' x)}
  (eq-H₁₃ : H₁₃ == H₁₃' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                        ↓ square=-raw eq-A₂₂ eq-A₀₂ eq-A₂₄ eq-A₀₄ eq-f₁₂ eq-f₂₃ eq-f₀₃ eq-f₁₄ ])
  {H₃₁ : (x : A₂₂) → f₃₀ (f₂₁ x) == f₄₁ (f₃₂ x)} {H₃₁' : (x : A₂₂') → f₃₀' (f₂₁' x) == f₄₁' (f₃₂' x)}
  (eq-H₃₁ : H₃₁ == H₃₁' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                        ↓ square=-raw eq-A₂₂ eq-A₂₀ eq-A₄₂ eq-A₄₀ eq-f₂₁ eq-f₃₂ eq-f₃₀ eq-f₄₁ ])
  {H₃₃ : (x : A₂₂) → f₄₃ (f₃₂ x) == f₃₄ (f₂₃ x)} {H₃₃' : (x : A₂₂') → f₄₃' (f₃₂' x) == f₃₄' (f₂₃' x)}
  (eq-H₃₃ : H₃₃ == H₃₃' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                        ↓ square=-raw eq-A₂₂ eq-A₄₂ eq-A₂₄ eq-A₄₄ eq-f₃₂ eq-f₂₃ eq-f₄₃ eq-f₃₄ ])
    → ap transpose (span^2=-raw eq-A₀₀ eq-A₀₂ eq-A₀₄ eq-A₂₀ eq-A₂₂ eq-A₂₄ eq-A₄₀ eq-A₄₂ eq-A₄₄ eq-f₀₁ eq-f₀₃ eq-f₂₁ eq-f₂₃ eq-f₄₁ eq-f₄₃ eq-f₁₀ eq-f₃₀ eq-f₁₂ eq-f₃₂ eq-f₁₄ eq-f₃₄ eq-H₁₁ eq-H₁₃ eq-H₃₁ eq-H₃₃)
   == span^2=-raw eq-A₀₀ eq-A₂₀ eq-A₄₀ eq-A₀₂ eq-A₂₂ eq-A₄₂ eq-A₀₄ eq-A₂₄ eq-A₄₄ eq-f₁₀ eq-f₃₀ eq-f₁₂ eq-f₃₂ eq-f₁₄ eq-f₃₄ eq-f₀₁ eq-f₀₃ eq-f₂₁ eq-f₂₃ eq-f₄₁ eq-f₄₃ (square-thing _ _ _ _ _ _ _ _ (ap↓ (λ u → ! ∘ u) eq-H₁₁)) eq-H₃₁ eq-H₁₃ (square-thing _ _ _ _ _ _ _ _ (ap↓ (λ u → ! ∘ u) eq-H₃₃))
ap-span^2=-priv2 idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp = idp

module _ {i} (d : Span^2 {i}) where

  open Span^2 d

  transpose-transpose : transpose (transpose d) == d
  transpose-transpose = span^2=-raw idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp
                        (λ= (!-! ∘ Span^2.H₁₁ d)) idp idp (λ= (!-! ∘ Span^2.H₃₃ d))

module _ {i} (d : Span^2 {i}) where

  transpose-equiv : Span^2 {i} ≃ Span^2
  transpose-equiv = equiv transpose transpose transpose-transpose transpose-transpose

module _ {i} (d : Span^2 {i}) where

  open Span^2 d

  d' : (H₁₁' : type-of H₁₁) (H₃₃' : type-of H₃₃) → Span^2
  d' H₁₁' H₃₃' = record d {H₁₁ = H₁₁'; H₃₃ = H₃₃'}

  e : {H₁₁' : type-of H₁₁} (eq₁ : H₁₁ == H₁₁') {H₃₃' : type-of H₃₃} (eq₃ : H₃₃ == H₃₃') (c : M.A₂∙ (d' H₁₁' H₃₃'))
      → left (M.f₁∙ (d' H₁₁' H₃₃') c) == right (M.f₃∙ (d' H₁₁' H₃₃') c)
  e {H₁₁'} eq₁ {H₃₃'} eq₃ = E.f  module _ where

    e-glue : {H₁₁' : type-of H₁₁} (eq₁ : H₁₁ == H₁₁') {H₃₃' : type-of H₃₃} (eq₃ : H₃₃ == H₃₃') (c : Span^2.A₂₂ (d' H₁₁' H₃₃'))
      → glue (left (f₂₁ c)) == glue (right (f₂₃ c)) [ (λ z → left (M.f₁∙ (d' H₁₁' H₃₃') z) == right (M.f₃∙ (d' H₁₁' H₃₃') z)) ↓ glue c ]
    e-glue idp idp c = apd glue (glue c)

    module E = PushoutElim {P = λ c → left (M.f₁∙ (d' H₁₁' H₃₃') c) == right (M.f₃∙ (d' H₁₁' H₃₃') c) :> Pushout^2 d} (glue ∘ left) (glue ∘ right) (e-glue eq₁ eq₃)

  module F {H₁₁' : type-of H₁₁} (eq₁ : H₁₁ == H₁₁') {H₃₃' : type-of H₃₃} (eq₃ : H₃₃ == H₃₃')
    = PushoutRec {d = M.v-h-span (d' H₁₁' H₃₃')} {D = Pushout^2 d}
                 left right (e eq₁ eq₃)

  tr-tr-fun : Pushout^2 (transpose (transpose d)) → Pushout^2 d
  tr-tr-fun = F.f (! (λ= (!-! ∘ H₁₁))) (! (λ= (!-! ∘ H₃₃)))

  lemma12 : (c : M.A₂∙ d) → e idp idp c == glue c
  lemma12 = Pushout-elim (λ a → idp) (λ b → idp) (λ c → ↓-=-in (! (E.glue-β idp idp c)))

  result' : {H₁₁' : type-of H₁₁} (eq₁ : H₁₁ == H₁₁') {H₃₃' : type-of H₃₃} (eq₃ : H₃₃ == H₃₃') (x : Pushout^2 (d' H₁₁' H₃₃'))
    → transport Pushout^2 (span^2=-raw idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp (! eq₁) idp idp (! eq₃) :> (d' H₁₁' H₃₃' == d)) x == F.f eq₁ eq₃ x
  result' idp idp = Pushout-elim (λ a → idp) (λ b → idp) (λ c → ↓-='-in' (F.glue-β idp idp c ∙ lemma12 c ∙ ! (ap-idf (glue c))))

  result : {H₁₁' : type-of H₁₁} (eq₁ : H₁₁' == H₁₁) {H₃₃' : type-of H₃₃} (eq₃ : H₃₃' == H₃₃) (x : Pushout^2 (d' H₁₁' H₃₃'))
    → transport Pushout^2 (span^2=-raw idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp eq₁ idp idp eq₃ :> (d' H₁₁' H₃₃' == d)) x == F.f (! eq₁) (! eq₃) x
  result eq₁ eq₃ x = ap (λ u → transport Pushout^2 (span^2=-raw idp idp idp idp idp idp idp idp idp idp idp idp idp
                                                                idp idp idp idp idp idp idp idp (fst u) idp idp (snd u) :> (_ == d)) x)
                        (pair×= (! (!-! eq₁)) (! (!-! eq₃)))
                     ∙ result' (! eq₁) (! eq₃) x

  result2 : (x : Pushout^2 (transpose (transpose d))) → transport Pushout^2 (transpose-transpose d) x == tr-tr-fun x
  result2 = result (λ= (!-! ∘ Span^2.H₁₁ d)) (λ= (!-! ∘ Span^2.H₃₃ d))

-- module _ {i} where

--   postulate
--     to : (d : Span^2 {i}) → Pushout^2 d → Pushout^2 (transpose d)

--   from : (d : Span^2 {i}) → Pushout^2 (transpose d) → Pushout^2 d
--   from d = tr-tr-fun d ∘ to (transpose d)

--   postulate
--     from-to : (d : Span^2 {i}) (x : Pushout^2 d) → from d (to d x) == x

--   lemma3 : {d d' : Span^2 {i}} (p : d == d') (x : Pushout^2 d) → transport (Pushout^2 ∘ transpose) p (to d x) == to d' (transport Pushout^2 p x)
--   lemma3 {d} {.d} idp x = idp

--   lemma34 : (d : Span^2 {i}) (x : Pushout^2 (transpose (transpose d))) → transport (Pushout^2 ∘ transpose) (transpose-transpose d) (to (transpose (transpose d)) x) == to d (tr-tr-fun d x)
--   lemma34 d x = lemma3 (transpose-transpose d) x ∙ ap (to d) (result2 d x)

--   lm2 : (d : Span^2 {i}) → ap transpose (transpose-transpose d) == transpose-transpose (transpose d)
--   lm2 d = ap-span^2=-priv2 idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp
--                         (! (! (λ= (!-! ∘ Span^2.H₁₁ d)))) idp idp (! (! (λ= (!-! ∘ Span^2.H₃₃ d)))) ∙ ap (λ u → span^2=-raw idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp (fst u) idp idp (snd u)) (pair×= (lm3 (Span^2.H₁₁ d)) (lm3 (Span^2.H₃₃ d))) where

--     lm3 : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B} (p : (a : A) → f a == g a)
--       → ap (λ f → ! ∘ f) (! (! (λ= (!-! ∘ p)))) == ! (! (λ= (!-! ∘ ! ∘ p)))
--     lm3 p = transport (λ u → ap (λ f → ! ∘ f) (! (! (λ= (!-! ∘ u)))) == ! (! (λ= (!-! ∘ ! ∘ u)))) (λ= (app=-β p)) (lm3' (λ= p))  where

--       lm3' : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B} (p : f == g)
--         → ap (λ f → ! ∘ f) (! (! (λ= (!-! ∘ app= p)))) == ! (! (λ= (!-! ∘ ! ∘ app= p)))
--       lm3' idp = ap (λ u → ap (λ u → ! ∘ u) (! (! u))) (! (λ=-η idp)) ∙ ap (! ∘ !) (λ=-η idp)

--   lemma345 : (d : Span^2 {i}) (x : Pushout^2 (transpose (transpose (transpose d))))
--     → transport (Pushout^2 ∘ transpose) (transpose-transpose d) x == tr-tr-fun (transpose d) x
--   lemma345 d x =
--     transport (Pushout^2 ∘ transpose) (transpose-transpose d) x
--       =⟨ ap (λ u → coe u x) (ap-∘ Pushout^2 transpose (transpose-transpose d)) ⟩
--     transport Pushout^2 (ap transpose (transpose-transpose d)) x
--       =⟨ ap (λ u → transport Pushout^2 u x) (lm2 d) ⟩
--     transport Pushout^2 (transpose-transpose (transpose d)) x
--       =⟨ result2 (transpose d) x ⟩
--     tr-tr-fun (transpose d) x ∎

--   to-from : (d : Span^2 {i}) (x : Pushout^2 (transpose d)) → to d (from d x) == x
--   to-from d x =
--     to d (tr-tr-fun d (to (transpose d) x))
--       =⟨ ! (lemma34 d (to (transpose d) x)) ⟩
--     transport (Pushout^2 ∘ transpose) (transpose-transpose d) (to (transpose (transpose d)) (to (transpose d) x))
--       =⟨ lemma345 d (to (transpose (transpose d)) (to (transpose d) x)) ⟩
--     tr-tr-fun (transpose d) (to (transpose (transpose d)) (to (transpose d) x))
--       =⟨ from-to (transpose d) x ⟩
--     x ∎
