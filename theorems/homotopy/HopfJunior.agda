{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.HopfJunior where

-- We define the negation function and prove that it’s an equivalence

not : Bool → Bool
not true = false
not false = true

not-not : (b : Bool) → not (not b) == b
not-not true = idp
not-not false = idp

not-equiv : Bool ≃ Bool
not-equiv = equiv not not not-not not-not

-- Definition of the junior Hopf fibration
module HopfJunior = S¹RecType Bool not-equiv
open HopfJunior using (module Wt; Wt; cct; ppt; flattening-S¹)

HopfJunior : S¹ → Type₀
HopfJunior = HopfJunior.f

-- We get that the total space is the type Wt defined in the flattening lemma.
tot-is-Wt : Σ S¹ HopfJunior == Wt
tot-is-Wt = flattening-S¹

-- Now we prove that Wt is equivalent to S¹

private
  -- Map from [Wt] to [S¹]
  to-cct : Unit × Bool → S¹
  to-cct _ = base

  to-ppt : (x : Unit × Bool) → to-cct x == to-cct x
  to-ppt (_ , true) = loop
  to-ppt (_ , false) = idp

  module To = Wt.Rec to-cct to-ppt

  to : Wt → S¹
  to = To.f

  -- Map from [S¹] to [Wt]
  from-base : Wt
  from-base = cct tt true

  from-loop : from-base == from-base
  from-loop = ppt tt true ∙ ppt tt false

  module From = S¹Rec from-base from-loop

  from : S¹ → Wt
  from = From.f

  -- First composite
  abstract
    to-from : (x : S¹) → to (from x) == x
    to-from = S¹-elim idp (↓-∘=idf-in' to from {p = loop}
      (ap to (ap from loop)                       =⟨ From.loop-β |in-ctx ap to ⟩
      ap to (ppt tt true ∙ ppt tt false)         =⟨ ap-∙ to (ppt tt true) (ppt tt false) ⟩
      ap to (ppt tt true) ∙ ap to (ppt tt false) =⟨ To.pp-β (tt , true) |in-ctx (λ u → u ∙ ap to (ppt tt false)) ⟩
      loop ∙ ap to (ppt tt false)                =⟨ To.pp-β (tt , false) |in-ctx (λ u → loop ∙ u) ⟩
      loop ∙ idp                                 =⟨ ∙-unit-r loop ⟩
      loop ∎))

  -- Second composite
  from-to-cct : (b : Bool) → from (to (cct tt b)) == cct tt b
  from-to-cct true = idp
  from-to-cct false = ! (ppt tt false)

  abstract
    from-to-ppt : (b : Bool) → ap from (ap to (ppt tt b)) ∙' from-to-cct (not b) == from-to-cct b ∙ ppt tt b
    from-to-ppt true =
      ap from (ap to (ppt tt true)) ∙' ! (ppt tt false) =⟨ To.pp-β (tt , true) |in-ctx (λ u → ap from u ∙' ! (ppt tt false)) ⟩
      ap from loop ∙' ! (ppt tt false)                  =⟨ From.loop-β |in-ctx (λ u → u ∙' ! (ppt tt false)) ⟩
      (ppt tt true ∙ ppt tt false) ∙' ! (ppt tt false)  =⟨ lemma (ppt tt true) (ppt tt false) ⟩
      ppt tt true ∎  where
        lemma : ∀ {i} {A : Type i} {a b c : A} (p : a == b) (q : b == c) → (p ∙ q) ∙' (! q) == p
        lemma idp idp = idp
    from-to-ppt false =
      ap from (ap to (ppt tt false))                    =⟨ To.pp-β (tt , false) |in-ctx ap from ⟩
      ap from (idp {a = base})                          =⟨ ! (!-inv-l (ppt tt false)) ⟩
      ! (ppt tt false) ∙ ppt tt false ∎

    from-to : (x : Wt) → from (to x) == x
    from-to = Wt.elim (from-to-cct ∘ snd) (λ b → ↓-∘=idf-in' from to {p = ppt tt (snd b)} (from-to-ppt (snd b)))

  -- Conclusion
  subresult : Wt ≃ S¹
  subresult = equiv to from to-from from-to

-- Conclusion
result : Σ S¹ HopfJunior ≃ S¹
result = subresult ∘e (coe-equiv tot-is-Wt)
