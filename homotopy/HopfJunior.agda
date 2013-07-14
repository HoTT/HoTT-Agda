{-# OPTIONS --without-K #-}

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

not-path : Bool == Bool
not-path = ua not-equiv

-- Definition of the junior Hopf fibration
HopfJunior : S¹ → Type₀
HopfJunior = S¹-rec Bool not-path

-- To compute the total space, we apply the flattening lemma
open import homotopy.Flattening
  Unit Unit (idf _) (idf _) (cst Bool) (cst not-equiv)
  renaming (eqv to flattening-eqv)

-- We get that the total space is the type Wt defined in the flattening lemma.
--
-- The version of the flattening lemma we’re using is a generic version, hence
-- the base type is not exactly S¹, but S¹ with some junky Unit added to both
-- constructors. The function [S¹-generic.eqv-tot] proves that the total space
-- of [HopfJunior] is the same as the total space of the corresponding junky
-- fibration considered in the flattening lemma.
tot-is-Wt : Σ S¹ HopfJunior == Wt
tot-is-Wt = S¹-generic.eqv-tot not-equiv ∙ ua flattening-eqv

-- Now we prove that Wt is equivalent to S¹

private
  -- Map from [Wt] to [S¹]
  to-cct : Unit × Bool → S¹
  to-cct _ = base

  to-ppt : (x : Unit × Bool) → to-cct x == to-cct x
  to-ppt (_ , true) = loop
  to-ppt (_ , false) = idp

  to : Wt → S¹
  to = Wt-rec to-cct to-ppt

  -- Map from [S¹] to [Wt]
  from-base : Wt
  from-base = cct tt true

  from-loop : from-base == from-base
  from-loop = ppt tt true ∙ ppt tt false

  from : S¹ → Wt
  from = S¹-rec from-base from-loop

  -- First composite
  to-from : (x : S¹) → to (from x) == x
  to-from = S¹-elim idp (↓-∘=idf-in to from
    (ap to (ap from loop)                       =⟨ loop-β' from-base from-loop |in-ctx ap to ⟩
     ap to (ppt tt true ∙ ppt tt false)         =⟨ ap-∙ to (ppt tt true) (ppt tt false) ⟩
     ap to (ppt tt true) ∙ ap to (ppt tt false) =⟨ ppt-β' to-cct to-ppt (tt , true) |in-ctx (λ u → u ∙ ap to (ppt tt false)) ⟩
     loop ∙ ap to (ppt tt false)                =⟨ ppt-β' to-cct to-ppt (tt , false) |in-ctx (λ u → loop ∙ u) ⟩
     loop ∙ idp                                 =⟨ ∙-unit-r loop ⟩
     loop ∎))

  -- Second composite
  from-to-cct : (b : Bool) → from (to (cct tt b)) == cct tt b
  from-to-cct true = idp
  from-to-cct false = ! (ppt tt false)

  from-to-ppt : (b : Bool) → ap from (ap to (ppt tt b)) ∙' from-to-cct (not b) == from-to-cct b ∙ ppt tt b
  from-to-ppt true =
    ap from (ap to (ppt tt true)) ∙' ! (ppt tt false) =⟨ ppt-β' to-cct to-ppt (tt , true) |in-ctx (λ u → ap from u ∙' ! (ppt tt false)) ⟩
    ap from loop ∙' ! (ppt tt false)                  =⟨ loop-β' from-base from-loop |in-ctx (λ u → u ∙' ! (ppt tt false)) ⟩
    (ppt tt true ∙ ppt tt false) ∙' ! (ppt tt false)  =⟨ lemma (ppt tt true) (ppt tt false) ⟩
    ppt tt true ∎  where
      lemma : ∀ {i} {A : Type i} {a b c : A} (p : a == b) (q : b == c) → (p ∙ q) ∙' (! q) == p
      lemma idp idp = idp
  from-to-ppt false =
    ap from (ap to (ppt tt false))                    =⟨ ppt-β' to-cct to-ppt (tt , false) |in-ctx ap from ⟩
    ap from (idp {a = base})                          =⟨ ! (!-inv-l (ppt tt false)) ⟩
    ! (ppt tt false) ∙ ppt tt false ∎

  from-to : (x : Wt) → from (to x) == x
  from-to = Wt-elim (from-to-cct ∘ snd) (λ b → ↓-∘=idf-in from to (from-to-ppt (snd b)))

  -- Conclusion
  subresult : Wt ≃ S¹
  subresult = equiv to from to-from from-to

-- Conclusion
result : Σ S¹ HopfJunior ≃ S¹
result = coe-equiv (tot-is-Wt ∙ ua subresult)
