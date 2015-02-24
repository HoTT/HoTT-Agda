{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory
open import cohomology.CofiberSequence

module cohomology.LongExactSequence {i} (CT : CohomologyTheory i)
  {X Y : Ptd i} (n : ℤ) (f : fst (X ⊙→ Y)) where

open CohomologyTheory CT
open import cohomology.Functor CT

co∂ : C n X →ᴳ C (succ n) (⊙Cof f)
co∂ = CF-hom (succ n) ⊙ext-glue ∘ᴳ fst ((C-Susp n X)⁻¹ᴳ)

long-cofiber-seq : HomSequence _ _
long-cofiber-seq =
  C n Y                ⟨ CF-hom n f                 ⟩→
  C n X                ⟨ co∂                        ⟩→
  C (succ n) (⊙Cof f)  ⟨ CF-hom (succ n) (⊙cfcod f) ⟩→
  C (succ n) Y         ⟨ CF-hom (succ n) f          ⟩→
  C (succ n) X         ⊣|

long-cofiber-exact : is-exact-seq long-cofiber-seq
long-cofiber-exact =
  transport
    (λ {(r , s) → is-exact-seq s})
    (pair= _ $ sequence-iso-ua _ _ $
      C-Susp n Y ↓⟨ C-SuspF n f ⟩↓
      C-Susp n X ↓⟨ hom= _ _ $ ap (λ w → fst (CF (succ n) ⊙ext-glue) ∘ w) $
                    ! $ λ= $ is-equiv.g-f (snd (C-Susp n X)) ⟩↓
      idiso _    ↓⟨ hom= _ _ idp ⟩↓
      idiso _    ↓⟨ hom= _ _ idp ⟩↓
      idiso _    ↓⊣|)
    (transport
      (λ {(_ , g , h) → is-exact-seq $
        _ ⟨ CF-hom (succ n) h ⟩→ _ ⟨ CF-hom (succ n) g ⟩→
        _ ⟨ CF-hom (succ n) (⊙cfcod f) ⟩→ _ ⟨ CF-hom (succ n) f ⟩→ _ ⊣|})
      (cofiber-sequence f)
      (exact-build
        (_ ⟨ CF-hom (succ n) (⊙cfcod³ f) ⟩→ _ ⟨ CF-hom (succ n) (⊙cfcod² f) ⟩→
         _ ⟨ CF-hom (succ n) (⊙cfcod f) ⟩→ _ ⟨ CF-hom (succ n) f ⟩→ _ ⊣|)
        (C-exact (succ n) (⊙cfcod² f))
        (C-exact (succ n) (⊙cfcod f)) (C-exact (succ n) f)))
