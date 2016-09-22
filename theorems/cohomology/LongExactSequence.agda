{-# OPTIONS --without-K #-}

open import HoTT
open import groups.ExactSequence
open import homotopy.FunctionOver
open import cohomology.Theory
open import cohomology.CofiberSequence

module cohomology.LongExactSequence {i} (CT : CohomologyTheory i)
  {X Y : Ptd i} (n : ℤ) (f : fst (X ⊙→ Y)) where

open CohomologyTheory CT
open import cohomology.Functor CT
open import cohomology.BaseIndependence CT

co∂ : C n X →ᴳ C (succ n) (⊙Cof f)
co∂ = CF-hom (succ n) ⊙ext-glue ∘ᴳ fst ((C-Susp n X)⁻¹ᴳ)

long-cofiber-seq : HomSequence _ _
long-cofiber-seq =
  C n Y                ⟨ CF-hom n f                  ⟩→
  C n X                ⟨ co∂                         ⟩→
  C (succ n) (⊙Cof f)  ⟨ CF-hom (succ n) (⊙cfcod' f) ⟩→
  C (succ n) Y         ⟨ CF-hom (succ n) f           ⟩→
  C (succ n) X         ⊣|

long-cofiber-exact : is-exact-seq long-cofiber-seq
long-cofiber-exact =
  {- apply the suspension isomorphism -}
  transport
    (λ {(r , s) → is-exact-seq s})
    (pair= _ $ sequence= _ _ $
      uaᴳ (C-Susp n Y)
        ∥⟨ C-Susp-↓ n f ⟩∥
      uaᴳ (C-Susp n X)
        ∥⟨ ↓-over-×-in _→ᴳ_
             (domain-over-iso
               (λ= (! ∘ ap (GroupHom.f (CF-hom _ ⊙ext-glue))
                      ∘ is-equiv.g-f (snd (C-Susp n X)))
                ◃ domain-over-equiv _ _))
             idp ⟩∥
      idp    ∥⟨ idp ⟩∥
      idp    ∥⟨ idp ⟩∥
      idp    ∥⊣|)
    {- fix the function basepoints -}
    (transport
      (λ {(φ , ψ) → is-exact-seq $
        _ ⟨ φ ⟩→ _ ⟨ ψ ⟩→
        _ ⟨ CF-hom (succ n) (⊙cfcod' f) ⟩→ _ ⟨ CF-hom (succ n) f ⟩→ _ ⊣|})
      (pair×= (CF-base-indep (succ n) _ _ _)
              (CF-base-indep (succ n) _ _ _))
      {- do the CofiberSequence transport -}
      (transport {A = Σ _ (λ {((U , V) , g , h) →
                        (g cfbase == snd U) × (h (snd U) == snd V)})}
        (λ {((_ , g , h) , (p , q)) → is-exact-seq $
          _ ⟨ CF-hom (succ n) (h , q)     ⟩→ _ ⟨ CF-hom (succ n) (g , p) ⟩→
          _ ⟨ CF-hom (succ n) (⊙cfcod' f) ⟩→ _ ⟨ CF-hom (succ n) f ⟩→ _ ⊣|})
        (pair= (cofiber-sequence f)
               (↓-×-in (from-transp _ _ idp) (from-transp _ _ idp)))
        (exact-build
          (_ ⟨ CF-hom (succ n) (⊙cfcod³ f) ⟩→ _ ⟨ CF-hom (succ n) (⊙cfcod² f) ⟩→
           _ ⟨ CF-hom (succ n) (⊙cfcod' f) ⟩→ _ ⟨ CF-hom (succ n) f ⟩→ _ ⊣|)
          (C-exact (succ n) (⊙cfcod² f))
          (C-exact (succ n) (⊙cfcod' f)) (C-exact (succ n) f))))
