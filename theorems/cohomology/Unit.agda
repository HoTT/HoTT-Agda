{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

module cohomology.Unit {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT
open import cohomology.BaseIndependence CT

module _ (n : ℤ) where

  private
    ⊙LU = ⊙Lift {j = i} ⊙Unit

  abstract
    C-Unit : is-trivialᴳ (C n ⊙LU)
    C-Unit x =
      x
        =⟨ ! (CEl-fmap-idf n x) ⟩
      CEl-fmap n (⊙idf _) x
        =⟨ CEl-fmap-base-indep' n (λ _ → idp) x ⟩
      CEl-fmap n (⊙cst ⊙∘ ⊙cfcod' (⊙idf _)) x
        =⟨ CEl-fmap-∘ n ⊙cst (⊙cfcod' (⊙idf _)) x ⟩
      CEl-fmap n (⊙cfcod' (⊙idf _)) (CEl-fmap n ⊙cst x)
        =⟨ ! (CEl-fmap-idf n (CEl-fmap n (⊙cfcod' (⊙idf _)) (CEl-fmap n ⊙cst x))) ⟩
      CEl-fmap n (⊙idf _) (CEl-fmap n (⊙cfcod' (⊙idf _)) (CEl-fmap n ⊙cst x))
        =⟨ im-sub-ker (C-exact n (⊙idf _)) _ [ CEl-fmap n ⊙cst x , idp ] ⟩
      Cident n ⊙LU
        =∎
