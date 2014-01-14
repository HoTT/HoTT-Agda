open import HoTT

module cohomology.Exactness where

module _ {i} {j} {k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (F : fst (X ∙→ Y)) (G : fst (Y ∙→ Z)) where

  private
    f = fst F
    g = fst G

  {- in kernel of G ⇒ in image of F -}
  is-exact-ktoi : Type (lmax k (lmax j i))
  is-exact-ktoi = (y : fst Y) → g y == snd Z → Σ (fst X) (λ x → f x == y)

  is-exact-ktoi-mere : Type (lmax k (lmax j i))
  is-exact-ktoi-mere = (y : fst Y) → g y == snd Z 
    → Trunc ⟨-1⟩ (Σ (fst X) (λ x → f x == y))

  {- in image of F ⇒ in kernel of G -}  
  is-exact-itok : Type (lmax k i)
  is-exact-itok = (x : fst X) → g (f x) == snd Z
