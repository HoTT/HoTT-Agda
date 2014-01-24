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

  ktoi-to-mere : is-exact-ktoi → is-exact-ktoi-mere
  ktoi-to-mere ie y p = [ ie y p ]

  {- in image of F ⇒ in kernel of G -}  
  is-exact-itok : Type (lmax k i)
  is-exact-itok = (x : fst X) → g (f x) == snd Z

  is-exact-itok-mere : Type (lmax k (lmax j i))
  is-exact-itok-mere = (y : fst Y) → Trunc ⟨-1⟩ (Σ (fst X) (λ x → f x == y))
    → g y == snd Z 

  itok-to-mere : has-level ⟨0⟩ (fst Z) → is-exact-itok → is-exact-itok-mere
  itok-to-mere pZ ie y = Trunc-rec 
    (pZ _ _)
    (λ {(x , p) → ap g (! p) ∙ ie x})
