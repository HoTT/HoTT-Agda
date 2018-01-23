{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.FinProduct where

  Πᴳ-basis : ∀ {i} {I : ℕ} (F : Fin I → Group i)
    → (<I : Fin I) (g : Group.El (F <I))
    → Π (Fin I) (Group.El ∘ F)
  Πᴳ-basis F = Fin-basis (Group.⊙El ∘ F)

  Πᴳ-basis-late : ∀ {i} m {I : ℕ} (F : Fin (ℕ-S^' (S m) I) → Group i) <I g
    →  Πᴳ-basis F (Fin-S^' (S m) <I) g (Fin-S^' m (I , ltS))
    == Group.ident (F (Fin-S^' m (I , ltS)))
  Πᴳ-basis-late m F = Fin-basis-late m (Group.⊙El ∘ F)

  Πᴳ-basis-early : ∀ {i} m {I : ℕ} (F : Fin (ℕ-S^' (S m) I) → Group i) <I g
    →  Πᴳ-basis F (Fin-S^' m (I , ltS)) g (Fin-S^' (S m) <I)
    == Group.ident (F (Fin-S^' (S m) <I))
  Πᴳ-basis-early m F = Fin-basis-early m (Group.⊙El ∘ F)

  Πᴳ-basis-diag : ∀ {i} {I : ℕ} (F : Fin I → Group i) <I g
    → Πᴳ-basis F <I g <I == g
  Πᴳ-basis-diag F = Fin-basis-diag (Group.⊙El ∘ F)

  private
    sum-basis-late' : ∀ {i} n m {I : ℕ}
      → (F : Fin (ℕ-S^' n (S (ℕ-S^' m I))) → Group i)
      → (g : Π (Fin (S (ℕ-S^' m I))) (Group.El ∘ F ∘ Fin-S^' n))
      →  Group.sum (Πᴳ _ F) (λ <I → Πᴳ-basis F (Fin-S^' (S n) (Fin-S^' m <I)) (g (Fin-S (Fin-S^' m <I))))
           (Fin-S^' n (ℕ-S^' m I , ltS))
      == Group.ident (F (Fin-S^' n (ℕ-S^' m I , ltS)))
    sum-basis-late' n m {I = O} F g = idp
    sum-basis-late' n m {I = S I} F g =
        ap2 (Group.comp (F (Fin-S^' n (ℕ-S^' (S m) I , ltS))))
          (sum-basis-late' n (S m) F g)
          (Πᴳ-basis-late n {I = ℕ-S^' m (S I)} F (Fin-S^' m (I , ltS)) _)
      ∙ Group.unit-l (F (Fin-S^' n (ℕ-S^' (S m) I , ltS))) (Group.ident (F (Fin-S^' n (ℕ-S^' (S m) I , ltS))))

  sum-basis-late : ∀ {i} n {I : ℕ}
    → (F : Fin (ℕ-S^' (S n) I) → Group i)
    → (g : Π (Fin (S I)) (Group.El ∘ F ∘ Fin-S^' n))
    →  Group.sum (Πᴳ _ F) (λ <I → Πᴳ-basis F (Fin-S^' (S n) <I) (g (Fin-S <I))) (Fin-S^' n (I , ltS))
    == Group.ident (F (Fin-S^' n (I , ltS)))
  sum-basis-late n = sum-basis-late' n O

  private
    {- eta in reverse -}
    sum-basis' : ∀ {i} n {I : ℕ} (F : Fin (ℕ-S^' n I) → Group i)
      → (g : Π (Fin I) (Group.El ∘ F ∘ Fin-S^' n))
      → Group.sum (Πᴳ _ F) (λ <I → Πᴳ-basis F (Fin-S^' n <I) (g <I)) ∘ Fin-S^' n ∼ g
    sum-basis' n F g (I , ltS) =
        ap2 (Group.comp (F (Fin-S^' n (I , ltS))))
          (sum-basis-late n F g)
          (Πᴳ-basis-diag {I = ℕ-S^' n (S I)} F (Fin-S^' n (I , ltS)) (g (I , ltS)))
      ∙ Group.unit-l (F (Fin-S^' n (I , ltS))) _
    sum-basis' n {I = S I} F g (m , ltSR m<I) =
        ap2 (Group.comp (F (Fin-S^' n (m , ltSR m<I))))
          (sum-basis' (S n) F (g ∘ Fin-S) (m , m<I))
          (Πᴳ-basis-early n F (m , m<I) (g (I , ltS)))
      ∙ Group.unit-r (F (Fin-S^' n (m , ltSR m<I))) _
  
  sum-basis : ∀ {i} {I : ℕ} (F : Fin I → Group i)
    → (g : Π (Fin I) (Group.El ∘ F))
    → Group.sum (Πᴳ _ F) (λ <I → Πᴳ-basis F <I (g <I)) ∼ g
  sum-basis = sum-basis' O
