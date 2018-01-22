{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.FinProduct where

  Πᴳ-base : ∀ {i} {I : ℕ} (F : Fin I → Group i)
    → (n : Fin I) (g : Group.El (F n))
    → Π (Fin I) (Group.El ∘ F)
  Πᴳ-base F (_ , ltS) g (_ , ltS) = g
  Πᴳ-base F (_ , ltSR lt₀) g (_ , ltSR lt₁) =
    Πᴳ-base (F ∘ Fin-S) (_ , lt₀) g (_ , lt₁)
  Πᴳ-base F (_ , ltSR _) g (_ , ltS) = Group.ident (F (_ , ltS))
  Πᴳ-base F (_ , ltS) g (_ , ltSR lt) = Group.ident (F (_ , ltSR lt))

  Πᴳ-base-late : ∀ {i} (m n I : ℕ) (F : Fin (ℕ-S^' m (n + S I)) → Group i) <I g
    →  Πᴳ-base F (Fin-S^' m (Fin-S^ n (Fin-S <I))) g (Fin-S^' m (Fin-S^ n (I , ltS)))
    == Group.ident (F (Fin-S^' m (Fin-S^ n (I , ltS))))
  Πᴳ-base-late O O I F <I g = idp
  Πᴳ-base-late O (S n) I F <I g = Πᴳ-base-late O n I (F ∘ Fin-S) <I g
  Πᴳ-base-late (S m) n I F <I g = Πᴳ-base-late m (S n) I F <I g
  
  Πᴳ-base-early : ∀ {i} (m n I : ℕ) (F : Fin (ℕ-S^' m (n + S I)) → Group i) <I g
    →  Πᴳ-base F (Fin-S^' m (Fin-S^ n (I , ltS))) g (Fin-S^' m (Fin-S^ n (Fin-S <I)))
    == Group.ident (F (Fin-S^' m (Fin-S^ n (Fin-S <I))))
  Πᴳ-base-early O O I F <I g = idp
  Πᴳ-base-early O (S n) I F <I g = Πᴳ-base-early O n I (F ∘ Fin-S) <I g
  Πᴳ-base-early (S m) n I F <I g = Πᴳ-base-early m (S n) I F <I g

  Πᴳ-base-diag : ∀ {i} (I : ℕ) (F : Fin I → Group i) <I g
    → Πᴳ-base F <I g <I == g
  Πᴳ-base-diag _ F (_ , ltS) g = idp
  Πᴳ-base-diag (S I) F (_ , ltSR <I) g = Πᴳ-base-diag I (F ∘ Fin-S) (_ , <I) g

  sum-base-late : ∀ {i} (n m I : ℕ)
    → (F : Fin (ℕ-S^' n (S (ℕ-S^' m I))) → Group i)
    → (g : Π (Fin (S (ℕ-S^' m I))) (Group.El ∘ F ∘ Fin-S^' n))
    →  Group.sum (Πᴳ _ F) (λ <I → Πᴳ-base F (Fin-S^' n (Fin-S (Fin-S^' m <I))) (g (Fin-S (Fin-S^' m <I))))
         (Fin-S^' n (ℕ-S^' m I , ltS))
    == Group.ident (F (Fin-S^' n (ℕ-S^' m I , ltS)))
  sum-base-late n m O F g = idp
  sum-base-late n m (S I) F g =
      ap2 (Group.comp (F (Fin-S^' n (ℕ-S^' (S m) I , ltS))))
        (sum-base-late n (S m) I F g)
        (Πᴳ-base-late n O (ℕ-S^' m (S I)) F (Fin-S^' m (I , ltS)) _)
    ∙ Group.unit-l (F (Fin-S^' n (ℕ-S^' (S m) I , ltS))) (Group.ident (F (Fin-S^' n (ℕ-S^' (S m) I , ltS))))

  {- eta in reverse -}
  sum-base : ∀ {i} (n I : ℕ) (F : Fin (ℕ-S^' n I) → Group i)
    → (g : Π (Fin I) (Group.El ∘ F ∘ Fin-S^' n))
    → Group.sum (Πᴳ _ F) (λ <I → Πᴳ-base F (Fin-S^' n <I) (g <I)) ∘ Fin-S^' n ∼ g
  sum-base n (S .I) F g (I , ltS) =
      ap2 (Group.comp (F (Fin-S^' n (I , ltS))))
        (sum-base-late n O I F g)
        (Πᴳ-base-diag (ℕ-S^' n (S I)) F (Fin-S^' n (I , ltS)) (g (I , ltS)))
    ∙ Group.unit-l (F (Fin-S^' n (I , ltS))) _
  sum-base n (S I) F g (_ , ltSR <I) =
      ap2 (Group.comp (F (Fin-S^' n (_ , ltSR <I))))
        (sum-base (S n) I F (g ∘ Fin-S) (_ , <I))
        (Πᴳ-base-early n O I F (_ , <I) (g (I , ltS)))
    ∙ Group.unit-r (F (Fin-S^' n (_ , ltSR <I))) _
