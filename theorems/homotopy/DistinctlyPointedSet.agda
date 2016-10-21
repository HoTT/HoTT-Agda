{-# OPTIONS --without-K #-}

open import HoTT

{-
Various lemmas that will be used in cohomology.DistinctlyPointedSet.
Many of them, for example the choice lemma about coproducts, should be
put into core/.
-}

module homotopy.DistinctlyPointedSet where

module _ {i} where

  has-distinct-pt : (X : Ptd i) → Type i
  has-distinct-pt (_ , x) = has-dec-onesided-eq x

  abstract
    has-distinct-pt-is-prop : {X : Ptd i}
      → is-prop (has-distinct-pt X)
    has-distinct-pt-is-prop = has-dec-onesided-eq-is-prop

  WithoutPoint : (X : Ptd i) → Type i
  WithoutPoint (X , x) = Σ X (x ≠_)

  unite-pt : (X : Ptd i) → (⊤ ⊔ WithoutPoint X → fst X)
  unite-pt X (inl _) = snd X
  unite-pt X (inr (x , _)) = x

  is-separable : (X : Ptd i) → Type i
  is-separable X = is-equiv (unite-pt X)

  abstract
    distinct-pt-is-separable : {X : Ptd i}
      → has-distinct-pt X → is-separable X
    distinct-pt-is-separable {X} dec =
      is-eq _ sep unite-sep sep-unite where
        sep : fst X → ⊤ ⊔ (Σ (fst X) (snd X ≠_))
        sep x with dec x
        sep x | inl _  = inl unit
        sep x | inr ¬p = inr (x , ¬p)

        sep-unite : ∀ x → sep (unite-pt X x) == x
        sep-unite (inl _) with dec (snd X)
        sep-unite (inl _) | inl _  = idp
        sep-unite (inl _) | inr ¬p = ⊥-rec (¬p idp)
        sep-unite (inr (x , ¬p)) with dec x
        sep-unite (inr (x , ¬p)) | inl p   = ⊥-rec (¬p p)
        sep-unite (inr (x , ¬p)) | inr ¬p' = ap inr $ pair= idp (prop-has-all-paths ¬-is-prop ¬p' ¬p)

        unite-sep : ∀ x → unite-pt X (sep x) == x
        unite-sep x with dec x
        unite-sep x | inl p = p
        unite-sep x | inr ¬p = idp

    separable-has-distinct-pt : {X : Ptd i}
      → is-separable X → has-distinct-pt X
    separable-has-distinct-pt unite-ise x with unite.g x | unite.f-g x
      where module unite = is-equiv unite-ise
    separable-has-distinct-pt unite-ise x | inl unit       | p   = inl p
    separable-has-distinct-pt unite-ise x | inr (y , pt≠y) | y=x = inr λ pt=x → pt≠y (pt=x ∙ ! y=x)

module _ {i j k} n (A : Type i) (B : Type j) where
  abstract
    ⊔-has-choice-implies-inr-has-choice : has-choice n (A ⊔ B) k → has-choice n B k
    ⊔-has-choice-implies-inr-has-choice ⊔-ac W =
      transport is-equiv (λ= lemma₃)
        (snd lemma₂ ∘ise ⊔-ac W' ∘ise is-equiv-inverse (snd (Trunc-emap n lemma₁))) where
          W' : A ⊔ B → Type k
          W' (inl _) = Lift {j = k} ⊤
          W' (inr b) = W b

          lemma₁ : Π (A ⊔ B) W' ≃ Π B W
          lemma₁ = equiv to from to-from from-to where
            to : Π (A ⊔ B) W' → Π B W
            to f b = f (inr b)

            from : Π B W → Π (A ⊔ B) W'
            from f (inl a) = lift tt
            from f (inr b) = f b

            to-from : ∀ f → to (from f) == f
            to-from f = λ= λ b → idp

            from-to : ∀ f → from (to f) == f
            from-to f = λ= λ{(inl a) → idp; (inr b) → idp}

          lemma₂ : Π (A ⊔ B) (Trunc n ∘ W') ≃ Π B (Trunc n ∘ W)
          lemma₂ = equiv to from to-from from-to where
            to : Π (A ⊔ B) (Trunc n ∘ W') → Π B (Trunc n ∘ W)
            to f b = f (inr b)

            from : Π B (Trunc n ∘ W) → Π (A ⊔ B) (Trunc n ∘ W')
            from f (inl a) = [ lift tt ]
            from f (inr b) = f b

            to-from : ∀ f → to (from f) == f
            to-from f = λ= λ b → idp

            from-to : ∀ f → from (to f) == f
            from-to f = λ= λ{
              (inl a) → Trunc-elim
                {P = λ t → [ lift tt ] == t}
                (λ _ → =-preserves-level n Trunc-level)
                (λ _ → idp) (f (inl a));
              (inr b) → idp}

          lemma₃ : ∀ f → –> lemma₂ (unchoose (<– (Trunc-emap n lemma₁) f)) == unchoose f
          lemma₃ = Trunc-elim
            {P = λ f → –> lemma₂ (unchoose (<– (Trunc-emap n lemma₁) f)) == unchoose f}
            (λ _ → =-preserves-level n (Π-level λ _ → Trunc-level))
            (λ f → λ= λ b → idp)

module _ {i j} n {X : Ptd i} (X-sep : is-separable X) where
  abstract
    WithoutPoint-has-choice : has-choice n (fst X) j → has-choice n (WithoutPoint X) j
    WithoutPoint-has-choice X-ac =
      ⊔-has-choice-implies-inr-has-choice n ⊤ (WithoutPoint X) $
        transport! (λ A → has-choice n A j) (ua (_ , X-sep)) X-ac
