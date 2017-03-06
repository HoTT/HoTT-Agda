{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{-
Various lemmas that will be used in cohomology.DisjointlyPointedSet.
Many of them, for example the choice lemma about coproducts, should be
put into core/.
-}

module homotopy.DisjointlyPointedSet where

module _ {i} where

  is-detachable : (X : Ptd i) → Type i
  is-detachable (_ , x) = has-dec-onesided-eq x

  abstract
    is-detachable-is-prop : {X : Ptd i}
      → is-prop (is-detachable X)
    is-detachable-is-prop = has-dec-onesided-eq-is-prop

  MinusPoint : (X : Ptd i) → Type i
  MinusPoint (X , x) = Σ X (x ≠_)

  unite-pt : (X : Ptd i) → (⊤ ⊔ MinusPoint X → fst X)
  unite-pt X (inl _) = snd X
  unite-pt X (inr (x , _)) = x

  has-disjoint-pt : (X : Ptd i) → Type i
  has-disjoint-pt X = is-equiv (unite-pt X)

  abstract
    detachable-has-disjoint-pt : {X : Ptd i}
      → is-detachable X → has-disjoint-pt X
    detachable-has-disjoint-pt {X} dec =
      is-eq _ sep unite-sep sep-unite where
        sep : fst X → ⊤ ⊔ (Σ (fst X) (snd X ≠_))
        sep x with dec x
        sep x | inl _  = inl unit
        sep x | inr ¬p = inr (x , ¬p)

        abstract
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

    disjoint-pt-is-detachable : {X : Ptd i}
      → has-disjoint-pt X → is-detachable X
    disjoint-pt-is-detachable unite-ise x with unite.g x | unite.f-g x
      where module unite = is-equiv unite-ise
    disjoint-pt-is-detachable unite-ise x | inl unit       | p   = inl p
    disjoint-pt-is-detachable unite-ise x | inr (y , pt≠y) | y=x = inr λ pt=x → pt≠y (pt=x ∙ ! y=x)

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

            abstract
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

            abstract
              to-from : ∀ f → to (from f) == f
              to-from f = λ= λ b → idp

              from-to : ∀ f → from (to f) == f
              from-to f = λ= λ{
                (inl a) → Trunc-elim
                  {P = λ t → [ lift tt ] == t}
                  (λ _ → =-preserves-level Trunc-level)
                  (λ _ → idp) (f (inl a));
                (inr b) → idp}

          lemma₃ : ∀ f → –> lemma₂ (unchoose (<– (Trunc-emap n lemma₁) f)) == unchoose f
          lemma₃ = Trunc-elim
            {P = λ f → –> lemma₂ (unchoose (<– (Trunc-emap n lemma₁) f)) == unchoose f}
            (λ _ → =-preserves-level (Π-level λ _ → Trunc-level))
            (λ f → λ= λ b → idp)

module _ {i j} n {X : Ptd i} (X-sep : has-disjoint-pt X) where
  abstract
    MinusPoint-has-choice : has-choice n (fst X) j → has-choice n (MinusPoint X) j
    MinusPoint-has-choice X-ac =
      ⊔-has-choice-implies-inr-has-choice n ⊤ (MinusPoint X) $
        transport! (λ A → has-choice n A j) (ua (_ , X-sep)) X-ac
