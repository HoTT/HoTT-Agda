{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet

{-
Various lemmas that will be used in cohomology.DisjointlyPointedSet.
Many of them, for example the choice lemma about coproducts, should be
put into core/.
-}

module homotopy.DisjointlyPointedSet where

module _ {i} where

  is-separable : (X : Ptd i) → Type i
  is-separable X = has-dec-onesided-eq (pt X)

  abstract
    is-separable-is-prop : {X : Ptd i}
      → is-prop (is-separable X)
    is-separable-is-prop = has-dec-onesided-eq-is-prop

  MinusPoint : (X : Ptd i) → Type i
  MinusPoint X = Σ (de⊙ X) (pt X ≠_)

  MinusPoint-prop : (X : Ptd i) → SubtypeProp (de⊙ X) i
  MinusPoint-prop X = (pt X ≠_) , ⟨⟩

  abstract
    MinusPoint-has-dec-eq : {X : Ptd i}
      → has-dec-eq (de⊙ X)
      → has-dec-eq (MinusPoint X)
    MinusPoint-has-dec-eq {X} X-dec =
      Subtype-has-dec-eq (MinusPoint-prop X) X-dec

  unite-pt : (X : Ptd i) → (⊤ ⊔ MinusPoint X → de⊙ X)
  unite-pt X (inl _) = pt X
  unite-pt X (inr (x , _)) = x

  separate-pt : {X : Ptd i}
    → is-separable X
    → (de⊙ X → ⊤ ⊔ (Σ (de⊙ X) (pt X ≠_)))
  separate-pt dec x with dec x
  separate-pt dec x | inl _  = inl unit
  separate-pt dec x | inr ¬p = inr (x , ¬p)

  has-disjoint-pt : (X : Ptd i) → Type i
  has-disjoint-pt X = is-equiv (unite-pt X)

  separable-has-disjoint-pt : {X : Ptd i}
    → is-separable X → has-disjoint-pt X
  separable-has-disjoint-pt {X} dec =
    is-eq _ (separate-pt dec) unite-sep sep-unite where
      abstract
        sep-unite : ∀ x → separate-pt dec (unite-pt X x) == x
        sep-unite (inl _) with dec (pt X)
        sep-unite (inl _) | inl _  = idp
        sep-unite (inl _) | inr ¬p = ⊥-rec (¬p idp)
        sep-unite (inr (x , ¬p)) with dec x
        sep-unite (inr (x , ¬p)) | inl p   = ⊥-rec (¬p p)
        sep-unite (inr (x , ¬p)) | inr ¬p' = ap inr $ pair= idp (prop-has-all-paths ¬p' ¬p)

        unite-sep : ∀ x → unite-pt X (separate-pt dec x) == x
        unite-sep x with dec x
        unite-sep x | inl p = p
        unite-sep x | inr ¬p = idp

  disjoint-pt-is-separable : {X : Ptd i}
    → has-disjoint-pt X → is-separable X
  disjoint-pt-is-separable unite-ise x with unite.g x | unite.f-g x
    where module unite = is-equiv unite-ise
  disjoint-pt-is-separable unite-ise x | inl unit       | p   = inl p
  disjoint-pt-is-separable unite-ise x | inr (y , pt≠y) | y=x = inr λ pt=x → pt≠y (pt=x ∙ ! y=x)

  separable-unite-equiv : ∀ {X}
    → is-separable X
    → (⊤ ⊔ MinusPoint X ≃ de⊙ X)
  separable-unite-equiv dX = _ , separable-has-disjoint-pt dX

module _ {i j k} n (A : Type i) (B : Type j) where
  {- Hmm. Where should we put this lemma? -}
  abstract
    ⊔-has-choice-implies-inr-has-choice : has-choice n (A ⊔ B) k → has-choice n B k
    ⊔-has-choice-implies-inr-has-choice ⊔-ac W =
      transport is-equiv (λ= lemma₃)
        (snd lemma₂ ∘ise ⊔-ac W' ∘ise is-equiv-inverse (snd (Trunc-emap lemma₁))) where
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
                  (λ _ → idp) (f (inl a));
                (inr b) → idp}

          lemma₃ : ∀ f → –> lemma₂ (unchoose (<– (Trunc-emap lemma₁) f)) == unchoose f
          lemma₃ = Trunc-elim
            {P = λ f → –> lemma₂ (unchoose (<– (Trunc-emap lemma₁) f)) == unchoose f}
            (λ f → λ= λ b → idp)

module _ {i j} {n} {X : Ptd i} (X-sep : is-separable X) where
  abstract
    MinusPoint-has-choice : has-choice n (de⊙ X) j → has-choice n (MinusPoint X) j
    MinusPoint-has-choice X-ac =
      ⊔-has-choice-implies-inr-has-choice n ⊤ (MinusPoint X) $
        transport! (λ A → has-choice n A j) (ua (_ , separable-has-disjoint-pt X-sep)) X-ac

module _ {i} {X : Ptd i} (X-sep : is-separable X) where

  Bouquet-equiv-X : Bouquet (MinusPoint X) 0 ≃ de⊙ X
  Bouquet-equiv-X = equiv to from to-from from-to where
    from : de⊙ X → BigWedge {A = MinusPoint X} (λ _ → ⊙Bool)
    from x with X-sep x
    from x | inl p  = bwbase
    from x | inr ¬p = bwin (x , ¬p) false

    module To = BigWedgeRec {A = MinusPoint X} {X = λ _ → ⊙Bool}
      (pt X) (λ{_ true → pt X; (x , _) false → x}) (λ _ → idp)
    to = To.f

    abstract
      from-to : ∀ x → from (to x) == x
      from-to = BigWedge-elim base* in* glue* where
        base* : from (pt X) == bwbase
        base* with X-sep (pt X)
        base* | inl _  = idp
        base* | inr ¬p = ⊥-rec (¬p idp)

        in* : (wp : MinusPoint X) (b : Bool)
          → from (to (bwin wp b)) == bwin wp b
        in* wp true with X-sep (pt X)
        in* wp true | inl _ = bwglue wp
        in* wp true | inr pt≠pt = ⊥-rec (pt≠pt idp)
        in* (x , pt≠x) false with X-sep x
        in* (x , pt≠x) false | inl pt=x = ⊥-rec (pt≠x pt=x)
        in* (x , pt≠x) false | inr pt≠'x =
          ap (λ ¬p → bwin (x , ¬p) false) $ prop-has-all-paths pt≠'x pt≠x

        glue* : (wp : MinusPoint X)
          → base* == in* wp true [ (λ x → from (to x) == x) ↓ bwglue wp ]
        glue* wp = ↓-∘=idf-from-square from to $ ap (ap from) (To.glue-β wp) ∙v⊡ square where
          square : Square base* idp (bwglue wp) (in* wp true)
          square with X-sep (pt X)
          square | inl _ = br-square (bwglue wp)
          square | inr ¬p = ⊥-rec (¬p idp)

      to-from : ∀ x → to (from x) == x
      to-from x with X-sep x
      to-from x | inl pt=x = pt=x
      to-from x | inr pt≠x = idp

  Bouquet-⊙equiv-X : ⊙Bouquet (MinusPoint X) 0 ⊙≃ X
  Bouquet-⊙equiv-X = ≃-to-⊙≃ Bouquet-equiv-X idp
