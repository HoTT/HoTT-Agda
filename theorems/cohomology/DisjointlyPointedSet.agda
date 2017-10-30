{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import homotopy.DisjointlyPointedSet

module cohomology.DisjointlyPointedSet {i} (OT : OrdinaryTheory i) where

  open OrdinaryTheory OT

  module _ (n : ℤ) (X : Ptd i)
    (X-is-set : is-set (de⊙ X)) (dec : is-separable X)
    (ac : has-choice 0 (de⊙ X) i) where

    private

      lemma : BigWedge {A = MinusPoint X} (λ _ → ⊙Bool) ≃ de⊙ X
      lemma = equiv to from to-from from-to where
        from : de⊙ X → BigWedge {A = MinusPoint X} (λ _ → ⊙Bool)
        from x with dec x
        from x | inl p  = bwbase
        from x | inr ¬p = bwin (x , ¬p) false

        module From = BigWedgeRec {A = MinusPoint X} {X = λ _ → ⊙Bool}
          (pt X) (λ{_ true → pt X; (x , _) false → x}) (λ _ → idp)
        to = From.f

        abstract
          from-to : ∀ x → from (to x) == x
          from-to = BigWedge-elim base* in* glue* where
            base* : from (pt X) == bwbase
            base* with dec (pt X)
            base* | inl _  = idp
            base* | inr ¬p = ⊥-rec (¬p idp)

            in* : (wp : MinusPoint X) (b : Bool)
              → from (to (bwin wp b)) == bwin wp b
            in* wp true with dec (pt X)
            in* wp true | inl _ = bwglue wp
            in* wp true | inr pt≠pt = ⊥-rec (pt≠pt idp)
            in* (x , pt≠x) false with dec x
            in* (x , pt≠x) false | inl pt=x = ⊥-rec (pt≠x pt=x)
            in* (x , pt≠x) false | inr pt≠'x =
              ap (λ ¬p → bwin (x , ¬p) false) $ prop-has-all-paths pt≠'x pt≠x

            glue* : (wp : MinusPoint X)
              → base* == in* wp true [ (λ x → from (to x) == x) ↓ bwglue wp ]
            glue* wp = ↓-∘=idf-from-square from to $ ap (ap from) (From.glue-β wp) ∙v⊡ square where
              square : Square base* idp (bwglue wp) (in* wp true)
              square with dec (pt X)
              square | inl _ = br-square (bwglue wp)
              square | inr ¬p = ⊥-rec (¬p idp)

          to-from : ∀ x → to (from x) == x
          to-from x with dec x
          to-from x | inl pt=x = pt=x
          to-from x | inr pt≠x = idp

    C-set : C n X ≃ᴳ Πᴳ (MinusPoint X) (λ _ → C n (⊙Lift ⊙Bool))
    C-set =
      C n X
        ≃ᴳ⟨ C-emap n (≃-to-⊙≃ lemma idp) ⟩
      C n (⊙BigWedge {A = MinusPoint X} (λ _ → ⊙Bool))
        ≃ᴳ⟨ C-emap n (⊙BigWedge-emap-r λ _ → ⊙lower-equiv) ⟩
      C n (⊙BigWedge {A = MinusPoint X} (λ _ → ⊙Lift ⊙Bool))
        ≃ᴳ⟨ C-additive-iso n (λ _ → ⊙Lift ⊙Bool)
              (MinusPoint-has-choice 0 (separable-has-disjoint-pt dec) ac) ⟩
      Πᴳ (MinusPoint X) (λ _ → C n (⊙Lift ⊙Bool))
        ≃ᴳ∎

  module _ {n : ℤ} (n≠0 : n ≠ 0) (X : Ptd i)
    (X-is-set : is-set (de⊙ X)) (dec : is-separable X)
    (ac : has-choice 0 (de⊙ X) i) where

    C-set-≠-is-trivial : is-trivialᴳ (C n X)
    C-set-≠-is-trivial = iso-preserves'-trivial
      (C-set n X X-is-set dec ac)
      (Πᴳ-is-trivial (MinusPoint X)
        (λ _ → C n (⊙Lift ⊙Bool))
        (λ _ → C-dimension n≠0))
