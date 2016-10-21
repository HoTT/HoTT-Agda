{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import homotopy.DistinctlyPointedSet

module cohomology.DistinctlyPointedSet {i} (CT : CohomologyTheory i) where

  open CohomologyTheory CT

  module _ (n : ℤ) (X : Ptd i)
    (X-is-set : is-set (fst X)) (dec : has-distinct-pt X)
    (ac : has-choice 0 (fst X) i) where

    private

      lemma : BigWedge {A = WithoutPoint X} (λ _ → ⊙Bool) ≃ fst X
      lemma = equiv to from to-from from-to where
        from : fst X → BigWedge {A = WithoutPoint X} (λ _ → ⊙Bool)
        from x with dec x
        from x | inl p  = bwbase
        from x | inr ¬p = bwin (x , ¬p) false

        module From = BigWedgeRec {A = WithoutPoint X} {X = λ _ → ⊙Bool}
          (snd X) (λ{_ true → snd X; (x , _) false → x}) (λ _ → idp)
        to = From.f

        from-to : ∀ x → from (to x) == x
        from-to = BigWedge-elim base* in* glue* where
          base* : from (snd X) == bwbase
          base* with dec (snd X)
          base* | inl _  = idp
          base* | inr ¬p = ⊥-rec (¬p idp)

          in* : (wp : WithoutPoint X) (b : Bool)
            → from (to (bwin wp b)) == bwin wp b
          in* wp true with dec (snd X)
          in* wp true | inl _ = bwglue wp
          in* wp true | inr pt≠pt = ⊥-rec (pt≠pt idp)
          in* (x , pt≠x) false with dec x
          in* (x , pt≠x) false | inl pt=x = ⊥-rec (pt≠x pt=x)
          in* (x , pt≠x) false | inr pt≠'x =
            ap (λ ¬p → bwin (x , ¬p) false) $ prop-has-all-paths ¬-is-prop pt≠'x pt≠x

          glue* : (wp : WithoutPoint X)
            → base* == in* wp true [ (λ x → from (to x) == x) ↓ bwglue wp ]
          glue* wp = ↓-∘=idf-from-square from to $ ap (ap from) (From.glue-β wp) ∙v⊡ square where
            square : Square base* idp (bwglue wp) (in* wp true)
            square with dec (snd X)
            square | inl _ = br-square (bwglue wp)
            square | inr ¬p = ⊥-rec (¬p idp)

        to-from : ∀ x → to (from x) == x
        to-from x with dec x
        to-from x | inl pt=x = pt=x
        to-from x | inr pt≠x = idp

    C-set : C n X ≃ᴳ Πᴳ (WithoutPoint X) (λ _ → C n (⊙Lift ⊙Bool))
    C-set =
      C n X
        ≃ᴳ⟨ C-emap n (≃-to-⊙≃ lemma idp) ⟩
      C n (⊙BigWedge {A = WithoutPoint X} (λ _ → ⊙Bool))
        ≃ᴳ⟨ C-emap n (⊙BigWedge-emap-r λ _ → ⊙lower-equiv) ⟩
      C n (⊙BigWedge {A = WithoutPoint X} (λ _ → ⊙Lift ⊙Bool))
        ≃ᴳ⟨ C-additive-iso n (λ _ → ⊙Lift ⊙Bool)
              (WithoutPoint-has-choice 0 (distinct-pt-is-separable dec) ac) ⟩
      Πᴳ (WithoutPoint X) (λ _ → C n (⊙Lift ⊙Bool))
        ≃ᴳ∎
