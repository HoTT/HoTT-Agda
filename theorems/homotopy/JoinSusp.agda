{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.JoinComm
open import homotopy.JoinAssocCubical

module homotopy.JoinSusp where

module _ {i} (A : Type i) where

  private

      module Into = JoinRec {A = Bool} {B = A}
        {D = Susp A}
        (if_then north else south)
        (λ _ → south)
        (λ {(true , a) → merid a;
            (false , a) → idp})

      into = Into.f

      module Out = SuspRec {C = Bool * A}
        (left true)
        (left false)
        (λ a → glue (true , a) ∙ ! (glue (false , a)))

      out = Out.f

      into-out : ∀ σ → into (out σ) == σ
      into-out = Susp-elim
        idp
        idp
        (λ a → ↓-∘=idf-in' into out {p = merid a} $
           ap (ap into) (Out.merid-β a)
           ∙ ap-∙ into (glue (true , a)) (! (glue (false , a)))
           ∙ (Into.glue-β (true , a)
              ∙2 (ap-! into (glue (false , a))
                  ∙ ap ! (Into.glue-β (false , a))))
           ∙ ∙-unit-r _)

      out-into-left : (b : Bool) → out (into (left b)) == left b
      out-into-left true = idp
      out-into-left false = idp

      out-into-glue : (b : Bool) (a : A)
        → Square (out-into-left b) (ap out (ap into (glue (b , a)))) (glue (b , a)) (glue (false , a))
      out-into-glue true a =
        (ap (ap out) (Into.glue-β (true , a)) ∙ Out.merid-β a)
        ∙v⊡ (vid-square {p = glue (true , a)}
             ⊡h rt-square (glue (false , a)))
        ⊡v∙ ∙-unit-r _
      out-into-glue false a =
        ap (ap out) (Into.glue-β (false , a)) ∙v⊡ connection

      out-into : ∀ j → out (into j) == j
      out-into = Join-elim
        out-into-left
        (λ a → glue (false , a))
        (λ ba → ↓-∘=idf-from-square out into {p = glue ba} (uncurry out-into-glue ba))

  *-Bool-l : Bool * A ≃ Susp A
  *-Bool-l = equiv into out into-out out-into

module _ {i} (X : Ptd i) where

  ⊙*-Bool-l : ⊙Bool ⊙* X ⊙≃ ⊙Susp X
  ⊙*-Bool-l = ≃-to-⊙≃ (*-Bool-l (fst X)) idp

module _ {i j} (A : Type i) (B : Type j) where

  *-Susp-l : Susp A * B ≃ Susp (A * B)
  *-Susp-l = *-Bool-l (A * B) ∘e *-assoc Bool A B ∘e *-emap (*-Bool-l A) (ide B) ⁻¹

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙*-Susp-l : ⊙Susp X ⊙* Y ⊙≃ ⊙Susp (X ⊙* Y)
  ⊙*-Susp-l = ≃-to-⊙≃ (*-Susp-l (fst X) (fst Y)) idp

module _ {i} where

  ⊙*-Sphere-l : (m : ℕ) (X : Ptd i) → ⊙Sphere m ⊙* X ⊙≃ ⊙Susp^ (S m) X
  ⊙*-Sphere-l O X = ⊙*-Bool-l X
  ⊙*-Sphere-l (S m) X = ⊙Susp-emap (⊙*-Sphere-l m X) ⊙∘e ⊙*-Susp-l (⊙Sphere m) X
