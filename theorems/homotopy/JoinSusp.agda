{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.JoinComm
open import homotopy.JoinAssocCubical

module homotopy.JoinSusp where

module _ {i} (A : Type i) where

  private

      module Into = JoinRec {A = Bool} {B = A}
        {C = Susp A}
        (Bool-rec north south)
        (λ _ → south)
        (λ {true a → merid a;
            false a → idp})

      into = Into.f

      module Out = SuspRec {C = Bool * A}
        (left true)
        (left false)
        (λ a → jglue true a ∙ ! (jglue false a))

      out = Out.f

      into-out : ∀ σ → into (out σ) == σ
      into-out = Susp-elim
        idp
        idp
        (λ a → ↓-∘=idf-from-square into out $ vert-degen-square $
           ap (ap into) (Out.merid-β a)
           ∙ ap-∙ into (jglue true a) (! (jglue false a))
           ∙ (Into.glue-β true a
              ∙2 (ap-! into (jglue false a)
                  ∙ ap ! (Into.glue-β false a)))
           ∙ ∙-unit-r _)

      out-into : ∀ j → out (into j) == j
      out-into = Join-elim
        (Bool-elim idp idp)
        (λ a → jglue false a)
        (λ{true a → ↓-∘=idf-from-square out into $
              (ap (ap out) (Into.glue-β true a) ∙ Out.merid-β a)
              ∙v⊡ (vid-square {p = jglue true a}
                    ⊡h rt-square (jglue false a))
              ⊡v∙ ∙-unit-r _;
           false a → ↓-∘=idf-from-square out into $
             ap (ap out) (Into.glue-β false a) ∙v⊡ connection})

  *-Bool-l : Bool * A ≃ Susp A
  *-Bool-l = equiv into out into-out out-into

module _ {i} (X : Ptd i) where

  ⊙*-Bool-l : ⊙Bool ⊙* X ⊙≃ ⊙Susp X
  ⊙*-Bool-l = ≃-to-⊙≃ (*-Bool-l (de⊙ X)) idp

module _ {i j} (A : Type i) (B : Type j) where

  *-Susp-l : Susp A * B ≃ Susp (A * B)
  *-Susp-l = *-Bool-l (A * B) ∘e *-assoc Bool A B ∘e *-emap (*-Bool-l A) (ide B) ⁻¹

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙*-Susp-l : ⊙Susp X ⊙* Y ⊙≃ ⊙Susp (X ⊙* Y)
  ⊙*-Susp-l = ≃-to-⊙≃ (*-Susp-l (de⊙ X) (de⊙ Y)) idp

module _ {i} where

  ⊙*-Sphere-l : (m : ℕ) (X : Ptd i) → ⊙Sphere m ⊙* X ⊙≃ ⊙Susp^ (S m) X
  ⊙*-Sphere-l O X = ⊙*-Bool-l X
  ⊙*-Sphere-l (S m) X = ⊙Susp-emap (⊙*-Sphere-l m X) ⊙∘e ⊙*-Susp-l (⊙Sphere m) X
