{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.JoinComm
open import homotopy.JoinAssocCubical

module homotopy.JoinSusp where

module _ {i} {A : Type i} where

  private

      module Into = JoinRec {A = Bool} {B = A}
        {D = Suspension A}
        (if_then north else south)
        (λ _ → south)
        (λ {(true , a) → merid a;
            (false , a) → idp})

      into = Into.f

      module Out = SuspensionRec {C = Bool * A}
        (left true)
        (left false)
        (λ a → glue (true , a) ∙ ! (glue (false , a)))

      out = Out.f

      into-out : ∀ σ → into (out σ) == σ
      into-out = Suspension-elim
        idp
        idp
        (↓-∘=idf-from-square into out ∘ λ a → vert-degen-square $
           ap (ap into) (Out.merid-β a)
           ∙ ap-∙ into (glue (true , a)) (! (glue (false , a)))
           ∙ (Into.glue-β (true , a)
              ∙2 (ap-! into (glue (false , a))
                  ∙ ap ! (Into.glue-β (false , a))))
           ∙ ∙-unit-r _)

      out-into : ∀ j → out (into j) == j
      out-into = Join-elim
        (λ{true → idp ; false → idp})
        (λ a → glue (false , a))
        (↓-∘=idf-from-square out into ∘
          λ {(true , a) →
                (ap (ap out) (Into.glue-β (true , a)) ∙ Out.merid-β a)
                ∙v⊡ (vid-square {p = glue (true , a)}
                      ⊡h rt-square (glue (false , a)))
                ⊡v∙ ∙-unit-r _;
             (false , a) →
               ap (ap out) (Into.glue-β (false , a)) ∙v⊡ connection})

  *-Bool-equiv : Bool * A ≃ Suspension A
  *-Bool-equiv = equiv into out into-out out-into

  *-Lift-Bool-equiv : Lift {j = i} Bool * A ≃ Suspension A
  *-Lift-Bool-equiv = *-Bool-equiv ∘e *-equiv lower-equiv (ide A)

  *-Bool-path = ua *-Bool-equiv

module _ {i} (X : Ptd i) where

  ⊙*-⊙Bool-path : ⊙Bool ⊙* X == ⊙Susp X
  ⊙*-⊙Bool-path = ⊙ua (⊙≃-in *-Bool-equiv idp)

  ⊙*-⊙Lift-⊙Bool-path : ⊙Lift {j = i} ⊙Bool ⊙* X == ⊙Susp X
  ⊙*-⊙Lift-⊙Bool-path = ⊙ua (⊙≃-in *-Lift-Bool-equiv idp)

module _ {i j} {A : Type i} {B : Type j} where

  *-Suspension-path : Suspension A * B == Suspension (A * B)
  *-Suspension-path =
    ap (_* B) (! *-Bool-path)
    ∙ join-rearrange-path
    ∙ ua swap-equiv
    ∙ *-Bool-path
    ∙ ap Suspension (ua swap-equiv)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙*-⊙Susp : ⊙Susp X ⊙* Y == ⊙Susp (X ⊙* Y)
  ⊙*-⊙Susp =
    ap (_⊙* Y) (! (⊙*-⊙Bool-path X))
    ∙ join-rearrange-⊙path (⊙Sphere 0) X Y
    ∙ ⊙ua (⊙≃-in swap-equiv (! (glue _)))
    ∙ ⊙*-⊙Bool-path (Y ⊙* X)
    ∙ ap (λ A → (Suspension A , north)) (ua swap-equiv)

module _ {i} where

  ⊙*-⊙Sphere : (m : ℕ) (X : Ptd i) → ⊙Sphere m ⊙* X == ⊙Susp^ (S m) X
  ⊙*-⊙Sphere O X = ⊙*-⊙Bool-path X
  ⊙*-⊙Sphere (S m) X = ⊙*-⊙Susp (⊙Sphere m) X
                     ∙ ap ⊙Susp (⊙*-⊙Sphere m X)

  ⊙*-⊙Lift-⊙Sphere : (m : ℕ) (X : Ptd i) → ⊙Lift {j = i} (⊙Sphere m) ⊙* X == ⊙Susp^ (S m) X
  ⊙*-⊙Lift-⊙Sphere O X = ⊙*-⊙Lift-⊙Bool-path X
  ⊙*-⊙Lift-⊙Sphere (S m) X = ap (_⊙* X) (! $ ⊙Susp-⊙Lift-path (⊙Sphere m))
                           ∙ ⊙*-⊙Susp (⊙Lift (⊙Sphere m)) X
                           ∙ ap ⊙Susp (⊙*-⊙Lift-⊙Sphere m X)
