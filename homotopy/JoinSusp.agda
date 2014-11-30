{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.JoinComm
open import homotopy.JoinAssocCubical

module homotopy.JoinSusp where

module _ {i} {A : Type i} where

  private

      module Into = PushoutRec {d = *-span (Lift {j = i} Bool) A}
        {D = Suspension A}
        (λ {(lift true) → north _;
            (lift false) → south _})
        (λ _ → south _)
        (λ {(lift true , a) → merid _ a;
            (lift false , a) → idp})

      into = Into.f

      module Out = SuspensionRec A {C = Lift {j = i} Bool * A}
        (left (lift true))
        (left (lift false))
        (λ a → glue (lift true , a) ∙ ! (glue (lift false , a)))

      out = Out.f

      into-out : ∀ σ → into (out σ) == σ
      into-out = Suspension-elim _
        idp
        idp
        (↓-∘=idf-from-square into out ∘ λ a → vert-degen-square $
           ap (ap into) (Out.glue-β a)
           ∙ ap-∙ into (glue (lift true , a)) (! (glue (lift false , a)))
           ∙ (Into.glue-β (lift true , a)
              ∙2 (ap-! into (glue (lift false , a))
                  ∙ ap ! (Into.glue-β (lift false , a))))
           ∙ ∙-unit-r _)

      out-into : ∀ j → out (into j) == j
      out-into = Pushout-elim
        (λ {(lift true) → idp;
            (lift false) → idp})
        (λ a → glue (lift false , a))
        (↓-∘=idf-from-square out into ∘
          λ {(lift true , a) →
                (ap (ap out) (Into.glue-β (lift true , a)) ∙ Out.glue-β a)
                ∙v⊡ (vid-square {p = glue (lift true , a)}
                      ⊡h ru-square (glue (lift false , a)))
                ⊡v∙ ∙-unit-r _;
             (lift false , a) →
               ap (ap out) (Into.glue-β (lift false , a)) ∙v⊡ connection})

  join-S⁰-equiv : Lift {j = i} Bool * A ≃ Suspension A
  join-S⁰-equiv = equiv into out into-out out-into

  join-S⁰-path = ua join-S⁰-equiv

module _ {i} (X : Ptd i) where

  join-S⁰-⊙path : ⊙Sphere {i} 0 ⊙* X == ⊙Susp X
  join-S⁰-⊙path = ⊙ua join-S⁰-equiv idp

module _ {i} {A B : Type i} where

  join-susp-shift : Suspension A * B == Suspension (A * B)
  join-susp-shift =
    ap (λ C → C * B) (! join-S⁰-path)
    ∙ join-rearrange-path
    ∙ ua swap-equiv
    ∙ join-S⁰-path
    ∙ ap Suspension (ua swap-equiv)

module _ {i} (X Y : Ptd i) where

  ⊙join-susp-shift : ⊙Susp X ⊙* Y == ⊙Susp (X ⊙* Y)
  ⊙join-susp-shift =
    ap (λ Z → Z ⊙* Y) (! (join-S⁰-⊙path X))
    ∙ join-rearrange-⊙path (⊙Sphere 0) X Y
    ∙ ⊙ua swap-equiv (! (glue _))
    ∙ join-S⁰-⊙path (Y ⊙* X)
    ∙ ap (λ A → (Suspension A , north _)) (ua swap-equiv)

module _ {i} (X : Ptd i) where

  ⊙join-sphere : (m : ℕ) → ⊙Sphere {i} m ⊙* X == ⊙Susp^ (S m) X
  ⊙join-sphere O = join-S⁰-⊙path X
  ⊙join-sphere (S m) = ⊙join-susp-shift (⊙Sphere m) X
                          ∙ ap ⊙Susp (⊙join-sphere m)

