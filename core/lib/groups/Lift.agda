{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Lift
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism

module lib.groups.Lift where

Lift-group-structure : ∀ {i j} {A : Type i}
  → GroupStructure A → GroupStructure (Lift {j = j} A)
Lift-group-structure GS = record
  { ident = lift ident
  ; inv = λ {(lift x) → lift (inv x)}
  ; comp = λ {(lift x) (lift y) → lift (comp x y)}
  ; unit-l = λ {(lift y) → ap lift (unit-l y)}
  ; assoc = λ {(lift x) (lift y) (lift z) → ap lift (assoc x y z)}
  ; inv-l = λ {(lift x) → ap lift (inv-l x)}
  }
  where open GroupStructure GS

Lift-group : ∀ {i j} → Group i → Group (lmax i j)
Lift-group {j = j} G = group (Lift {j = j} El)
                             (Lift-group-structure group-struct)
  where open Group G

lift-hom : ∀ {i j} {G : Group i} → (G →ᴳ Lift-group {j = j} G)
lift-hom = group-hom lift (λ _ _ → idp)

lower-hom : ∀ {i j} {G : Group i} → (Lift-group {j = j} G →ᴳ G)
lower-hom = group-hom lower (λ _ _ → idp)

lift-iso : ∀ {i j} {G : Group i} → (G ≃ᴳ Lift-group {j = j} G)
lift-iso = lift-hom , snd lift-equiv

lower-iso : ∀ {i j} {G : Group i} → (Lift-group {j = j} G ≃ᴳ G)
lower-iso = lower-hom , snd lower-equiv

Lift-group-is-abelian : ∀ {i j} (G : Group i) → is-abelian G → is-abelian (Lift-group {j = j} G)
Lift-group-is-abelian G comm (lift g₁) (lift g₂) = ap lift (comm g₁ g₂)

Lift-abgroup : ∀ {i j} (G : AbGroup i) → AbGroup (lmax i j)
Lift-abgroup {j = j} G = Lift-group {j = j} (AbGroup.grp G)
  , Lift-group-is-abelian (AbGroup.grp G) (AbGroup.comm G)
