{-# OPTIONS --without-K #-}

open import Base

module CategoryTheory.ReflectiveSubCategory {m} where

record rsc : Set (suc m) where
  constructor Rsc
  field
    P : Set m → Set m
    P-is-prop : (A : Set m) → is-prop (P A)
    reflect : Set m → Set m
    to-reflect : (A : Set m) → A → reflect A
    reflect-in-P : (A : Set m) → P (reflect A)
    adjoint : (A B : Set m) ⦃ B-in-P : P B ⦄ → is-equiv (λ (f : reflect A → B) → f ◯ to-reflect A)

open rsc ⦃...⦄

adjoint-equiv : ⦃ rs : rsc ⦄ (A B : Set m) (B-in-P : P B) → (reflect A → B) ≃ (A → B)
adjoint-equiv A B B-in-P = (_ , adjoint A B)

map-reflect : ⦃ rs : rsc ⦄ {X Y : Set m} (f : X → Y) → (reflect X → reflect Y)
map-reflect {X} {Y} f = (adjoint-equiv X (reflect Y) (reflect-in-P Y)) ⁻¹ $ (to-reflect Y ◯ f)

reduce-map-reflect : ⦃ rs : rsc ⦄ {X Y : Set m} (f : X → Y) → (map-reflect f ◯ to-reflect X ≡ to-reflect Y ◯ f)
reduce-map-reflect {X} {Y} f = inverse-right-inverse (adjoint-equiv X (reflect Y) (reflect-in-P Y)) (to-reflect Y ◯ f)

compose-map-reflect : ⦃ rs : rsc ⦄ {X Y Z : Set m} (g : Y → Z) (f : X → Y) → map-reflect g ◯ map-reflect f ≡ map-reflect (g ◯ f)
compose-map-reflect {X} {Y} {Z} g f = equiv-is-inj (adjoint-equiv X (reflect Z) (reflect-in-P Z)) _ _
  lemma where
  lemma : map-reflect g ◯ (map-reflect f ◯ to-reflect X) ≡ map-reflect (g ◯ f) ◯ to-reflect X
  lemma = map (λ u → map-reflect g ◯ u) (reduce-map-reflect f) ∘ (map (λ u → u ◯ f) (reduce-map-reflect g) ∘ ! (reduce-map-reflect (g ◯ f)))
