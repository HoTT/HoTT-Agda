{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PullbackDef

{- In this file we prove that if two diagrams are equivalent (there are
   equivalences between the types and the squares are commutative), then the
   natural map between the pullbacks is also an equivalence -}

module Homotopy.PullbackInvariantEquiv {i}
    (d d' : pullback-diag i) where

private
  pullback-to-pullback : ∀ {i} {A A' : Set i} (p : A ≡ A')
    {B B' : Set i} (q : B ≡ B') {C C' : Set i} (r : C ≡ C')
    {f : A → C} {f' : A' → C'}
    (s : (a : A) → f' ((transport _ p) a) ≡ transport _ r (f a))
    {g : B → C} {g' : B' → C'}
    (t : (b : B) → transport _ r (g b) ≡ g' ((transport _ q) b))
    → pullback (diag A , B , C , f , g) → pullback (diag A' , B' , C' , f' , g')
  pullback-to-pullback p q r s t (a , b , e) =
    (transport _ p a , transport _ q b , (s a ∘ (map (transport _ r) e ∘ t b)))

  transport-pullback : ∀ {i} {A A' : Set i} (p : A ≡ A')
    {B B' : Set i} (q : B ≡ B') {C C' : Set i} (r : C ≡ C')
    {f : A → C} {f' : A' → C'} (s : f' ◯ (transport _ p) ≡ transport _ r ◯ f)
    {g : B → C} {g' : B' → C'} (t : transport _ r ◯ g ≡ g' ◯ (transport _ q))
    → transport pullback (pullback-diag-raw-eq p q r {f' = f'} s {g' = g'} t)
      ≡ pullback-to-pullback p q r (happly s) (happly t)
  transport-pullback (refl _) (refl _) (refl _) (refl _) (refl _) =
    funext (λ r → map (λ u → _ , _ , u)
                  (! (map-id _) ∘ ! (refl-right-unit _)))

  transport-pullback-funext : ∀ {i} {A A' : Set i} (p : A ≡ A')
    {B B' : Set i} (q : B ≡ B') {C C' : Set i} (r : C ≡ C')
    {f : A → C} {f' : A' → C'}
    (s : (a : A) → f' ((transport _ p) a) ≡ transport _ r (f a))
    {g : B → C} {g' : B' → C'}
    (t : (b : B) → transport _ r (g b) ≡ g' ((transport _ q) b))
    → transport pullback (pullback-diag-raw-eq p q r {f' = f'} (funext s)
                                                     {g' = g'} (funext t))
      ≡ pullback-to-pullback p q r s t
  transport-pullback-funext p q r s t =
    transport-pullback p q r (funext s) (funext t)
    ∘ (map (λ u → pullback-to-pullback p q r u (happly (funext t)))
           (happly-funext s)
    ∘ map (λ u → pullback-to-pullback p q r s u) (happly-funext t))

  path-to-eq-map : ∀ {i j} {A : Set i} (P : A → Set j) {x y : A} (p : x ≡ y)
    → π₁ (path-to-eq (map P p)) ≡ transport P p
  path-to-eq-map P (refl _) = refl _

open pullback-diag d
open pullback-diag d' renaming (A to A'; B to B'; C to C'; f to f'; g to g')

module PullbackInvariantEquiv (eqA : A ≃ A') (eqB : B ≃ B') (eqC : C ≃ C')
           (p : (a : A) → f' (eqA ☆ a) ≡ eqC ☆ (f a))
           (q : (b : B) → eqC ☆ (g b) ≡ g' (eqB ☆ b)) where

  private
    d≡d' : d ≡ d'
    d≡d' = pullback-diag-eq eqA eqB eqC p q

    pullback-equiv-pullback : pullback d ≃ pullback d'
    pullback-equiv-pullback = path-to-eq (map pullback d≡d')

    h : (a : A) → f' ((transport (λ v → v) (eq-to-path eqA) a))
                  ≡ transport (λ v → v) (eq-to-path eqC) (f a)
    h a = map f' (trans-id-eq-to-path eqA a)
          ∘ (p a ∘ (! (trans-id-eq-to-path eqC (f a))))

    h' : (b : B) → transport (λ v → v) (eq-to-path eqC) (g b)
                   ≡ g' ((transport (λ v → v) (eq-to-path eqB) b))
    h' b = trans-id-eq-to-path eqC (g b)
           ∘ (q b ∘ map g' (! (trans-id-eq-to-path eqB b)))

  pullback-to-equiv-pullback : pullback d → pullback d'
  pullback-to-equiv-pullback (a , b , e) =
    ((eqA ☆ a) , (eqB ☆ b) , (p a ∘ (map (π₁ eqC) e ∘ q b)))

  private
    pb-to-pb-equal-pb-to-equiv-pb : (x : pullback d)
      → pullback-to-pullback (eq-to-path eqA) (eq-to-path eqB) (eq-to-path eqC)
                             h h' x
        ≡ pullback-to-equiv-pullback x
    pb-to-pb-equal-pb-to-equiv-pb (a , b , h) =
      pullback-eq d' (trans-id-eq-to-path eqA a)
        (trans-id-eq-to-path eqB b)
        (concat-assoc (map f' (trans-id (eq-to-path eqA) a ∘ _) ∘ _) _ _
         ∘ (concat-assoc (map f' (trans-id (eq-to-path eqA) a ∘ _)) _ _
         ∘ whisker-left (map f' (trans-id (eq-to-path eqA) a ∘ _))
        (concat-assoc (p a) _ _
         ∘ whisker-left (p a)
        (whisker-left (! (trans-id (eq-to-path eqC) (f a) ∘ _))
          (concat-assoc (map (transport (λ v → v) (eq-to-path eqC)) h) _ _
           ∘ whisker-left (map (transport (λ v → v) (eq-to-path eqC)) h)
          (concat-assoc (trans-id (eq-to-path eqC) (g b) ∘ _) _ _
           ∘ whisker-left (trans-id (eq-to-path eqC) (g b) ∘ _)
          (concat-assoc (q b) _ _
           ∘ (whisker-left (q b)
          (concat-map g' (! (trans-id (eq-to-path eqB) b ∘ _)) _
           ∘ map (map g')
             (opposite-left-inverse (trans-id (eq-to-path eqB) b ∘ _)))
           ∘ refl-right-unit (q b)))))
         ∘ move!-right-on-left (trans-id (eq-to-path eqC) (f a) ∘ _) _ _
         (! (concat-assoc (map (transport (λ v → v) (eq-to-path eqC)) h)
                (trans-id (eq-to-path eqC) (g b) ∘ _) _)
         ∘ ((whisker-right (q b)
              (homotopy-naturality (transport (λ v → v) (eq-to-path eqC))
                 (π₁ eqC)
                 (λ t → trans-id (eq-to-path eqC) t
                        ∘ map (λ u → π₁ u t) (eq-to-path-right-inverse eqC))
                 h))
           ∘ concat-assoc (trans-id (eq-to-path eqC) (f a) ∘ _) (map (π₁ eqC) h)
               (q b)))))))

    pb-equiv-pb-equal-pb-to-equiv-pb
      : π₁ pullback-equiv-pullback ≡ pullback-to-equiv-pullback
    pb-equiv-pb-equal-pb-to-equiv-pb =
        path-to-eq-map pullback d≡d'
        ∘ (transport-pullback-funext (eq-to-path eqA) (eq-to-path eqB)
                                     (eq-to-path eqC) h h'
        ∘ funext pb-to-pb-equal-pb-to-equiv-pb)

  abstract
    pullback-invariant-is-equiv : is-equiv pullback-to-equiv-pullback
    pullback-invariant-is-equiv =
      transport is-equiv pb-equiv-pb-equal-pb-to-equiv-pb
                (π₂ pullback-equiv-pullback)

  pullback-invariant-equiv : pullback d ≃ pullback d'
  pullback-invariant-equiv =
    (pullback-to-equiv-pullback , pullback-invariant-is-equiv)

open PullbackInvariantEquiv public
