{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.cubical.Square
open import lib.types.Bool
open import lib.types.Cofiber
open import lib.types.Lift
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.PushoutFmap
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Wedge

module lib.types.BigWedge where

module _ {i j} {A : Type i} where

  {- the function for cofiber -}
  bigwedge-f : (X : A → Ptd j) → A → Σ A (fst ∘ X)
  bigwedge-f X a = a , snd (X a)

  bigwedge-span : (A → Ptd j) → Span
  bigwedge-span X = cofiber-span (bigwedge-f X)

  BigWedge : (A → Ptd j) → Type (lmax i j)
  BigWedge X = Cofiber (bigwedge-f X)

  bwbase : {X : A → Ptd j} → BigWedge X
  bwbase = cfbase

  bwin : {X : A → Ptd j} → (a : A) → fst (X a) → BigWedge X
  bwin = curry cfcod

  ⊙BigWedge : (A → Ptd j) → Ptd (lmax i j)
  ⊙BigWedge X = ⊙[ BigWedge X , bwbase ]

  bwglue : {X : A → Ptd j} → (a : A) → bwbase {X} == bwin a (snd (X a))
  bwglue = cfglue

  ⊙bwin : {X : A → Ptd j} → (a : A) → X a ⊙→ ⊙BigWedge X
  ⊙bwin a = (bwin a , ! (bwglue a))

  module BigWedgeElim {X : A → Ptd j} {k} {P : BigWedge X → Type k}
    (base* : P bwbase) (in* : (a : A) (x : fst (X a)) → P (bwin a x))
    (glue* : (a : A) → base* == in* a (snd (X a)) [ P ↓ bwglue a ])
    = CofiberElim {f = bigwedge-f X} {P = P} base* (uncurry in*) glue*

  BigWedge-elim = BigWedgeElim.f

  module BigWedgeRec {X : A → Ptd j} {k} {C : Type k}
    (base* : C) (in* : (a : A) → fst (X a) → C)
    (glue* : (a : A) → base* == in* a (snd (X a)))
    = CofiberRec {f = bigwedge-f X} {C = C} base* (uncurry in*) glue*

module _ {i j₀ j₁} {A : Type i} {X₀ : A → Ptd j₀} {X₁ : A → Ptd j₁}
  (Xeq : ∀ a → X₀ a ⊙≃ X₁ a) where

  bigwedge-span-emap-r : SpanEquiv (cofiber-span (bigwedge-f X₀)) (cofiber-span (bigwedge-f X₁))
  bigwedge-span-emap-r = span-map (idf _) (Σ-fmap-r λ a → fst (⊙–> (Xeq a))) (idf _)
    (comm-sqr λ _ → idp) (comm-sqr λ a → pair= idp (⊙–>-pt (Xeq a))) ,
    idf-is-equiv _ , Σ-isemap-r (λ a → snd (Xeq a)) , idf-is-equiv _

  BigWedge-emap-r : BigWedge X₀ ≃ BigWedge X₁
  BigWedge-emap-r = Pushout-emap bigwedge-span-emap-r

{- A BigWedge indexed by Bool is just a binary Wedge -}
module _ {i} (Pick : Lift {j = i} Bool → Ptd i) where

  BigWedge-Bool-equiv :
    BigWedge Pick ≃ Wedge (Pick (lift true)) (Pick (lift false))
  BigWedge-Bool-equiv = equiv f g f-g g-f
    where
    module F = BigWedgeRec {X = Pick}
      {C = Wedge (Pick (lift true)) (Pick (lift false))}
      (winl (snd (Pick (lift true))))
      (λ {(lift true) → winl; (lift false) → winr})
      (λ {(lift true) → idp; (lift false) → wglue})

    module G = WedgeRec {X = Pick (lift true)} {Y = Pick (lift false)}
      {C = BigWedge Pick}
      (bwin (lift true))
      (bwin (lift false))
      (! (bwglue (lift true)) ∙ bwglue (lift false))

    f = F.f
    g = G.f

    f-g : ∀ w → f (g w) == w
    f-g = Wedge-elim
      (λ _ → idp)
      (λ _ → idp)
      (↓-∘=idf-in' f g $
        ap f (ap g wglue)
          =⟨ ap (ap f) G.glue-β ⟩
        ap f (! (bwglue (lift true)) ∙ bwglue (lift false))
          =⟨ ap-∙ f (! (bwglue (lift true))) (bwglue (lift false)) ⟩
        ap f (! (bwglue (lift true))) ∙ ap f (bwglue (lift false))
          =⟨ ap-! f (bwglue (lift true))
             |in-ctx (λ w → w ∙ ap f (bwglue (lift false))) ⟩
        ! (ap f (bwglue (lift true))) ∙ ap f (bwglue (lift false))
          =⟨ F.glue-β (lift true)
             |in-ctx (λ w → ! w ∙ ap f (bwglue (lift false))) ⟩
        ap f (bwglue (lift false))
          =⟨ F.glue-β (lift false) ⟩
        wglue =∎)

    g-f : ∀ bw → g (f bw) == bw
    g-f = BigWedge-elim
      (! (bwglue (lift true)))
      (λ {(lift true) → λ _ → idp; (lift false) → λ _ → idp})
      (λ {(lift true) → ↓-∘=idf-from-square g f $
            ap (ap g) (F.glue-β (lift true)) ∙v⊡
            bl-square (bwglue (lift true));
          (lift false) → ↓-∘=idf-from-square g f $
            (ap (ap g) (F.glue-β (lift false)) ∙ G.glue-β) ∙v⊡
            lt-square (! (bwglue (lift true))) ⊡h vid-square})

  BigWedge-Bool-⊙path :
    ⊙BigWedge Pick == ⊙Wedge (Pick (lift true)) (Pick (lift false))
  BigWedge-Bool-⊙path = ⊙ua (≃-to-⊙≃ BigWedge-Bool-equiv idp)
