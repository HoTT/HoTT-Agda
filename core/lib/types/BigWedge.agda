{-# OPTIONS --without-K --rewriting #-}

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
open import lib.types.Suspension
open import lib.types.Wedge

module lib.types.BigWedge where

module _ {i j} {A : Type i} where

  {- the function for cofiber -}
  bigwedge-f : (X : A → Ptd j) → A → Σ A (de⊙ ∘ X)
  bigwedge-f X a = a , pt (X a)

  bigwedge-span : (A → Ptd j) → Span
  bigwedge-span X = cofiber-span (bigwedge-f X)

  BigWedge : (A → Ptd j) → Type (lmax i j)
  BigWedge X = Cofiber (bigwedge-f X)

  bwbase : {X : A → Ptd j} → BigWedge X
  bwbase = cfbase

  bwin : {X : A → Ptd j} → (a : A) → de⊙ (X a) → BigWedge X
  bwin = curry cfcod

  ⊙BigWedge : (A → Ptd j) → Ptd (lmax i j)
  ⊙BigWedge X = ⊙[ BigWedge X , bwbase ]

  bwglue : {X : A → Ptd j} → (a : A) → bwbase {X} == bwin a (pt (X a))
  bwglue = cfglue

  ⊙bwin : {X : A → Ptd j} → (a : A) → X a ⊙→ ⊙BigWedge X
  ⊙bwin a = (bwin a , ! (bwglue a))

  module BigWedgeElim {X : A → Ptd j} {k} {P : BigWedge X → Type k}
    (base* : P bwbase) (in* : (a : A) (x : de⊙ (X a)) → P (bwin a x))
    (glue* : (a : A) → base* == in* a (pt (X a)) [ P ↓ bwglue a ])
    = CofiberElim {f = bigwedge-f X} {P = P} base* (uncurry in*) glue*

  BigWedge-elim = BigWedgeElim.f

  module BigWedgeRec {X : A → Ptd j} {k} {C : Type k}
    (base* : C) (in* : (a : A) → de⊙ (X a) → C)
    (glue* : (a : A) → base* == in* a (pt (X a)))
    = CofiberRec {f = bigwedge-f X} {C = C} base* (uncurry in*) glue*

module _ {i j₀ j₁} {A : Type i} {X₀ : A → Ptd j₀} {X₁ : A → Ptd j₁}
  (Xeq : ∀ a → X₀ a ⊙≃ X₁ a) where

  bigwedge-span-emap-r : SpanEquiv (cofiber-span (bigwedge-f X₀)) (cofiber-span (bigwedge-f X₁))
  bigwedge-span-emap-r = span-map (idf _) (Σ-fmap-r λ a → fst (⊙–> (Xeq a))) (idf _)
    (comm-sqr λ _ → idp) (comm-sqr λ a → pair= idp (⊙–>-pt (Xeq a))) ,
    idf-is-equiv _ , Σ-isemap-r (λ a → snd (Xeq a)) , idf-is-equiv _

  BigWedge-emap-r : BigWedge X₀ ≃ BigWedge X₁
  BigWedge-emap-r = Pushout-emap bigwedge-span-emap-r

  ⊙BigWedge-emap-r : ⊙BigWedge X₀ ⊙≃ ⊙BigWedge X₁
  ⊙BigWedge-emap-r = ≃-to-⊙≃ BigWedge-emap-r idp

module _ {i₀ i₁ j} {A₀ : Type i₀} {A₁ : Type i₁}
  (X : A₁ → Ptd j) (Aeq : A₀ ≃ A₁) where

  bigwedge-span-emap-l : SpanEquiv (cofiber-span (bigwedge-f (X ∘ –> Aeq))) (cofiber-span (bigwedge-f X))
  bigwedge-span-emap-l = span-map (idf _) (Σ-fmap-l (de⊙ ∘ X) (–> Aeq)) (–> Aeq)
    (comm-sqr λ _ → idp) (comm-sqr λ _ → idp) ,
    idf-is-equiv _ , Σ-isemap-l (de⊙ ∘ X) (snd Aeq) , snd Aeq

  BigWedge-emap-l : BigWedge (X ∘ –> Aeq) ≃ BigWedge X
  BigWedge-emap-l = Pushout-emap bigwedge-span-emap-l

  ⊙BigWedge-emap-l : ⊙BigWedge (X ∘ –> Aeq) ⊙≃ ⊙BigWedge X
  ⊙BigWedge-emap-l = ≃-to-⊙≃ BigWedge-emap-l idp

module _ {i j} {A : Type i} (X : A → Ptd j) where

  extract-glue-from-BigWedge-is-const :
    ∀ bw → extract-glue {s = bigwedge-span X} bw == north
  extract-glue-from-BigWedge-is-const = BigWedge-elim
    idp
    (λ x y → ! (merid x))
    (↓-='-from-square ∘ λ x →
      ExtractGlue.glue-β x ∙v⊡
        tr-square (merid x)
      ⊡v∙ ! (ap-cst north (cfglue x)))

{- A BigWedge indexed by Bool is just a binary Wedge -}
module _ {i} (Pick : Bool → Ptd i) where

  BigWedge-Bool-equiv-Wedge : BigWedge Pick ≃ Wedge (Pick true) (Pick false)
  BigWedge-Bool-equiv-Wedge = equiv f g f-g g-f
    where
    module F = BigWedgeRec {X = Pick}
      {C = Wedge (Pick true) (Pick false)}
      (winl (pt (Pick true)))
      (λ {true → winl; false → winr})
      (λ {true → idp; false → wglue})

    module G = WedgeRec {X = Pick true} {Y = Pick false}
      {C = BigWedge Pick}
      (bwin true)
      (bwin false)
      (! (bwglue true) ∙ bwglue false)

    f = F.f
    g = G.f

    abstract
      f-g : ∀ w → f (g w) == w
      f-g = Wedge-elim
        (λ _ → idp)
        (λ _ → idp)
        (↓-∘=idf-in' f g {p = wglue} {v = idp} $
          ap f (ap g wglue)
            =⟨ ap (ap f) G.glue-β ⟩
          ap f (! (bwglue true) ∙ bwglue false)
            =⟨ ap-∙ f (! (bwglue true)) (bwglue false) ⟩
          ap f (! (bwglue true)) ∙ ap f (bwglue false)
            =⟨ ap-! f (bwglue true)
               |in-ctx (λ w → w ∙ ap f (bwglue false)) ⟩
          ! (ap f (bwglue true)) ∙ ap f (bwglue false)
            =⟨ F.glue-β true
               |in-ctx (λ w → ! w ∙ ap f (bwglue false)) ⟩
          ap f (bwglue false)
            =⟨ F.glue-β false ⟩
          wglue =∎)

      g-f : ∀ bw → g (f bw) == bw
      g-f = BigWedge-elim
        (! (bwglue true))
        (λ {true → λ _ → idp; false → λ _ → idp})
        (λ {true → ↓-∘=idf-from-square g f $
              ap (ap g) (F.glue-β true) ∙v⊡
              bl-square (bwglue true);
            false → ↓-∘=idf-from-square g f $
              (ap (ap g) (F.glue-β false) ∙ G.glue-β) ∙v⊡
              lt-square (! (bwglue true)) ⊡h vid-square})

module _ {i j} {A : Type i} (dec : has-dec-eq A) {X : Ptd j} where

  {- The dependent version increases the complexity significantly
     and we do not need it. -}

  ⊙bwproj-in : A → A → X ⊙→ X
  ⊙bwproj-in a a' with dec a a'
  ... | inl _ = ⊙idf _
  ... | inr _ = ⊙cst

  module BigWedgeProj (a : A) = BigWedgeRec
    {X = λ _ → X}
    (pt X)
    (λ a' → fst (⊙bwproj-in a a'))
    (λ a' → ! (snd (⊙bwproj-in a a')))

  bwproj : A → BigWedge (λ _ → X) → de⊙ X
  bwproj = BigWedgeProj.f

  ⊙bwproj : A → ⊙BigWedge (λ _ → X) ⊙→ X
  ⊙bwproj a = bwproj a , idp

  abstract
    bwproj-bwin-diag : (a : A) → bwproj a ∘ bwin a ∼ idf (de⊙ X)
    bwproj-bwin-diag a x with dec a a
    ... | inl _ = idp
    ... | inr a≠a with a≠a idp
    ...           | ()

    bwproj-bwin-≠ : {a a' : A} → a ≠ a' → bwproj a ∘ bwin a' ∼ cst (pt X)
    bwproj-bwin-≠ {a} {a'} a≠a' x with dec a a'
    ... | inr _ = idp
    ... | inl a=a' with a≠a' a=a'
    ...            | ()

module _ {i j k} {A : Type i} (dec : has-dec-eq A) {X : Ptd j} (a : A) where

  abstract
    private
      bwproj-BigWedge-emap-r-lift-in : ∀ a'
        → bwproj dec {X = ⊙Lift {j = k} X} a ∘ bwin a' ∘ lift
        ∼ lift {j = k} ∘ bwproj dec {X = X} a ∘ bwin a'
      bwproj-BigWedge-emap-r-lift-in a' with dec a a'
      ... | inl _ = λ _ → idp
      ... | inr _ = λ _ → idp

      bwproj-BigWedge-emap-r-lift-glue' : ∀ (a' : A)
        → ap (lift {j = k}) (! (snd (⊙bwproj-in dec {X = X} a a')))
        == ! (snd (⊙bwproj-in dec {X = ⊙Lift {j = k} X} a a')) ∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)
      bwproj-BigWedge-emap-r-lift-glue' a' with dec a a'
      ... | inl _ = idp
      ... | inr _ = idp

    bwproj-BigWedge-emap-r-lift-glue : ∀ (a' : A)
      →  idp == bwproj-BigWedge-emap-r-lift-in a' (pt X)
      [ (λ x → bwproj dec {X = ⊙Lift {j = k} X} a (–> (BigWedge-emap-r (λ _ → ⊙lift-equiv {j = k})) x)
            == lift {j = k} (bwproj dec {X = X} a x)) ↓ bwglue a' ]
    bwproj-BigWedge-emap-r-lift-glue a' = ↓-='-in' $
      ap (lift {j = k} ∘ bwproj dec a) (bwglue a')
        =⟨ ap-∘ (lift {j = k}) (bwproj dec a) (bwglue a') ⟩
      ap (lift {j = k}) (ap (bwproj dec a) (bwglue a'))
        =⟨ ap (ap (lift {j = k})) $ BigWedgeProj.glue-β dec a a' ⟩
      ap (lift {j = k}) (! (snd (⊙bwproj-in dec a a')))
        =⟨ bwproj-BigWedge-emap-r-lift-glue' a' ⟩
      ! (snd (⊙bwproj-in dec a a')) ∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)
        =⟨ ap (_∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)) $
            ( ! $ BigWedgeProj.glue-β dec a a') ⟩
      ap (bwproj dec a) (bwglue a') ∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)
        =⟨ ap (λ p → ap (bwproj dec a) p
                  ∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)) $
            (! $ PushoutFmap.glue-β (fst (bigwedge-span-emap-r (λ _ → ⊙lift-equiv {j = k}))) a') ⟩
      ap (bwproj dec a) (ap (–> (BigWedge-emap-r (λ _ → ⊙lift-equiv {j = k}))) (bwglue a'))
      ∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)
        =⟨ ap (_∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)) $
            (∘-ap (bwproj dec a) (–> (BigWedge-emap-r (λ _ → ⊙lift-equiv {j = k}))) (bwglue a')) ⟩
      ap (bwproj dec a ∘ –> (BigWedge-emap-r (λ _ → ⊙lift-equiv {j = k}))) (bwglue a')
      ∙' bwproj-BigWedge-emap-r-lift-in a' (pt X)
        =∎

    bwproj-BigWedge-emap-r-lift :
        bwproj dec {X = ⊙Lift {j = k} X} a ∘ –> (BigWedge-emap-r (λ _ → ⊙lift-equiv {j = k}))
      ∼ lift {j = k} ∘ bwproj dec a
    bwproj-BigWedge-emap-r-lift =
      BigWedge-elim {X = λ _ → X} idp
        bwproj-BigWedge-emap-r-lift-in
        bwproj-BigWedge-emap-r-lift-glue
