{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Lift
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Wedge
open import lib.cubical.Square

module lib.types.BigWedge where

module _ {i j} {A : Type i} where

  private
    data #BigWedge-aux (X : A → Ptd j) : Type (lmax i j) where
      #bwbase : #BigWedge-aux X
      #bwin : (a : A) → fst (X a) → #BigWedge-aux X

    data #BigWedge (X : A → Ptd j) : Type (lmax i j) where
      #bigwedge : #BigWedge-aux X → (Unit → Unit) → #BigWedge X

  BigWedge : (A → Ptd j) → Type (lmax i j)
  BigWedge X = #BigWedge X

  bwbase : {X : A → Ptd j} → BigWedge X
  bwbase = #bigwedge #bwbase _

  bwin : {X : A → Ptd j} → (a : A) → fst (X a) → BigWedge X
  bwin a x = #bigwedge (#bwin a x) _

  Ptd-BigWedge : (A → Ptd j) → Ptd (lmax i j)
  Ptd-BigWedge X = ∙[ BigWedge X , bwbase ]

  postulate  -- HIT
    bwglue : {X : A → Ptd j} → (a : A) → bwbase {X} == bwin a (snd (X a))

  ptd-bwin : {X : A → Ptd j} → (a : A) → fst (X a ∙→ Ptd-BigWedge X)
  ptd-bwin a = (bwin a , ! (bwglue a))

  module BigWedgeElim {X : A → Ptd j} {k} {P : BigWedge X → Type k}
    (base* : P bwbase)
    (in* : (a : A) (x : fst (X a)) → P (bwin a x))
    (glue* : (a : A) → base* == in* a (snd (X a)) [ P ↓ bwglue a ]) where

    f : Π (BigWedge X) P
    f = f-aux phantom where

      f-aux : Phantom glue* → Π (BigWedge X) P
      f-aux phantom (#bigwedge #bwbase _) = base*
      f-aux phantom (#bigwedge (#bwin a x) _) = in* a x

    postulate  -- HIT
      glue-β : (a : A) → apd f (bwglue a) == glue* a

  open BigWedgeElim public using () renaming (f to BigWedge-elim)

  module BigWedgeRec {X : A → Ptd j} {k} {C : Type k}
    (base* : C)
    (in* : (a : A) → fst (X a) → C)
    (glue* : (a : A) → base* == in* a (snd (X a))) where

    private
      module M = BigWedgeElim base* in* (λ c → ↓-cst-in (glue* c))

    f : BigWedge X → C
    f = M.f

    glue-β : (a : A) → ap f (bwglue a) == glue* a
    glue-β a = apd=cst-in {f = f} (M.glue-β a)

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
      (↓-∘=idf-in f g $
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
        wglue ∎)

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

  BigWedge-Bool-path :
    BigWedge Pick == Wedge (Pick (lift true)) (Pick (lift false))
  BigWedge-Bool-path = ua BigWedge-Bool-equiv

  BigWedge-Bool-ptd-path :
    Ptd-BigWedge Pick == Ptd-Wedge (Pick (lift true)) (Pick (lift false))
  BigWedge-Bool-ptd-path = ptd-ua BigWedge-Bool-equiv idp
