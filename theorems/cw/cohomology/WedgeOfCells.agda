{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import homotopy.PushoutSplit
open import cw.CW

module cw.cohomology.WedgeOfCells {i} (CT : OrdinaryTheory i) where

open OrdinaryTheory CT
private
  G = C 0 (⊙Lift ⊙Bool)

incl-last : ∀ {n} (skel : Skeleton {i} (S n))
  → (⟦ skel ⟧₋₁ → ⟦ skel ⟧)
incl-last (skel-attach _ _ _) = incl

{- the equivalence is in the opposite direction because
   cohomology functors are contravariant. -}
Cofiber-incl-last : ∀ {n} (skel : Skeleton {i} (S n))
  → BigWedge {A = fst (cells-last skel)} (λ _ → ⊙Sphere (S n))
  ≃ Cofiber (incl-last skel)
Cofiber-incl-last {n} (skel-attach skel cells attaching)
  = PS.split-equiv ∘e equiv to from to-from from-to
  where
    module PS = PushoutLSplit (uncurry attaching) (λ _ → tt) fst

    module SphereToCofiber (a : fst cells) = SuspRec {A = Sphere n}
      (cfbase' (fst :> (fst cells × Sphere n → fst cells)))
      (cfcod a) (λ s → cfglue (a , s))

    module To = BigWedgeRec {A = fst cells} {X = λ _ → ⊙Sphere (S n)}
      cfbase SphereToCofiber.f (λ _ → idp)
    to = To.f

    module From = CofiberRec {f = fst :> (fst cells × Sphere n → fst cells)}
      (bwbase {A = fst cells} {X = λ _ → ⊙Sphere (S n)})
      (λ a → bwin a south) (λ{(a , s) → bwglue a ∙ ap (bwin a) (merid s)})
    from = From.f

    from-to : ∀ b → from (to b) == b
    from-to = BigWedge-elim
      idp
      (λ a → Susp-elim (bwglue a) idp
        (λ s → ↓-='-from-square $
          ( ap-∘ from (SphereToCofiber.f a) (merid s)
          ∙ ap (ap from) (SphereToCofiber.merid-β a s)
          ∙ From.glue-β (a , s))
          ∙v⊡ (tl-square (bwglue a) ⊡h vid-square)))
      (λ a → ↓-∘=idf-from-square from to $
        ap (ap from) (To.glue-β a) ∙v⊡ br-square (bwglue a))

    to-from : ∀ c → to (from c) == c
    to-from = Cofiber-elim
      idp (λ a → idp)
      (λ{(a , s) → ↓-∘=idf-in' to from $
          ap (ap to) (From.glue-β (a , s))
        ∙ ap-∙ to (bwglue a) (ap (bwin a) (merid s))
        ∙ ap2 _∙_ (To.glue-β a)
                  ( ∘-ap to (bwin a) (merid s)
                  ∙ SphereToCofiber.merid-β a s)})

⊙Cofiber-incl-last : ∀ {n} (skel : Skeleton {i} (S n))
  → ⊙BigWedge {A = fst (cells-last skel)} (λ _ → ⊙Sphere (S n))
  ⊙≃ ⊙[ Cofiber (incl-last skel) , cfbase ]
⊙Cofiber-incl-last (skel-attach skel cells attaching)
  = ≃-to-⊙≃ (Cofiber-incl-last (skel-attach skel cells attaching)) idp

C-incl-last : ∀ n {m} (skel : Skeleton {i} (S m))
  → (ac : has-cells-with-choice 0 skel i)
  →  C n (Cofiber (incl-last skel) , cfbase)
  ≃ᴳ Πᴳ (fst (cells-last skel)) (λ _ → C n (⊙Lift (⊙Sphere (S m))))
C-incl-last n {m} (skel-attach skel cells attaching) (_ , cells-ac)
  =   C-additive-iso n (λ _ → ⊙Lift (⊙Sphere (S m))) cells-ac
  ∘eᴳ C-emap n (   ⊙Cofiber-incl-last (skel-attach skel cells attaching)
               ⊙∘e ⊙BigWedge-emap-r (λ a → ⊙lower-equiv))
