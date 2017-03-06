{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import homotopy.PushoutSplit
open import homotopy.DisjointlyPointedSet
open import cw.CW

module cw.cohomology.WedgeOfCells {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S n)) where

open OrdinaryTheory OT
open import cohomology.Sphere OT

Xₙ/Xₙ₋₁ : Ptd i
Xₙ/Xₙ₋₁ = ⊙Cofiber (⊙cw-incl-last ⊙skel)

module _ (m : ℤ) where
  CXₙ/Xₙ₋₁ : Group i
  CXₙ/Xₙ₋₁ = C m Xₙ/Xₙ₋₁

  CEl-Xₙ/Xₙ₋₁ : Type i
  CEl-Xₙ/Xₙ₋₁ = Group.El CXₙ/Xₙ₋₁

  abstract
    CXₙ/Xₙ₋₁-is-abelian : is-abelian CXₙ/Xₙ₋₁
    CXₙ/Xₙ₋₁-is-abelian = C-is-abelian m Xₙ/Xₙ₋₁

  CXₙ/Xₙ₋₁-abgroup : AbGroup i
  CXₙ/Xₙ₋₁-abgroup = CXₙ/Xₙ₋₁ , CXₙ/Xₙ₋₁-is-abelian

{- the equivalence is in the opposite direction because
   cohomology functors are contravariant. -}
BigWedge-⊙equiv-Xₙ/Xₙ₋₁ : ⊙BigWedge {A = ⊙cells-last ⊙skel} (λ _ → ⊙Sphere (S n)) ⊙≃ Xₙ/Xₙ₋₁
BigWedge-⊙equiv-Xₙ/Xₙ₋₁ = ≃-to-⊙≃
  (PS.split-equiv ∘e equiv to from to-from from-to) idp
  where
    open AttachedSkeleton (⊙Skeleton.skel ⊙skel)

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

    abstract
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

CXₙ/Xₙ₋₁-β : ∀ m → ⊙has-cells-with-choice 0 ⊙skel i
  → C m Xₙ/Xₙ₋₁ ≃ᴳ Πᴳ (⊙cells-last ⊙skel) (λ _ → C m (⊙Lift (⊙Sphere (S n))))
CXₙ/Xₙ₋₁-β m ac = C-additive-iso m (λ _ → ⊙Lift (⊙Sphere (S n))) (⊙cells-last-has-choice ⊙skel ac)
              ∘eᴳ C-emap m ( BigWedge-⊙equiv-Xₙ/Xₙ₋₁
                         ⊙∘e ⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))

CXₙ/Xₙ₋₁-β-diag : ⊙has-cells-with-choice 0 ⊙skel i
  → CXₙ/Xₙ₋₁ (ℕ-to-ℤ (S n)) ≃ᴳ Πᴳ (⊙cells-last ⊙skel) (λ _ → C2 0)
CXₙ/Xₙ₋₁-β-diag ac = Πᴳ-emap-r (⊙cells-last ⊙skel) (λ _ → C-Sphere-diag (S n))
                 ∘eᴳ CXₙ/Xₙ₋₁-β (ℕ-to-ℤ (S n)) ac

abstract
  CXₙ/Xₙ₋₁-≠-is-trivial : ∀ {m} (m≠Sn : m ≠ ℕ-to-ℤ (S n))
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CXₙ/Xₙ₋₁ m)
  CXₙ/Xₙ₋₁-≠-is-trivial {m} m≠Sn ac =
    iso-preserves'-trivial (CXₙ/Xₙ₋₁-β m ac) $
      Πᴳ-is-trivial (⊙cells-last ⊙skel)
        (λ _ → C m (⊙Lift (⊙Sphere (S n))))
        (λ _ → C-Sphere-≠-is-trivial m (S n) m≠Sn)

  CXₙ/Xₙ₋₁-<-is-trivial : ∀ {m} (m<Sn : m < S n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CXₙ/Xₙ₋₁ (ℕ-to-ℤ m))
  CXₙ/Xₙ₋₁-<-is-trivial m<Sn = CXₙ/Xₙ₋₁-≠-is-trivial (ℕ-to-ℤ-≠ (<-to-≠ m<Sn))

  CXₙ/Xₙ₋₁->-is-trivial : ∀ {m} (m>Sn : S n < m)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CXₙ/Xₙ₋₁ (ℕ-to-ℤ m))
  CXₙ/Xₙ₋₁->-is-trivial m>Sn = CXₙ/Xₙ₋₁-≠-is-trivial (≠-inv (ℕ-to-ℤ-≠ (<-to-≠ m>Sn)))
