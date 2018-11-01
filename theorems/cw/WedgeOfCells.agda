{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import homotopy.PushoutSplit
open import homotopy.DisjointlyPointedSet
open import cw.CW

module cw.WedgeOfCells {i} {n} (skel : Skeleton {i} (S n)) where

Xₙ/Xₙ₋₁ : Type i
Xₙ/Xₙ₋₁ = Cofiber (cw-incl-last skel)

⊙Xₙ/Xₙ₋₁ : Ptd i
⊙Xₙ/Xₙ₋₁ = ⊙[ Xₙ/Xₙ₋₁ , cfbase ]

private
  cells : Type i
  cells = cells-last skel

  attaching : cells → (Sphere n → ⟦ skel ⟧₋₁)
  attaching = attaching-last skel

  {- this is also a cofiber -}
  BigWedgeSusp : Type i
  BigWedgeSusp = Attached {A = ⊤} {B = cells} {C = Sphere n} (λ _ _ → unit)

  ⊙BigWedgeSusp : Ptd i
  ⊙BigWedgeSusp = ⊙[ BigWedgeSusp , cfbase ]

private
  module SphereToBigWedgeSusp (a : cells) = SuspRec {A = Sphere n}
    (cfbase :> BigWedgeSusp) (cfcod a) (λ s → cfglue (a , s))

  module BouquetToBigWedgeSusp =
    BigWedgeRec {A = cells} {X = Bouquet-family cells (S n)}
    cfbase SphereToBigWedgeSusp.f (λ _ → idp)

  module BigWedgeSuspEquivQuotient = PushoutLSplit (uncurry attaching) (λ _ → unit) fst

Bouquet-to-Xₙ/Xₙ₋₁ : Bouquet cells (S n) → Xₙ/Xₙ₋₁
Bouquet-to-Xₙ/Xₙ₋₁ = BigWedgeSuspEquivQuotient.split ∘ BouquetToBigWedgeSusp.f

abstract
  Bouquet-to-Xₙ/Xₙ₋₁-in-merid-β : ∀ (a : cells) x
    → ap (Bouquet-to-Xₙ/Xₙ₋₁ ∘ bwin a) (merid x)
    == cfglue (attaching a x) ∙' ap cfcod (spoke a x)
  Bouquet-to-Xₙ/Xₙ₋₁-in-merid-β a x =
      ap-∘ BigWedgeSuspEquivQuotient.split (SphereToBigWedgeSusp.f a) (merid x)
    ∙ ap (ap BigWedgeSuspEquivQuotient.split) (SphereToBigWedgeSusp.merid-β a x)
    ∙ BigWedgeSuspEquivQuotient.split-glue-β (a , x)

private
  Bouquet-to-BigWedgeSusp-is-equiv : is-equiv BouquetToBigWedgeSusp.f
  Bouquet-to-BigWedgeSusp-is-equiv = is-eq to from to-from from-to
    where
    to = BouquetToBigWedgeSusp.f

    module From = AttachedRec {A = ⊤}
      (λ _ → bwbase :> Bouquet cells (S n))
      (λ a → bwin a south) (λ a s → bwglue a ∙ ap (bwin a) (merid s))
    from = From.f

    abstract
      from-to : ∀ b → from (to b) == b
      from-to = BigWedge-elim
        idp
        (λ a → Susp-elim (bwglue a) idp
          (λ s → ↓-='-from-square $
            ( ap-∘ from (SphereToBigWedgeSusp.f a) (merid s)
            ∙ ap (ap from) (SphereToBigWedgeSusp.merid-β a s)
            ∙ From.spoke-β a s)
            ∙v⊡ tl-square (bwglue a) ⊡h vid-square))
        (λ a → ↓-∘=idf-from-square from to $
          ap (ap from) (BouquetToBigWedgeSusp.glue-β a) ∙v⊡ br-square (bwglue a))

      to-from : ∀ c → to (from c) == c
      to-from = Attached-elim
        (λ _ → idp) (λ a → idp)
        (λ a s → ↓-∘=idf-in' to from $
            ap (ap to) (From.spoke-β a s)
          ∙ ap-∙ to (bwglue a) (ap (bwin a) (merid s))
          ∙ ap2 _∙_ (BouquetToBigWedgeSusp.glue-β a)
                    ( ∘-ap to (bwin a) (merid s)
                    ∙ SphereToBigWedgeSusp.merid-β a s))

  Bouquet-equiv-BigWedgeSusp : Bouquet cells (S n) ≃ BigWedgeSusp
  Bouquet-equiv-BigWedgeSusp = BouquetToBigWedgeSusp.f , Bouquet-to-BigWedgeSusp-is-equiv

Bouquet-equiv-Xₙ/Xₙ₋₁ : Bouquet cells (S n) ≃ Xₙ/Xₙ₋₁
Bouquet-equiv-Xₙ/Xₙ₋₁ = BigWedgeSuspEquivQuotient.split-equiv ∘e Bouquet-equiv-BigWedgeSusp

Bouquet-⊙equiv-Xₙ/Xₙ₋₁ : ⊙Bouquet cells (S n) ⊙≃ ⊙Xₙ/Xₙ₋₁
Bouquet-⊙equiv-Xₙ/Xₙ₋₁ = ≃-to-⊙≃ Bouquet-equiv-Xₙ/Xₙ₋₁ idp
