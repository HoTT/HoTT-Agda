{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1 using (EM₁-level₁)
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FundamentalCategory

module homotopy.EM1HSpaceAssoc where

module EM₁HSpaceAssoc {i} (G : AbGroup i) where

  private
    module G = AbGroup G
  open EM₁HSpace G public
  private
    module H-⊙EM₁ = HSpaceStructure H-⊙EM₁

  mult-loop-assoc : (g : G.El) (y z : EM₁ G.grp)
    → mult-loop g (mult y z) == ap (λ x' → mult x' z) (mult-loop g y)
  mult-loop-assoc g y z =
    EM₁-prop-elim {P = λ y → mult-loop g (mult y z) == ap (λ x' → mult x' z) (mult-loop g y)}
                  {{λ y → has-level-apply (has-level-apply (EM₁-level₁ G.grp) _ _) _ _}}
                  base' y
    where
    base' : mult-loop g (mult embase z) == ap (λ x' → mult x' z) (mult-loop g embase)
    base' = ! (mult-emloop-β g z)

  H-⊙EM₁-assoc : (x y z : EM₁ G.grp) → mult (mult x y) z == mult x (mult y z)
  H-⊙EM₁-assoc x y z =
    EM₁-set-elim {P = λ x → mult (mult x y) z == mult x (mult y z)}
                 {{λ x → has-level-apply (EM₁-level₁ G.grp) _ _}}
                 idp
                 comp'
                 x
    where
      abstract
        comp' : (g : G.El) → idp == idp [ (λ x → mult (mult x y) z == mult x (mult y z)) ↓ emloop g ]
        comp' g =
          ↓-='-in $
          idp ∙' ap (λ x → mult x (mult y z)) (emloop g)
            =⟨ ∙'-unit-l _ ⟩
          ap (λ x → mult x (mult y z)) (emloop g)
            =⟨ mult-emloop-β g (mult y z) ⟩
          mult-loop g (mult y z)
            =⟨ mult-loop-assoc g y z ⟩
          ap (λ v → mult v z) (mult-loop g y)
            =⟨ ap (ap (λ v → mult v z)) (! (mult-emloop-β g y)) ⟩
          ap (λ v → mult v z) (ap (λ x → mult x y) (emloop g))
            =⟨ ∘-ap (λ v → mult v z) (λ x → mult x y) (emloop g) ⟩
          ap (λ x → mult (mult x y) z) (emloop g)
            =⟨ ! (∙-unit-r _) ⟩
          ap (λ x → mult (mult x y) z) (emloop g) ∙ idp =∎

  H-EM₁-assoc-coh-unit-l : coh-unit-l H-⊙EM₁ H-⊙EM₁-assoc
  H-EM₁-assoc-coh-unit-l x y = =ₛ-in idp

  H-EM₁-assoc-coh-unit-r : coh-unit-r H-⊙EM₁ H-⊙EM₁-assoc
  H-EM₁-assoc-coh-unit-r =
    EM₁-prop-elim {P = λ x → ∀ y → P x y} {{λ x → Π-level (P-level x)}}
      (EM₁-prop-elim {P = P embase} {{P-level embase}} (=ₛ-in idp))
    where
    P : EM₁ G.grp → EM₁ G.grp → Type i
    P = coh-unit-r-eq H-⊙EM₁ H-⊙EM₁-assoc
    P-level : ∀ x y → is-prop (P x y)
    P-level x y = =ₛ-level (EM₁-level₁ G.grp)

  H-EM₁-assoc-coh-unit-l-r-pentagon : coh-unit-l-r-pentagon H-⊙EM₁ H-⊙EM₁-assoc
  H-EM₁-assoc-coh-unit-l-r-pentagon =
    coh-unit-l-to-unit-l-r-pentagon H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-coh-unit-l

  import homotopy.Pi2HSuspCompose H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-coh-unit-l-r-pentagon as Pi2EMSuspCompose
  open Pi2EMSuspCompose hiding (comp-functor) public

  abstract
    H-EM₁-assoc-pentagon : coh-assoc-pentagon H-⊙EM₁ H-⊙EM₁-assoc
    H-EM₁-assoc-pentagon w x y z =
      EM₁-prop-elim {P = λ w' → P w' x y z} {{λ w' → P-level w' x y z}}
        (EM₁-prop-elim {P = λ x' → P embase x' y z} {{λ x' → P-level embase x' y z}} (=ₛ-in idp) x)
        w
      where
      P : (w x y z : EM₁ G.grp) → Type i
      P = coh-assoc-pentagon-eq H-⊙EM₁ H-⊙EM₁-assoc
      P-level : ∀ w x y z → is-prop (P w x y z)
      P-level w x y z = =ₛ-level (EM₁-level₁ G.grp)

  EM₁-2-semi-category : TwoSemiCategory lzero i
  EM₁-2-semi-category = HSpace-2-semi-category H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-pentagon

  comp-functor :
    TwoSemiFunctor
      EM₁-2-semi-category
      (=ₜ-fundamental-cat (Susp (EM₁ G.grp)))
  comp-functor =
    record
    { F₀ = λ _ → [ north ]
    ; F₁ = λ x → [ η x ]
    ; pres-comp = comp
    ; pres-comp-coh = comp-coh
    }
    -- this is *exactly* the same as
    --   `Pi2EMSuspCompose.comp-functor H-EM₁-assoc-pentagon`
    -- inlined but Agda chokes on this shorter definition
