{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.Exactness
open import cohomology.ExactPairIso
open import cohomology.FunctionOver
open import cohomology.MayerVietoris
open import cohomology.SplitExactLeft
open import cohomology.OrdinaryTheory

module cohomology.Coproduct {i} (OT : OrdinaryTheory i) where

{- Calculating Cₙ(X ⊔ Y) in terms of Cₙ(X) and Cₙ(Y). We have
 - Cₙ(X ⊔ Y) == C₀(S⁰) × Cₙ(X) × Cₙ(Y),  if n = 0
 -           == Cₙ(X) × Cₙ(Y),           if n > 0 -}

open OrdinaryTheory OT
open import cohomology.Functor OT
open import cohomology.LongExactSequence OT
open import cohomology.Sn OT

module _ (n : ℕ) (X Y : Ptd i) where

  {- The proof is (approximately) by exhibiting a splitting exact sequence

         0 → Cₙ(S⁰) → Cₙ(X ⊔ Y) → Cₙ(X ∨ Y) → 0

   - We apply the Mayer-Vietoris theorem to a span [ΣX ← S⁰ → ΣY]
     ([Σ⊔-ps], defined below) to obtain the sequence

         Cₙ₊₂(ΣΣS⁰) → Cₙ₊₂(Σ(Pushout Σ⊔-ps)) → Cₙ₊₂(Σ(ΣX ∨ ΣY)) → Cₙ₊₂(ΣS⁰)

   - We prove that the map from [Cₙ₊₂(ΣΣS⁰)] to [Cₙ₊₂(Σ(Pushout Σ⊔-ps))] has a
     left inverse. Since [Cₙ₊₂(ΣS⁰) == 0], the exact sequence splits. We have
     [Cₙ₊₂(ΣΣS⁰) == Cₙ(S⁰)] and [Cₙ₊₂(Σ(ΣX ∨ ΣY)) == Cₙ(X) × Cₙ(Y)], and [Σ⊔-ps]
     is defined such that [Pushout Σ⊔-ps == Σ(X ⊔ Y)], which implies that
     [Cₙ₊₂(Σ(Pushout Σ⊔-ps)) == Cₙ(X ⊔ Y)].
   -}

  private

    {- Defining the pushout of a span ΣX ← S⁰ → ΣY such that the pushout
     - is equal to Σ(X ⊔ Y) -}

    poles : (Z : Ptd i) → Sphere {i} 0 → fst (Ptd-Susp Z)
    poles _ (lift true) = north _
    poles _ (lift false) = south _

    ptd-poles : (Z : Ptd i) → fst (Ptd-Sphere {i} 0 ∙→ Ptd-Susp Z)
    ptd-poles Z = (poles Z , idp)

    Σ⊔-ps = ptd-span _ _ _ (ptd-poles X) (ptd-poles Y)
    Σ⊔-s = ptd-span-out Σ⊔-ps
    Σ⊔ = Ptd-Pushout Σ⊔-ps

    Σ⊔-eq : fst Σ⊔ ≃ fst (Ptd-Susp (X ∙⊔ Y))
    Σ⊔-eq = equiv f g f-g g-f
      where
      module F = PushoutRec {d = Σ⊔-s} {D = fst (Ptd-Susp (X ∙⊔ Y))}
        (susp-fmap inl) (susp-fmap inr)
        (λ {(lift true) → idp; (lift false) → idp})

      module G = SuspensionRec (fst (X ∙⊔ Y)) {C = fst Σ⊔}
        (left (north _)) (right (south _))
        (λ {(inl x) → ap left (merid (fst X) x) ∙' glue (lift false);
            (inr y) → glue (lift true) ∙ ap right (merid (fst Y) y)})

      f = F.f
      g = G.f

      f-g : ∀ σ → f (g σ) == σ
      f-g = Suspension-elim (fst (X ∙⊔ Y)) idp idp
        (λ {(inl x) → ↓-∘=idf-in f g $
              ap f (ap g (merid _ (inl x)))
                =⟨ G.glue-β (inl x) |in-ctx ap f ⟩
              ap f (ap left (merid _ x) ∙' glue (lift false))
                =⟨ ap-∙' f (ap left (merid _ x)) (glue (lift false)) ⟩
              ap f (ap left (merid _ x)) ∙' ap f (glue (lift false))
                =⟨ F.glue-β (lift false)
                   |in-ctx (λ w → ap f (ap left (merid _ x)) ∙' w) ⟩
              ap f (ap left (merid _ x))
                =⟨ ∘-ap f left (merid _ x) ⟩
              ap (susp-fmap inl) (merid _ x)
                =⟨ SuspFmap.glue-β inl x ⟩
              merid _ (inl x) ∎;
            (inr y) → ↓-∘=idf-in f g $
              ap f (ap g (glue (inr y)))
                =⟨ G.glue-β (inr y) |in-ctx ap f ⟩
              ap f (glue (lift true) ∙ ap right (merid _ y))
                =⟨ ap-∙ f (glue (lift true)) (ap right (merid _ y)) ⟩
              ap f (glue (lift true)) ∙ ap f (ap right (merid _ y))
                =⟨ F.glue-β (lift true)
                   |in-ctx (λ w → w ∙ ap f (ap right (merid _ y))) ⟩
              ap f (ap right (merid _ y))
                =⟨ ∘-ap f right (merid _ y) ⟩
              ap (susp-fmap inr) (merid _ y)
                =⟨ SuspFmap.glue-β inr y ⟩
              merid _ (inr y) ∎})

      g-f : ∀ ξ → g (f ξ) == ξ
      g-f = Pushout-elim g-f-left g-f-right g-f-glue
        where
        g-f-left : ∀ σx → g (f (left σx)) == left σx
        g-f-left = Suspension-elim (fst X) idp (! (glue (lift false)))
          (λ x → ↓-='-in $
            ap left (merid _ x)
              =⟨ ! (!-inv'-r (glue (lift false)))
                 |in-ctx (λ w → ap left (merid _ x) ∙' w) ⟩
            ap left (merid _ x) ∙' glue (lift false) ∙' ! (glue (lift false))
              =⟨ ! (∙'-assoc (ap left (merid _ x)) (glue (lift false))
                             (! (glue (lift false)))) ⟩
            (ap left (merid _ x) ∙' glue (lift false)) ∙' ! (glue (lift false))
              =⟨ ! (G.glue-β (inl x))
                 |in-ctx (λ w → w ∙' ! (glue (lift false))) ⟩
            ap g (merid _ (inl x)) ∙' ! (glue (lift false))
              =⟨ ! (SuspFmap.glue-β inl x)
                 |in-ctx (λ w → ap g w ∙' ! (glue (lift false))) ⟩
            ap g (ap (susp-fmap inl) (merid _ x)) ∙' ! (glue (lift false))
              =⟨ ∘-ap g (susp-fmap inl) (merid _ x)
                 |in-ctx (λ w → w ∙' ! (glue (lift false))) ⟩
            ap (g ∘ susp-fmap inl) (merid _ x) ∙' ! (glue (lift false)) ∎)

        g-f-right : ∀ σy → g (f (right σy)) == right σy
        g-f-right = Suspension-elim (fst Y) (glue (lift true)) idp
          (λ y → ↓-='-in $
            glue (lift true) ∙ ap right (merid _ y)
              =⟨ ! (G.glue-β (inr y)) ⟩
            ap g (merid _ (inr y))
              =⟨ ! (SuspFmap.glue-β inr y) |in-ctx ap g ⟩
            ap g (ap (susp-fmap inr) (merid _ y))
              =⟨ ∘-ap g (susp-fmap inr) (merid _ y)  ⟩
            ap (g ∘ susp-fmap inr) (merid _ y) ∎)

        g-f-glue : ∀ b → g-f-left (poles X b) == g-f-right (poles Y b)
                         [ (λ ξ → g (f ξ) == ξ) ↓ glue b ]
        g-f-glue (lift true) = ↓-∘=idf-in g f $
          ap g (ap f (glue (lift true))) ∙' glue (lift true)
            =⟨ F.glue-β (lift true)
               |in-ctx (λ w → ap g w ∙' glue (lift true)) ⟩
          idp ∙' glue (lift true)
            =⟨ ∙'-unit-l (glue (lift true)) ⟩
          glue (lift true) ∎
        g-f-glue (lift false) = ↓-∘=idf-in g f $
          ap g (ap f (glue (lift false)))
            =⟨ F.glue-β (lift false) |in-ctx ap g ⟩
          idp
            =⟨ ! (!-inv-l (glue (lift false))) ⟩
          ! (glue (lift false)) ∙ glue (lift false) ∎

    Σ⊔-ptd-path : Σ⊔ == Ptd-Susp (X ∙⊔ Y)
    Σ⊔-ptd-path = ptd-ua Σ⊔-eq idp


    {- Defining a right inverse to [extract-glue Σ⊔-ps], which gives
     - a left inverse to [Cₙ(Σ(extract-glue Σ⊔-ps))] -}

    module InsertGlue = SuspensionRec (Sphere {i} 0) {C = fst Σ⊔}
      (left (north _))
      (right (south _))
      (λ {(lift true) → glue (lift true) ∙ ap right (merid _ (snd Y));
          (lift false) → ap left (merid _ (snd X)) ∙ glue (lift false)})

    ins-glue = InsertGlue.f

    ptd-ins-glue : fst (Ptd-Sphere {i} 1 ∙→ Σ⊔)
    ptd-ins-glue = (ins-glue , idp)

    ins-glue-rinv : (s : Sphere {i} 1) →
      extract-glue Σ⊔-ps (ins-glue s) == s
    ins-glue-rinv = Suspension-elim (Sphere {i} 0)
      idp
      idp
      (λ {(lift true) → ↓-∘=idf-in (extract-glue Σ⊔-ps) ins-glue $
            ap (extract-glue Σ⊔-ps) (ap ins-glue (merid _ (lift true)))
              =⟨ ap (ap (extract-glue Σ⊔-ps)) (InsertGlue.glue-β (lift true)) ⟩
            ap (extract-glue Σ⊔-ps) (glue (lift true)
                                     ∙ ap right (merid _ (snd Y)))
              =⟨ ap-∙ (extract-glue Σ⊔-ps)
                   (glue (lift true)) (ap right (merid _ (snd Y))) ⟩
            ap (extract-glue Σ⊔-ps) (glue (lift true))
            ∙ ap (extract-glue Σ⊔-ps) (ap right (merid _ (snd Y)))
              =⟨ ExtractGlue.glue-β Σ⊔-ps (lift true) |in-ctx (λ w →
                   w ∙ ap (extract-glue Σ⊔-ps) (ap right (merid _ (snd Y)))) ⟩
            merid _ (lift true)
            ∙ ap (extract-glue Σ⊔-ps) (ap right (merid _ (snd Y)))
              =⟨ ∘-ap (extract-glue Σ⊔-ps) right (merid _ (snd Y))
                 ∙ ap-cst (south _) (merid _ (snd Y))
                 |in-ctx (λ w → merid _ (lift true) ∙ w) ⟩
            merid _ (lift true) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            merid _ (lift true) ∎;

          (lift false) → ↓-∘=idf-in (extract-glue Σ⊔-ps) ins-glue $
            ap (extract-glue Σ⊔-ps) (ap ins-glue (merid _ (lift false)))
              =⟨ ap (ap (extract-glue Σ⊔-ps)) (InsertGlue.glue-β (lift false)) ⟩
            ap (extract-glue Σ⊔-ps) (ap left (merid _ (snd X))
                                     ∙ glue (lift false))
              =⟨ ap-∙ (extract-glue Σ⊔-ps)
                   (ap left (merid _ (snd X))) (glue (lift false)) ⟩
            ap (extract-glue Σ⊔-ps) (ap left (merid _ (snd X)))
            ∙ ap (extract-glue Σ⊔-ps) (glue (lift false))
              =⟨ ∘-ap (extract-glue Σ⊔-ps) left (merid _ (snd X))
                 ∙ ap-cst (north _) (merid _ (snd X))
                 |in-ctx (λ w → w ∙ ap (extract-glue Σ⊔-ps)
                                       (glue (lift false))) ⟩
            ap (extract-glue Σ⊔-ps) (glue (lift false))
              =⟨ ExtractGlue.glue-β Σ⊔-ps (lift false) ⟩
            merid _ (lift false) ∎})

    ptd-ins-glue-rinv : ptd-extract-glue Σ⊔-ps ∘ptd ptd-ins-glue
                        == ptd-idf (Ptd-Sphere 1)
    ptd-ins-glue-rinv = ptd-λ= ins-glue-rinv idp

    ptd-susp-ins-glue-rinv :
      ptd-susp-fmap (ptd-extract-glue Σ⊔-ps) ∘ptd ptd-susp-fmap ptd-ins-glue
      == ptd-idf (Ptd-Sphere 2)
    ptd-susp-ins-glue-rinv =
      ! (ptd-susp-fmap-∘ (ptd-extract-glue Σ⊔-ps) ptd-ins-glue)
      ∙ ap ptd-susp-fmap ptd-ins-glue-rinv
      ∙ ptd-susp-fmap-idf (Ptd-Sphere 1)

    {- Will prove this sequence splits -}
    ed : ExactDiag _ _
    ed =
      C (S (S n)) (Ptd-Sphere 2)
        ⟨ CF-hom (S (S n)) (ptd-susp-fmap (ptd-extract-glue Σ⊔-ps)) ⟩→
      C (S (S n)) (Ptd-Susp Σ⊔)
        ⟨ CF-hom (S (S n)) (ptd-susp-fmap (ptd-reglue Σ⊔-ps)) ⟩→
      C (S (S n)) (Ptd-Susp (Ptd-Wedge (Ptd-Susp X) (Ptd-Susp Y)))
        ⟨ cst-hom ⟩→
      0G ⊣|

    es : ExactSeq ed
    es = exact-build ed first₂ second₂
      where
      first₁ = transport
        (λ {(_ , _ , g , h) → is-exact (CF (S (S n)) h) (CF (S (S n)) g)})
        (cofiber-sequence (ptd-reglue Σ⊔-ps))
        (C-exact (S (S n)) (ptd-cfcod³ (ptd-reglue Σ⊔-ps)))

      first₂ = transport
        (λ {(_ , g) →
          is-exact (CF (S (S n)) (ptd-susp-fmap g))
                   (CF (S (S n)) (ptd-susp-fmap (ptd-reglue Σ⊔-ps)))})
        (pair= (mayer-vietoris-ptd-path Σ⊔-ps)
               (mayer-vietoris-cfcod-over Σ⊔-ps))
        first₁

      second₁ = transport
        (λ {(_ , f , g , _) → is-exact (CF (S (S n)) g) (CF (S (S n)) f)})
        (cofiber-sequence (ptd-reglue Σ⊔-ps))
        (C-exact (S (S n)) (ptd-cfcod² (ptd-reglue Σ⊔-ps)))

      second₂ : is-exact
        (CF (S (S n)) (ptd-susp-fmap (ptd-reglue Σ⊔-ps)))
        (ptd-cst {X = Ptd-CEl (S (S n))
                        (Ptd-Susp (Ptd-Wedge (Ptd-Susp X) (Ptd-Susp Y)))})
      second₂ = transport
        (λ {(Z , g) → is-exact {Z = Z}
                        (CF (S (S n)) (ptd-susp-fmap (ptd-reglue Σ⊔-ps))) g})
        (pair= (ap Group.Ptd-El
                   (ap (C (S (S n))) (mayer-vietoris-ptd-path Σ⊔-ps)
                    ∙ C-Sphere-above (S (S n)) 1 (<-ap-S (O< n))))
               (prop-has-all-paths-↓
                 (raise-level _ (LiftUnit-ptd-in-level {X = _ , Cid _ _}))))
        second₁


  C-⊔ : C n (X ∙⊔ Y) == C n (Ptd-Sphere 0) ×G (C n X ×G C n Y)
  C-⊔ = ! (C-SuspS (S n) Σ⊔ ∙ ap (C (S n)) Σ⊔-ptd-path ∙ C-SuspS n (X ∙⊔ Y))
      ∙ SEL.iso
      ∙ ap2 _×G_ (C-SuspS (S n) (Ptd-Sphere 1) ∙ C-SuspS n (Ptd-Sphere 0))
                 (C-SuspS (S n) (Ptd-Wedge (Ptd-Susp X) (Ptd-Susp Y))
                  ∙ C-binary-additive (S n) (Ptd-Susp X) (Ptd-Susp Y)
                  ∙ ap2 _×G_ (C-SuspS n X) (C-SuspS n Y))
    where
    module SEL = SplitExactLeft
      (C-abelian (S (S n)) (Ptd-Susp Σ⊔))
      (CF-hom (S (S n)) (ptd-susp-fmap (ptd-extract-glue Σ⊔-ps)))
      (CF-hom (S (S n)) (ptd-susp-fmap (ptd-reglue Σ⊔-ps)))
      es
      (CF-hom (S (S n)) (ptd-susp-fmap ptd-ins-glue))
      (app= (ap GroupHom.f (CF-inverse (S (S n)) _ _ ptd-susp-ins-glue-rinv)))


C-⊔-S : (n : ℕ) (X Y : Ptd i) → 0 < n → C n (X ∙⊔ Y) == C n X ×G C n Y
C-⊔-S n X Y lt = C-⊔ n X Y
               ∙ ap (λ H → H ×G (C n X ×G C n Y)) (C-Sphere-above n 0 lt)
               ∙ ×G-unit-l
