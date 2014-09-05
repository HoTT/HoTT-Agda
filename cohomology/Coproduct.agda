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
   Cₙ(X ⊔ Y) == C₀(S⁰) × Cₙ(X) × Cₙ(Y),  if n = 0
             == Cₙ(X) × Cₙ(Y),           if n ≠ 0
 - There are two different proofs here, one which works for n ≠ -1 and one
 - which works for n ≠ 0,1. -}

open OrdinaryTheory OT
open import cohomology.Functor OT
open import cohomology.LongExactSequence OT
open import cohomology.Sn OT

{- The case n ≠ -1 -}
module C⊔Part1 (n : ℤ) (X Y : Ptd i) (neq : n ≠ neg O) where

  {- The proof is (approximately) by exhibiting a splitting exact sequence

         0 → Cₙ(S⁰) → Cₙ(X ⊔ Y) → Cₙ(X ∨ Y) → 0

   - We apply the Mayer-Vietoris theorem to a span [ΣX ← S⁰ → ΣY]
     ([Σ⊔-ps], which defined is defined so that [Pushout Σ⊔-ps == Σ(X ⊔ Y)])
     to obtain the sequence

         Cₙ₊₂(ΣΣS⁰) → Cₙ₊₂(Σ(Pushout Σ⊔-ps)) → Cₙ₊₂(Σ(ΣX ∨ ΣY)) → Cₙ₊₂(ΣS⁰)

   - We prove that the map from [Cₙ₊₂(ΣΣS⁰)] to [Cₙ₊₂(Σ(Pushout Σ⊔-ps))] has a
     left inverse. Since [Cₙ₊₂(ΣS⁰) == 0] for n ≠ -1, the exact sequence splits.
     We have [Cₙ₊₂(ΣΣS⁰) == Cₙ(S⁰)], [Cₙ₊₂(Σ(ΣX ∨ ΣY)) == Cₙ(X) × Cₙ(Y)],
     and [Pushout Σ⊔-ps == Σ(X ⊔ Y)], so
     [Cₙ(X ⊔ Y) == Cₙ₊₂(Σ(Pushout Σ⊔-ps)) == Cₙ(S⁰) × Cₙ(X) × Cₙ(Y)].
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

    module MV = MayerVietoris Σ⊔-ps

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
              ap (ap f) (G.glue-β (inl x))
              ∙ ap-∙' f (ap left (merid _ x)) (glue (lift false))
              ∙ ap (λ w → ap f (ap left (merid _ x)) ∙' w)
                   (F.glue-β (lift false))
              ∙ ∘-ap f left (merid _ x)
              ∙ SuspFmap.glue-β inl x;
            (inr y) → ↓-∘=idf-in f g $
              ap (ap f) (G.glue-β (inr y))
              ∙ ap-∙ f (glue (lift true)) (ap right (merid _ y))
              ∙ ap (λ w → w ∙ ap f (ap right (merid _ y)))
                   (F.glue-β (lift true))
              ∙ ∘-ap f right (merid _ y)
              ∙ SuspFmap.glue-β inr y})

      g-f : ∀ ξ → g (f ξ) == ξ
      g-f = Pushout-elim g-f-left g-f-right g-f-glue
        where
        g-f-left : ∀ σx → g (f (left σx)) == left σx
        g-f-left = Suspension-elim (fst X) idp (! (glue (lift false)))
          (λ x → ↓-='-from-square $
            (ap-∘ g (susp-fmap inl) (merid _ x)
              ∙ ap (ap g) (SuspFmap.glue-β inl x) ∙ G.glue-β (inl x))
            ∙v⊡ vid-square {p = ap left (merid _ x)}
                ⊡h' ur-square (glue (lift false)))

        g-f-right : ∀ σy → g (f (right σy)) == right σy
        g-f-right = Suspension-elim (fst Y) (glue (lift true)) idp
          (λ y → ↓-='-from-square $
            (ap-∘ g (susp-fmap inr) (merid _ y)
              ∙ ap (ap g) (SuspFmap.glue-β inr y) ∙ G.glue-β (inr y))
            ∙v⊡ lt-square (glue (lift true))
                ⊡h vid-square {p = ap right (merid _ y)})

        g-f-glue : ∀ b → g-f-left (poles X b) == g-f-right (poles Y b)
                         [ (λ ξ → g (f ξ) == ξ) ↓ glue b ]
        g-f-glue (lift true) = ↓-∘=idf-in g f $
          ap (λ w → ap g w ∙' glue (lift true)) (F.glue-β (lift true))
          ∙ ∙'-unit-l (glue (lift true))
        g-f-glue (lift false) = ↓-∘=idf-in g f $
          ap (ap g) (F.glue-β (lift false)) ∙ ! (!-inv-l (glue (lift false)))

    Σ⊔-ptd-path : Σ⊔ == Ptd-Susp (X ∙⊔ Y)
    Σ⊔-ptd-path = ptd-ua Σ⊔-eq idp


    {- Defining a right inverse to [ext-glue], which gives
     - a left inverse to [Cₙ(Σ(ext-glue))] -}

    module InsertGlue = SuspensionRec (Sphere {i} 0) {C = fst Σ⊔}
      (left (north _))
      (right (south _))
      (λ {(lift true) → glue (lift true) ∙ ap right (merid _ (snd Y));
          (lift false) → ap left (merid _ (snd X)) ∙ glue (lift false)})

    ins-glue = InsertGlue.f

    ptd-ins-glue : fst (Ptd-Sphere {i} 1 ∙→ Σ⊔)
    ptd-ins-glue = (ins-glue , idp)

    ext-Σ⊔-glue : fst Σ⊔ → Sphere {i} 1
    ext-Σ⊔-glue = ext-glue

    ptd-ext-Σ⊔-glue : fst (Σ⊔ ∙→ Ptd-Sphere {i} 1)
    ptd-ext-Σ⊔-glue = ptd-ext-glue

    ins-glue-rinv : (s : Sphere {i} 1) →
      ext-Σ⊔-glue (ins-glue s) == s
    ins-glue-rinv = Suspension-elim (Sphere {i} 0)
      idp
      idp
      (λ {(lift true) → ↓-∘=idf-in ext-Σ⊔-glue ins-glue $
            ap (ap ext-Σ⊔-glue) (InsertGlue.glue-β (lift true))
            ∙ ap-∙ ext-Σ⊔-glue (glue (lift true)) (ap right (merid _ (snd Y)))
            ∙ ap (λ w → w ∙ ap ext-Σ⊔-glue (ap right (merid _ (snd Y))))
                 (ExtGlue.glue-β (lift true))
            ∙ ap (λ w → merid _ (lift true) ∙ w)
                 (∘-ap ext-Σ⊔-glue right (merid _ (snd Y))
                  ∙ ap-cst (south _) (merid _ (snd Y)))
            ∙ ∙-unit-r _;

          (lift false) → ↓-∘=idf-in ext-Σ⊔-glue ins-glue $
            ap (ap ext-Σ⊔-glue) (InsertGlue.glue-β (lift false))
            ∙ ap-∙ ext-Σ⊔-glue (ap left (merid _ (snd X))) (glue (lift false))
            ∙ ap (λ w → w ∙ ap ext-Σ⊔-glue (glue (lift false)))
                 (∘-ap ext-Σ⊔-glue left (merid _ (snd X))
                  ∙ ap-cst (north _) (merid _ (snd X)))
            ∙ ExtGlue.glue-β (lift false)})

    ptd-ins-glue-rinv :
      ptd-ext-glue ∘ptd ptd-ins-glue == ptd-idf (Ptd-Sphere 1)
    ptd-ins-glue-rinv = ptd-λ= ins-glue-rinv idp

    ptd-susp-ins-glue-rinv :
      ptd-susp-fmap ptd-ext-Σ⊔-glue ∘ptd ptd-susp-fmap ptd-ins-glue
      == ptd-idf (Ptd-Sphere 2)
    ptd-susp-ins-glue-rinv =
      ! (ptd-susp-fmap-∘ ptd-ext-glue ptd-ins-glue)
      ∙ ap ptd-susp-fmap ptd-ins-glue-rinv
      ∙ ptd-susp-fmap-idf (Ptd-Sphere 1)

    {- Will prove this sequence splits -}
    ed : ExactDiag _ _
    ed =
      C (succ (succ n)) (Ptd-Sphere 2)
        ⟨ CF-hom (succ (succ n)) (ptd-susp-fmap ptd-ext-Σ⊔-glue) ⟩→
      C (succ (succ n)) (Ptd-Susp Σ⊔)
        ⟨ CF-hom (succ (succ n)) (ptd-susp-fmap MV.ptd-reglue) ⟩→
      C (succ (succ n)) (Ptd-Susp (Ptd-Wedge (Ptd-Susp X) (Ptd-Susp Y)))
        ⟨ cst-hom ⟩→
      0G ⊣|

    es : ExactSeq ed
    es = exact-build ed first₂ second₂
      where
      first₁ = transport
        (λ {(_ , _ , g , h) →
          is-exact (CF (succ (succ n)) h) (CF (succ (succ n)) g)})
        (cofiber-sequence MV.ptd-reglue)
        (C-exact (succ (succ n)) (ptd-cfcod³ MV.ptd-reglue))

      first₂ = transport
        (λ {(_ , g) →
          is-exact (CF (succ (succ n)) (ptd-susp-fmap g))
                   (CF (succ (succ n)) (ptd-susp-fmap MV.ptd-reglue))})
        (pair= MV.ptd-path MV.cfcod-over)
        first₁

      second₁ = transport
        (λ {(_ , f , g , _) →
          is-exact (CF (succ (succ n)) g) (CF (succ (succ n)) f)})
        (cofiber-sequence MV.ptd-reglue)
        (C-exact (succ (succ n)) (ptd-cfcod² MV.ptd-reglue))

      second₂ : is-exact
        (CF (succ (succ n)) (ptd-susp-fmap MV.ptd-reglue))
        (GroupHom.ptd-f cst-hom)
      second₂ = transport
        (λ {(Z , g) → is-exact {Z = Z}
                        (CF (succ (succ n)) (ptd-susp-fmap MV.ptd-reglue)) g})
        (pair= (ap Group.Ptd-El
                   (ap (C (succ (succ n))) MV.ptd-path
                    ∙ C-Sphere-≠ (succ (succ n)) 1
                       (neq ∘ succ-injective _ _ ∘ succ-injective _ _)))
               (prop-has-all-paths-↓
                 (raise-level _ (LiftUnit-ptd-in-level {X = _ , Cid _ _}))))
        second₁


  C-⊔ : C n (X ∙⊔ Y) == C n (Ptd-Sphere 0) ×G (C n X ×G C n Y)
  C-⊔ = ! (C-Susp (succ n) Σ⊔ ∙ ap (C (succ n)) Σ⊔-ptd-path ∙ C-Susp n (X ∙⊔ Y))
      ∙ SEL.iso
      ∙ ap2 _×G_ (C-Susp (succ n) (Ptd-Sphere 1) ∙ C-Susp n (Ptd-Sphere 0))
                 (C-Susp (succ n) (Ptd-Wedge (Ptd-Susp X) (Ptd-Susp Y))
                  ∙ C-binary-additive (succ n) (Ptd-Susp X) (Ptd-Susp Y)
                  ∙ ap2 _×G_ (C-Susp n X) (C-Susp n Y))
    where
    module SEL = SplitExactLeft
      (C-abelian (succ (succ n)) (Ptd-Susp Σ⊔))
      (CF-hom (succ (succ n)) (ptd-susp-fmap ptd-ext-Σ⊔-glue))
      (CF-hom (succ (succ n)) (ptd-susp-fmap MV.ptd-reglue))
      es
      (CF-hom (succ (succ n)) (ptd-susp-fmap ptd-ins-glue))
      (app= (ap GroupHom.f (CF-inverse (succ (succ n)) _ _
                              ptd-susp-ins-glue-rinv)))


{- The case n ≠ 0,1 -}
module C⊔Part2 (n : ℤ) (X Y : Ptd i) (neq₀ : n ≠ O) (neq₁ : n ≠ pos O) where

  {- We define a function [select : S⁰ → X ⊔ Y] such that
   - [Cofiber select == X ∨ Y]. Then we have the exact sequence

        Cₙ(S¹) → Cₙ(X ∨ Y) → Cₙ(X ⊔ Y) → Cₙ(S⁰)

   - which, for n ≠ 0,1, shows that [Cₙ(X ⊔ Y) == Cₙ(X ∨ Y)].

   - Note: select has a left inverse, so this proof could be extended
     to prove the case n = 0 via the splitting lemma. -}

  private

    select : Sphere {i} 0 → fst (X ∙⊔ Y)
    select (lift true) = inl (snd X)
    select (lift false) = inr (snd Y)

    ptd-select : fst (Ptd-Sphere {i} 0 ∙→ X ∙⊔ Y)
    ptd-select = (select , idp)

    eq : Cofiber select ≃ Wedge X Y
    eq = equiv into out into-out out-into
      where
      module Into = CofiberRec select {C = Wedge X Y}
        (winl (snd X))
        (λ {(inl x) → winl x; (inr y) → winr y})
        (λ {(lift true) → idp; (lift false) → wglue})

      module Out = WedgeRec {X = X} {Y = Y} {C = Cofiber select}
        (λ x → cfcod _ (inl x))
        (λ y → cfcod _ (inr y))
        (! (cfglue _ (lift true)) ∙ cfglue _ (lift false))

      into = Into.f
      out = Out.f

      into-out : ∀ w → into (out w) == w
      into-out = Wedge-elim
        (λ x → idp)
        (λ y → idp)
        (↓-∘=idf-in into out $
          ap into (ap out wglue)
            =⟨ ap (ap into) Out.glue-β ⟩
          ap into (! (cfglue _ (lift true)) ∙ cfglue _ (lift false))
            =⟨ ap-∙ into (! (cfglue _ (lift true))) (cfglue _ (lift false)) ⟩
          ap into (! (cfglue _ (lift true))) ∙ ap into (cfglue _ (lift false))
            =⟨ ap-! into (cfglue _ (lift true)) ∙ ap ! (Into.glue-β (lift true))
               |in-ctx (λ w → w ∙ ap into (cfglue _ (lift false))) ⟩
          ap into (cfglue _ (lift false))
            =⟨ Into.glue-β (lift false) ⟩
          wglue ∎)

      out-into : ∀ κ → out (into κ) == κ
      out-into = Cofiber-elim _
        (! (cfglue _ (lift true)))
        (λ {(inl x) → idp; (inr y) → idp})
        (λ {(lift true) → ↓-∘=idf-from-square out into $
              ap (ap out) (Into.glue-β (lift true)) ∙v⊡ bl-square _;
            (lift false) → ↓-∘=idf-from-square out into $
              (ap (ap out) (Into.glue-β (lift false)) ∙ Out.glue-β)
              ∙v⊡ lt-square (! (cfglue _ (lift true))) ⊡h vid-square})

    ptd-path : Ptd-Cof ptd-select == Ptd-Wedge X Y
    ptd-path = ptd-ua eq idp

    ed : ExactDiag _ _
    ed =
      C n (Ptd-Sphere 1)
        ⟨ CF-hom n ptd-ext-glue ⟩→
      C n (Ptd-Cof ptd-select)
        ⟨ CF-hom n (ptd-cfcod ptd-select) ⟩→
      C n (X ∙⊔ Y)
        ⟨ CF-hom n ptd-select ⟩→
      C n (Ptd-Sphere 0) ⊣|

    es : ExactSeq ed
    es = exact-build ed
      (transport
        (λ {(_ , g , _ , _) →
          is-exact (CF n g) (CF n (ptd-cfcod ptd-select))})
        (cofiber-sequence ptd-select)
        (C-exact n (ptd-cfcod ptd-select)))
      (C-exact n ptd-select)

  C-⊔ : C n (X ∙⊔ Y) == C n X ×G C n Y
  C-⊔ = ! eppi ∙ ap (C n) ptd-path ∙ C-binary-additive n X Y
    where
    eppi = exact-pair-path-iso
      (C-Sphere-≠ n 1 neq₁) (C-Sphere-≠ n 0 neq₀) es

C-⊔-Group : (n : ℤ) (X Y : Ptd i) → Group i
C-⊔-Group O X Y = C O (Ptd-Sphere 0) ×G (C O X ×G C O Y)
C-⊔-Group n X Y = C n X ×G C n Y

C-⊔ : (n : ℤ) (X Y : Ptd i) → C n (X ∙⊔ Y) == C-⊔-Group n X Y
C-⊔ O X Y = C⊔Part1.C-⊔ O X Y (ℤ-O≠neg O)
C-⊔ (pos O) X Y = C⊔Part1.C-⊔ (pos O) X Y (ℤ-pos≠neg O O)
                  ∙ ap (λ H → H ×G (C (pos O) X ×G C (pos O) Y))
                       (C-dimension (pos O) (ℤ-pos≠O O))
                  ∙ ×G-unit-l
C-⊔ (pos (S m)) X Y = C⊔Part2.C-⊔ (pos (S m)) X Y
                        (ℤ-pos≠O (S m)) (ℤ-pos≠O m ∘ succ-injective _ _)
C-⊔ (neg m) X Y = C⊔Part2.C-⊔ (neg m) X Y (ℤ-neg≠O m) (ℤ-neg≠pos m O)

C-⊔-≠O : (n : ℤ) (X Y : Ptd i) → n ≠ O → C n (X ∙⊔ Y) == C n X ×G C n Y
C-⊔-≠O O X Y neq = ⊥-rec (neq idp)
C-⊔-≠O (pos m) X Y _ = C-⊔ (pos m) X Y
C-⊔-≠O (neg m) X Y _ = C-⊔ (neg m) X Y
