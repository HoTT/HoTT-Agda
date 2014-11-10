{-# OPTIONS --without-K #-}

open import HoTT
open import lib.cubical.elims.SuspSmash

module homotopy.SuspProduct where

module SuspProduct {i} {j} (X : Ptd i) (Y : Ptd j) where

  private

    σloop : ∀ {i} (X : Ptd i) → fst X → north (fst X) == north (fst X)
    σloop (_ , x₀) x = merid _ x ∙ ! (merid _ x₀)

    σloop-pt : ∀ {i} {X : Ptd i} → σloop X (snd X) == idp
    σloop-pt {X = (_ , x₀)} = !-inv-r (merid _ x₀)

    {- into -}

    into-glue : fst (X ×ptd Y) → winl (north _) == winr (winr (north _))
    into-glue (x , y) =
      ap winl (σloop X x) ∙ wglue
      ∙ ap (winr ∘ winl) (σloop (Ptd-Smash X Y) (cfcod _ (x , y)))
      ∙ ap winr wglue ∙ ap (winr ∘ winr) (σloop Y y)

    into-glue-x : (x : fst X) →
      into-glue (x , snd Y) == ap winl (σloop X x) ∙ wglue ∙ ap winr wglue
    into-glue-x x =
      ap (λ p → ap winl (σloop X x) ∙ wglue ∙ p
                 ∙ ap winr wglue ∙ ap (winr ∘ winr) (σloop Y (snd Y)))
         (ap (ap (winr ∘ winl) ∘ σloop (Ptd-Smash X Y)) (! (cfglue _ (winl x)))
          ∙ ap (ap (winr ∘ winl)) σloop-pt)
      ∙
      ap (λ q → ap winl (σloop X x) ∙ wglue ∙ ap winr wglue
                ∙ ap (winr ∘ winr) q)
         σloop-pt
      ∙
      ap (λ q → ap winl (σloop X x) ∙ wglue ∙ q) (∙-unit-r _)

    into-glue-y : (y : fst Y) →
      into-glue (snd X , y)
      == wglue ∙ ap winr wglue ∙ ap (winr ∘ winr) (σloop Y y)
    into-glue-y y =
      ap (λ p → ap winl (σloop X (snd X)) ∙ wglue ∙ p
                 ∙ ap winr wglue ∙ ap (winr ∘ winr) (σloop Y y))
         (ap (ap (winr ∘ winl) ∘ σloop (Ptd-Smash X Y)) (! (cfglue _ (winr y)))
          ∙ ap (ap (winr ∘ winl)) σloop-pt)
      ∙
      ap (λ q → ap winl q ∙ wglue ∙ ap winr wglue
                ∙ ap (winr ∘ winr) (σloop Y y))
         σloop-pt

    into-glue-0 : into-glue (snd X , snd Y) == wglue ∙ ap winr wglue
    into-glue-0 = into-glue-x (snd X)
                  ∙ ap (λ p → ap winl p ∙ wglue ∙ ap winr wglue) σloop-pt

    module Into = SuspensionRec (fst (X ×ptd Y))
      {C = fst (Ptd-Wedge (Ptd-Susp X)
               (Ptd-Wedge (Ptd-Susp (Ptd-Smash X Y)) (Ptd-Susp Y)))}
      (winl (north _))
      (winr (winr (north _)))
      into-glue

    into = Into.f

    {- out -}

    out-× : fst X × fst Y → north _ == north _
    out-× (x , y) = merid _ (snd X , snd Y) ∙ ! (merid _ (x , snd Y))
                    ∙ merid _ (x , y) ∙ ! (merid _ (snd X , y))

    expand₁ : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → idp == p ∙ ! q ∙ q ∙ ! p
    expand₁ idp idp = idp

    expand₂ : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : x == z)
      → idp == p ∙ ! p ∙ q ∙ ! q
    expand₂ idp idp = idp

    shift : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
      {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
      → Square p₀₋ p₋₀ p₋₁ p₁₋
      → Square p₀₋ idp p₋₁ (p₋₀ ∙ p₁₋)
    shift ids = ids

    fill : Σ (idp == idp) (λ p →
      Square (expand₁ (merid _ (snd X , snd Y)) (merid _ (snd X , snd Y))) p
             (ap (λ w → out-× (fst (∨-in-× X Y) w)) wglue)
             (expand₂ (merid _ (snd X , snd Y)) (merid _ (snd X , snd Y))))
    fill = fill-square-top _ _ _

    module OutSmash = SuspensionRec (Smash X Y)
      (north (fst (X ×ptd Y)))
      (north _)
      (CofiberRec.f _
        idp
        out-×
        (Wedge-elim
          (λ x → expand₁ (merid _ (snd X , snd Y)) (merid _ (x , snd Y)))
          (λ y → fst fill
                 ∙ expand₂ (merid _ (snd X , snd Y)) (merid _ (snd X , y)))
          (↓-cst=app-from-square $ shift (snd fill))))

    module OutWinr = WedgeRec {X = Ptd-Susp (Ptd-Smash X Y)} {Y = Ptd-Susp Y}
      {C = fst (Ptd-Susp (X ×ptd Y))}
      OutSmash.f
      (susp-fmap (λ y → (snd X , y)))
      idp

    module Out = WedgeRec {X = Ptd-Susp X}
      {Y = Ptd-Wedge (Ptd-Susp (Ptd-Smash X Y)) (Ptd-Susp Y)}
      {C = fst (Ptd-Susp (X ×ptd Y))}
      (susp-fmap (λ x → (x , snd Y)))
      OutWinr.f
      idp

    out = Out.f

    {- into-out -}

    into-out-x : ∀ σx → into (out (winl σx)) == winl σx
    into-out-x = Suspension-elim _
      idp
      (! (ap winl (! (merid _ (snd X))) ∙ wglue ∙ ap winr wglue))
      (λ x → ↓-='-from-square $
        (ap-∘ into (out ∘ winl) (merid _ x)
         ∙ ap (ap into) (SuspFmap.glue-β (λ x → (x , snd Y)) x)
         ∙ Into.glue-β (x , snd Y) ∙ into-glue-x x
         ∙ ap (λ p → p ∙ wglue ∙ ap winr wglue)
              (ap-∙ winl (merid _ x) (! (merid _ (snd X))))
         ∙ ∙-assoc (ap winl (merid _ x)) (ap winl (! (merid _ (snd X))))
                   (wglue ∙ ap winr wglue))
        ∙v⊡ (vid-square {p = ap winl (merid _ x)} ⊡h
             ur-square (ap winl (! (merid _ (snd X))) ∙ wglue ∙ ap winr wglue))
        ⊡v∙ ∙-unit-r _)

    into-out-y : ∀ σy → into (out (winr (winr σy))) == winr (winr σy)
    into-out-y = Suspension-elim _
      (wglue ∙ ap winr wglue)
      (ap (winr ∘ winr) (merid _ (snd Y)))
      (λ y → ↓-='-from-square $
        (ap-∘ into (out ∘ winr ∘ winr) (merid _ y)
         ∙ ap (ap into) (SuspFmap.glue-β (λ y → (snd X , y)) y)
         ∙ Into.glue-β (snd X , y) ∙ into-glue-y y
         ∙ ap (λ p → wglue ∙ ap winr wglue ∙ p)
              (ap-∙ (winr ∘ winr) (merid _ y) (! (merid _ (snd Y)))
               ∙ ap (λ q → ap (winr ∘ winr) (merid _ y) ∙ q)
                    (ap-! (winr ∘ winr) (merid _ (snd Y)))))
        ∙v⊡ lemma wglue (ap winr wglue) (ap (winr ∘ winr) (merid _ y))
                  (ap (winr ∘ winr) (merid _ (snd Y))))
      where
      lemma : ∀ {i} {A : Type i} {a₁ a₂ a₃ a₄ : A}
        (p : a₁ == a₂) (q : a₂ == a₃) (r : a₃ == a₄) (s : a₃ == a₄)
        → Square (p ∙ q) (p ∙ q ∙ r ∙ ! s) r s
      lemma idp idp idp s = disc-to-square (! (!-inv-l s))

    into-out-s : ∀ σs → into (out (winr (winl σs))) == winr (winl σs)
    into-out-s = susp-smash-path-elim _ _
      wglue
      (wglue ∙ ap (winr ∘ winl) (merid _ (cfbase _)))
      (λ {(x , y) →
        (ap-∘ into (out ∘ winr ∘ winl) (merid _ (cfcod _ (x , y)))
         ∙ ap (ap into) (OutSmash.glue-β (cfcod _ (x , y)))
         ∙ lemma₁ into
             (Into.glue-β (snd X , snd Y) ∙ into-glue-0)
             (Into.glue-β (x , snd Y) ∙ into-glue-x x)
             (Into.glue-β (x , y))
             (Into.glue-β (snd X , y) ∙ into-glue-y y))
        ∙v⊡ lemma₂ wglue (ap winr wglue) (ap winl (σloop X x))
                    (ap (winr ∘ winl) (σloop (Ptd-Smash X Y) (cfcod _ (x , y))))
                    (ap (winr ∘ winr) (σloop Y y))
                    (ap (winr ∘ winl) (merid _ (cfcod _ (x , y))))
                    (ap (winr ∘ winl) (merid _ (cfbase _)))
                    (ap-∙ (winr ∘ winl) (merid _ (cfcod _ (x , y)))
                                        (! (merid _ (cfbase _)))
                     ∙ ap (λ p → ap (winr ∘ winl) (merid _ (cfcod _ (x , y)))
                                 ∙ p)
                          (ap-! (winr ∘ winl) (merid _ (cfbase _))))})
      where
      {- Let's not do these by hand -}
      lemma₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₀ a₁ a₂ a₃ a₄ : A}
        {p : a₀ == a₁} {q : a₂ == a₁} {r : a₂ == a₃} {s : a₄ == a₃}
        {p' : f a₀ == f a₁} {q' : f a₂ == f a₁}
        {r' : f a₂ == f a₃} {s' : f a₄ == f a₃}
        (α : ap f p == p') (β : ap f q == q')
        (γ : ap f r == r') (δ : ap f s == s')
        → ap f (p ∙ ! q ∙ r ∙ ! s) == p' ∙ ! q' ∙ r' ∙ ! s'
      lemma₁ f {p = idp} {q = idp} {r = idp} {s = idp} idp idp idp idp = idp

      lemma₂ : ∀ {i} {A : Type i} {a₀ a₁ a₂ a₃ a₄ a₅ : A}
        (p : a₀ == a₁) (q : a₁ == a₂) (r : a₃ == a₀) (s : a₁ == a₁)
        (t : a₂ == a₄) (u : a₁ == a₅) (v : a₁ == a₅)
        → s == u ∙ ! v
        → Square p ((p ∙ q) ∙ ! (r ∙ p ∙ q) ∙ (r ∙ p ∙ s ∙ q ∙ t)
                    ∙ ! (p ∙ q ∙ t))
                 u (p ∙ v)
      lemma₂ idp idp idp ._ idp idp v idp = disc-to-square $
        ! (ap (λ w → w ∙ v) (∙-unit-r _ ∙ ∙-unit-r (! v)) ∙ !-inv-l v)

    into-out-winr : ∀ r → into (out (winr r)) == winr r
    into-out-winr = Wedge-elim
      into-out-s
      into-out-y
      (↓-='-from-square $
        (ap-∘ into (out ∘ winr) wglue
         ∙ ap (ap into) OutWinr.glue-β)
        ∙v⊡ disc-to-square idp)

    into-out : ∀ w → into (out w) == w
    into-out = Wedge-elim
      into-out-x
      into-out-winr
      (↓-∘=idf-from-square into out $
        ap (ap into) Out.glue-β ∙v⊡ connection)

    out-into-merid : (s : fst (X ×ptd Y))
      → idp == merid _ (snd X , snd Y) [ (λ σ → out (into σ) == σ) ↓ merid _ s ]
    out-into-merid (x , y) = ↓-∘=idf-from-square out into $
      (ap (ap out) (Into.glue-β (x , y))
        ∙ lemma₁ out
            (∘-ap out winl (σloop X x)
             ∙ ap-∙ (out ∘ winl) (merid _ x) (! (merid _ (snd X)))
             ∙ SuspFmap.glue-β (λ x → (x , snd Y)) x
               ∙2 (ap-! (out ∘ winl) (merid _ (snd X))
                   ∙ ap ! (SuspFmap.glue-β (λ x → (x , snd Y)) (snd X))))
            Out.glue-β
            (∘-ap out (winr ∘ winl) (σloop _ (cfcod _ (x , y)))
             ∙ ap-∙ OutSmash.f (merid _ (cfcod _ (x , y)))
                               (! (merid _ (cfbase _)))
             ∙ OutSmash.glue-β (cfcod _ (x , y))
               ∙2 (ap-! OutSmash.f (merid _ (cfbase _))
                   ∙ ap ! (OutSmash.glue-β (cfbase _))))
            (∘-ap out winr wglue ∙ OutWinr.glue-β)
            (∘-ap out (winr ∘ winr) (σloop Y y)
             ∙ ap-∙ (out ∘ winr ∘ winr) (merid _ y) (! (merid _ (snd Y)))
             ∙ SuspFmap.glue-β (λ y → (snd X , y)) y
               ∙2 (ap-! (out ∘ winr ∘ winr) (merid _ (snd Y))
                   ∙ ap ! (SuspFmap.glue-β (λ y → (snd X , y)) (snd Y)))))
      ∙v⊡ lemma₂ (merid _ (x , snd Y)) (merid _ (snd X , snd Y))
                  (merid _ (x , y)) (merid _ (snd X , y))
                  (merid _ (snd X , snd Y))
      where
      lemma₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₀ a₁ a₂ a₃ a₄ a₅ : A}
        {p : a₀ == a₁} {q : a₁ == a₂} {r : a₂ == a₃}
        {s : a₃ == a₄} {t : a₄ == a₅}
        {p' : f a₀ == f a₁} {q' : f a₁ == f a₂} {r' : f a₂ == f a₃}
        {s' : f a₃ == f a₄} {t' : f a₄ == f a₅}
        (α : ap f p == p') (β : ap f q == q') (γ : ap f r == r')
        (δ : ap f s == s') (ε : ap f t == t')
        → ap f (p ∙ q ∙ r ∙ s ∙ t) == p' ∙ q' ∙ r' ∙ s' ∙ t'
      lemma₁ f {p = idp} {q = idp} {r = idp} {s = idp} {t = idp}
        idp idp idp idp idp = idp

      lemma₂ : ∀ {i} {A : Type i} {a₀ a₁ a₂ a₃ a₄ a₅ : A}
        (p : a₀ == a₁) (q : a₂ == a₁) (r : a₀ == a₃)
        (s : a₄ == a₃) (t : a₅ == a₃)
        → Square idp ((p ∙ ! q) ∙ ((q ∙ ! p ∙ r ∙ ! s) ∙ idp) ∙ (s ∙ ! t)) r t
      lemma₂ idp idp idp idp idp = ids

    out-into : ∀ σ → out (into σ) == σ
    out-into = Suspension-elim _
      idp
      (merid _ (snd X , snd Y))
      out-into-merid


  abstract
    eq : fst (Ptd-Susp (X ×ptd Y))
         ≃ fst (Ptd-Wedge (Ptd-Susp X)
                  (Ptd-Wedge (Ptd-Susp (Ptd-Smash X Y)) (Ptd-Susp Y)))
    eq = equiv into out into-out out-into

    ptd-path : Ptd-Susp (X ×ptd Y)
               == (Ptd-Wedge (Ptd-Susp X)
                     (Ptd-Wedge (Ptd-Susp (Ptd-Smash X Y)) (Ptd-Susp Y)))
    ptd-path = ptd-ua eq idp
