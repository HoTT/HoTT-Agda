{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdAdjoint

module homotopy.SuspAdjointLoop {i} where

private
  SuspFunctor : PtdFunctor i i
  SuspFunctor = record {
    obj = ⊙Susp;
    arr = ⊙Susp-fmap;
    id = ⊙Susp-fmap-idf;
    comp = ⊙Susp-fmap-∘}

  LoopFunctor : PtdFunctor i i
  LoopFunctor = record {
    obj = ⊙Ω;
    arr = ⊙Ω-fmap;
    id = λ _ → ⊙Ω-fmap-idf;
    comp = ⊙Ω-fmap-∘}

  module _ (X : Ptd i) where

    η : de⊙ X → Ω (⊙Susp X)
    η x = merid x ∙ ! (merid (pt X))

    module E = SuspRec (pt X) (pt X) (idf _)

    ε : de⊙ (⊙Susp (⊙Ω X)) → de⊙ X
    ε = E.f

    ⊙η : X ⊙→ ⊙Ω (⊙Susp X)
    ⊙η = (η , !-inv-r (merid (pt X)))

    ⊙ε : ⊙Susp (⊙Ω X) ⊙→ X
    ⊙ε = (ε , idp)

  η-natural : {X Y : Ptd i} (f : X ⊙→ Y)
    → ⊙η Y ⊙∘ f == ⊙Ω-fmap (⊙Susp-fmap f) ⊙∘ ⊙η X
  η-natural {X = X} (f , idp) = ⊙λ='
    (λ x → ! $
      ap-∙ (Susp-fmap f) (merid x) (! (merid (pt X)))
      ∙ SuspFmap.merid-β f x
        ∙2 (ap-! (Susp-fmap f) (merid (pt X))
            ∙ ap ! (SuspFmap.merid-β f (pt X))))
    (pt-lemma (Susp-fmap f) (merid (pt X)) (SuspFmap.merid-β f (pt X)))
    where
    pt-lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} (p : x == y) {q : f x == f y} (α : ap f p == q)
      → !-inv-r q == ap (ap f) (!-inv-r p) ∙ idp
        [ _== idp ↓ ! (ap-∙ f p (! p) ∙ α ∙2 (ap-! f p ∙ ap ! α)) ]
    pt-lemma f idp idp = idp

  ε-natural : {X Y : Ptd i} (f : X ⊙→ Y)
    → ⊙ε Y ⊙∘ ⊙Susp-fmap (⊙Ω-fmap f) == f ⊙∘ ⊙ε X
  ε-natural (f , idp) = ⊙λ='
    (SuspElim.f idp idp
      (λ p → ↓-='-from-square $ vert-degen-square $
        ap-∘ (ε _) (Susp-fmap (ap f)) (merid p)
        ∙ ap (ap (ε _)) (SuspFmap.merid-β (ap f) p)
        ∙ E.merid-β _ (ap f p)
        ∙ ap (ap f) (! (E.merid-β _ p))
        ∙ ∘-ap f (ε _) (merid p)))
    idp

  εΣ-Ση : (X : Ptd i) → ⊙ε (⊙Susp X) ⊙∘ ⊙Susp-fmap (⊙η X) == ⊙idf _
  εΣ-Ση X = ⊙λ='
    (SuspElim.f
      idp
      (merid (pt X))
      (λ x → ↓-='-from-square $
        (ap-∘ (ε (⊙Susp X)) (Susp-fmap (η X)) (merid x)
         ∙ ap (ap (ε (⊙Susp X))) (SuspFmap.merid-β (η X) x)
         ∙ E.merid-β _ (merid x ∙ ! (merid (pt X))))
        ∙v⊡ square-lemma (merid x) (merid (pt X))
        ⊡v∙ ! (ap-idf (merid x))))
    idp
    where
    square-lemma : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : z == y)
      → Square idp (p ∙ ! q) p q
    square-lemma idp idp = ids

  Ωε-ηΩ : (X : Ptd i) → ⊙Ω-fmap (⊙ε X) ⊙∘ ⊙η (⊙Ω X) == ⊙idf _
  Ωε-ηΩ X = ⊙λ='
    (λ p → ap-∙ (ε X) (merid p) (! (merid idp))
         ∙ (E.merid-β X p ∙2 (ap-! (ε X) (merid idp) ∙ ap ! (E.merid-β X idp)))
         ∙ ∙-unit-r _)
    (pt-lemma (ε X) (merid idp) (E.merid-β X idp))
    where
    pt-lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} (p : x == y) {q : f x == f y} (α : ap f p == q)
      → ap (ap f) (!-inv-r p) ∙ idp == idp
        [ _== idp ↓ ap-∙ f p (! p) ∙ (α ∙2 (ap-! f p ∙ ap ! α)) ∙ !-inv-r q ]
    pt-lemma f idp idp = idp

adj : CounitUnitAdjoint SuspFunctor LoopFunctor
adj = record {
  η = ⊙η;
  ε = ⊙ε;

  η-natural = η-natural;
  ε-natural = ε-natural;

  εF-Fη = εΣ-Ση;
  Gε-ηG = Ωε-ηΩ}

hadj = counit-unit-to-hom adj

open HomAdjoint hadj public
