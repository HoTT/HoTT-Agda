{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.gbm.PullbackSplit where

--     L --> B    K = A ×_D C / (f,h)       d₁ = A -> D <- C
--     |     |g   L = B ×_A K / (g,left)    d₂ = B -> A <- K
--     v     v                              d  = B -> D <- C
--     K --> A
--     |     |f
--     v     v
--     C --> D
--        h

module PullbackLSplit {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : A → D) (g : B → A) (h : C → D) where

  private
    d₁ : Cospan
    d₁ = cospan C A D h f

    d₂ : Cospan
    d₂ = cospan (Pullback d₁) B A Pullback.b g

    d : Cospan
    d = cospan C B D h (f ∘ g)

  split-equiv : Pullback d ≃ Pullback d₂
  split-equiv = equiv to from to-from from-to

    where to : Pullback d → Pullback d₂
          to (pullback c b p) = pullback (pullback c (g b) p) b idp

          from : Pullback d₂ → Pullback d
          from (pullback (pullback c a p) b idp) = pullback c b p

          to-from : (x : Pullback d₂) → to (from x) == x
          to-from (pullback _ b idp) = idp

          from-to : (x : Pullback d) → from (to x) == x
          from-to _ = idp

record CospanMap {i₀ j₀ k₀ i₁ j₁ k₁} (cospan₀ : Cospan {i₀} {j₀} {k₀}) (cospan₁ : Cospan {i₁} {j₁} {k₁})
  : Type (lmax (lmax (lmax i₀ j₀) k₀) (lmax (lmax i₁ j₁) k₁)) where
  constructor cospan-map
  module cospan₀ = Cospan cospan₀
  module cospan₁ = Cospan cospan₁
  field
    hA : cospan₀.A → cospan₁.A
    hB : cospan₀.B → cospan₁.B
    hC : cospan₀.C → cospan₁.C
    f-commutes : CommSquare cospan₀.f cospan₁.f hA hC 
    g-commutes : CommSquare cospan₀.g cospan₁.g hB hC 

CospanEquiv : ∀ {i₀ j₀ k₀ i₁ j₁ k₁} (cospan₀ : Cospan {i₀} {j₀} {k₀}) (cospan₁ : Cospan {i₁} {j₁} {k₁})
  → Type (lmax (lmax (lmax i₀ j₀) k₀) (lmax (lmax i₁ j₁) k₁))
CospanEquiv cospan₀ cospan₁ = Σ (CospanMap cospan₀ cospan₁)
  (λ cospan-map → is-equiv (CospanMap.hA cospan-map)
                 × is-equiv (CospanMap.hB cospan-map)
                 × is-equiv (CospanMap.hC cospan-map))

CospanEquiv-inverse : ∀ {i₀ j₀ k₀ i₁ j₁ k₁} {cospan₀ : Cospan {i₀} {j₀} {k₀}} {cospan₁ : Cospan {i₁} {j₁} {k₁}}
  → CospanEquiv cospan₀ cospan₁ → CospanEquiv cospan₁ cospan₀
CospanEquiv-inverse (cospan-map hA hB hC f-commutes g-commutes , hA-ise , hB-ise , hC-ise)
  = (cospan-map hA.g hB.g hC.g
        (CommSquare-inverse-v f-commutes hA-ise hC-ise)
        (CommSquare-inverse-v g-commutes hB-ise hC-ise))
      , ( is-equiv-inverse hA-ise
        , is-equiv-inverse hB-ise
        , is-equiv-inverse hC-ise)
   where module hA = is-equiv hA-ise
         module hB = is-equiv hB-ise
         module hC = is-equiv hC-ise

module PullbackFmap {i₀ j₀ k₀ i₁ j₁ k₁} {cospan₀ : Cospan {i₀} {j₀} {k₀}}
  {cospan₁ : Cospan {i₁} {j₁} {k₁}} (cospan-map : CospanMap cospan₀ cospan₁) where

  f : Pullback cospan₀ → Pullback cospan₁
  f (pullback a b h) = pullback
    (CospanMap.hA cospan-map a)
    (CospanMap.hB cospan-map b)
    (! (commutes (CospanMap.f-commutes cospan-map) a) ∙
      ap (λ x → CospanMap.hC cospan-map x) h ∙
      (commutes (CospanMap.g-commutes cospan-map) b))

Pullback-fmap = PullbackFmap.f

module _ {i₀ j₀ k₀ i₁ j₁ k₁} {cospan₀ : Cospan {i₀} {j₀} {k₀}}
  {cospan₁ : Cospan {i₁} {j₁} {k₁}} (cospan-equiv : CospanEquiv cospan₀ cospan₁) where

  private
    module cospan₀ = Cospan cospan₀
    module cospan₁ = Cospan cospan₁
    cospan-to = fst cospan-equiv
    cospan-from = fst (CospanEquiv-inverse cospan-equiv)
    module cospan-to = CospanMap cospan-to
    module cospan-from = CospanMap cospan-from
    module To = PullbackFmap cospan-to
    module From = PullbackFmap cospan-from
    cospan-ise = snd cospan-equiv
    hA-ise = fst cospan-ise
    hB-ise = fst (snd cospan-ise)
    hC-ise = snd (snd cospan-ise)
    module hA-ise = is-equiv hA-ise
    module hB-ise = is-equiv hB-ise
    module hC-ise = is-equiv hC-ise

    to = To.f
    from = From.f

    to-from : ∀ y → to (from y) == y
    to-from (pullback a b h) = pullback= _ (hA-ise.f-g a) (hB-ise.f-g b) {!cospan-to.hA!}

      where gA = cospan-from.hA
            gB = cospan-from.hB
            gC = cospan-from.hC
            
            a₁ = gA a
            b₁ = gB b
            h₁ = Pullback.h (from (pullback a b h))
            fc = commutes cospan-to.f-commutes

            test : a₁ == gA a
            test = idp


    -- (! (commutes (CospanMap.f-commutes cospan-map) a) ∙
    --   ap (λ x → CospanMap.hC cospan-map x) h ∙
    --   (commutes (CospanMap.g-commutes cospan-map) b))

    postulate
      -- to-from : ∀ y → to (from y) == y
      -- to-from (pullback a b h) = pullback= _ (hA-ise.f-g a) (hB-ise.f-g b) {!!}

      from-to : ∀ x → from (to x) == x
      -- from-to (pullback a b h) = pullback= _ (hA-ise.g-f a) (hB-ise.g-f b) {!!}

  Pullback-emap : Pullback cospan₀ ≃ Pullback cospan₁
  Pullback-emap = equiv to from to-from from-to

