{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.gbm.GbmUtil

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

    f = cospan₀.f
    g = cospan₀.g
    f' = cospan₁.f
    g' = cospan₁.g

    α = commutes cospan-to.f-commutes
    β = commutes cospan-to.g-commutes

    α' = commutes cospan-from.f-commutes
    β' = commutes cospan-from.g-commutes
    
    hA = cospan-to.hA
    hB = cospan-to.hB
    hC = cospan-to.hC
    
    kA = cospan-from.hA
    kB = cospan-from.hB
    kC = cospan-from.hC

    module kA-ise = is-equiv (is-equiv-inverse hA-ise)
    module kB-ise = is-equiv (is-equiv-inverse hB-ise)
    module kC-ise = is-equiv (is-equiv-inverse hC-ise)

    kA-ise = is-equiv-inverse hA-ise
    kB-ise = is-equiv-inverse hB-ise
    kC-ise = is-equiv-inverse hC-ise

    to = To.f
    from = From.f

    from-to : ∀ x → from (to x) == x
    from-to (pullback a b h) = pullback= _ (hA-ise.g-f a) (hB-ise.g-f b) goal

      where eq₀ = hC-ise.g-f (f a) ∙ h ∙ ! (hC-ise.g-f (g b))
                    =⟨ ! (ap-idf h) |in-ctx (λ x → hC-ise.g-f (f a) ∙ x ∙ ! (hC-ise.g-f (g b))) ⟩
                  hC-ise.g-f (f a) ∙ ap (idf _) h ∙ ! (hC-ise.g-f (g b))
                    =⟨ ! (∙-assoc (hC-ise.g-f (f a)) _ _) ⟩ 
                  (hC-ise.g-f (f a) ∙ ap (idf _) h) ∙ ! (hC-ise.g-f (g b))
                    =⟨ ↓-==-out (apd hC-ise.g-f h) |in-ctx (λ x → x ∙ ! (hC-ise.g-f (g b))) ⟩
                  (ap (kC ∘ hC) h ∙ hC-ise.g-f (g b)) ∙ ! (hC-ise.g-f (g b))
                    =⟨ ∙-assoc (ap (kC ∘ hC) h) _ _ ⟩ 
                  ap (kC ∘ hC) h ∙ hC-ise.g-f (g b) ∙ ! (hC-ise.g-f (g b))
                    =⟨ !-inv-r (hC-ise.g-f (g b)) |in-ctx (λ x → ap (kC ∘ hC) h ∙ x) ⟩ 
                  ap (kC ∘ hC) h ∙ idp
                    =⟨ ∙-unit-r (ap (kC ∘ hC) h) ⟩ 
                  ap (kC ∘ hC) h ∎

            eq₁ = β' (hB b)
                    =⟨ ! (hB-ise.adj b) |in-ctx (λ x → ap kC (! (β (kB (hB b)) ∙ ap g' x)) ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ap kC (! (β (kB (hB b)) ∙ ap g' (ap hB (hB-ise.g-f b)))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ∘-ap g' hB (hB-ise.g-f b) |in-ctx (λ x → ap kC (! (β (kB (hB b)) ∙ x)) ∙ hC-ise.g-f (g (kB (hB b)))) ⟩
                  ap kC (! (β (kB (hB b)) ∙ ap (g' ∘ hB) (hB-ise.g-f b))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ↓-==-out (apd β (hB-ise.g-f b)) |in-ctx (λ x → ap kC (! x) ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ap kC (! (ap (hC ∘ g) (hB-ise.g-f b) ∙ β b)) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ap-! kC (ap (hC ∘ g) (hB-ise.g-f b) ∙ β b) |in-ctx (λ x → x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ! (ap kC (ap (hC ∘ g) (hB-ise.g-f b) ∙ β b)) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ap-∙ kC (ap (hC ∘ g) (hB-ise.g-f b)) (β b) |in-ctx (λ x → ! x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ! (ap kC (ap (hC ∘ g) (hB-ise.g-f b)) ∙ ap kC (β b)) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ !-∙ (ap kC (ap (hC ∘ g) (hB-ise.g-f b))) (ap kC (β b)) |in-ctx (λ x → x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩
                  (! (ap kC (β b)) ∙ ! (ap kC (ap (hC ∘ g) (hB-ise.g-f b)))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ∙-assoc (! (ap kC (β b))) _ _ ⟩
                  ! (ap kC (β b)) ∙ ! (ap kC (ap (hC ∘ g) (hB-ise.g-f b))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ∘-ap kC (hC ∘ g) (hB-ise.g-f b) |in-ctx (λ x → ! (ap kC (β b)) ∙ ! x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ! (ap kC (β b)) ∙ ! (ap (kC ∘ hC ∘ g) (hB-ise.g-f b)) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ! (∘-ap (kC ∘ hC) g (hB-ise.g-f b)) |in-ctx (λ x → ! (ap kC (β b)) ∙ ! x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ! (ap kC (β b)) ∙ ! (ap (kC ∘ hC) (ap g (hB-ise.g-f b))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ eqv-square' (hC , hC-ise) (ap g (hB-ise.g-f b)) |in-ctx (λ x → ! (ap kC (β b)) ∙ ! x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ! (ap kC (β b)) ∙ ! (hC-ise.g-f (g (kB (hB b))) ∙ (ap g (hB-ise.g-f b)) ∙ ! (hC-ise.g-f (g b))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ !-∙ (hC-ise.g-f (g (kB (hB b)))) ((ap g (hB-ise.g-f b)) ∙ ! (hC-ise.g-f (g b))) |in-ctx (λ x → ! (ap kC (β b)) ∙ x ∙ hC-ise.g-f (g (kB (hB b)))) ⟩ 
                  ! (ap kC (β b)) ∙ (! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b))) ∙ ! (hC-ise.g-f (g (kB (hB b))))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ ∙-assoc (! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b)))) _ _ |in-ctx (λ x → ! (ap kC (β b)) ∙ x) ⟩ 
                  ! (ap kC (β b)) ∙ ! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b))) ∙ ! (hC-ise.g-f (g (kB (hB b)))) ∙ hC-ise.g-f (g (kB (hB b)))
                    =⟨ !-inv-l (hC-ise.g-f (g (kB (hB b)))) |in-ctx (λ x → ! (ap kC (β b)) ∙ ! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b))) ∙ x) ⟩ 
                  ! (ap kC (β b)) ∙ ! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b))) ∙ idp
                    =⟨ ∙-unit-r (! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b)))) |in-ctx (λ x → ! (ap kC (β b)) ∙ x) ⟩ 
                  ! (ap kC (β b)) ∙ ! (ap g (hB-ise.g-f b) ∙ ! (hC-ise.g-f (g b)))
                    =⟨ !-∙ (ap g (hB-ise.g-f b)) (! (hC-ise.g-f (g b))) |in-ctx (λ x → ! (ap kC (β b)) ∙ x) ⟩ 
                  ! (ap kC (β b)) ∙ ! (! (hC-ise.g-f (g b))) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-! (hC-ise.g-f (g b)) |in-ctx (λ x → ! (ap kC (β b)) ∙ x ∙ ! (ap g (hB-ise.g-f b))) ⟩ 
                  ! (ap kC (β b)) ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b)) ∎

            eq₂ = α' (hA a)
                    =⟨ ! (hA-ise.adj a) |in-ctx (λ x → ap kC (! (α (kA (hA a)) ∙ ap f' x)) ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ap kC (! (α (kA (hA a)) ∙ ap f' (ap hA (hA-ise.g-f a)))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ∘-ap f' hA (hA-ise.g-f a) |in-ctx (λ x → ap kC (! (α (kA (hA a)) ∙ x)) ∙ hC-ise.g-f (f (kA (hA a)))) ⟩
                  ap kC (! (α (kA (hA a)) ∙ ap (f' ∘ hA) (hA-ise.g-f a))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ↓-==-out (apd α (hA-ise.g-f a)) |in-ctx (λ x → ap kC (! x) ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ap kC (! (ap (hC ∘ f) (hA-ise.g-f a) ∙ α a)) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ap-! kC (ap (hC ∘ f) (hA-ise.g-f a) ∙ α a) |in-ctx (λ x → x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ! (ap kC (ap (hC ∘ f) (hA-ise.g-f a) ∙ α a)) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ap-∙ kC (ap (hC ∘ f) (hA-ise.g-f a)) (α a) |in-ctx (λ x → ! x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ! (ap kC (ap (hC ∘ f) (hA-ise.g-f a)) ∙ ap kC (α a)) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ !-∙ (ap kC (ap (hC ∘ f) (hA-ise.g-f a))) (ap kC (α a)) |in-ctx (λ x → x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩
                  (! (ap kC (α a)) ∙ ! (ap kC (ap (hC ∘ f) (hA-ise.g-f a)))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ∙-assoc (! (ap kC (α a))) _ _ ⟩
                  ! (ap kC (α a)) ∙ ! (ap kC (ap (hC ∘ f) (hA-ise.g-f a))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ∘-ap kC (hC ∘ f) (hA-ise.g-f a) |in-ctx (λ x → ! (ap kC (α a)) ∙ ! x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ! (ap kC (α a)) ∙ ! (ap (kC ∘ hC ∘ f) (hA-ise.g-f a)) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ! (∘-ap (kC ∘ hC) f (hA-ise.g-f a)) |in-ctx (λ x → ! (ap kC (α a)) ∙ ! x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ! (ap kC (α a)) ∙ ! (ap (kC ∘ hC) (ap f (hA-ise.g-f a))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ eqv-square' (hC , hC-ise) (ap f (hA-ise.g-f a)) |in-ctx (λ x → ! (ap kC (α a)) ∙ ! x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ! (ap kC (α a)) ∙ ! (hC-ise.g-f (f (kA (hA a))) ∙ (ap f (hA-ise.g-f a)) ∙ ! (hC-ise.g-f (f a))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ !-∙ (hC-ise.g-f (f (kA (hA a)))) ((ap f (hA-ise.g-f a)) ∙ ! (hC-ise.g-f (f a))) |in-ctx (λ x → ! (ap kC (α a)) ∙ x ∙ hC-ise.g-f (f (kA (hA a)))) ⟩ 
                  ! (ap kC (α a)) ∙ (! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a))) ∙ ! (hC-ise.g-f (f (kA (hA a))))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ ∙-assoc (! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a)))) _ _ |in-ctx (λ x → ! (ap kC (α a)) ∙ x) ⟩ 
                  ! (ap kC (α a)) ∙ ! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a))) ∙ ! (hC-ise.g-f (f (kA (hA a)))) ∙ hC-ise.g-f (f (kA (hA a)))
                    =⟨ !-inv-l (hC-ise.g-f (f (kA (hA a)))) |in-ctx (λ x → ! (ap kC (α a)) ∙ ! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a))) ∙ x) ⟩ 
                  ! (ap kC (α a)) ∙ ! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a))) ∙ idp
                    =⟨ ∙-unit-r (! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a)))) |in-ctx (λ x → ! (ap kC (α a)) ∙ x) ⟩ 
                  ! (ap kC (α a)) ∙ ! (ap f (hA-ise.g-f a) ∙ ! (hC-ise.g-f (f a)))
                    =⟨ !-∙ (ap f (hA-ise.g-f a)) (! (hC-ise.g-f (f a))) |in-ctx (λ x → ! (ap kC (α a)) ∙ x) ⟩ 
                  ! (ap kC (α a)) ∙ ! (! (hC-ise.g-f (f a))) ∙ ! (ap f (hA-ise.g-f a))
                    =⟨ !-! (hC-ise.g-f (f a)) |in-ctx (λ x → ! (ap kC (α a)) ∙ x ∙ ! (ap f (hA-ise.g-f a))) ⟩
                  ! (ap kC (α a)) ∙ hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a)) ∎

            lem = ! (α' (hA a)) ∙ ap kC (! (α a) ∙ ap hC h ∙ β b) ∙ β' (hB b)
                    =⟨ ap-∙ kC (! (α a)) (ap hC h ∙ β b) |in-ctx (λ x → ! (α' (hA a)) ∙ x ∙ β' (hB b)) ⟩
                  ! (α' (hA a)) ∙ (ap kC (! (α a)) ∙ ap kC (ap hC h ∙ β b)) ∙ β' (hB b)
                    =⟨ ∙-assoc (ap kC (! (α a))) (ap kC (ap hC h ∙ β b)) (β' (hB b)) |in-ctx (λ x → ! (α' (hA a)) ∙ x) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap kC (ap hC h ∙ β b) ∙ β' (hB b)
                    =⟨ ap-∙ kC (ap hC h) (β b) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x ∙ β' (hB b)) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (ap kC (ap hC h) ∙ ap kC (β b)) ∙ β' (hB b)
                    =⟨ ∙-assoc (ap kC (ap hC h)) (ap kC (β b)) (β' (hB b)) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap kC (ap hC h) ∙ ap kC (β b) ∙ β' (hB b)
                    =⟨ ∘-ap kC hC h |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x ∙ ap kC (β b) ∙ β' (hB b)) ⟩
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ ap kC (β b) ∙ β' (hB b)
                    =⟨ eq₁ |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ ap kC (β b) ∙ x) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ ap kC (β b) ∙ ! (ap kC (β b)) ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ! (∙-assoc (ap kC (β b)) _ _) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ x) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ (ap kC (β b) ∙ ! (ap kC (β b))) ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b)) 
                    =⟨ !-inv-r (ap kC (β b)) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ x ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))) ⟩
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ap (kC ∘ hC) h ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ! eq₀ |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))) ⟩
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (hC-ise.g-f (f a) ∙ h ∙ ! (hC-ise.g-f (g b))) ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))                    
                    =⟨ ! (∙-assoc (hC-ise.g-f (f a)) _ _) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))) ⟩
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ ((hC-ise.g-f (f a) ∙ h) ∙ ! (hC-ise.g-f (g b))) ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ∙-assoc (hC-ise.g-f (f a) ∙ h) _ _ |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (hC-ise.g-f (f a) ∙ h) ∙ ! (hC-ise.g-f (g b)) ∙ hC-ise.g-f (g b) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ! (∙-assoc (! (hC-ise.g-f (g b))) _ _) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (hC-ise.g-f (f a) ∙ h) ∙ x) ⟩ 
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (hC-ise.g-f (f a) ∙ h) ∙ (! (hC-ise.g-f (g b)) ∙ hC-ise.g-f (g b)) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-inv-l (hC-ise.g-f (g b)) |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (hC-ise.g-f (f a) ∙ h) ∙ x ∙ ! (ap g (hB-ise.g-f b))) ⟩
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ (hC-ise.g-f (f a) ∙ h) ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ∙-assoc (hC-ise.g-f (f a)) _ _ |in-ctx (λ x → ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ x) ⟩
                  ! (α' (hA a)) ∙ ap kC (! (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ eq₂ |in-ctx (λ x → ! x ∙ ap kC (! (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩  
                  ! (! (ap kC (α a)) ∙ hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ ap kC (! (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-∙ (! (ap kC (α a))) _ |in-ctx (λ x → x ∙ ap kC (! (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩
                  (! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ ! (! (ap kC (α a)))) ∙ ap kC (! (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ∙-assoc (! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a)))) _ _ ⟩
                  ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ ! (! (ap kC (α a))) ∙ ap kC (! (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ap-! kC (α a) |in-ctx (λ x → ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ ! (! (ap kC (α a))) ∙ x ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩ 
                  ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ ! (! (ap kC (α a))) ∙ ! (ap kC (α a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ! (∙-assoc (! (! (ap kC (α a)))) _ _) |in-ctx (λ x → ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ x) ⟩ 
                  ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ (! (! (ap kC (α a))) ∙ ! (ap kC (α a))) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-inv-l (! (ap kC (α a))) |in-ctx (λ x → ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ x ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩ 
                  ! (hC-ise.g-f (f a) ∙ ! (ap f (hA-ise.g-f a))) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-∙ (hC-ise.g-f (f a)) _  |in-ctx (λ x → x ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩ 
                  (! (! (ap f (hA-ise.g-f a))) ∙ ! (hC-ise.g-f (f a))) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ∙-assoc (! (! (ap f (hA-ise.g-f a)))) _ _ ⟩
                  ! (! (ap f (hA-ise.g-f a))) ∙ ! (hC-ise.g-f (f a)) ∙ hC-ise.g-f (f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ ! (∙-assoc (! (hC-ise.g-f (f a))) _ _) |in-ctx (λ x → ! (! (ap f (hA-ise.g-f a))) ∙ x) ⟩ 
                  ! (! (ap f (hA-ise.g-f a))) ∙ (! (hC-ise.g-f (f a)) ∙ hC-ise.g-f (f a)) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-inv-l (hC-ise.g-f (f a)) |in-ctx (λ x → ! (! (ap f (hA-ise.g-f a))) ∙ x ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩
                  ! (! (ap f (hA-ise.g-f a))) ∙ h ∙ ! (ap g (hB-ise.g-f b))
                    =⟨ !-! (ap f (hA-ise.g-f a)) |in-ctx (λ x → x ∙ h ∙ ! (ap g (hB-ise.g-f b))) ⟩ 
                  ap f (hA-ise.g-f a) ∙ h ∙ ! (ap g (hB-ise.g-f b)) ∎

            goal = (! (α' (hA a)) ∙ ap kC (! (α a) ∙ ap hC h ∙ β b) ∙ β' (hB b)) ∙ ap g (hB-ise.g-f b)
                     =⟨ lem |in-ctx (λ x → x ∙ ap g (hB-ise.g-f b)) ⟩
                   (ap f (hA-ise.g-f a) ∙ h ∙ ! (ap g (hB-ise.g-f b))) ∙ ap g (hB-ise.g-f b)
                     =⟨ ∙-assoc (ap f (hA-ise.g-f a)) (h ∙ ! (ap g (hB-ise.g-f b))) _ ⟩ 
                   ap f (hA-ise.g-f a) ∙ (h ∙ ! (ap g (hB-ise.g-f b))) ∙ ap g (hB-ise.g-f b)
                     =⟨ ∙-assoc h _ _ |in-ctx (λ x → ap f (hA-ise.g-f a) ∙ x) ⟩ 
                   ap f (hA-ise.g-f a) ∙ h ∙ ! (ap g (hB-ise.g-f b)) ∙ ap g (hB-ise.g-f b)
                     =⟨ !-inv-l (ap g (hB-ise.g-f b)) |in-ctx (λ x → ap f (hA-ise.g-f a) ∙ h ∙ x) ⟩ 
                   ap f (hA-ise.g-f a) ∙ h ∙ idp
                     =⟨ ∙-unit-r h |in-ctx (λ x → ap f (hA-ise.g-f a) ∙ x) ⟩ 
                   ap f (hA-ise.g-f a) ∙ h ∎


    postulate
      to-from : ∀ y → to (from y) == y
      -- to-from (pullback a b h) = pullback= _ (hA-ise.f-g a) (hB-ise.f-g b) {!!}

  Pullback-emap : Pullback cospan₀ ≃ Pullback cospan₁
  Pullback-emap = equiv to from to-from from-to

