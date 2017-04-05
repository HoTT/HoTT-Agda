{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.gbm.PushoutMono where

  is-mono : ∀ {i j} {A : Type i} {B : Type j} → (A → B) → Type _
  is-mono {B = B} f = (b : B) → has-level (S ⟨-2⟩) (hfiber f b)

  module _ {i} (s : Span {i} {i} {i}) (m : is-mono (Span.g s)) where

    open Span s

    private
      D = Pushout s

    mleft : A → D
    mleft = left

    mright : B → D
    mright = right

    mglue : (c : C) → mleft (f c) == mright (g c)
    mglue c = glue c
    
    -- The total space of this fibration should be
    -- equivalent to A
    A' : (d : D) → Type i
    A' = Pushout-rec (λ a → hfiber (idf A) a) (λ b → hfiber g b) (λ c → ua (eqv c))

      where lem₀ : (c : C) → is-contr (hfiber g (g c))
            lem₀ c = inhab-prop-is-contr (c , idp) (m (g c))

            lem₁ : (c : C) → is-contr (hfiber (idf A) (f c))
            lem₁ c = equiv-is-contr-map (idf-is-equiv A) (f c)

            eqv : (c : C) → hfiber (idf A) (f c) ≃ hfiber g (g c)
            eqv c = (contr-equiv-Unit (lem₀ c)) ⁻¹ ∘e (contr-equiv-Unit (lem₁ c)) 

    -- This is a fibration over B whose total space should
    -- be equivalent to C
    C' : Type i
    C' = Σ B (A' ∘ mright)

    -- Yeah, this is going to work.  You're going to use
    -- transport after pushing the element a into the pushout.
    -- Just need to see how "rewriting" works ...
    to : Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab)) → C'
    to ((a , b) , p) = b , transport A' p (a , idp)

    from : C' → Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    from (b , c , p) = (f c , b) , mglue c ∙ ap mright p

    fst-eqv : C' ≃ Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    fst-eqv = equiv from to f-g {!!}

      where f-g : (x : Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))) → from (to x) == x
            f-g ((a , b) , p) = {!!}
            
    C-to-C' : C → C'
    C-to-C' c = g c , (c , idp)

    C'-to-C : C' → C
    C'-to-C (b , c , p) = c

    snd-eqv : C ≃ C'
    snd-eqv = equiv C-to-C' C'-to-C f-g g-f

      where f-g : (c' : C') → C-to-C' (C'-to-C c') == c'
            f-g (b , c , p) = pair= p {!!}

            g-f : (c : C) → C'-to-C (C-to-C' c) == c
            g-f c = idp
            
    -- Right, and then you're going to have a map from C, and
    -- you're going to try to show that this is an equivalence.

    thm : C ≃ Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    thm = fst-eqv ∘e snd-eqv

    -- Yeah, but then after this you'll still need that the
    -- composite of pushouts is a pushout.  That one seems like
    -- a real pain in the ass.  I feel like there has to be
    -- a shorter way.
