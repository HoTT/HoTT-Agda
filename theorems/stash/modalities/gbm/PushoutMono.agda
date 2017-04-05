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

    -- Construct a fibration over the pushout
    -- whose total space is equivalent to A

    lemma₀ : (c : C) → is-contr (hfiber g (g c))
    lemma₀ c = inhab-prop-is-contr (c , idp) (m (g c))

    lemma₁ : (c : C) → is-contr (hfiber (idf A) (f c))
    lemma₁ c = equiv-is-contr-map (idf-is-equiv A) (f c)

    glue-equiv : (c : C) → hfiber (idf A) (f c) ≃ hfiber g (g c)
    glue-equiv c = (contr-equiv-Unit (lemma₀ c)) ⁻¹ ∘e (contr-equiv-Unit (lemma₁ c))
    
    A' : (d : D) → Type i
    A' = Pushout-rec (λ a → hfiber (idf A) a) (λ b → hfiber g b) (λ c → ua (glue-equiv c))


    -- Pulling back over B, we should have a space
    -- equivalent to C as well as the path spaces
    -- we are interested in.

    C' : Type i
    C' = Σ B (A' ∘ mright)

    C'-equiv-pths : C' ≃ Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    C'-equiv-pths = equiv to from to-from from-to

      where to : C' → Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
            to (b , c , p) = (f c , b) , mglue c ∙ ap mright p

            from : Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab)) → C'
            from ((a , b) , p) = b , transport A' p (a , idp)
            
            to-from : (x : Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))) → to (from x) == x
            to-from ((a , b) , p) = {!!}

            from-to : (c' : C') → from (to c') == c'
            from-to c' = {!!}

    C-equiv-C' : C ≃ C'
    C-equiv-C' = equiv to from to-from from-to

      where to : C → C'
            to c = g c , (c , idp)

            from : C' → C
            from (b , c , p) = c

            to-from : (c' : C') → to (from c') == c'
            to-from (b , c , p) = pair= p {!!}

            from-to : (c : C) → from (to c) == c
            from-to c = idp
            

    -- Combining the two equivalences from above
    -- gives us the result we want.

    pushout-mono-is-pullback : C ≃ Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    pushout-mono-is-pullback = C'-equiv-pths ∘e C-equiv-C'

