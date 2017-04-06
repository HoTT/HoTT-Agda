{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.gbm.PushoutMono where

  --
  --  The goal of this file is to prove the following:
  --  Suppose we have a pushout
  --
  --        g
  --    C ------> B
  --    v         |
  --    |         |
  --  f |         |
  --    v         v
  --    A ------> D
  --
  --  and the map f is a monomorphism.  Then the square
  --  is also a pullback.
  -- 

  is-mono : ∀ {i j} {A : Type i} {B : Type j} → (A → B) → Type _
  is-mono {B = B} f = (b : B) → has-level (S ⟨-2⟩) (hfiber f b)

  module MonoLemma {i} (s : Span {i} {i} {i}) (m : is-mono (Span.f s)) where

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
    -- whose total space is equivalent to B

    glue-equiv : (c : C) → hfiber f (f c) ≃ Lift {j = i} ⊤
    glue-equiv c = contr-equiv-LiftUnit (inhab-prop-is-contr (c , idp) (m (f c)))
    
    B' : (d : D) → Type i
    B' = Pushout-rec (λ a → hfiber f a) (λ _ → Lift ⊤) (λ c → ua (glue-equiv c))

    -- Pulling back over A, we should have a space
    -- equivalent to C as well as the path spaces
    -- we are interested in.

    C' : Type i
    C' = Σ A (B' ∘ mleft)

    -- Some scratch work ...
    --
    -- B-equiv-B' : B ≃ Σ D B'
    -- B-equiv-B' = equiv to (λ { (d , b') → from d b' }) {!!} {!!}

    --   where to : B → Σ D B'
    --         to b = mright b , lift unit

    --         from : (d : D) → B' d → B
    --         from = Pushout-elim (λ a e → g (fst e)) (λ b _ → b) (λ c → ↓-Π-in (λ q → {!B' (left (f c))!}))

            
    -- Given (b : B) and an element it is equal to in the
    -- the pushout, we can find an element in the fiber which
    -- witnesses that equaltiy

    witness-for : ∀ {a b} (p : mleft a == mright b) → hfiber f a
    witness-for {b = b} p = transport! B' p (lift unit)

    -- We need the following two coherences to finish the proof
    
    postulate
    
      witness-for-coh₀ : ∀ {a b} (p : mleft a == mright b) → g (fst (witness-for p)) == b

      witness-for-coh₁ : ∀ {a b} (p : mleft a == mright b) →
        (! (ap mleft (snd (witness-for p))) ∙ mglue (fst (witness-for p))) == p
          [ (λ ab → mleft (fst ab) == mright (snd ab)) ↓ (ap (λ x → (a , x)) (witness-for-coh₀ p)) ]
    
    C'-equiv-pths : C' ≃ Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    C'-equiv-pths = equiv to from to-from from-to

      where to : C' → Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
            to (a , c , p) = (a , g c) , ! (ap mleft p) ∙ mglue c 

            from : Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab)) → C'
            from ((a , b) , p) = a , witness-for p 
            
            to-from : (x : Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))) → to (from x) == x
            to-from ((a , b) , p) = pair= (pair= idp (witness-for-coh₀ p)) (witness-for-coh₁ p)

            from-to : (c' : C') → from (to c') == c'
            from-to (a , c , p) = pair= idp (fst (m _ _ (c , p)))

    lemma₂ : {a₀ a₁ : A} (p : a₀ == a₁) (e₀ : hfiber f a₀) (e₁ : hfiber f a₁)
      → e₀ == e₁ [ (λ a → hfiber f a) ↓ p ]
    lemma₂ idp e₀ e₁ = fst (m _ e₀ e₁)
  
    C-equiv-C' : C ≃ C'
    C-equiv-C' = equiv to from to-from from-to

      where to : C → C'
            to c = f c , (c , idp)

            from : C' → C
            from (a , c , p) = c

            to-from : (c' : C') → to (from c') == c'
            to-from (a , c , p) = pair= p (lemma₂ p (c , idp) (c , p))
                    
            from-to : (c : C) → from (to c) == c
            from-to c = idp

    -- Combining the two equivalences from above
    -- gives us the result we want.

    pushout-mono-is-pullback : C ≃ Σ (A × B) (λ ab → mleft (fst ab) == mright (snd ab))
    pushout-mono-is-pullback = C'-equiv-pths ∘e C-equiv-C'
