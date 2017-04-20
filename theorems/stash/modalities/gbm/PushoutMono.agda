{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import stash.modalities.gbm.GbmUtil

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

  mono-eq : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a₀ a₁ : A}
    (p : f a₀ == f a₁) → is-mono f → a₀ == a₁
  mono-eq f {a₀} {a₁} p ism = ! (fst= (fst (ism (f a₁) (a₁ , idp) (a₀ , p))))

  mono-eq-ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a₀ a₁ : A}
    (p : f a₀ == f a₁) → (is-m : is-mono f) → ap f (mono-eq f p is-m) == p
  mono-eq-ap f p is-m = {!!}
  
  Lift-Unit-is-contr : ∀ {i} → is-contr (Lift {j = i} ⊤)
  Lift-Unit-is-contr = equiv-preserves-level (lower-equiv ⁻¹) Unit-is-contr

  Lift-Unit-is-prop : ∀ {i} → is-prop (Lift {j = i} ⊤)
  Lift-Unit-is-prop = contr-is-prop Lift-Unit-is-contr

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

    -- Now, I claim that the values of this fibration are props.
    -- How do you prove this?

    module B' = PushoutRec {d = s} (hfiber f) (cst (Lift ⊤)) (ua ∘ glue-equiv)
    
    B' : (d : D) → Type i
    B' = B'.f

    B'-β : (c : C) → ap B' (glue c) == ua (glue-equiv c)
    B'-β c = B'.glue-β c 

    B'-is-prop : (d : D) → is-prop (B' d)
    B'-is-prop = Pushout-elim (λ a → m a) (λ b → Lift-Unit-is-prop)
      (λ c → prop-lemma (λ z → is-prop (B' z) , is-prop-is-prop) (mglue c) (m (f c))
      Lift-Unit-is-prop)

    B'-prop : (d : D) → hProp i
    B'-prop d = B' d , B'-is-prop d

    B'-pth-in : ∀ {a b} (p : mleft a == mright b) (x : B' (mleft a)) (y : B' (mright b))
      → x == y [ B' ↓ p ]
    B'-pth-in p x y = prop-lemma B'-prop p x y      

    B'-pth-in' : ∀ {a b} (p : mright b == mleft a) (x : B' (mleft a)) (y : B' (mright b))
      → y == x [ B' ↓ p ]
    B'-pth-in' p x y = prop-lemma B'-prop p y x

    -- Yeah, these triples of data seem to come up a bunch
    -- the point is, such data is contractible...
    data-contr : (c : C) → is-contr (Σ (B' (left (f c))) (λ l → Σ (B' (right (g c))) (λ r → l == r [ B' ↓ glue c ])))
    data-contr c = Σ-level (inhab-prop-is-contr (c , idp) (m (f c)))
      (λ l → Σ-level Lift-Unit-is-contr (λ r → pths-ovr-contr B'-prop (glue c) l r))

    data-elim : (c : C) (P : (l : B' (left (f c))) (r : B' (right (g c))) → (l == r [ B' ↓ glue c ]) → Type i)
                → (t : Σ (B' (left (f c))) (λ l → Σ (B' (right (g c))) (λ r → l == r [ B' ↓ glue c ])))
                → P (fst t) (fst (snd t)) (snd (snd t))
                → (l : B' (left (f c))) → (r : B' (right (g c))) → (q : l == r [ B' ↓ glue c ]) → P l r q
    data-elim c P t x l r q = transport (λ { (l₀ , r₀ , q₀) → P l₀ r₀ q₀ })
      (contr-has-all-paths (data-contr c) _ _) x
    
    module _ where

      private
      
        to : B → Σ D B'
        to b = mright b , lift unit

        from : Σ D B' → B
        from = uncurry $ Pushout-elim
          (λ a e → g (fst e))
          (λ b _ → b)
          (λ c → ↓-Π-in (λ {l} {r} q → ↓-cst-in (ap g (mono-eq f (snd l) m))))

        to-from : (db : Σ D B') → to (from db) == db
        to-from = uncurry $ Pushout-elim lem₀ (λ b _ → idp) 
          (λ c → ↓-Π-in (λ {l} {r} q → ↓-app=idf-in (lem₁ c l r q)))

          where lem₀ : (a : A) (l : B' (left a)) → to (from (left a , l)) == left a , l
                lem₀ .(f c) (c , idp) = ! (pair= (mglue c) (B'-pth-in (mglue c) (c , idp) (lift unit))) 

                P : (c : C) (l : B' (left (f c))) (r : B' (right (g c))) (q : l == r [ B' ↓ glue c ]) → Type i
                P c l r q = lem₀ (f c) l ∙' pair= (glue c) q ==
                            ap (λ v → to (from v)) (pair= (glue c) q) ∙ idp

                -- Okay, I see what to do.  You have to kind of "unwrap" the
                -- ap as it is applied to the uncurry guy above.  Then you use
                -- glue-β to get that it's the value of from given above.
                -- The other side already reduces quite a bit.  Just a bit of
                -- path algebra.
                lem₂ : (c : C) → P c (c , idp) (lift unit) (fst (pths-ovr-contr B'-prop (glue c) (c , idp) (lift unit)))
                lem₂ c = lem₀ (f c) (c , idp) ∙' pair= (glue c) q =⟨ {!!} ⟩ 
                         ap (λ v → to (from v)) (pair= (glue c) q) ∙ idp ∎
                  
                    where q = (fst (pths-ovr-contr B'-prop (glue c) (c , idp) (lift unit)))
                  
                lem₁ : (c : C) (l : B' (left (f c))) (r : B' (right (g c))) (q : l == r [ B' ↓ glue c ]) 
                  → lem₀ (f c) l ∙' pair= (glue c) q ==
                     ap (λ v → to (from v)) (pair= (glue c) q) ∙ idp
                lem₁ c l r q = data-elim c (P c) {!!} {!!} l r q
                     
      B≃B' : B ≃ Σ D B'
      B≃B' = equiv to from to-from (λ b → idp)
            
    -- From the above equivalence, we can prove that
    -- mright is also a mono
    mright-is-mono : is-mono mright
    mright-is-mono d = equiv-preserves-level (lem ⁻¹ ∘e (hfiber-fst d) ⁻¹) (B'-is-prop d)

      where lem : hfiber mright d ≃ hfiber fst d
            lem = hfiber-sq-eqv mright fst (fst B≃B') (idf D) (comm-sqr (λ b → idp)) (snd B≃B') (idf-is-equiv D) d
            
    -- Pulling back over A, we should have a space
    -- equivalent to C as well as the path spaces
    -- we are interested in.

    C' : Type i
    C' = Σ A (B' ∘ mleft)
            
    -- Given (b : B) and an element it is equal to in the
    -- the pushout, we can find an element in the fiber which
    -- witnesses that equaltiy

    witness-for : ∀ {a b} (p : mleft a == mright b) → hfiber f a
    witness-for p = transport! B' p (lift unit)
    
    -- Using the fact that mright is a mono, we can
    -- find a proof of the following
    witness-for-coh₀ : ∀ {a b} (p : mleft a == mright b) → g (fst (witness-for p)) == b
    witness-for-coh₀ {a} {b} p = mono-eq mright lem mright-is-mono

      where c : C
            c = fst (witness-for p)

            lem : mright (g c) == mright b
            lem = ! (mglue c) ∙ ap mleft (snd (witness-for p)) ∙ p

    witness-for-coh₁ : ∀ {a b} (p : mleft a == mright b)
      → (! (ap mleft (snd (witness-for p))) ∙ mglue (fst (witness-for p))) == p
         [ (λ ab → mleft (fst ab) == mright (snd ab)) ↓ (ap (λ x → (a , x)) (witness-for-coh₀ p)) ]
    witness-for-coh₁ {a} p = ↓-ap-in _ (λ b₀ → (a , b₀)) (↓-cst=app-in calc)

      where α = ap mleft (snd (witness-for p))
            β = mglue (fst (witness-for p))
            
            calc = (! α ∙ β) ∙' ap mright (witness-for-coh₀ p)
                      =⟨ mono-eq-ap mright (! β ∙ α ∙ p) mright-is-mono |in-ctx (λ x → (! α ∙ β) ∙' x) ⟩
                   (! α ∙ β) ∙' ! β ∙ α ∙ p =⟨ ∙'=∙ (! α ∙ β) (! β ∙ α ∙ p) ⟩
                   (! α ∙ β) ∙ ! β ∙ α ∙ p =⟨ ∙-assoc (! α) β (! β ∙ α ∙ p) ⟩
                   ! α ∙ β ∙ ! β ∙ α ∙ p =⟨ ! (∙-assoc β (! β) (α ∙ p)) |in-ctx (λ x → ! α ∙ x) ⟩
                   ! α ∙ (β ∙ ! β) ∙ α ∙ p =⟨ !-inv-r β |in-ctx (λ x → ! α ∙ x ∙ α ∙ p) ⟩
                   ! α ∙ α ∙ p =⟨ ! (∙-assoc (! α) α p) ⟩
                   (! α ∙ α) ∙ p =⟨ !-inv-l α |in-ctx (λ x → x ∙ p) ⟩ 
                   p ∎
            
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
