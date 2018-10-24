{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLaneFunctor
open import homotopy.SmashFmapConn
open import homotopy.IterSuspSmash
open import cohomology.CupProduct.OnEM.InLowDegrees
open import cohomology.CupProduct.OnEM.InLowDegrees2

module cohomology.CupProduct.OnEM.InAllDegrees where

module _ {i} (A : AbGroup i) where

  private
    module A = AbGroup A
  open EMExplicit

  inv-path : A == A
  inv-path = uaᴬᴳ A A (inv-iso A)

  cond-neg : ∀ (k : ℕ) → Bool
    → EM A k → EM A k
  cond-neg k b =
    transport (λ G → EM G k) {x = A} {y = A} (Bool-elim inv-path idp b)

  cond-neg-∘ : ∀ (k : ℕ) → (b c : Bool)
    → cond-neg k b ∘ cond-neg k c ∼ cond-neg k (xor b c)
  cond-neg-∘ k true  true  x =
    (transport (λ G → EM G k) {x = A} {y = A} inv-path $
     transport (λ G → EM G k) {x = A} {y = A} inv-path x)
      =⟨ ap (transport (λ G → EM G k) {x = A} {y = A} inv-path) $
         app= (transport-EM-uaᴬᴳ A A (inv-iso A) k) x ⟩
    (transport (λ G → EM G k) {x = A} {y = A} inv-path $
     EM-fmap A A (inv-hom A) k x)
      =⟨ app= (transport-EM-uaᴬᴳ A A (inv-iso A) k) $
         EM-fmap A A (inv-hom A) k x ⟩
    (EM-fmap A A (inv-hom A) k $
     EM-fmap A A (inv-hom A) k x)
      =⟨ app= (! (EM-fmap-∘ A A A (inv-hom A) (inv-hom A) k)) x ⟩
    EM-fmap A A (inv-hom A ∘ᴳ inv-hom A) k x
      =⟨ ap (λ φ → EM-fmap A A φ k x) $
         group-hom= {ψ = idhom _} (λ= A.inv-inv) ⟩
    EM-fmap A A (idhom _) k x
      =⟨ app= (EM-fmap-idhom A k) x ⟩
    x =∎
  cond-neg-∘ k true  false x = idp
  cond-neg-∘ k false true  x = idp
  cond-neg-∘ k false false x = idp

  maybe-Susp^-flip-cond-neg : ∀ (k : ℕ) (b : Bool)
    → (k == 0 → b == false)
    → Trunc-fmap (maybe-Susp^-flip k b) ∼ cond-neg (S k) b
  maybe-Susp^-flip-cond-neg O b h x =
    Trunc-fmap (idf _) x
      =⟨ Trunc-fmap-idf x ⟩
    x
      =⟨ ap (λ c → cond-neg 1 c x) (! (h idp)) ⟩
    cond-neg 1 b x =∎
  maybe-Susp^-flip-cond-neg (S k) true h x =
    Trunc-fmap Susp-flip x
      =⟨ ! (Susp-flip-EM-neg A k x) ⟩
    EM-neg A (S (S k)) x
      =⟨ app= (! (transport-EM-uaᴬᴳ A A (inv-iso A) (S (S k)))) x ⟩
    transport (λ G → EM G (S (S k))) {x = A} {y = A} inv-path x =∎
  maybe-Susp^-flip-cond-neg (S k) false h x = Trunc-fmap-idf x

  EM2-Susp : ∀ (k : ℕ)
    → Susp^ k (EM A 2)
    → EM A (S (S k))
  EM2-Susp k =
    transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ∘
    Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp})) ∘
    Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k

  EM2-Susp-maybe-Susp^-flip : ∀ (k : ℕ) (b : Bool)
    → (k == 0 → b == false)
    → EM2-Susp k ∘ maybe-Susp^-flip k b ∼
      Trunc-fmap (maybe-Susp^-flip (S k) b) ∘ EM2-Susp k
  EM2-Susp-maybe-Susp^-flip k b h x =
    (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) $
     Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp})) $
     Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k $
     maybe-Susp^-flip k b x)
      =⟨ ap (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2)) $
         ap (Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp}))) $
         Susp^-Trunc-swap-maybe-Susp^-flip (Susp (EM₁ A.grp)) 2 k b x ⟩
    (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) $
     Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp})) $
     Trunc-fmap (maybe-Susp^-flip k b) $
     Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x)
      =⟨ ap (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2)) $
         Trunc-fmap-∘ (coe (Susp^-comm k 1 {EM₁ A.grp})) (maybe-Susp^-flip k b) $
         Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x ⟩
    (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) $
     Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp}) ∘ maybe-Susp^-flip k b) $
     Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x)
      =⟨ ap (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2)) $
         app= (ap Trunc-fmap (λ= p)) $
         Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x ⟩
    (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) $
     Trunc-fmap (maybe-Susp^-flip (S k) b ∘ coe (Susp^-comm k 1 {EM₁ A.grp})) $
     Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x)
      =⟨ ap (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2)) $
         ! $ Trunc-fmap-∘ (maybe-Susp^-flip (S k) b) (coe (Susp^-comm k 1 {EM₁ A.grp})) $
         Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x ⟩
    (transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) $
     Trunc-fmap (maybe-Susp^-flip (S k) b) $
     Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp})) $
     Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x)
      =⟨ ! $ app= (transp-naturality (λ {l} → Trunc-fmap {n = l} (maybe-Susp^-flip (S k) b))
                                     (+2+-comm ⟨ k ⟩₋₂ 2)) $
         Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp})) $
         Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x ⟩
    (Trunc-fmap (maybe-Susp^-flip (S k) b) $
     transport (λ l → Trunc l (Susp^ (S k) (EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) $
     Trunc-fmap (coe (Susp^-comm k 1 {EM₁ A.grp})) $
     Susp^-Trunc-swap (Susp (EM₁ A.grp)) 2 k x) =∎
    where
    p : coe (Susp^-comm k 1 {EM₁ A.grp}) ∘ maybe-Susp^-flip k b ∼
        maybe-Susp^-flip (S k) b ∘ coe (Susp^-comm k 1 {EM₁ A.grp})
    p y =
      coe (Susp^-comm k 1 {EM₁ A.grp}) (maybe-Susp^-flip k b y)
        =⟨ ! (maybe-Susp^-flip-Susp^-comm (EM₁ A.grp) k 1 b y) ⟩
      Susp-fmap (maybe-Susp^-flip k b) (coe (Susp^-comm k 1) y)
        =⟨ ! (Susp-fmap-maybe-Susp^-flip k b h (coe (Susp^-comm k 1) y)) ⟩
      maybe-Susp^-flip (S k) b (coe (Susp^-comm k 1) y) =∎

  cpₕₕ'' : ∀ (m n : ℕ)
    → Susp^ (m + n) (EM A 2)
    → EM A (S m + S n)
  cpₕₕ'' m n =
    cond-neg (S m + S n) (odd n) ∘
    transport (EM A) (! (+-βr (S m) n)) ∘
    EM2-Susp (m + n)

module _ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G = AbGroup G
    module H = AbGroup H
    module G⊗H = TensorProduct G H
  open EMExplicit

  cpₕₕ' : ∀ (m n : ℕ)
    → ⊙Susp^ m (⊙EM₁ G.grp) ∧ ⊙Susp^ n (⊙EM₁ H.grp)
    → EM G⊗H.abgroup (S m + S n)
  cpₕₕ' m n =
    cpₕₕ'' G⊗H.abgroup m n ∘
    Susp^-fmap (m + n) (∧-cp₁₁ G H) ∘
    Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n

  smash-truncate : ∀ (m n : ℕ)
    → ⊙Susp^ m (⊙EM₁ G.grp) ∧ ⊙Susp^ n (⊙EM₁ H.grp)
    → ⊙EM G (S m) ∧ ⊙EM H (S n)
  smash-truncate m n =
    ∧-fmap
      ([_] {n = ⟨ S m ⟩} {A = Susp^ m (EM₁ G.grp)} , idp)
      ([_] {n = ⟨ S n ⟩} {A = Susp^ n (EM₁ H.grp)} , idp)

  smash-truncate-conn : ∀ (m n : ℕ)
    → has-conn-fibers ⟨ S m + S n ⟩ (smash-truncate m n)
  smash-truncate-conn m n =
    transport (λ k → has-conn-fibers k (smash-truncate m n)) p $
    ∧-fmap-conn
      ([_] {n = ⟨ S m ⟩} {A = Susp^ m (EM₁ G.grp)} , idp)
      ([_] {n = ⟨ S n ⟩} {A = Susp^ n (EM₁ H.grp)} , idp)
      (EM-conn G m)
      (⊙Susp^-conn' n {{EM₁-conn}})
      (trunc-proj-conn (Susp^ m (EM₁ G.grp)) ⟨ S m ⟩)
      (trunc-proj-conn (Susp^ n (EM₁ H.grp)) ⟨ S n ⟩)
    where
    p₁ : ⟨ n ⟩₋₁ +2+ ⟨ S m ⟩ == ⟨ S m + S n ⟩
    p₁ =
      ⟨ n ⟩₋₁ +2+ ⟨ S m ⟩
        =⟨ ! (+-+2+ (S n) (S (S (S m)))) ⟩
      ⟨ n + S (S (S m)) ⟩₋₁
        =⟨ ap ⟨_⟩₋₁ (+-βr n (S (S m))) ⟩
      ⟨ n + S (S m) ⟩
        =⟨ ap ⟨_⟩ (+-βr n (S m)) ⟩
      ⟨ S n + S m ⟩
        =⟨ ap ⟨_⟩ (+-comm (S n) (S m)) ⟩
      ⟨ S m + S n ⟩ =∎
    p₂ : ⟨ m ⟩₋₁ +2+ ⟨ S n ⟩ == ⟨ S m + S n ⟩
    p₂ =
      ⟨ m ⟩₋₁ +2+ ⟨ S n ⟩
        =⟨ ! (+-+2+ (S m) (S (S (S n)))) ⟩
      ⟨ m + S (S (S n)) ⟩₋₁
        =⟨ ap ⟨_⟩₋₁ (+-βr m (S (S n))) ⟩
      ⟨ m + S (S n) ⟩
        =⟨ ap ⟨_⟩ (+-βr m (S n)) ⟩
      ⟨ S m + S n ⟩ =∎
    p : minT (⟨ n ⟩₋₁ +2+ ⟨ S m ⟩) (⟨ m ⟩₋₁ +2+ ⟨ S n ⟩) == ⟨ S m + S n ⟩
    p =
      minT (⟨ n ⟩₋₁ +2+ ⟨ S m ⟩) (⟨ m ⟩₋₁ +2+ ⟨ S n ⟩)
        =⟨ ap2 minT p₁ p₂ ⟩
      minT ⟨ S m + S n ⟩ ⟨ S m + S n ⟩
        =⟨ minT-out-l ≤T-refl ⟩
      ⟨ S m + S n ⟩ =∎

  cpₕₕ : ∀ (m n : ℕ)
    → ⊙EM G (S m) ∧ ⊙EM H (S n)
    → EM G⊗H.abgroup (S m + S n)
  cpₕₕ m n =
    conn-extend
      (smash-truncate-conn m n)
      (λ _ → EM G⊗H.abgroup (S m + S n) , EM-level G⊗H.abgroup (S m + S n))
      (cpₕₕ' m n)
