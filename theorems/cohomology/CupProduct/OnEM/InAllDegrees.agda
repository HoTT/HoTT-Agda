{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLaneFunctor
open import homotopy.SmashFmapConn
open import homotopy.IterSuspSmash
open import cohomology.CupProduct.OnEM.InLowDegrees2

module cohomology.CupProduct.OnEM.InAllDegrees where

module _ {i} (A : AbGroup i) where

  private
    module A = AbGroup A
  open EMExplicit

  inv-path : A == A
  inv-path = uaᴬᴳ A A (inv-iso A)

  ⊙cond-neg : ∀ (k : ℕ) → Bool
    → ⊙EM A k ⊙→ ⊙EM A k
  ⊙cond-neg k b =
    ⊙transport (λ G → ⊙EM G k) {x = A} {y = A} (Bool-elim inv-path idp b)

  cond-neg : ∀ (k : ℕ) → Bool
    → EM A k → EM A k
  cond-neg k b =
    transport (λ G → EM G k) {x = A} {y = A} (Bool-elim inv-path idp b)

  ⊙cond-neg-∘ : ∀ (k : ℕ) (b c : Bool)
    → ⊙cond-neg k b ◃⊙∘ ⊙cond-neg k c ◃⊙idf
      =⊙∘
      ⊙cond-neg k (xor b c) ◃⊙idf
  ⊙cond-neg-∘ k true true =
    ⊙transport (λ G → ⊙EM G k) {x = A} {y = A} inv-path ◃⊙∘
    ⊙transport (λ G → ⊙EM G k) {x = A} {y = A} inv-path ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & ⊙transport-⊙EM-uaᴬᴳ A A (inv-iso A) k ⟩
    ⊙EM-fmap A A (–>ᴳ (inv-iso A)) k ◃⊙∘
    ⊙transport (λ G → ⊙EM G k) {x = A} {y = A} inv-path ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ⊙transport-⊙EM-uaᴬᴳ A A (inv-iso A) k ⟩
    ⊙EM-fmap A A (–>ᴳ (inv-iso A)) k ◃⊙∘
    ⊙EM-fmap A A (–>ᴳ (inv-iso A)) k ◃⊙idf
      =⊙∘₁⟨ ! $ ⊙EM-fmap-∘ A A A (–>ᴳ (inv-iso A)) (–>ᴳ (inv-iso A)) k ⟩
    ⊙EM-fmap A A (–>ᴳ (inv-iso A) ∘ᴳ –>ᴳ (inv-iso A)) k ◃⊙idf
      =⊙∘₁⟨ ap (λ φ → ⊙EM-fmap A A φ k) $
            group-hom= {ψ = idhom _} (λ= A.inv-inv) ⟩
    ⊙EM-fmap A A (idhom _) k ◃⊙idf
      =⊙∘₁⟨ ⊙EM-fmap-idhom A k ⟩
    ⊙idf _ ◃⊙idf ∎⊙∘
  ⊙cond-neg-∘ k true  false = =⊙∘-in idp
  ⊙cond-neg-∘ k false true  = =⊙∘-in (⊙λ= (⊙∘-unit-l (⊙cond-neg k true)))
  ⊙cond-neg-∘ k false false = =⊙∘-in idp

  ⊙maybe-Susp^-flip-⊙cond-neg : ∀ (k : ℕ) (b : Bool)
    → (k == 0 → b == false)
    → ⊙Trunc-fmap (⊙maybe-Susp^-flip k b) == ⊙cond-neg (S k) b
  ⊙maybe-Susp^-flip-⊙cond-neg O b h =
    ⊙Trunc-fmap (⊙idf (⊙EM₁ A.grp))
      =⟨ ⊙λ= ⊙Trunc-fmap-⊙idf ⟩
    ⊙idf (⊙EM A 1)
      =⟨ ap (⊙cond-neg 1) (! (h idp)) ⟩
    ⊙cond-neg 1 b =∎
  ⊙maybe-Susp^-flip-⊙cond-neg (S k) true h =
    ⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ A.grp)))
      =⟨ ! (⊙EM-neg=⊙Trunc-fmap-⊙Susp-flip A k) ⟩
    ⊙EM-neg A (S (S k))
      =⟨ ! (⊙transport-⊙EM-uaᴬᴳ A A (inv-iso A) (S (S k))) ⟩
    ⊙transport (λ G → ⊙EM G (S (S k))) {x = A} {y = A} inv-path =∎
  ⊙maybe-Susp^-flip-⊙cond-neg (S k) false h = ⊙λ= (⊙Trunc-fmap-⊙idf)

  ⊙EM2-Susp-seq : ∀ (k : ℕ)
    → ⊙Susp^ k (⊙EM A 2) ⊙–→ ⊙EM A (S (S k))
  ⊙EM2-Susp-seq k =
    ⊙transport (λ l → ⊙Trunc l (⊙Susp^ (S k) (⊙EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-swap k 1 {⊙EM₁ A.grp}) ◃⊙∘
    ⊙Susp^-Trunc-swap (⊙Susp (EM₁ A.grp)) 2 k ◃⊙idf

  ⊙EM2-Susp : ∀ (k : ℕ)
    → ⊙Susp^ k (⊙EM A 2) ⊙→ ⊙EM A (S (S k))
  ⊙EM2-Susp k = ⊙compose (⊙EM2-Susp-seq k)

  ⊙EM2-Susp-⊙maybe-Susp^-flip : ∀ (k : ℕ) (b : Bool)
    → (k == 0 → b == false)
    → ⊙EM2-Susp k ◃⊙∘
      ⊙maybe-Susp^-flip k b ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙maybe-Susp^-flip {X = ⊙EM₁ A.grp} (S k) b) ◃⊙∘
      ⊙EM2-Susp k ◃⊙idf
  ⊙EM2-Susp-⊙maybe-Susp^-flip k b h =
    ⊙EM2-Susp k ◃⊙∘
    ⊙maybe-Susp^-flip k b ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙expand (⊙EM2-Susp-seq k) ⟩
    ⊙transport (λ l → ⊙Trunc l (⊙Susp^ (S k) (⊙EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-swap k 1 {⊙EM₁ A.grp}) ◃⊙∘
    ⊙Susp^-Trunc-swap (⊙Susp (EM₁ A.grp)) 2 k ◃⊙∘
    ⊙maybe-Susp^-flip k b ◃⊙idf
      =⊙∘⟨ 2 & 2 & ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip (⊙Susp (EM₁ A.grp)) 2 k b ⟩
    ⊙transport (λ l → ⊙Trunc l (⊙Susp^ (S k) (⊙EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-swap k 1 {⊙EM₁ A.grp}) ◃⊙∘
    ⊙Trunc-fmap (⊙maybe-Susp^-flip k b) ◃⊙∘
    ⊙Susp^-Trunc-swap (⊙Susp (EM₁ A.grp)) 2 k ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙Trunc-fmap-seq-=⊙∘ p ⟩
    ⊙transport (λ l → ⊙Trunc l (⊙Susp^ (S k) (⊙EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ◃⊙∘
    ⊙Trunc-fmap (⊙maybe-Susp-flip (⊙Susp^ k (⊙EM₁ A.grp)) b) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-swap k 1 {⊙EM₁ A.grp}) ◃⊙∘
    ⊙Susp^-Trunc-swap (⊙Susp (EM₁ A.grp)) 2 k ◃⊙idf
      =⊙∘⟨ 0 & 2 & !⊙∘ $
           ⊙transport-natural-=⊙∘
             (+2+-comm ⟨ k ⟩₋₂ 2)
             (λ l → ⊙Trunc-fmap {n = l} (⊙maybe-Susp^-flip (S k) b)) ⟩
    ⊙Trunc-fmap (⊙maybe-Susp-flip (⊙Susp^ k (⊙EM₁ A.grp)) b) ◃⊙∘
    ⊙transport (λ l → ⊙Trunc l (⊙Susp^ (S k) (⊙EM₁ A.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-swap k 1 {⊙EM₁ A.grp}) ◃⊙∘
    ⊙Susp^-Trunc-swap (⊙Susp (EM₁ A.grp)) 2 k ◃⊙idf
      =⊙∘⟨ 1 & 3 & ⊙contract ⟩
    ⊙Trunc-fmap (⊙maybe-Susp-flip (⊙Susp^ k (⊙EM₁ A.grp)) b) ◃⊙∘
    ⊙EM2-Susp k ◃⊙idf ∎⊙∘
    where
    p : ⊙Susp^-swap k 1 {⊙EM₁ A.grp} ◃⊙∘
        ⊙maybe-Susp^-flip k b ◃⊙idf
        =⊙∘
        ⊙maybe-Susp^-flip {X = ⊙EM₁ A.grp} (S k) b ◃⊙∘
        ⊙Susp^-swap k 1 {⊙EM₁ A.grp} ◃⊙idf
    p =
      ⊙Susp^-swap k 1 {⊙EM₁ A.grp} ◃⊙∘
      ⊙maybe-Susp^-flip k b ◃⊙idf
        =⊙∘⟨ !⊙∘ $ ⊙maybe-Susp^-flip-⊙Susp^-comm (⊙EM₁ A.grp) k 1 b ⟩
      ⊙Susp-fmap (fst (⊙maybe-Susp^-flip k b)) ◃⊙∘
      ⊙coe (⊙Susp^-comm k 1) ◃⊙idf
        =⊙∘₁⟨ 0 & 1 & ap ⊙Susp-fmap (de⊙-⊙maybe-Susp^-flip k b) ∙
                      ⊙Susp-fmap-maybe-Susp^-flip k b h ⟩
      ⊙maybe-Susp-flip (⊙Susp^ k (⊙EM₁ A.grp)) b ◃⊙∘
      ⊙Susp^-swap k 1 ◃⊙idf ∎⊙∘

  ⊙cpₕₕ''-seq : ∀ (m n : ℕ)
    → ⊙Susp^ (m + n) (⊙EM A 2) ⊙–→ ⊙EM A (S m + S n)
  ⊙cpₕₕ''-seq m n =
    ⊙cond-neg (S m + S n) (odd n) ◃⊙∘
    ⊙transport (⊙EM A) (! (+-βr (S m) n)) ◃⊙∘
    ⊙EM2-Susp (m + n) ◃⊙idf

  ⊙cpₕₕ'' : ∀ (m n : ℕ)
    → ⊙Susp^ (m + n) (⊙EM A 2) ⊙→ ⊙EM A (S m + S n)
  ⊙cpₕₕ'' m n = ⊙compose (⊙cpₕₕ''-seq m n)

module _ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G = AbGroup G
    module H = AbGroup H
    module G⊗H = TensorProduct G H
  open EMExplicit

  ⊙∧-cpₕₕ'-seq : ∀ (m n : ℕ)
    → (⊙Susp^ m (⊙EM₁ G.grp) ⊙∧ ⊙Susp^ n (⊙EM₁ H.grp))
      ⊙–→
      ⊙EM G⊗H.abgroup (S m + S n)
  ⊙∧-cpₕₕ'-seq m n =
    ⊙cpₕₕ'' G⊗H.abgroup m n ◃⊙∘
    ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
    ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf

  ⊙∧-cpₕₕ' : ∀ (m n : ℕ)
    → ⊙Susp^ m (⊙EM₁ G.grp) ⊙∧ ⊙Susp^ n (⊙EM₁ H.grp) ⊙→ ⊙EM G⊗H.abgroup (S m + S n)
  ⊙∧-cpₕₕ' m n = ⊙compose (⊙∧-cpₕₕ'-seq m n)

  ∧-cpₕₕ' : ∀ (m n : ℕ)
    → ⊙Susp^ m (⊙EM₁ G.grp) ∧ ⊙Susp^ n (⊙EM₁ H.grp)
    → EM G⊗H.abgroup (S m + S n)
  ∧-cpₕₕ' m n = fst (⊙∧-cpₕₕ' m n)

  ⊙smash-truncate : ∀ (m n : ℕ)
    → ⊙Susp^ m (⊙EM₁ G.grp) ⊙∧ ⊙Susp^ n (⊙EM₁ H.grp)
    ⊙→ ⊙EM G (S m) ⊙∧ ⊙EM H (S n)
  ⊙smash-truncate m n =
    ⊙∧-fmap
      ([_] {n = ⟨ S m ⟩} {A = Susp^ m (EM₁ G.grp)} , idp)
      ([_] {n = ⟨ S n ⟩} {A = Susp^ n (EM₁ H.grp)} , idp)

  smash-truncate : ∀ (m n : ℕ)
    → ⊙Susp^ m (⊙EM₁ G.grp) ∧ ⊙Susp^ n (⊙EM₁ H.grp)
    → ⊙EM G (S m) ∧ ⊙EM H (S n)
  smash-truncate m n = fst (⊙smash-truncate m n)

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

  module SmashCPₕₕ (m n : ℕ) =
    ⊙ConnExtend
      {Z = ⊙EM G⊗H.abgroup (S m + S n)}
      {n = ⟨ S m + S n ⟩}
      (⊙smash-truncate m n)
      (smash-truncate-conn m n)
      (EM-level G⊗H.abgroup (S m + S n))

  ⊙∧-cpₕₕ : ∀ (m n : ℕ)
    → ⊙EM G (S m) ⊙∧ ⊙EM H (S n) ⊙→ ⊙EM G⊗H.abgroup (S m + S n)
  ⊙∧-cpₕₕ m n = SmashCPₕₕ.⊙ext m n (⊙∧-cpₕₕ' m n)

  ∧-cpₕₕ : ∀ (m n : ℕ)
    → ⊙EM G (S m) ∧ ⊙EM H (S n)
    → EM G⊗H.abgroup (S m + S n)
  ∧-cpₕₕ m n = fst (⊙∧-cpₕₕ m n)

  ∧-cp₀ₕ' : ∀ (n : ℕ)
    → G.⊙El ∧ ⊙EM H (S n) → EM G⊗H.abgroup (S n)
  ∧-cp₀ₕ' n =
    Smash-rec
      (λ g → Trunc-fmap (Susp^-fmap n (cp₀₁ G H g)))
      (pt (⊙EM G⊗H.abgroup (S n)))
      (pt (⊙EM G⊗H.abgroup (S n)))
      (λ g → snd (⊙EM-fmap H G⊗H.abgroup (G⊗H.ins-r-hom g) (S n)))
      (λ y →
        EM-fmap H G⊗H.abgroup (G⊗H.ins-r-hom G.ident) (S n) y
          =⟨ ap (λ φ → EM-fmap H G⊗H.abgroup φ (S n) y) $
             group-hom= {φ = G⊗H.ins-r-hom G.ident} {ψ = cst-hom} $
             λ= G⊗H.⊗-ident-l ⟩
        EM-fmap H G⊗H.abgroup cst-hom (S n) y
          =⟨ app= (EM-fmap-cst-hom H G⊗H.abgroup (S n)) y ⟩
        pt (⊙EM G⊗H.abgroup (S n)) =∎)

  ⊙∧-cp₀ₕ' : ∀ (n : ℕ)
    → G.⊙El ⊙∧ ⊙EM H (S n) ⊙→ ⊙EM G⊗H.abgroup (S n)
  ⊙∧-cp₀ₕ' n = ∧-cp₀ₕ' n , snd (⊙Trunc-fmap (⊙Susp^-fmap n (cp₀₁ G H G.ident , idp)))

  ⊙∧-cp₀ₕ : ∀ (n : ℕ)
    → ⊙EM G 0 ⊙∧ ⊙EM H (S n) ⊙→ ⊙EM G⊗H.abgroup (S n)
  ⊙∧-cp₀ₕ n =
    ⊙∧-cp₀ₕ' n ⊙∘
    ⊙∧-fmap (⊙<– (⊙emloop-equiv G.grp)) (⊙idf (⊙EM H (S n)))

  ∧-cp₀ₕ : ∀ (n : ℕ)
    → ⊙EM G 0 ∧ ⊙EM H (S n) → EM G⊗H.abgroup (S n)
  ∧-cp₀ₕ n = fst (⊙∧-cp₀ₕ n)

module _ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G⊗H = TensorProduct G H
    module H⊗G = TensorProduct H G
  open EMExplicit

  ⊙∧-cpₕ₀-seq : ∀ (m : ℕ)
    → (⊙EM G (S m) ⊙∧ ⊙EM H 0) ⊙–→ ⊙EM G⊗H.abgroup (S m + 0)
  ⊙∧-cpₕ₀-seq m =
    ⊙transport (⊙EM G⊗H.abgroup) (+-comm 0 (S m)) ◃⊙∘
    ⊙EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap (S m) ◃⊙∘
    ⊙∧-cp₀ₕ H G m ◃⊙∘
    ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf

  ⊙∧-cpₕ₀ : ∀ (m : ℕ)
    → ⊙EM G (S m) ⊙∧ ⊙EM H 0 ⊙→ ⊙EM G⊗H.abgroup (S m + 0)
  ⊙∧-cpₕ₀ m = ⊙compose (⊙∧-cpₕ₀-seq m)

  ⊙∧-cp : ∀ (m n : ℕ)
    → ⊙EM G m ⊙∧ ⊙EM H n
    ⊙→ ⊙EM G⊗H.abgroup (m + n)
  ⊙∧-cp O O = ⊙∧-cp₀₀ G H
  ⊙∧-cp O (S n) = ⊙∧-cp₀ₕ G H n
  ⊙∧-cp (S m) O = ⊙∧-cpₕ₀ m
  ⊙∧-cp (S m) (S n) = ⊙∧-cpₕₕ G H m n

  ∧-cp : ∀ (m n : ℕ)
    → ⊙EM G m ∧ ⊙EM H n
    → EM G⊗H.abgroup (m + n)
  ∧-cp m n = fst (⊙∧-cp m n)
