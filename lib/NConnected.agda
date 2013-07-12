{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalences2
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Suspension

module lib.NConnected where

is-conn-map : ∀ {i j} {A : Type i} {B : Type j} → ℕ₋₂ → (A → B) → Type (lmax i j)
is-conn-map {A = A} {B = B} n f = 
  Π B (λ b → is-contr $ Trunc n (Σ A (λ a → f a == b)))

is-connected : ∀ {i} → ℕ₋₂ → Type i → Type i
is-connected n A = is-contr (Trunc n A)

{- all inhabited types are ⟨-1⟩-connected -}
inhab-conn : ∀ {i} (A : Type i) (a : A) → is-connected ⟨-1⟩ A
inhab-conn A a = ([ a ] , prop-has-all-paths Trunc-level [ a ])

{- "induction principle" for n-connected maps (where codomain is n-type) -}
abstract
  conn-elim-eqv : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → {h : A → B} → is-conn-map n h
    → (∀ {k} (P : B → n -Type k) → is-equiv (λ (s : Π B (fst ∘ P)) → s ∘ h))
  conn-elim-eqv {A = A} {B = B} {n = n} {h = h} c P = is-eq f g f-g g-f
    where f : Π B (fst ∘ P) → Π A (fst ∘ P ∘ h)
          f k a = k (h a)

          helper : Π A (fst ∘ P ∘ h) 
            → (b : B) → Trunc n (Σ A (λ a → h a == b)) → (fst (P b))
          helper t b r = 
            Trunc-rec (snd (P b)) 
              (λ x → transport (λ y → fst (P y)) (snd x) (t (fst x))) 
              r
          
          g : Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
          g t b = helper t b (fst (c b))
  
          f-g : ∀ t → f (g t) == t
          f-g t = λ= $ λ a → transport 
            (λ r →  Trunc-rec (snd (P (h a))) _ r == t a)
            (! (snd (c (h a)) [ (a , idp) ]))
            idp 
  
          g-f : ∀ k → g (f k) == k
          g-f k = λ= $ λ (b : B) → 
            Trunc-elim (λ r → =-preserves-level _ {helper (k ∘ h) b r} (snd (P b)))
                       (λ x → lemma (fst x) b (snd x)) (fst (c b))
            where Jbase : ∀ {j} (x : B) → {P : (y : B) → (x == y) → Type j} 
                    → P x idp → (∀ y p → P y p)
                  Jbase x {P} r .x idp = r
          
                  lemma : ∀ xl → ∀ b → (p : h xl == b) →
                    helper (k ∘ h) b [ (xl , p) ] == k b
                  lemma xl = Jbase (h xl) idp

conn-elim : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  → {h : A → B} → is-conn-map n h
  → (P : B → n -Type k) 
  → Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
conn-elim c P f = is-equiv.g (conn-elim-eqv c P) f

conn-elim-β : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  {h : A → B} (c : is-conn-map n h)
  (P : B → n -Type k) (f : Π A (fst ∘ P ∘ h))
  → ∀ a → (conn-elim c P f (h a)) == f a
conn-elim-β c P f = app= (is-equiv.f-g (conn-elim-eqv c P) f)


abstract
  move-right-on-right-eqv : ∀ {i} {A : Type i} {x y z : A}
    (p : x == y) (q : x == z) (r : y == z)
    → (p == q ∙ ! r) ≃ (p ∙ r == q)
  move-right-on-right-eqv p q idp = 
    equiv f g f-g g-f
    where 
      f : (p == q ∙ ! idp) → (p ∙ idp == q)
      f v = ∙-unit-r p ∙ v ∙ ∙-unit-r q

      g : (p ∙ idp == q) → (p == q ∙ ! idp)
      g u = ! (∙-unit-r p) ∙ u ∙ ! (∙-unit-r q)

      f-g : ∀ u → f (g u) == u
      f-g u =
          ∙-unit-r p ∙ (! (∙-unit-r p) ∙ u ∙ ! (∙-unit-r q))  ∙ ∙-unit-r q
            =⟨ ∙-assoc (! (∙-unit-r p)) (u ∙ ! (∙-unit-r q)) (∙-unit-r q)
              |in-ctx (λ w → ∙-unit-r p ∙ w) ⟩
          ∙-unit-r p ∙ (! (∙-unit-r p)) ∙ ((u ∙ ! (∙-unit-r q))  ∙ ∙-unit-r q)
            =⟨ ! (∙-assoc (∙-unit-r p) (! (∙-unit-r p)) ((u ∙ ! (∙-unit-r q))  ∙ ∙-unit-r q)) ⟩
          (∙-unit-r p ∙ (! (∙-unit-r p))) ∙ ((u ∙ ! (∙-unit-r q))  ∙ ∙-unit-r q)
            =⟨ !-inv-r (∙-unit-r p) |in-ctx (λ w → w ∙ ((u ∙ ! (∙-unit-r q)) ∙ ∙-unit-r q)) ⟩
          (u ∙ ! (∙-unit-r q))  ∙ ∙-unit-r q
            =⟨ ∙-assoc u (! (∙-unit-r q)) (∙-unit-r q) ⟩
          u ∙ ! (∙-unit-r q)  ∙ ∙-unit-r q
            =⟨ ap (λ w → u ∙ w) (!-inv-l (∙-unit-r q)) ∙ ∙-unit-r u ⟩
          u ∎

      g-f : ∀ v → g (f v) == v
      g-f v = 
          ! (∙-unit-r p) ∙ (∙-unit-r p ∙ v ∙ ∙-unit-r q)  ∙ ! (∙-unit-r q) 
            =⟨ ∙-assoc (∙-unit-r p) (v ∙ ∙-unit-r q) (! (∙-unit-r q) ) 
              |in-ctx (λ w → ! (∙-unit-r p) ∙ w) ⟩
          ! (∙-unit-r p) ∙ ∙-unit-r p ∙ ((v ∙ ∙-unit-r q)  ∙ ! (∙-unit-r q))
            =⟨ ! (∙-assoc (! (∙-unit-r p)) (∙-unit-r p) ((v ∙ ∙-unit-r q)  ∙ ! (∙-unit-r q))) ⟩
          (! (∙-unit-r p) ∙ ∙-unit-r p) ∙ ((v ∙ ∙-unit-r q)  ∙ ! (∙-unit-r q))
            =⟨ !-inv-l (∙-unit-r p) |in-ctx (λ w → w ∙ ((v ∙ ∙-unit-r q) ∙ ! (∙-unit-r q))) ⟩
          (v ∙ ∙-unit-r q)  ∙ ! (∙-unit-r q)
            =⟨ ∙-assoc v (∙-unit-r q) (! (∙-unit-r q)) ⟩
          v ∙ ∙-unit-r q  ∙ ! (∙-unit-r q)
            =⟨ ap (λ w → v ∙ w) (!-inv-r (∙-unit-r q)) ∙ ∙-unit-r v ⟩
          v ∎

{- generalized "almost induction principle" for maps into ≥n-types 
   TODO: rearrange this to use ≤T?                                 -}
conn-elim-general : ∀ {i j} {A : Type i} {B : Type j} {n k : ℕ₋₂}
  → {f : A → B} → is-conn-map n f
  → ∀ {l} (P : B → (k +2+ n) -Type l) 
  → ∀ t → has-level k (Σ (Π B (fst ∘ P)) (λ s → (s ∘ f) == t))
conn-elim-general {k = ⟨-2⟩} c P = 
  equiv-is-contr-map (conn-elim-eqv c P)
conn-elim-general {B = B} {n = n} {k = S k'} {f = f} c P t (g , p) (h , q) =
  equiv-preserves-level e $ conn-elim-general {k = k'} c Q (app= (p ∙ ! q))
  where 
    Q : B → (k' +2+ n) -Type _
    Q b = ((g b == h b) , snd (P b) _ _)

    app=-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : B → Type k}
      (f : A → B) {g h : Π B C} (p : g == h)
      → app= (ap (λ k → k ∘ f) p) == (app= p ∘ f)
    app=-ap f idp = idp

    lemma : (H : ∀ x → g x == h x)
      → ((H ∘ f) == app= (p ∙ ! q)) 
         ≃ (ap (λ v → v ∘ f) (λ= H) ∙ q == p)
    lemma H = 
      move-right-on-right-eqv (ap (λ v → v ∘ f) (λ= H)) p q 
      ∘e transport (λ w → (w == app= (p ∙ ! q)) 
                      ≃ (ap (λ v → v ∘ f) (λ= H) == p ∙ ! q))
                   (app=-ap f (λ= H) ∙ ap (λ k → k ∘ f) (λ= $ app=-β H))
                   ((equiv-ap app=-equiv _ _)⁻¹)

    e : (Σ (∀ x → g x == h x) (λ r → (r ∘ f) == app= (p ∙ ! q)))
        ≃ ((g , p) == (h , q)) 
    e = ((=Σ-eqv _ _ ∘e equiv-Σ-snd (λ u → (↓-fiber-to-eqv u)⁻¹))
        ∘e (equiv-Σ-fst _ (snd λ=-equiv))) ∘e equiv-Σ-snd lemma
              

conn-intro : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} {h : A → B}
  → (∀ (P : B → n -Type (lmax i j))
     → Σ (Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)) 
         (λ u → ∀ (t : Π A (fst ∘ P ∘ h)) →  (u t ∘ h) == t))
  → is-conn-map n h
conn-intro {A = A} {B = B} {h = h} sec b = 
  let s = sec (λ b → (Trunc _ (Σ A (λ a → h a == b)) , Trunc-level))
  in (fst s (λ a → [ a , idp ]) b , 
      λ kt → Trunc-elim (λ kt → =-preserves-level _ {_} {kt} Trunc-level) 
        (λ k → transport 
                 (λ v → fst s (λ a → [ a , idp ]) (fst v) == [ fst k , snd v ])
                 (snd (pathfrom-is-contr (h (fst k))) (b , snd k)) 
                 (app= (snd s (λ a → [ a , idp ])) (fst k)))
        kt)

abstract
  pointed-conn-in : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → is-conn-map {A = ⊤} n (cst a₀) → is-connected (S n) A
  pointed-conn-in {n = n} A a₀ c =
    ([ a₀ ] , 
     Trunc-elim (λ _ → =-preserves-level _ Trunc-level) 
       (λ a → Trunc-rec (Trunc-level {n = S n} _ _)
             (λ x → ap [_] (snd x)) (fst $ c a)))

abstract
  pointed-conn-out : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → is-connected (S n) A → is-conn-map {A = ⊤} n (cst a₀)
  pointed-conn-out {n = n} A a₀ c a = 
    (point , 
     λ y → ! (cancel point)
           ∙ (ap out $ contr-has-all-paths (=-preserves-level ⟨-2⟩ c) 
                                           (into point) (into y)) 
           ∙ cancel y)
    where 
      into-aux : Trunc n (Σ ⊤ (λ _ → a₀ == a)) → Trunc n (a₀ == a)
      into-aux = Trunc-fmap snd

      into : Trunc n (Σ ⊤ (λ _ → a₀ == a)) 
        → [_] {n = S n} a₀ == [ a ]
      into = <– (Trunc=-equiv [ a₀ ] [ a ]) ∘ into-aux

      out-aux : Trunc n (a₀ == a) → Trunc n (Σ ⊤ (λ _ → a₀ == a)) 
      out-aux = Trunc-fmap (λ p → (tt , p))

      out : [_] {n = S n} a₀ == [ a ] → Trunc n (Σ ⊤ (λ _ → a₀ == a))
      out = out-aux ∘ –> (Trunc=-equiv [ a₀ ] [ a ]) 

      cancel : (x : Trunc n (Σ ⊤ (λ _ → a₀ == a))) → out (into x) == x
      cancel x = 
        out (into x) 
          =⟨ ap out-aux (<–-inv-r (Trunc=-equiv [ a₀ ] [ a ]) (into-aux x)) ⟩
        out-aux (into-aux x)
          =⟨ Trunc-fmap-∘ _ _ x ⟩
        Trunc-fmap (λ q → (tt , (snd q))) x
          =⟨ Trunc-elim {B = λ x → Trunc-fmap (λ q → (tt , snd q)) x == x}
               (λ _ → =-preserves-level n Trunc-level) (λ _ → idp) x ⟩
        x ∎

      point : Trunc n (Σ ⊤ (λ _ → a₀ == a))
      point = out $ contr-has-all-paths c [ a₀ ] [ a ]

Trunc-preserves-conn : ∀ {i} {A : Type i} {n : ℕ₋₂} (m : ℕ₋₂)
  → is-connected n A → is-connected n (Trunc m A)
Trunc-preserves-conn {n = ⟨-2⟩} m c = Trunc-level
Trunc-preserves-conn {A = A} {n = S n} m c = lemma (fst c) (snd c)
  where
  lemma : (x₀ : Trunc (S n) A) → (∀ x → x₀ == x) → is-connected (S n) (Trunc m A)
  lemma = Trunc-elim 
    (λ _ → Π-level (λ _ → Σ-level Trunc-level 
                     (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))))
    (λ a → λ p → ([ [ a ] ] , 
       Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
         (Trunc-elim 
           (λ _ → =-preserves-level _ 
                    (Trunc-preserves-level (S n) Trunc-level))
           (λ x → <– (Trunc=-equiv [ [ a ] ] [ [ x ] ]) 
              (Trunc-fmap (ap [_]) 
                (–> (Trunc=-equiv [ a ] [ x ]) (p [ x ])))))))


{- Suspension of an n-connected space is n+1-connected 
   what is the best place for this?                    -}
abstract
  Susp-conn : ∀ {i} {A : Type i} {n : ℕ₋₂} 
    → is-connected n A → is-connected (S n) (Suspension A)
  Susp-conn {A = A} {n = n} cA = 
    ([ north A ] ,
     Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
       (Suspension-elim A 
         idp 
         (Trunc-rec (Trunc-level {n = S n} _ _)
                    (λ a → ap [_] (merid A a)) 
                    (fst cA))
         (λ x → Trunc-elim
            {B = λ y → idp == 
              Trunc-rec (Trunc-level {n = S n} _ _) (λ a → ap [_] (merid A a)) y
              [ (λ z → [ north A ] == [ z ]) ↓ (merid A x) ]}
            (λ _ → ↓-preserves-level _ (λ _ → Trunc-level {n = S n} _ _))
            (λ x' → <– (↓-fiber-from-eqv (merid A x)) (mers-eq n cA x x'))
            (fst cA))))
    where 
    mers-eq : ∀ {i} {A : Type i} (n : ℕ₋₂) 
      → is-connected n A → (x x' : A)
      → ap ([_] {n = S n}) (merid A x) 
        == Trunc-rec (Trunc-level {n = S n} _ _) 
                     (λ a → ap [_] (merid A a)) [ x' ]
    mers-eq ⟨-2⟩ cA x x' = contr-has-all-paths (Trunc-level {n = ⟨-1⟩} _ _) _ _
    mers-eq {A = A} (S n) cA x x' = 
      conn-elim (pointed-conn-out A x cA) 
        (λ y → ((ap [_] (merid A x) == ap [_] (merid A y)) ,
                Trunc-level {n = S (S n)} _ _ _ _)) 
        (λ _ → idp) x'
