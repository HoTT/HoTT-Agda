{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Paths
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Suspension

module lib.NConnected where

is-connected : ∀ {i} → ℕ₋₂ → Type i → Type i
is-connected n A = is-contr (Trunc n A)

has-conn-fibers : ∀ {i j} {A : Type i} {B : Type j} → ℕ₋₂ → (A → B) → Type (lmax i j)
has-conn-fibers {A = A} {B = B} n f =
  Π B (λ b → is-connected n (hfiber f b))

{- all types are -2-connected -}
-2-conn : ∀ {i} (A : Type i) → is-connected -2 A
-2-conn A = Trunc-level

{- all inhabited types are -1-connected -}
inhab-conn : ∀ {i} (A : Type i) (a : A) → is-connected -1 A
inhab-conn A a = ([ a ] , prop-has-all-paths Trunc-level [ a ])

{- connectedness is a prop -}
is-connected-is-prop : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → is-prop (is-connected n A)
is-connected-is-prop = is-contr-is-prop

-- XXX What is the naming convention?
{- "induction principle" for n-connected maps (where codomain is n-type) -}
abstract
  conn-elim-iseconv : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → {h : A → B} → has-conn-fibers n h
    → (∀ {k} (P : B → n -Type k) → is-equiv (λ (s : Π B (fst ∘ P)) → s ∘ h))
  conn-elim-iseconv {A = A} {B = B} {n = n} {h = h} c P = is-eq f g f-g g-f
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
            where
            lemma : ∀ xl → ∀ b → (p : h xl == b) →
              helper (k ∘ h) b [ (xl , p) ] == k b
            lemma xl ._ idp = idp

conn-elim : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  → {h : A → B} → has-conn-fibers n h
  → (P : B → n -Type k)
  → Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
conn-elim c P f = is-equiv.g (conn-elim-iseconv c P) f

conn-elim-β : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  {h : A → B} (c : has-conn-fibers n h)
  (P : B → n -Type k) (f : Π A (fst ∘ P ∘ h))
  → ∀ a → (conn-elim c P f (h a)) == f a
conn-elim-β c P f = app= (is-equiv.f-g (conn-elim-iseconv c P) f)


{- generalized "almost induction principle" for maps into ≥n-types
   TODO: rearrange this to use ≤T?                                 -}
conn-elim-general : ∀ {i j} {A : Type i} {B : Type j} {n k : ℕ₋₂}
  → {f : A → B} → has-conn-fibers n f
  → ∀ {l} (P : B → (k +2+ n) -Type l)
  → ∀ t → has-level k (Σ (Π B (fst ∘ P)) (λ s → (s ∘ f) == t))
conn-elim-general {k = ⟨-2⟩} c P t =
  equiv-is-contr-map (conn-elim-iseconv c P) t
conn-elim-general {B = B} {n = n} {k = S k'} {f = f} c P t =
  λ {(g , p) (h , q) →
    equiv-preserves-level (e g h p q) $
      conn-elim-general {k = k'} c (Q g h) (app= (p ∙ ! q))}
  where
    Q : (g h : Π B (fst ∘ P)) → B → (k' +2+ n) -Type _
    Q g h b = ((g b == h b) , snd (P b) _ _)

    app=-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : B → Type k}
      (f : A → B) {g h : Π B C} (p : g == h)
      → app= (ap (λ k → k ∘ f) p) == (app= p ∘ f)
    app=-ap f idp = idp

    move-right-on-right-econv : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : x == z) (r : y == z)
      → (p == q ∙ ! r) ≃ (p ∙ r == q)
    move-right-on-right-econv {x = x} p idp idp =
      (_ , pre∙-is-equiv (∙-unit-r p))

    lemma : ∀ g h p q → (H : ∀ x → g x == h x)
      → ((H ∘ f) == app= (p ∙ ! q))
         ≃ (ap (λ v → v ∘ f) (λ= H) ∙ q == p)
    lemma g h p q H =
      move-right-on-right-econv (ap (λ v → v ∘ f) (λ= H)) p q
      ∘e transport (λ w → (w == app= (p ∙ ! q))
                      ≃ (ap (λ v → v ∘ f) (λ= H) == p ∙ ! q))
                   (app=-ap f (λ= H) ∙ ap (λ k → k ∘ f) (λ= $ app=-β H))
                   (ap-equiv app=-equiv _ _ ⁻¹)

    e : ∀ g h p q  →
      (Σ (∀ x → g x == h x) (λ r → (r ∘ f) == app= (p ∙ ! q)))
      ≃ ((g , p) == (h , q))
    e g h p q =
      ((=Σ-econv _ _ ∘e Σ-emap-r (λ u → ↓-app=cst-econv ∘e !-equiv))
      ∘e (Σ-emap-l _ λ=-equiv)) ∘e Σ-emap-r (lemma g h p q)


conn-intro : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} {h : A → B}
  → (∀ (P : B → n -Type (lmax i j))
     → Σ (Π A (fst ∘ P ∘ h) → Π B (fst ∘ P))
         (λ u → ∀ (t : Π A (fst ∘ P ∘ h)) → ∀ x → (u t ∘ h) x == t x))
  → has-conn-fibers n h
conn-intro {A = A} {B = B} {h = h} sec b =
  let s = sec (λ b → (Trunc _ (hfiber h b) , Trunc-level))
  in (fst s (λ a → [ a , idp ]) b ,
      λ kt → Trunc-elim (λ kt → =-preserves-level _ {_} {kt} Trunc-level)
        (λ k → transport
                 (λ v → fst s (λ a → [ a , idp ]) (fst v) == [ fst k , snd v ])
                 (snd (pathfrom-is-contr (h (fst k))) (b , snd k))
                 (snd s (λ a → [ a , idp ]) (fst k)))
        kt)

abstract
  pointed-conn-in : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → has-conn-fibers {A = ⊤} n (cst a₀) → is-connected (S n) A
  pointed-conn-in {n = n} A a₀ c =
    ([ a₀ ] ,
     Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
       (λ a → Trunc-rec (Trunc-level {n = S n} _ _)
             (λ x → ap [_] (snd x)) (fst $ c a)))

abstract
  pointed-conn-out : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → is-connected (S n) A → has-conn-fibers {A = ⊤} n (cst a₀)
  pointed-conn-out {n = n} A a₀ c a =
    (point ,
     λ y → ! (cancel point)
           ∙ (ap out $ contr-has-all-paths (=-preserves-level -2 c)
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
          =⟨ Trunc-elim {P = λ x → Trunc-fmap (λ q → (tt , snd q)) x == x}
               (λ _ → =-preserves-level n Trunc-level) (λ _ → idp) x ⟩
        x =∎

      point : Trunc n (Σ ⊤ (λ _ → a₀ == a))
      point = out $ contr-has-all-paths c [ a₀ ] [ a ]

prop-over-connected :  ∀ {i j} {A : Type i} {a : A} (p : is-connected 0 A)
  → (P : A → hProp j)
  → fst (P a) → Π A (fst ∘ P)
prop-over-connected p P x = conn-elim (pointed-conn-out _ _ p) P (λ _ → x)

{- Connectedness of a truncated type -}
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

{- Connectedness of a Σ-type -}
abstract
  Σ-conn : ∀ {i} {j} {A : Type i} {B : A → Type j} {n : ℕ₋₂}
    → is-connected n A → (∀ a → is-connected n (B a))
    → is-connected n (Σ A B)
  Σ-conn {A = A} {B = B} {n = ⟨-2⟩} cA cB = -2-conn (Σ A B)
  Σ-conn {A = A} {B = B} {n = S m} cA cB =
    Trunc-elim
      {P = λ ta → (∀ tx → ta == tx) → is-connected (S m) (Σ A B)}
      (λ _ → Π-level (λ _ → prop-has-level-S is-contr-is-prop))
      (λ a₀ pA →
        Trunc-elim
          {P = λ tb → (∀ ty → tb == ty) → is-connected (S m) (Σ A B)}
          (λ _ → Π-level (λ _ → prop-has-level-S is-contr-is-prop))
          (λ b₀ pB →
            ([ a₀ , b₀ ] ,
              Trunc-elim
                {P = λ tp → [ a₀ , b₀ ] == tp}
                (λ _ → =-preserves-level _ Trunc-level)
                (λ {(r , s) →
                  Trunc-rec (Trunc-level {n = S m} _ _)
                    (λ pa → Trunc-rec (Trunc-level {n = S m} _ _)
                      (λ pb → ap [_] (pair= pa (from-transp! B pa pb)))
                      (–> (Trunc=-equiv [ b₀ ] [ transport! B pa s ])
                          (pB [ transport! B pa s ])))
                    (–> (Trunc=-equiv [ a₀ ] [ r ]) (pA [ r ]))})))
          (fst (cB a₀)) (snd (cB a₀)))
      (fst cA) (snd cA)

  ×-conn : ∀ {i} {j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → is-connected n A → is-connected n B
    → is-connected n (A × B)
  ×-conn cA cB = Σ-conn cA (λ _ → cB)

{- Suspension of an n-connected space is n+1-connected
   what is the best place for this?                    -}
abstract
  Susp-conn : ∀ {i} {A : Type i} {n : ℕ₋₂}
    → is-connected n A → is-connected (S n) (Susp A)
  Susp-conn {A = A} {n = n} cA =
    ([ north ] ,
     Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
       (Susp-elim
         idp
         (Trunc-rec (Trunc-level {n = S n} _ _)
                    (λ a → ap [_] (merid a))
                    (fst cA))
         (λ x → Trunc-elim
            {P = λ y → idp ==
              Trunc-rec (Trunc-level {n = S n} _ _) (λ a → ap [_] (merid a)) y
              [ (λ z → [ north ] == [ z ]) ↓ (merid x) ]}
            (λ _ → ↓-preserves-level _ (Trunc-level {n = S n} _ _))
            (λ x' → ↓-cst=app-in (∙'-unit-l _ ∙ mers-eq n cA x x'))
            (fst cA))))
    where
    mers-eq : ∀ {i} {A : Type i} (n : ℕ₋₂)
      → is-connected n A → (x x' : A)
      → ap ([_] {n = S n}) (merid x)
        == Trunc-rec (Trunc-level {n = S n} _ _)
                     (λ a → ap [_] (merid a)) [ x' ]
    mers-eq ⟨-2⟩ cA x x' = contr-has-all-paths (Trunc-level {n = -1} _ _) _ _
    mers-eq {A = A} (S n) cA x x' =
      conn-elim (pointed-conn-out A x cA)
        (λ y → ((ap [_] (merid x) == ap [_] (merid y)) ,
                Trunc-level {n = S (S n)} _ _ _ _))
        (λ _ → idp) x'

{- connectedness of a path space -}
abstract
  path-conn : ∀ {i} {A : Type i} {x y : A} {n : ℕ₋₂}
    → is-connected (S n) A → is-connected n (x == y)
  path-conn {x = x} {y = y} cA =
    equiv-preserves-level (Trunc=-equiv [ x ] [ y ])
      (contr-is-prop cA [ x ] [ y ])

{- an n-Type which is n-connected is contractible -}
connected-at-level-is-contr : ∀ {i} {A : Type i} {n : ℕ₋₂}
  → has-level n A → is-connected n A → is-contr A
connected-at-level-is-contr pA cA =
  equiv-preserves-level (unTrunc-equiv _ pA) cA

{- if A is n-connected and m ≤ n, then A is m-connected -}
connected-≤T : ∀ {i} {m n : ℕ₋₂} {A : Type i}
  → m ≤T n → is-connected n A → is-connected m A
connected-≤T {m = m} {n = n} {A = A} leq cA =
  transport (λ B → is-contr B)
            (ua (Trunc-fuse A m n) ∙ ap (λ k → Trunc k A) (minT-out-l leq))
            (Trunc-preserves-level m cA)

{- Equivalent types have the same connectedness -}
equiv-preserves-conn : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} (e : A ≃ B)
  → (is-connected n A → is-connected n B)
equiv-preserves-conn {n = n} e = equiv-preserves-level (Trunc-emap n e)

{- Composite of two connected functions is connected -}
∘-conn : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → {n : ℕ₋₂} → (f : A → B) → (g : B → C)
  → has-conn-fibers n f
  → has-conn-fibers n g
  → has-conn-fibers n (g ∘ f)
∘-conn {n = n} f g cf cg =
  conn-intro (λ P → conn-elim cg P ∘ conn-elim cf (P ∘ g) , lemma P)
    where
      lemma : ∀ P h x → conn-elim cg P (conn-elim cf (P ∘ g) h) (g (f x)) == h x
      lemma P h x =
        conn-elim cg P (conn-elim cf (P ∘ g) h) (g (f x))
          =⟨ conn-elim-β cg P (conn-elim cf (P ∘ g) h) (f x) ⟩
        conn-elim cf (P ∘ g) h (f x)
          =⟨ conn-elim-β cf (P ∘ g) h x ⟩
        h x
          =∎
