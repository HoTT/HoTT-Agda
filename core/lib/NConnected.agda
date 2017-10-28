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
inhab-conn : ∀ {i} {A : Type i} (a : A) → is-connected -1 A
inhab-conn a = has-level-make ([ a ] , prop-has-all-paths [ a ])

{- connectedness is a prop -}
is-connected-is-prop : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → is-prop (is-connected n A)
is-connected-is-prop = is-contr-is-prop

{- "induction principle" for n-connected maps (where codomain is n-type) -}
abstract
  pre∘-conn-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → {h : A → B} → has-conn-fibers n h
    → (∀ {k} (P : B → n -Type k) → is-equiv (λ (s : Π B (fst ∘ P)) → s ∘ h))
  pre∘-conn-is-equiv {A = A} {B = B} {n = n} {h = h} c P = is-eq f g f-g g-f
    where f : Π B (fst ∘ P) → Π A (fst ∘ P ∘ h)
          f k a = k (h a)

          helper : Π A (fst ∘ P ∘ h)
            → (b : B) → Trunc n (Σ A (λ a → h a == b)) → (fst (P b))
          helper t b r =
            Trunc-rec {{snd (P b)}}
              (λ x → transport (λ y → fst (P y)) (snd x) (t (fst x)))
              r

          g : Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
          g t b = helper t b (contr-center (c b))

          f-g : ∀ t → f (g t) == t
          f-g t = λ= $ λ a → transport
            (λ r →  Trunc-rec {{snd (P (h a))}} _ r == t a)
            (! (contr-path(c (h a)) [ (a , idp) ]))
            idp

          g-f : ∀ k → g (f k) == k
          g-f k = λ= $ λ (b : B) →
            Trunc-elim {{λ r → =-preserves-level {x = helper (k ∘ h) b r} (snd (P b))}}
                       (λ x → lemma (fst x) b (snd x)) (contr-center (c b))
            where
            lemma : ∀ xl → ∀ b → (p : h xl == b) →
              helper (k ∘ h) b [ (xl , p) ] == k b
            lemma xl ._ idp = idp

conn-extend : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  → {h : A → B} → has-conn-fibers n h
  → (P : B → n -Type k)
  → Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
conn-extend c P f = is-equiv.g (pre∘-conn-is-equiv c P) f

conn-out = conn-extend

conn-extend-β : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  {h : A → B} (c : has-conn-fibers n h)
  (P : B → n -Type k) (f : Π A (fst ∘ P ∘ h))
  → ∀ a → (conn-extend c P f (h a)) == f a
conn-extend-β c P f = app= (is-equiv.f-g (pre∘-conn-is-equiv c P) f)


{- generalized "almost induction principle" for maps into ≥n-types
   TODO: rearrange this to use ≤T?                                 -}
conn-extend-general : ∀ {i j} {A : Type i} {B : Type j} {n k : ℕ₋₂}
  → {f : A → B} → has-conn-fibers n f
  → ∀ {l} (P : B → (k +2+ n) -Type l)
  → ∀ t → has-level k (Σ (Π B (fst ∘ P)) (λ s → (s ∘ f) == t))
conn-extend-general {k = ⟨-2⟩} c P t =
  equiv-is-contr-map (pre∘-conn-is-equiv c P) t
conn-extend-general {B = B} {n = n} {k = S k'} {f = f} c P t = has-level-make
  λ {(g , p) (h , q) →
    equiv-preserves-level (e g h p q)
      {{conn-extend-general {k = k'} c (Q g h) (app= (p ∙ ! q))}} }
  where
    Q : (g h : Π B (fst ∘ P)) → B → (k' +2+ n) -Type _
    Q g h b = ((g b == h b) , has-level-apply (snd (P b)) _ _)

    app=-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : B → Type k}
      (f : A → B) {g h : Π B C} (p : g == h)
      → app= (ap (λ k → k ∘ f) p) == (app= p ∘ f)
    app=-ap f idp = idp

    move-right-on-right-econv : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : x == z) (r : y == z)
      → (p == q ∙ ! r) ≃ (p ∙ r == q)
    move-right-on-right-econv {x = x} p idp idp =
      (_ , pre∙-is-equiv (∙-unit-r p))

    lemma : ∀ g h p q → (H : g ∼ h)
      → ((H ∘ f) == app= (p ∙ ! q))
         ≃ (ap (λ v → v ∘ f) (λ= H) ∙ q == p)
    lemma g h p q H =
      move-right-on-right-econv (ap (λ v → v ∘ f) (λ= H)) p q
      ∘e transport (λ w → (w == app= (p ∙ ! q))
                      ≃ (ap (λ v → v ∘ f) (λ= H) == p ∙ ! q))
                   (app=-ap f (λ= H) ∙ ap (λ k → k ∘ f) (λ= $ app=-β H))
                   (ap-equiv app=-equiv _ _ ⁻¹)

    e : ∀ g h p q  →
      (Σ (g ∼ h) (λ r → (r ∘ f) == app= (p ∙ ! q)))
      ≃ ((g , p) == (h , q))
    e g h p q =
      ((=Σ-econv _ _ ∘e Σ-emap-r (λ u → ↓-app=cst-econv ∘e !-equiv))
      ∘e (Σ-emap-l _ λ=-equiv)) ∘e Σ-emap-r (lemma g h p q)


conn-in : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} {h : A → B}
  → (∀ (P : B → n -Type (lmax i j))
     → Σ (Π A (fst ∘ P ∘ h) → Π B (fst ∘ P))
         (λ u → ∀ (t : Π A (fst ∘ P ∘ h)) → u t ∘ h ∼ t))
  → has-conn-fibers n h
conn-in {A = A} {B = B} {h = h} sec b =
  let s = sec (λ b → (Trunc _ (hfiber h b) , Trunc-level))
  in has-level-make (fst s (λ a → [ a , idp ]) b ,
      Trunc-elim (λ k → transport
                   (λ v → fst s (λ a → [ a , idp ]) (fst v) == [ fst k , snd v ])
                   (contr-path (pathfrom-is-contr (h (fst k))) (b , snd k))
                   (snd s (λ a → [ a , idp ]) (fst k))))

abstract
  pointed-conn-in : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → has-conn-fibers {A = ⊤} n (cst a₀) → is-connected (S n) A
  pointed-conn-in {n = n} A a₀ c = has-level-make
    ([ a₀ ] ,
     Trunc-elim
       (λ a → Trunc-rec
             (λ x → ap [_] (snd x)) (contr-center $ c a)))

abstract
  pointed-conn-out : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    {{_ : is-connected (S n) A}} → has-conn-fibers {A = ⊤} n (cst a₀)
  pointed-conn-out {n = n} A a₀ {{c}} a = has-level-make
    (point ,
     λ y → ! (cancel point)
           ∙ (ap out $ contr-has-all-paths (into point) (into y))
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
               (λ _ → idp) x ⟩
        x =∎

      point : Trunc n (Σ ⊤ (λ _ → a₀ == a))
      point = out $ contr-has-all-paths [ a₀ ] [ a ]

prop-over-connected :  ∀ {i j} {A : Type i} {a : A} {{p : is-connected 0 A}}
  → (P : A → hProp j)
  → fst (P a) → Π A (fst ∘ P)
prop-over-connected P x = conn-extend (pointed-conn-out _ _) P (λ _ → x)

{- Connectedness of a truncated type -}
Trunc-preserves-conn : ∀ {i} {A : Type i} {n : ℕ₋₂} (m : ℕ₋₂)
  {{_ : is-connected n A}} → is-connected n (Trunc m A)
Trunc-preserves-conn {n = ⟨-2⟩} m = Trunc-level
Trunc-preserves-conn {A = A} {n = S n} m {{c}} = lemma (contr-center c) (contr-path c)
  where
  lemma : (x₀ : Trunc (S n) A) → (∀ x → x₀ == x) → is-connected (S n) (Trunc m A)
  lemma = Trunc-elim
    (λ a → λ p → has-level-make ([ [ a ] ] ,
       Trunc-elim
         (Trunc-elim
           {{λ _ → =-preserves-level
                    (Trunc-preserves-level (S n) Trunc-level)}}
           (λ x → <– (Trunc=-equiv [ [ a ] ] [ [ x ] ])
              (Trunc-fmap (ap [_])
                (–> (Trunc=-equiv [ a ] [ x ]) (p [ x ])))))))

{- Connectedness of a Σ-type -}
abstract
 instance
  Σ-conn : ∀ {i} {j} {A : Type i} {B : A → Type j} {n : ℕ₋₂}
    → is-connected n A → (∀ a → is-connected n (B a))
    → is-connected n (Σ A B)
  Σ-conn {A = A} {B = B} {n = ⟨-2⟩} cA cB = -2-conn (Σ A B)
  Σ-conn {A = A} {B = B} {n = S m} cA cB =
    Trunc-elim
      {P = λ ta → (∀ tx → ta == tx) → is-connected (S m) (Σ A B)}
      (λ a₀ pA →
        Trunc-elim
          {P = λ tb → (∀ ty → tb == ty) → is-connected (S m) (Σ A B)}
          (λ b₀ pB → has-level-make
            ([ a₀ , b₀ ] ,
              Trunc-elim
                {P = λ tp → [ a₀ , b₀ ] == tp}
                (λ {(r , s) →
                  Trunc-rec
                    (λ pa → Trunc-rec
                      (λ pb → ap [_] (pair= pa (from-transp! B pa pb)))
                      (–> (Trunc=-equiv [ b₀ ] [ transport! B pa s ])
                          (pB [ transport! B pa s ])))
                    (–> (Trunc=-equiv [ a₀ ] [ r ]) (pA [ r ]))})))
          (contr-center (cB a₀)) (contr-path (cB a₀)))
      (contr-center cA) (contr-path cA)

  ×-conn : ∀ {i} {j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → is-connected n A → is-connected n B
    → is-connected n (A × B)
  ×-conn cA cB = Σ-conn cA (λ _ → cB)

{- connectedness of a path space -}
abstract
  path-conn : ∀ {i} {A : Type i} {x y : A} {n : ℕ₋₂}
    → is-connected (S n) A → is-connected n (x == y)
  path-conn {x = x} {y = y} cA =
    equiv-preserves-level (Trunc=-equiv [ x ] [ y ])
      {{has-level-apply (contr-is-prop cA) [ x ] [ y ]}}

{- an n-Type which is n-connected is contractible -}
connected-at-level-is-contr : ∀ {i} {A : Type i} {n : ℕ₋₂}
  {{pA : has-level n A}} {{cA : is-connected n A}} → is-contr A
connected-at-level-is-contr {{pA}} {{cA}} =
  equiv-preserves-level (unTrunc-equiv _) {{cA}}

{- if A is n-connected and m ≤ n, then A is m-connected -}
connected-≤T : ∀ {i} {m n : ℕ₋₂} {A : Type i}
  → m ≤T n → {{_ : is-connected n A}} → is-connected m A
connected-≤T {m = m} {n = n} {A = A} leq =
  transport (λ B → is-contr B)
            (ua (Trunc-fuse A m n) ∙ ap (λ k → Trunc k A) (minT-out-l leq))
            (Trunc-preserves-level m ⟨⟩)

{- Equivalent types have the same connectedness -}
equiv-preserves-conn : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} (e : A ≃ B)
  {{_ : is-connected n A}} → is-connected n B
equiv-preserves-conn {n = n} e = equiv-preserves-level (Trunc-emap n e)

{- Composite of two connected functions is connected -}
∘-conn : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → {n : ℕ₋₂} → (f : A → B) → (g : B → C)
  → has-conn-fibers n f
  → has-conn-fibers n g
  → has-conn-fibers n (g ∘ f)
∘-conn {n = n} f g cf cg =
  conn-in (λ P → conn-extend cg P ∘ conn-extend cf (P ∘ g) , lemma P)
    where
      lemma : ∀ P h x → conn-extend cg P (conn-extend cf (P ∘ g) h) (g (f x)) == h x
      lemma P h x =
        conn-extend cg P (conn-extend cf (P ∘ g) h) (g (f x))
          =⟨ conn-extend-β cg P (conn-extend cf (P ∘ g) h) (f x) ⟩
        conn-extend cf (P ∘ g) h (f x)
          =⟨ conn-extend-β cf (P ∘ g) h x ⟩
        h x
          =∎
