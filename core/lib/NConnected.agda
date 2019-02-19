{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2
open import lib.path-seq.Rotations
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Pointed
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
inhab-conn a = has-level-in ([ a ] , prop-has-all-paths [ a ])

{- connectedness is a prop -}
is-connected-is-prop : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → is-prop (is-connected n A)
is-connected-is-prop = is-contr-is-prop

{- "induction principle" for n-connected maps (where codomain is n-type) -}
module ConnExtend {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
                  {h : A → B} (c : has-conn-fibers n h)
                  (P : B → n -Type k) where

  private
    helper : Π A (fst ∘ P ∘ h)
      → (b : B) → Trunc n (Σ A (λ a → h a == b)) → (fst (P b))
    helper t b r =
      Trunc-rec {{snd (P b)}}
        (λ x → transport (λ y → fst (P y)) (snd x) (t (fst x)))
        r

  restr : Π B (fst ∘ P) → Π A (fst ∘ P ∘ h)
  restr t = t ∘ h

  abstract
    ext : Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
    ext f b = helper f b (contr-center (c b))

  private
    abstract
      ext-β' : (f : Π A (fst ∘ P ∘ h)) (a : A) → restr (ext f) a == f a
      ext-β' f a =
        transport
          (λ r →  Trunc-rec {{snd (P (h a))}} _ r == f a)
          (! (contr-path(c (h a)) [ (a , idp) ]))
          idp

  abstract
    restr-β : (t : Π B (fst ∘ P)) (b : B) → ext (restr t) b == t b
    restr-β t b =
      Trunc-elim
        {{λ r → =-preserves-level {x = helper (t ∘ h) b r} (snd (P b))}}
        (λ x → lemma (fst x) b (snd x))
        (contr-center (c b))
      where
      lemma : ∀ xl → ∀ b → (p : h xl == b) →
        helper (t ∘ h) b [ (xl , p) ] == t b
      lemma xl ._ idp = idp

  restr-is-equiv : is-equiv restr
  restr-is-equiv = is-eq restr ext (λ= ∘ ext-β') (λ= ∘ restr-β)

  restr-equiv : Π B (fst ∘ P) ≃ Π A (fst ∘ P ∘ h)
  restr-equiv = restr , restr-is-equiv

  ext-β : (f : Π A (fst ∘ P ∘ h)) (a : A) → restr (ext f) a == f a
  ext-β f = app= (is-equiv.f-g restr-is-equiv f)

  abstract
    restr-β-ext-β-adj : (t : Π B (fst ∘ P)) (a : A)
      → ext-β (restr t) a == restr-β t (h a)
    restr-β-ext-β-adj t a =
      ext-β (restr t) a
        =⟨ ! (ap (λ s → app= s a) (is-equiv.adj restr-is-equiv t)) ⟩
      app= (ap restr (λ= (restr-β t))) a
        =⟨ ∘-ap (_$ a) restr (λ= (restr-β t)) ⟩
      app= (λ= (restr-β t)) (h a)
        =⟨ app=-β (restr-β t) (h a) ⟩
      restr-β t (h a) =∎

open ConnExtend using () renaming
  (ext to conn-extend;
   ext-β to conn-extend-β;
   restr-is-equiv to pre∘-conn-is-equiv) public

module ⊙ConnExtend {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {n : ℕ₋₂}
                   (h : X ⊙→ Y) (c : has-conn-fibers n (fst h))
                   (Z-level : has-level n (de⊙ Z)) where

  open ConnExtend c (λ _ → de⊙ Z , Z-level) public

  ⊙restr : Y ⊙→ Z → X ⊙→ Z
  ⊙restr = _⊙∘ h

  ext-pt-seq : (f : X ⊙→ Z) → ext (fst f) (pt Y) =-= pt Z
  ext-pt-seq f =
    ext (fst f) (pt Y)
      =⟪ ! (ap (ext (fst f)) (snd h)) ⟫
    ext (fst f) (fst h (pt X))
      =⟪ ext-β (fst f) (pt X) ⟫
    fst f (pt X)
      =⟪ snd f ⟫
    pt Z ∎∎

  ext-pt : (f : X ⊙→ Z) → ext (fst f) (pt Y) == pt Z
  ext-pt f = ↯ (ext-pt-seq f)

  ⊙ext : X ⊙→ Z → Y ⊙→ Z
  ⊙ext f = ext (fst f) , ext-pt f

  abstract
    ⊙ext-β : (f : X ⊙→ Z) → ⊙restr (⊙ext f) == f
    ⊙ext-β f =
      ⊙λ=' (ext-β (fst f)) $
      ↓-idf=cst-in $ =ₛ-out $
      ap (fst (⊙ext f)) (snd h) ◃∙ ext-pt-seq f
        =ₛ⟨ 0 & 2 & seq-!-inv-r (ap (fst (⊙ext f)) (snd h) ◃∎) ⟩
      ext-β (fst f) (pt X) ◃∙ snd f ◃∎ ∎ₛ

    ⊙restr-β : (t : Y ⊙→ Z) → ⊙ext (⊙restr t) == t
    ⊙restr-β t =
      ⊙λ=' (restr-β (fst t)) $
      ↓-idf=cst-in $ =ₛ-out $
      ext-pt-seq (⊙restr t)
        =ₛ₁⟨ 1 & 1 & restr-β-ext-β-adj (fst t) (pt X) ⟩
      ! (ap (ext (fst (⊙restr t))) (snd h)) ◃∙
      restr-β (fst t) (fst h (pt X)) ◃∙
      snd (⊙restr t) ◃∎
        =ₛ⟨ 2 & 1 & expand (ap (fst t) (snd h) ◃∙ snd t ◃∎) ⟩
      ! (ap (ext (fst (⊙restr t))) (snd h)) ◃∙
      restr-β (fst t) (fst h (pt X)) ◃∙
      ap (fst t) (snd h) ◃∙
      snd t ◃∎
        =ₛ⟨ 0 & 3 & !ₛ $ pre-rotate-in $
            homotopy-naturality
              (ext (fst (⊙restr t)))
              (fst t)
              (restr-β (fst t))
              (snd h) ⟩
      restr-β (fst t) (pt Y) ◃∙ snd t ◃∎ ∎ₛ

  ⊙restr-is-equiv : is-equiv ⊙restr
  ⊙restr-is-equiv = is-eq ⊙restr ⊙ext ⊙ext-β ⊙restr-β

  ⊙restr-equiv : (Y ⊙→ Z) ≃ (X ⊙→ Z)
  ⊙restr-equiv = ⊙restr , ⊙restr-is-equiv

open ⊙ConnExtend using () renaming
  (⊙ext to ⊙conn-extend;
   ⊙restr-is-equiv to pre⊙∘-conn-is-equiv) public

{- generalized "almost induction principle" for maps into ≥n-types
   TODO: rearrange this to use ≤T?                                 -}
conn-extend-general : ∀ {i j} {A : Type i} {B : Type j} {n k : ℕ₋₂}
  → {f : A → B} → has-conn-fibers n f
  → ∀ {l} (P : B → (k +2+ n) -Type l)
  → ∀ t → has-level k (Σ (Π B (fst ∘ P)) (λ s → (s ∘ f) == t))
conn-extend-general {k = ⟨-2⟩} c P t =
  equiv-is-contr-map (pre∘-conn-is-equiv c P) t
conn-extend-general {B = B} {n = n} {k = S k'} {f = f} c P t = has-level-in
  λ {(g , p) (h , q) →
    equiv-preserves-level (e g h p q)
      {{conn-extend-general {k = k'} c (Q g h) (app= (p ∙ ! q))}} }
  where
    Q : (g h : Π B (fst ∘ P)) → B → (k' +2+ n) -Type _
    Q g h b = ((g b == h b) , has-level-apply (snd (P b)) _ _)

    app=-pre∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : B → Type k}
      (f : A → B) {g h : Π B C} (p : g == h)
      → app= (ap (λ k → k ∘ f) p) == app= p ∘ f
    app=-pre∘ f idp = idp

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
                   (app=-pre∘ f (λ= H) ∙ ap (λ k → k ∘ f) (λ= $ app=-β H))
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
  in has-level-in (fst s (λ a → [ a , idp ]) b ,
      Trunc-elim (λ k → transport
                   (λ v → fst s (λ a → [ a , idp ]) (fst v) == [ fst k , snd v ])
                   (contr-path (pathfrom-is-contr (h (fst k))) (b , snd k))
                   (snd s (λ a → [ a , idp ]) (fst k))))

abstract
  pointed-conn-in : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → has-conn-fibers {A = ⊤} n (cst a₀) → is-connected (S n) A
  pointed-conn-in {n = n} A a₀ c = has-level-in
    ([ a₀ ] ,
     Trunc-elim
       (λ a → Trunc-rec
             (λ x → ap [_] (snd x)) (contr-center $ c a)))

abstract
  pointed-conn-out : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    {{_ : is-connected (S n) A}} → has-conn-fibers {A = ⊤} n (cst a₀)
  pointed-conn-out {n = n} A a₀ {{c}} a = has-level-in
    (point ,
     λ y → ! (cancel point)
           ∙ (ap out $ contr-has-all-paths (into point) (into y))
           ∙ cancel y)
    where
      into-aux : Trunc n (Σ ⊤ (λ _ → a₀ == a)) → Trunc n (a₀ == a)
      into-aux = Trunc-fmap snd

      into : Trunc n (Σ ⊤ (λ _ → a₀ == a))
        → [_] {n = S n} a₀ == [ a ]
      into = <– (=ₜ-equiv [ a₀ ] [ a ]) ∘ into-aux

      out-aux : Trunc n (a₀ == a) → Trunc n (Σ ⊤ (λ _ → a₀ == a))
      out-aux = Trunc-fmap (λ p → (tt , p))

      out : [_] {n = S n} a₀ == [ a ] → Trunc n (Σ ⊤ (λ _ → a₀ == a))
      out = out-aux ∘ –> (=ₜ-equiv [ a₀ ] [ a ])

      cancel : (x : Trunc n (Σ ⊤ (λ _ → a₀ == a))) → out (into x) == x
      cancel x =
        out (into x)
          =⟨ ap out-aux (<–-inv-r (=ₜ-equiv [ a₀ ] [ a ]) (into-aux x)) ⟩
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
instance
  Trunc-preserves-conn : ∀ {i} {A : Type i} {n : ℕ₋₂} {m : ℕ₋₂}
    → is-connected n A → is-connected n (Trunc m A)
  Trunc-preserves-conn {n = ⟨-2⟩} _ = Trunc-level
  Trunc-preserves-conn {A = A} {n = S n} {m} c = lemma (contr-center c) (contr-path c)
    where
    lemma : (x₀ : Trunc (S n) A) → (∀ x → x₀ == x) → is-connected (S n) (Trunc m A)
    lemma = Trunc-elim
      (λ a → λ p → has-level-in ([ [ a ] ] ,
        Trunc-elim
          (Trunc-elim
            {{λ _ → =-preserves-level
                      (Trunc-preserves-level (S n) Trunc-level)}}
            (λ x → <– (=ₜ-equiv [ [ a ] ] [ [ x ] ])
               (Trunc-fmap (ap [_])
                 (–> (=ₜ-equiv [ a ] [ x ]) (p [ x ])))))))

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
          (λ b₀ pB → has-level-in
            ([ a₀ , b₀ ] ,
              Trunc-elim
                {P = λ tp → [ a₀ , b₀ ] == tp}
                (λ {(r , s) →
                  Trunc-rec
                    (λ pa → Trunc-rec
                      (λ pb → ap [_] (pair= pa (from-transp! B pa pb)))
                      (–> (=ₜ-equiv [ b₀ ] [ transport! B pa s ])
                          (pB [ transport! B pa s ])))
                    (–> (=ₜ-equiv [ a₀ ] [ r ]) (pA [ r ]))})))
          (contr-center (cB a₀)) (contr-path (cB a₀)))
      (contr-center cA) (contr-path cA)

  ×-conn : ∀ {i} {j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → is-connected n A → is-connected n B
    → is-connected n (A × B)
  ×-conn cA cB = Σ-conn cA (λ _ → cB)

{- connectedness of a path space -}
abstract
 instance
  path-conn : ∀ {i} {A : Type i} {x y : A} {n : ℕ₋₂}
    → is-connected (S n) A → is-connected n (x == y)
  path-conn {x = x} {y = y} cA =
    equiv-preserves-level (=ₜ-equiv [ x ] [ y ])
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
  transport is-contr (ua (Trunc-fuse-≤ A leq)) (Trunc-preserves-level m ⟨⟩)

{- Equivalent types have the same connectedness -}
equiv-preserves-conn : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} (e : A ≃ B)
  {{_ : is-connected n A}} → is-connected n B
equiv-preserves-conn {n = n} e = equiv-preserves-level (Trunc-emap e)

trunc-proj-conn : ∀ {i} (A : Type i) (n : ℕ₋₂)
  → has-conn-fibers n ([_] {n = n} {A = A})
trunc-proj-conn A n =
  conn-in $ λ P →
  Trunc-elim {P = fst ∘ P} {{snd ∘ P}} , λ t a → idp

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
