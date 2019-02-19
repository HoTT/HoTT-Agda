{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Sigma where

-- pointed [Σ]
⊙Σ : ∀ {i j} (X : Ptd i) → (de⊙ X → Ptd j) → Ptd (lmax i j)
⊙Σ ⊙[ A , a₀ ] Y = ⊙[ Σ A (de⊙ ∘ Y) , (a₀ , pt (Y a₀)) ]

-- Cartesian product
_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A × B = Σ A (λ _ → B)

_⊙×_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙× Y = ⊙Σ X (λ _ → Y)

infixr 80 _×_ _⊙×_

-- XXX Do we really need two versions of [⊙fst]?
⊙fstᵈ : ∀ {i j} {X : Ptd i} (Y : de⊙ X → Ptd j) → ⊙Σ X Y ⊙→ X
⊙fstᵈ Y = fst , idp

⊙fst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → X ⊙× Y ⊙→ X
⊙fst = ⊙fstᵈ _

⊙snd : ∀ {i j} {X : Ptd i} {Y : Ptd j} → X ⊙× Y ⊙→ Y
⊙snd = (snd , idp)

fanout : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → (A → B) → (A → C) → (A → B × C)
fanout f g x = f x , g x

⊙fanout-pt : ∀ {i j} {A : Type i} {B : Type j}
  {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
  → (a₀ , b₀) == (a₁ , b₁) :> A × B
⊙fanout-pt = pair×=

⊙fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → X ⊙→ Y → X ⊙→ Z → X ⊙→ Y ⊙× Z
⊙fanout (f , fpt) (g , gpt) = fanout f g , ⊙fanout-pt fpt gpt

diag : ∀ {i} {A : Type i} → (A → A × A)
diag a = a , a

⊙diag : ∀ {i} {X : Ptd i} → X ⊙→ X ⊙× X
⊙diag = ((λ x → (x , x)) , idp)

⊙×-inl : ∀ {i j} (X : Ptd i) (Y : Ptd j) → X ⊙→ X ⊙× Y
⊙×-inl X Y = (λ x → x , pt Y) , idp

⊙×-inr : ∀ {i j} (X : Ptd i) (Y : Ptd j) → Y ⊙→ X ⊙× Y
⊙×-inr X Y = (λ y → pt X , y) , idp

⊙fst-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Y) (g : X ⊙→ Z)
  → ⊙fst ⊙∘ ⊙fanout f g == f
⊙fst-fanout (f , idp) (g , idp) = idp

⊙snd-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Y) (g : X ⊙→ Z)
  → ⊙snd ⊙∘ ⊙fanout f g == g
⊙snd-fanout (f , idp) (g , idp) = idp

⊙fanout-pre∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : Y ⊙→ Z) (g : Y ⊙→ W) (h : X ⊙→ Y)
  → ⊙fanout f g ⊙∘ h == ⊙fanout (f ⊙∘ h) (g ⊙∘ h)
⊙fanout-pre∘ (f , idp) (g , idp) (h , idp) = idp

module _ {i j} {A : Type i} {B : A → Type j} where

  pair : (a : A) (b : B a) → Σ A B
  pair a b = (a , b)

  -- pair= has already been defined

  fst= : {ab a'b' : Σ A B} (p : ab == a'b') → (fst ab == fst a'b')
  fst= = ap fst

  snd= : {ab a'b' : Σ A B} (p : ab == a'b')
    → (snd ab == snd a'b' [ B ↓ fst= p ])
  snd= {._} {_} idp = idp

  fst=-β : {a a' : A} (p : a == a')
    {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ])
    → fst= (pair= p q) == p
  fst=-β idp idp = idp

  snd=-β : {a a' : A} (p : a == a')
    {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ])
    → snd= (pair= p q) == q [ (λ v → b == b' [ B ↓ v ]) ↓ fst=-β p q ]
  snd=-β idp idp = idp

  pair=-η : {ab a'b' : Σ A B} (p : ab == a'b')
    → p == pair= (fst= p) (snd= p)
  pair=-η {._} {_} idp = idp

  pair== : {a a' : A} {p p' : a == a'} (α : p == p')
           {b : B a} {b' : B a'} {q : b == b' [ B ↓ p ]} {q' : b == b' [ B ↓ p' ]}
           (β : q == q' [ (λ u → b == b' [ B ↓ u ]) ↓ α ])
    → pair= p q == pair= p' q'
  pair== idp idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  fst×= : {ab a'b' : A × B} (p : ab == a'b') → (fst ab == fst a'b')
  fst×= = ap fst

  snd×= : {ab a'b' : A × B} (p : ab == a'b')
    → (snd ab == snd a'b')
  snd×= = ap snd

  fst×=-β : {a a' : A} (p : a == a')
    {b b' : B} (q : b == b')
    → fst×= (pair×= p q) == p
  fst×=-β idp idp = idp

  snd×=-β : {a a' : A} (p : a == a')
    {b b' : B} (q : b == b')
    → snd×= (pair×= p q) == q
  snd×=-β idp idp = idp

  pair×=-η : {ab a'b' : A × B} (p : ab == a'b')
    → p == pair×= (fst×= p) (snd×= p)
  pair×=-η {._} {_} idp = idp

module _ {i j} {A : Type i} {B : A → Type j} where

  =Σ : (x y : Σ A B) → Type (lmax i j)
  =Σ (a , b) (a' , b') = Σ (a == a') (λ p → b == b' [ B ↓ p ])

  =Σ-econv : (x y : Σ A B) →  (=Σ x y) ≃ (x == y)
  =Σ-econv x y =
    equiv (λ pq → pair= (fst pq) (snd pq)) (λ p → fst= p , snd= p)
          (λ p → ! (pair=-η p))
          (λ pq → pair= (fst=-β (fst pq) (snd pq)) (snd=-β (fst pq) (snd pq)))

  =Σ-conv : (x y : Σ A B) → (=Σ x y) == (x == y)
  =Σ-conv x y = ua (=Σ-econv x y)

Σ= : ∀ {i j} {A A' : Type i} (p : A == A') {B : A → Type j} {B' : A' → Type j}
  (q : B == B' [ (λ X → (X → Type j)) ↓ p ]) → Σ A B == Σ A' B'
Σ= idp idp = idp

instance
  Σ-level : ∀ {i j} {n : ℕ₋₂} {A : Type i} {P : A → Type j}
    → has-level n A → ((x : A) → has-level n (P x))
      → has-level n (Σ A P)
  Σ-level {n = ⟨-2⟩} p q = has-level-in ((contr-center p , (contr-center (q (contr-center p)))) , lemma)
    where abstract lemma = λ y → pair= (contr-path p _) (from-transp! _ _ (contr-path (q _) _))
  Σ-level {n = S n} p q = has-level-in lemma where
    abstract
      lemma = λ x y → equiv-preserves-level (=Σ-econv x y)
        {{Σ-level (has-level-apply p _ _) (λ _ →
          equiv-preserves-level ((to-transp-equiv _ _)⁻¹) {{has-level-apply (q _) _ _}})}}

×-level : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j}
  → (has-level n A → has-level n B → has-level n (A × B))
×-level pA pB = Σ-level pA (λ x → pB)

-- Equivalences in a Σ-type

Σ-fmap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k)
  → (f : A → B) → (Σ A (P ∘ f) → Σ B P)
Σ-fmap-l P f (a , r) = (f a , r)

×-fmap-l : ∀ {i₀ i₁ j} {A₀ : Type i₀} {A₁ : Type i₁} (B : Type j)
  → (f : A₀ → A₁) → (A₀ × B → A₁ × B)
×-fmap-l B = Σ-fmap-l (λ _ → B)

Σ-isemap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k) {h : A → B}
  → is-equiv h → is-equiv (Σ-fmap-l P h)
Σ-isemap-l {A = A} {B = B} P {h} e = is-eq _ g f-g g-f
  where f = Σ-fmap-l P h

        g : Σ B P → Σ A (P ∘ h)
        g (b , s) = (is-equiv.g e b , transport P (! (is-equiv.f-g e b)) s)

        f-g : ∀ y → f (g y) == y
        f-g (b , s) = pair= (is-equiv.f-g e b) (transp-↓ P (is-equiv.f-g e b) s)

        g-f : ∀ x → g (f x) == x
        g-f (a , r) =
          pair= (is-equiv.g-f e a)
                (transport (λ q → transport P (! q) r == r [ P ∘ h ↓ is-equiv.g-f e a ])
                           (is-equiv.adj e a)
                           (transp-ap-↓ P h (is-equiv.g-f e a) r))

×-isemap-l : ∀ {i₀ i₁ j} {A₀ : Type i₀} {A₁ : Type i₁} (B : Type j) {h : A₀ → A₁}
  → is-equiv h → is-equiv (×-fmap-l B h)
×-isemap-l B = Σ-isemap-l (λ _ → B)

Σ-emap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k)
  → (e : A ≃ B) → (Σ A (P ∘ –> e) ≃ Σ B P)
Σ-emap-l P (f , e) = _ , Σ-isemap-l P e

×-emap-l : ∀ {i₀ i₁ j} {A₀ : Type i₀} {A₁ : Type i₁} (B : Type j)
  → (e : A₀ ≃ A₁) → (A₀ × B ≃ A₁ × B)
×-emap-l B = Σ-emap-l (λ _ → B)

Σ-fmap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  → (∀ x → B x → C x) → (Σ A B → Σ A C)
Σ-fmap-r h (a , b) = (a , h a b)

×-fmap-r : ∀ {i j₀ j₁} (A : Type i) {B₀ : Type j₀} {B₁ : Type j₁}
  → (h : B₀ → B₁) → (A × B₀ → A × B₁)
×-fmap-r A h = Σ-fmap-r (λ _ → h)

Σ-isemap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  {h : ∀ x → B x → C x} → (∀ x → is-equiv (h x)) → is-equiv (Σ-fmap-r h)
Σ-isemap-r {A = A} {B = B} {C = C} {h} k = is-eq _ g f-g g-f
  where f = Σ-fmap-r h

        g : Σ A C → Σ A B
        g (a , c) = (a , is-equiv.g (k a) c)

        f-g : ∀ p → f (g p) == p
        f-g (a , c) = pair= idp (is-equiv.f-g (k a) c)

        g-f : ∀ p → g (f p) == p
        g-f (a , b) = pair= idp (is-equiv.g-f (k a) b)

×-isemap-r : ∀ {i j₀ j₁} (A : Type i) {B₀ : Type j₀} {B₁ : Type j₁}
  → {h : B₀ → B₁} → is-equiv h → is-equiv (×-fmap-r A h)
×-isemap-r A e = Σ-isemap-r (λ _ → e)

Σ-emap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  → (∀ x → B x ≃ C x) → (Σ A B ≃ Σ A C)
Σ-emap-r k = _ , Σ-isemap-r (λ x → snd (k x))

×-emap-r : ∀ {i j₀ j₁} (A : Type i) {B₀ : Type j₀} {B₁ : Type j₁}
  → (e : B₀ ≃ B₁) → (A × B₀ ≃ A × B₁)
×-emap-r A e = Σ-emap-r (λ _ → e)

hfiber-Σ-fmap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  → (h : ∀ x → B x → C x) → {a : A} → (c : C a)
  → hfiber (Σ-fmap-r h) (a , c) ≃ hfiber (h a) c
hfiber-Σ-fmap-r h {a} c = equiv to from to-from from-to

  where to : hfiber (Σ-fmap-r h) (a , c) → hfiber (h a) c
        to ((_ , b) , idp) = b , idp

        from : hfiber (h a) c → hfiber (Σ-fmap-r h) (a , c)
        from (b , idp) = (a , b) , idp

        abstract
          to-from : (x : hfiber (h a) c) → to (from x) == x
          to-from (b , idp) = idp

          from-to : (x : hfiber (Σ-fmap-r h) (a , c)) → from (to x) == x
          from-to ((_ , b) , idp) = idp

{-
-- 2016/08/20 favonia: no one is using the following two functions.

-- Two ways of simultaneously applying equivalences in each component.
module _ {i₀ i₁ j₀ j₁} {A₀ : Type i₀} {A₁ : Type i₁}
         {B₀ : A₀ → Type j₀} {B₁ : A₁ → Type j₁} where
  Σ-emap : (u : A₀ ≃ A₁) (v : ∀ a → B₀ (<– u a) ≃ B₁ a) → Σ A₀ B₀ ≃ Σ A₁ B₁
  Σ-emap u v = Σ A₀ B₀           ≃⟨ Σ-emap-l _ (u ⁻¹) ⁻¹ ⟩
               Σ A₁ (B₀ ∘ <– u)  ≃⟨ Σ-emap-r v ⟩
               Σ A₁ B₁           ≃∎

  Σ-emap' : (u : A₀ ≃ A₁) (v : ∀ a → B₀ a ≃ B₁ (–> u a)) → Σ A₀ B₀ ≃ Σ A₁ B₁
  Σ-emap' u v = Σ A₀ B₀           ≃⟨ Σ-emap-r v ⟩
                Σ A₀ (B₁ ∘ –> u)  ≃⟨ Σ-emap-l _ u ⟩
                Σ A₁ B₁           ≃∎
-}

×-fmap : ∀ {i₀ i₁ j₀ j₁} {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  → (h : A₀ → A₁) (k : B₀ → B₁) → (A₀ × B₀ → A₁ × B₁)
×-fmap u v = ×-fmap-r _ v ∘ ×-fmap-l _ u

⊙×-fmap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → X ⊙→ X' → Y ⊙→ Y' → X ⊙× Y ⊙→ X' ⊙× Y'
⊙×-fmap (f , fpt) (g , gpt) = ×-fmap f g , pair×= fpt gpt

×-isemap : ∀ {i₀ i₁ j₀ j₁} {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {h : A₀ → A₁} {k : B₀ → B₁} → is-equiv h → is-equiv k → is-equiv (×-fmap h k)
×-isemap eh ek = ×-isemap-r _ ek ∘ise ×-isemap-l _ eh

×-emap : ∀ {i₀ i₁ j₀ j₁} {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  → (u : A₀ ≃ A₁) (v : B₀ ≃ B₁) → (A₀ × B₀ ≃ A₁ × B₁)
×-emap u v = ×-emap-r _ v ∘e ×-emap-l _ u

⊙×-emap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → X ⊙≃ X' → Y ⊙≃ Y' → X ⊙× Y ⊙≃ X' ⊙× Y'
⊙×-emap (F , F-ise) (G , G-ise) = ⊙×-fmap F G , ×-isemap F-ise G-ise

-- Implementation of [_∙'_] on Σ
Σ-∙' : ∀ {i j} {A : Type i} {B : A → Type j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
  → (pair= p q ∙' pair= p' r) == pair= (p ∙' p') (q ∙'ᵈ r)
Σ-∙' {p = idp} {p' = idp} q idp = idp

-- Implementation of [_∙_] on Σ
Σ-∙ : ∀ {i j} {A : Type i} {B : A → Type j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
  → (pair= p q ∙ pair= p' r) == pair= (p ∙ p') (q ∙ᵈ r)
Σ-∙ {p = idp} {p' = idp} idp r = idp

-- Implementation of [!] on Σ
Σ-! : ∀ {i j} {A : Type i} {B : A → Type j}
  {x y : A} {p : x == y}
  {u : B x} {v : B y}
  (q : u == v [ B ↓ p ])
  → ! (pair= p q) == pair= (! p) (!ᵈ q)
Σ-! {p = idp} idp = idp

-- Implementation of [_∙'_] on ×
×-∙' : ∀ {i j} {A : Type i} {B : Type j}
  {x y z : A} (p : x == y) (p' : y == z)
  {u v w : B} (q : u == v) (q' : v == w)
  → (pair×= p q ∙' pair×= p' q') == pair×= (p ∙' p') (q ∙' q')
×-∙' idp idp q idp = idp

-- Implementation of [_∙_] on ×
×-∙ : ∀ {i j} {A : Type i} {B : Type j}
  {x y z : A} (p : x == y) (p' : y == z)
  {u v w : B} (q : u == v) (q' : v == w)
  → (pair×= p q ∙ pair×= p' q') == pair×= (p ∙ p') (q ∙ q')
×-∙ idp idp idp r = idp

-- Implementation of [!] on ×
×-! : ∀ {i j} {A : Type i} {B : Type j}
  {x y : A} (p : x == y) {u v : B} (q : u == v)
  → ! (pair×= p q) == pair×= (! p) (! q)
×-! idp idp = idp

-- Special case of [ap-,]
ap-cst,id : ∀ {i j} {A : Type i} (B : A → Type j)
  {a : A} {x y : B a} (p : x == y)
  → ap (λ x → _,_ {B = B} a x) p == pair= idp p
ap-cst,id B idp = idp

-- hfiber fst == B
module _ {i j} {A : Type i} {B : A → Type j} where

  private
    to : ∀ a → hfiber (fst :> (Σ A B → A)) a → B a
    to a ((.a , b) , idp) = b

    from : ∀ (a : A) → B a → hfiber (fst :> (Σ A B → A)) a
    from a b = (a , b) , idp

    to-from : ∀ (a : A) (b : B a) → to a (from a b) == b
    to-from a b = idp

    from-to : ∀ a b′ → from a (to a b′) == b′
    from-to a ((.a , b) , idp) = idp

  hfiber-fst : ∀ a → hfiber (fst :> (Σ A B → A)) a ≃ B a
  hfiber-fst a = to a , is-eq (to a) (from a) (to-from a) (from-to a)

{- Dependent paths in a Σ-type -}
module _ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
  where

  ↓-Σ-in : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x r} {s' : C x' r'}
    (q : r == r' [ B ↓ p ])
    → s == s' [ uncurry C ↓ pair= p q ]
    → (r , s) == (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ]
  ↓-Σ-in {p = idp} idp t = pair= idp t

  ↓-Σ-fst : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x r} {s' : C x' r'}
    → (r , s) == (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ]
    → r == r' [ B ↓ p ]
  ↓-Σ-fst {p = idp} u = fst= u

  ↓-Σ-snd : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x r} {s' : C x' r'}
    → (u : (r , s) == (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ])
    → s == s' [ uncurry C ↓ pair= p (↓-Σ-fst u) ]
  ↓-Σ-snd {p = idp} idp = idp

  ↓-Σ-β-fst : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x r} {s' : C x' r'}
    (q : r == r' [ B ↓ p ])
    (t : s == s' [ uncurry C ↓ pair= p q ])
    → ↓-Σ-fst (↓-Σ-in q t) == q
  ↓-Σ-β-fst {p = idp} idp idp = idp

  ↓-Σ-β-snd : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x r} {s' : C x' r'}
    (q : r == r' [ B ↓ p ])
    (t : s == s' [ uncurry C ↓ pair= p q ])
    → ↓-Σ-snd (↓-Σ-in q t) == t
      [ (λ q' → s == s' [ uncurry C ↓ pair= p q' ]) ↓ ↓-Σ-β-fst q t ]
  ↓-Σ-β-snd {p = idp} idp idp = idp

  ↓-Σ-η : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x r} {s' : C x' r'}
    (u : (r , s) == (r' , s') [ (λ x → Σ (B x) (C x)) ↓ p ])
    → ↓-Σ-in (↓-Σ-fst u) (↓-Σ-snd u) == u
  ↓-Σ-η {p = idp} idp = idp

{- Dependent paths in a ×-type -}
module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  where

  ↓-×-in : {x x' : A} {p : x == x'} {r : B x} {r' : B x'}
    {s : C x} {s' : C x'}
    → r == r' [ B ↓ p ]
    → s == s' [ C ↓ p ]
    → (r , s) == (r' , s') [ (λ x → B x × C x) ↓ p ]
  ↓-×-in {p = idp} q t = pair×= q t

{- Dependent paths over a ×-type -}
module _ {i j k} {A : Type i} {B : Type j} (C : A → B → Type k)
  where

  ↓-over-×-in : {x x' : A} {p : x == x'} {y y' : B} {q : y == y'}
    {u : C x y} {v : C x' y} {w : C x' y'}
    → u == v [ (λ a → C a y) ↓ p ]
    → v == w [ (λ b → C x' b) ↓ q ]
    → u == w [ uncurry C ↓ pair×= p q ]
  ↓-over-×-in {p = idp} {q = idp} idp idp = idp

  ↓-over-×-in' : {x x' : A} {p : x == x'} {y y' : B} {q : y == y'}
    {u : C x y} {v : C x y'} {w : C x' y'}
    → u == v [ (λ b → C x b) ↓ q ]
    → v == w [ (λ a → C a y') ↓ p ]
    → u == w [ uncurry C ↓ pair×= p q ]
  ↓-over-×-in' {p = idp} {q = idp} idp idp = idp

module _ where
  -- An orphan lemma.
  ↓-cst×app-in : ∀ {i j k} {A : Type i}
    {B : Type j} {C : A → B → Type k}
    {a₁ a₂ : A} (p : a₁ == a₂)
    {b₁ b₂ : B} (q : b₁ == b₂)
    {c₁ : C a₁ b₁}{c₂ : C a₂ b₂}
    → c₁ == c₂ [ uncurry C ↓ pair×= p q ]
    → (b₁ , c₁) == (b₂ , c₂) [ (λ x → Σ B (C x)) ↓ p ]
  ↓-cst×app-in idp idp idp = idp

{- pair= and pair×= where one argument is reflexivity -}
pair=-idp-l : ∀ {i j} {A : Type i} {B : A → Type j} (a : A) {b₁ b₂ : B a}
  (q : b₁ == b₂) → pair= {B = B} idp q == ap (λ y → (a , y)) q
pair=-idp-l _ idp = idp

pair×=-idp-l : ∀ {i j} {A : Type i} {B : Type j} (a : A) {b₁ b₂ : B}
  (q : b₁ == b₂) → pair×= idp q == ap (λ y → (a , y)) q
pair×=-idp-l _ idp = idp

pair×=-idp-r : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A} (p : a₁ == a₂)
  (b : B) → pair×= p idp == ap (λ x → (x , b)) p
pair×=-idp-r idp _ = idp

pair×=-split-l : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A} (p : a₁ == a₂)
  {b₁ b₂ : B} (q : b₁ == b₂)
  → pair×= p q == ap (λ a → (a , b₁)) p ∙ ap (λ b → (a₂ , b)) q
pair×=-split-l idp idp = idp

pair×=-split-r : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A} (p : a₁ == a₂)
  {b₁ b₂ : B} (q : b₁ == b₂)
  → pair×= p q == ap (λ b → (a₁ , b)) q ∙ ap (λ a → (a , b₂)) p
pair×=-split-r idp idp = idp

×-swap : ∀ {i j} {A : Type i} {B : Type j} → A × B → B × A
×-swap (a , b) = (b , a)

×-swap-natural : ∀ {i₀ i₁ j₀ j₁} {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  (f : A₀ → A₁)
  (g : B₀ → B₁)
  → ×-fmap g f ∘ ×-swap ∼ ×-swap ∘ ×-fmap f g
×-swap-natural f g (a , b) = idp

⊙×-swap : ∀ {i j} {X : Ptd i} {Y : Ptd j} → X ⊙× Y ⊙→ Y ⊙× X
⊙×-swap = ×-swap , idp

⊙×-swap-natural : ∀ {i₀ i₁ j₀ j₁} {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  (f : X₀ ⊙→ X₁)
  (g : Y₀ ⊙→ Y₁)
  → ⊙×-fmap g f ⊙∘ ⊙×-swap ⊙∼ ⊙×-swap ⊙∘ ⊙×-fmap f g
⊙×-swap-natural (f' , idp) (g' , idp) =
  ×-swap-natural f' g' , idp

-- Commutativity of products and derivatives.
module _ {i j} {A : Type i} {B : Type j} where

  ×-comm : A × B ≃ B × A
  ×-comm = equiv ×-swap ×-swap (λ _ → idp) (λ _ → idp)

module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} where
  Σ₂-×-comm : Σ (Σ A B) (λ ab → C (fst ab)) ≃ Σ (Σ A C) (λ ac → B (fst ac))
  Σ₂-×-comm = Σ-assoc ⁻¹ ∘e Σ-emap-r (λ a → ×-comm) ∘e Σ-assoc

module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k} where
  Σ₁-×-comm : Σ A (λ a → Σ B (λ b → C a b)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  Σ₁-×-comm = Σ-assoc ∘e Σ-emap-l _ ×-comm ∘e Σ-assoc ⁻¹
