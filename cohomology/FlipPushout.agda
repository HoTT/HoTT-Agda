{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences2
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Sigma
open import lib.types.Span

{- Flipping the pushout diagram (switching left and right) gives the
 - same pushout. -}

module cohomology.FlipPushout where

{- First some lemmas. Are any of these generally useful? -}
module _ where
  ↓-cst2-ap↓ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : A → Type k}
    {D : A → Type l} (f : {a : A} → B a → D a)
    {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    (r : u == v [ B ↓ p ])
    → ↓-cst2-in p q (ap↓ f r) == ap↓ f (↓-cst2-in p q r)
  ↓-cst2-ap↓ f idp idp idp = idp

  ap↓-↓-cst→app : ∀ {i j k} {A : Type i} {B : Type j}
    {C : A → B → Type k} {x x' : A} {p : x == x'}
    {u : (b : B) → C x b} {u' : (b : B) → C x' b}
    (α : (b : B) → u b == u' b [ (λ x → C x b) ↓ p ]) (b₀ : B)
    → ap↓ (λ f → f b₀) (↓-cst→app-in α) == α b₀
  ap↓-↓-cst→app {p = idp} = app=-β

  ↓-cst2-in-▹ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
    {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v w : B y}
    (r : u == v [ B ↓ p ]) (s : v == w)
    → ↓-cst2-in p q (r ▹ s) == ↓-cst2-in p q r ▹ s
  ↓-cst2-in-▹ idp idp r s = idp

  ↓-cst2-in-◃ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
    {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u v : B x} {w : B y}
    (r : v == w [ B ↓ p ]) (s : u == v)
    → ↓-cst2-in p q (s ◃ r) == s ◃ ↓-cst2-in p q r
  ↓-cst2-in-◃ idp idp r s = idp

  ▹-↓-idf-ua-in : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v w : B}
    (q : –> e u == v) (r : v == w)
    → ↓-idf-ua-in e q ▹ r == ↓-idf-ua-in e (q ∙ r)
  ▹-↓-idf-ua-in e idp idp = ▹idp _

  ◃-↓-idf-ua-in : ∀ {i} {A B : Type i} (e : A ≃ B) {u v : A} {w : B}
    (q : –> e v == w) (r : u == v)
    → r ◃ ↓-idf-ua-in e q == ↓-idf-ua-in e (ap (–> e) r ∙ q)
  ◃-↓-idf-ua-in e idp idp = idp◃ _

  snd-ptd=-is-↓-cst2 : ∀ {i} {X Y : Ptd i} (p : fst X == fst Y)
    (q : snd X == snd Y [ (λ A → A) ↓ p ])
    → apd snd (pair= p q) == ↓-cst2-in p q q
  snd-ptd=-is-↓-cst2 idp idp = idp

{- Span-flipping functions -}
flip-span : ∀ {i j k} → Span {i} {j} {k} → Span {j} {i} {k}
flip-span (span A B C f g) = span B A C g f

flip-ptd-span : ∀ {i j k} → Ptd-Span {i} {j} {k} → Ptd-Span {j} {i} {k}
flip-ptd-span (ptd-span X Y Z f g) = ptd-span Y X Z g f

{- Pushout-flipping function -}
module _ {i j k} {d : Span {i} {j} {k}} where

  module FlipPushout = PushoutRec
    (right {d = flip-span d})
    (left {d = flip-span d})
    (λ z → ! (glue {d = flip-span d} z))

  flip-pushout : Pushout d → Pushout (flip-span d)
  flip-pushout = FlipPushout.f

flip-pushout-involutive : ∀ {i j k} (d : Span {i} {j} {k})
  (s : Pushout d) → flip-pushout (flip-pushout s) == s
flip-pushout-involutive d = Pushout-elim
  (λ a → idp)
  (λ b → idp)
  (λ c → ↓-app=idf-in $
    idp ∙' glue c
      =⟨ ∙'-unit-l _ ⟩
    glue c
      =⟨ ! (!-! (glue c)) ⟩
    ! (! (glue c))
      =⟨ ap ! (! (FlipPushout.glue-β c)) ⟩
    ! (ap flip-pushout (glue c))
      =⟨ !-ap flip-pushout (glue c) ⟩
    ap flip-pushout (! (glue c))
      =⟨ ! (FlipPushout.glue-β c) |in-ctx (λ w → ap flip-pushout w) ⟩
    ap flip-pushout (ap flip-pushout (glue c))
      =⟨ ∘-ap flip-pushout flip-pushout (glue c) ⟩
    ap (flip-pushout ∘ flip-pushout) (glue c)
      =⟨ ! (∙-unit-r _) ⟩
    ap (flip-pushout ∘ flip-pushout) (glue c) ∙ idp ∎)

{- Equivalence for spans with proofs that the equivalence swaps the
 - injections -}
module _ {i j k} (d : Span {i} {j} {k}) where

  open Span d

  flip-pushout-equiv : Pushout d ≃ Pushout (flip-span d)
  flip-pushout-equiv =
    equiv flip-pushout flip-pushout
      (flip-pushout-involutive (flip-span d))
      (flip-pushout-involutive d)

  flip-pushout-path : Pushout d == Pushout (flip-span d)
  flip-pushout-path = ua flip-pushout-equiv

  flip-left : left == right [ (λ D → (A → D)) ↓ flip-pushout-path ]
  flip-left =
    ↓-cst→app-in $ λ _ → ↓-idf-ua-in flip-pushout-equiv idp

  flip-right : right == left [ (λ D → (B → D)) ↓ flip-pushout-path ]
  flip-right =
    ↓-cst→app-in $ λ _ → ↓-idf-ua-in flip-pushout-equiv idp

{- Path for pointed spans with proofs that the path swaps the pointed
 - injections -}
module _ {i j k} (ps : Ptd-Span {i} {j} {k}) where

  open Ptd-Span ps

  private
    s = ptd-span-out ps

    preserves : –> (flip-pushout-equiv s) (left (snd X)) == left (snd Y)
    preserves = snd (ptd-right {d = flip-ptd-span ps})

  flip-ptd-pushout-path : Ptd-Pushout ps == Ptd-Pushout (flip-ptd-span ps)
  flip-ptd-pushout-path = ptd-ua (flip-pushout-equiv s) preserves

  test : flip-ptd-pushout-path == ptd-ua (flip-pushout-equiv s) preserves
  test = idp

  abstract
    flip-ptd-left : ptd-left {d = ps} == ptd-right {d = flip-ptd-span ps}
                    [ (λ W → fst (X ∙→ W)) ↓ flip-ptd-pushout-path ]
    flip-ptd-left = ↓-Σ-in
      (↓-cst2-in (flip-pushout-path s)
                 (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                 (flip-left s))
      (↓-=-in $ lemma
        snd (λ r → r (snd X))
        (pair= (flip-pushout-path s) (↓-idf-ua-in _ preserves))
        (↓-cst2-in (flip-pushout-path s)
          (↓-idf-ua-in (flip-pushout-equiv s) preserves) (flip-left s))
        idp
        preserves $
          idp ◃ apd snd (pair= (flip-pushout-path s) (↓-idf-ua-in _ preserves))
            =⟨ idp◃ _ ⟩
          apd snd (pair= (flip-pushout-path s) (↓-idf-ua-in _ preserves))
            =⟨ snd-ptd=-is-↓-cst2 _
                 (↓-idf-ua-in (flip-pushout-equiv s) preserves) ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
            =⟨ ! (▹-↓-idf-ua-in (flip-pushout-equiv s) idp preserves)
               |in-ctx (↓-cst2-in _
                         (↓-idf-ua-in (flip-pushout-equiv s) preserves)) ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (↓-idf-ua-in (flip-pushout-equiv s) idp ▹ preserves)
            =⟨ ↓-cst2-in-▹ (flip-pushout-path s)
                  (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                  (↓-idf-ua-in (flip-pushout-equiv s) idp)
                  preserves ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (↓-idf-ua-in (flip-pushout-equiv s) idp)
          ▹ preserves
            =⟨ ! (ap↓-↓-cst→app (λ _ → ↓-idf-ua-in (flip-pushout-equiv s) idp) _)
               |in-ctx context ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (ap↓ (λ h → h _) (flip-left s))
          ▹ preserves
            =⟨ ↓-cst2-ap↓ (λ h → h (snd X)) (flip-pushout-path s)
                 (↓-idf-ua-in (flip-pushout-equiv s) preserves) (flip-left s)
               |in-ctx (λ w → w ▹ preserves) ⟩
          ap↓ (λ h → h (snd X)) (↓-cst2-in (flip-pushout-path s)
                                   (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                                   (flip-left s))
          ▹ preserves ∎)
      where
      lemma : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
        (f : Π A C) (g : {a : A} → B a → C a)
        {a₁ a₂ : A} (p : a₁ == a₂)
        {b₁ : B a₁} {b₂ : B a₂} (q : b₁ == b₂ [ B ↓ p ])
        (r : g b₁ == f a₁) (s : g b₂ == f a₂)
        → r ◃ apd f p == ap↓ g q ▹ s
        → r ◃ apd (f ∘ fst) (pair= p q) == apd (g ∘ snd) (pair= p q) ▹ s
      lemma f g idp idp r s α = α

      {- Separating this term as its own lemma is a performance hack to help
       - Agda typecheck it -}
      context : left (snd X) == right (snd X)
                [ (λ A → A) ↓ flip-pushout-path s ]
         → left (snd X) == left (snd Y)
           [ (λ Z → fst Z) ↓ flip-ptd-pushout-path ]
      context p =
        ↓-cst2-in (ua (flip-pushout-equiv s))
          (↓-idf-ua-in (flip-pushout-equiv s) {u = left (snd X)} preserves) p
        ▹ preserves

    {- An alternate, probably simpler way to prove this is to prove that
     - [! flip-ptd-pushout-path == flip-ptd-pushout-path]
     - and then simply invert [flip-ptd-right] -}

    flip-ptd-right : ptd-right {d = ps} == ptd-left {d = flip-ptd-span ps}
                    [ (λ W → fst (Y ∙→ W)) ↓ flip-ptd-pushout-path ]
    flip-ptd-right = ↓-Σ-in
      (↓-cst2-in (flip-pushout-path s)
                 (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                 (flip-right s))
      (↓-=-in $ lemma₁
        snd (λ r → r (snd Y))
        (pair= (flip-pushout-path s) (↓-idf-ua-in _ preserves))
        (↓-cst2-in (flip-pushout-path s)
          (↓-idf-ua-in (flip-pushout-equiv s) preserves) (flip-right s))
        (snd (ptd-right {d = ps}))
        idp $
          snd (ptd-right {d = ps}) ◃
          apd snd (pair= (flip-pushout-path s) (↓-idf-ua-in _ preserves))
            =⟨ snd-ptd=-is-↓-cst2 _
                 (↓-idf-ua-in (flip-pushout-equiv s) preserves)
               |in-ctx (λ w → snd (ptd-right {d = ps}) ◃ w) ⟩
          snd (ptd-right {d = ps}) ◃
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
            =⟨ ! (↓-cst2-in-◃ (flip-pushout-path s)
                               (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                               (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                               (snd (ptd-right {d = ps}))) ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (snd (ptd-right {d = ps}) ◃
                     ↓-idf-ua-in (flip-pushout-equiv s) preserves)
            =⟨ ◃-↓-idf-ua-in (flip-pushout-equiv s)
                              preserves (snd (ptd-right {d = ps}))
               |in-ctx context ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (↓-idf-ua-in (flip-pushout-equiv s)
                      (ap flip-pushout (snd (ptd-right {d = ps})) ∙ preserves))
            =⟨ lemma₂ ps |in-ctx context ∘ (↓-idf-ua-in (flip-pushout-equiv s)) ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (↓-idf-ua-in (flip-pushout-equiv s) idp)
            =⟨ ! (ap↓-↓-cst→app (λ _ → ↓-idf-ua-in (flip-pushout-equiv s) idp) _)
               |in-ctx context ⟩
          ↓-cst2-in (flip-pushout-path s)
                    (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                    (ap↓ (λ r → r (snd Y)) (flip-right s))
            =⟨ ↓-cst2-ap↓ (λ h → h (snd Y)) (flip-pushout-path s)
                 (↓-idf-ua-in (flip-pushout-equiv s) preserves) (flip-right s) ⟩
          ap↓ (λ r → r (snd Y)) (↓-cst2-in (flip-pushout-path s)
                                  (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                                  (flip-right s))
            =⟨ ! (▹idp _) ⟩
          ap↓ (λ r → r (snd Y)) (↓-cst2-in (flip-pushout-path s)
                                  (↓-idf-ua-in (flip-pushout-equiv s) preserves)
                                  (flip-right s))
          ▹ idp ∎)
      where
      lemma₁ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
        (f : Π A C) (g : {a : A} → B a → C a)
        {a₁ a₂ : A} (p : a₁ == a₂)
        {b₁ : B a₁} {b₂ : B a₂} (q : b₁ == b₂ [ B ↓ p ])
        (r : g b₁ == f a₁) (s : g b₂ == f a₂)
        → r ◃ apd f p == ap↓ g q ▹ s
        → r ◃ apd (f ∘ fst) (pair= p q) == apd (g ∘ snd) (pair= p q) ▹ s
      lemma₁ f g idp idp r s α = α

      lemma₂ : ∀ {i j k} (ps : Ptd-Span {i} {j} {k})
        → ap flip-pushout (snd (ptd-right {d = ps}))
          ∙ snd (ptd-right {d = flip-ptd-span ps})
          == idp
      lemma₂ = ptd-span-J _ $ λ {A} {B} {Z} f g →
        ap flip-pushout (! (glue (snd Z))) ∙ ! (glue (snd Z))
           =⟨ ap-! flip-pushout (glue (snd Z))
              |in-ctx (λ w → w ∙ ! (glue (snd Z))) ⟩
        ! (ap flip-pushout (glue (snd Z))) ∙ ! (glue (snd Z))
           =⟨ FlipPushout.glue-β (snd Z)
              |in-ctx (λ w → ! w ∙ ! (glue (snd Z))) ⟩
        ! (! (glue (snd Z))) ∙ ! (glue (snd Z))
           =⟨ !-inv-l (! (glue (snd Z))) ⟩
        idp ∎

      {- Separating this term as its own lemma is a performance hack to help
       - Agda typecheck it -}
      context : right (snd Y) == left (snd Y)
                [ (λ A → A) ↓ flip-pushout-path s ]
         → right (snd Y) == left (snd Y)
           [ (λ Z → fst Z) ↓ flip-ptd-pushout-path ]
      context p =
        ↓-cst2-in (ua (flip-pushout-equiv s))
          (↓-idf-ua-in (flip-pushout-equiv s) {u = left (snd X)} preserves) p
