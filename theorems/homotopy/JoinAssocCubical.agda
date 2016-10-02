{-# OPTIONS --without-K #-}

open import HoTT

{- A proof that (A * B) * C ≃ (C * B) * A, which combined with commutativity
 - proves associativity.
 -
 - Agda has a hard time compiling this but sometimes it succeeds.
 -
 - Favonia (2016 May): I have consistent success in compiling this file.
 -
 -}

open import homotopy.JoinComm

module homotopy.JoinAssocCubical where

{- Square and cube lemmas. Some of these are probably generally useful -}
private

  app=cst-square : ∀ {i j} {A : Type i} {B : Type j}
    {b : B} {f : A → B} (p : ∀ a → f a == b)
    {a₁ a₂ : A} (q : a₁ == a₂)
    → Square (p a₁) (ap f q) idp (p a₂)
  app=cst-square p idp = hid-square

  app=cst-square= : ∀ {i j} {A : Type i} {B : Type j}
    {b : B} {f : A → B} {p₁ p₂ : ∀ a → f a == b}
    (α : ∀ a → p₁ a == p₂ a) {a₁ a₂ : A} (q : a₁ == a₂)
    → Cube (app=cst-square p₁ q)
           (app=cst-square p₂ q)
           (horiz-degen-square $ α a₁)
           hid-square
           hid-square
           (horiz-degen-square $ α a₂)
  app=cst-square= α idp = y-degen-cube idp

  app=cst-square-β : ∀ {i j} {A : Type i} {B : Type j} {b : B} {f : A → B}
    (g : (a : A) → f a == b) {x y : A} (p : x == y)
    {sq : Square (g x) (ap f p) idp (g y)}
    → apd g p == ↓-app=cst-from-square sq
    → app=cst-square g p == sq
  app=cst-square-β g idp α =
    ! horiz-degen-square-idp ∙ ap horiz-degen-square α ∙ horiz-degen-square-β _

  ap-∘-app=cst-square : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
    {b : B} {f : A → B} (h : B → C) (g : (a : A) → f a == b)
    {x y : A} (p : x == y)
    → Cube (app=cst-square (ap h ∘ g) p)
           (ap-square h (app=cst-square g p))
           hid-square
           (horiz-degen-square $ ap-∘ h f p)
           ids
           hid-square
  ap-∘-app=cst-square h g idp =
    cube-shift-right (! ap-square-hid) $
      cube-shift-top (! horiz-degen-square-idp) $
        x-degen-cube idp

  cube-to-↓-rtriangle : ∀ {i j} {A : Type i} {B : Type j}
    {b₀ b₁ : A → B} {b : B} {p₀₁ : (a : A) → b₀ a == b₁ a}
    {p₀ : (a : A) → b₀ a == b} {p₁ : (a : A) → b₁ a == b}
    {x y : A} {q : x == y}
    {sqx : Square (p₀₁ x) (p₀ x) (p₁ x) idp}
    {sqy : Square (p₀₁ y) (p₀ y) (p₁ y) idp}
    → Cube sqx sqy (natural-square p₀₁ q) (app=cst-square p₀ q)
                   (app=cst-square p₁ q) ids
    → sqx == sqy [ (λ z → Square (p₀₁ z) (p₀ z) (p₁ z) idp) ↓ q ]
  cube-to-↓-rtriangle {q = idp} cu = x-degen-cube-out cu

{- approximately, [massage] describes the action of
 - [switch : (A * B) * C → (C * B) * A] on the level of squares -}
private

  massage : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋
    → Square (! p₀₋) (p₋₁ ∙ ! p₁₋) idp (! p₋₀)
  massage ids = ids

  massage-massage : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₁₋ : a₁₀ == a₀₁}
    (sq : Square p₀₋ p₋₀ idp p₁₋)
    → Cube (massage (massage sq)) sq
           (horiz-degen-square (!-! p₀₋)) (horiz-degen-square (!-! p₋₀))
           ids (horiz-degen-square (!-! p₁₋))
  massage-massage = square-bot-J
    (λ sq → Cube (massage (massage sq)) sq
              (horiz-degen-square (!-! _)) (horiz-degen-square (!-! _))
              ids (horiz-degen-square (!-! _)))
    idc

  ap-square-massage : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
    {a₀₀ a₀₁ a₁₀ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₁₋ : a₁₀ == a₀₁}
    (sq : Square p₀₋ p₋₀ idp p₁₋)
    → Cube (ap-square f (massage sq)) (massage (ap-square f sq))
           (horiz-degen-square (ap-! f p₀₋))
           (horiz-degen-square (ap-! f p₁₋))
           ids
           (horiz-degen-square (ap-! f p₋₀))
  ap-square-massage f = square-bot-J
    (λ sq → Cube (ap-square f (massage sq)) (massage (ap-square f sq))
                 (horiz-degen-square (ap-! f _))
                 (horiz-degen-square (ap-! f _))
                 ids
                 (horiz-degen-square (ap-! f _)))
    idc

  massage-cube : ∀ {i} {A : Type i}
    {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
    {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
    {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
    {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

    {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
    {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
    {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

    {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
    {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
    {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
    {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
    {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
    {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
    → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
    → Cube (massage sq₋₋₀) (massage sq₋₋₁)
           (!□v sq₀₋₋) (sq₋₁₋ ⊡v !□v sq₁₋₋) vid-square (!□v sq₋₀₋)
  massage-cube idc = idc

private
  module _  {i j k} {A : Type i} {B : Type j} {C : Type k} where

    {- Define an involutive map [switch] -}

    module SwitchLeft = PushoutRec {d = *-span A B} {D = (C * B) * A}
      (λ a → right a)
      (λ b → left (right b))
      (λ {(a , b) → ! (glue (right b , a))})

    switch-coh-fill : (a : A) (b : B) (c : C) → Σ
      (Square (! (glue (left c , a))) (ap SwitchLeft.f (glue (a , b)))
              idp (! (ap left (glue (c , b)))))
      (λ sq → Cube
        sq (massage $ app=cst-square (λ j → glue (j , a)) (glue (c , b)))
        hid-square (horiz-degen-square (SwitchLeft.glue-β (a , b)))
        ids hid-square)
    switch-coh-fill a b c = fill-cube-left _ _ _ _ _

    module SwitchCoh (c : C) = PushoutElim {d = *-span A B}
      {P = λ k → SwitchLeft.f k == left (left c)}
      (λ a → ! (glue (left c , a)))
      (λ b → ! (ap left (glue (c , b))))
      (↓-app=cst-from-square ∘ λ {(a , b) → fst (switch-coh-fill a b c)})

    module Switch = PushoutRec {d = *-span (A * B) C} {D = (C * B) * A}
      SwitchLeft.f
      (λ c → left (left c))
      (λ {(k , c) → SwitchCoh.f c k})

    switch = Switch.f

  module _ {i j k} {A : Type i} {B : Type j} {C : Type k} where

    {- Proof that [switch] is involutive. There are three squares involved:
     - one indexed by A × B, one indexed by A × C, and one by B × C.
     - These are related by a cube indexed by A × B × C.
     - We get the squares for free by defining the cube, as long as
     - we make sure the right faces are dependent on the right types. -}

    {- Three big square terms follow; unfortunately Agda can't figure out
     - what these have to be on its own. Don't worry about the defns. -}

    switch-inv-left-square : (a : A) (b : B)
      → Square idp (ap (switch {A = C} ∘ SwitchLeft.f) (glue (a , b)))
               (ap left (glue (a , b))) idp
    switch-inv-left-square a b = square-symmetry $
      (horiz-degen-square (ap-∘ switch SwitchLeft.f (glue (a , b))))
      ⊡h ap-square switch (horiz-degen-square (SwitchLeft.glue-β (a , b)))
      ⊡h horiz-degen-square (ap-! switch (glue (right b , a)))
      ⊡h !□v (!□h hid-square)
      ⊡h !□v (horiz-degen-square (Switch.glue-β (right b , a)))
      ⊡h !□v hid-square
      ⊡h horiz-degen-square (!-! _)

    switch-inv-coh-left : (c : C) (a : A)
      → Square idp (ap (switch {B = B}) (SwitchCoh.f c (left a)))
               (glue (left a , c)) idp
    switch-inv-coh-left c a = square-symmetry $
      hid-square
      ⊡h ap-square switch hid-square
      ⊡h horiz-degen-square (ap-! switch (glue (left c , a)))
      ⊡h !□v (!□h hid-square)
      ⊡h !□v (horiz-degen-square (Switch.glue-β (left c , a)))
      ⊡h !□v hid-square
      ⊡h horiz-degen-square (!-! _)

    switch-inv-coh-right : (c : C) (b : B)
      → Square idp (ap (switch {C = A}) (SwitchCoh.f c (right b)))
               (glue (right b , c)) idp
    switch-inv-coh-right c b = square-symmetry $
      hid-square
      ⊡h ap-square switch hid-square
      ⊡h horiz-degen-square (ap-! switch (ap left (glue (c , b))))
      ⊡h !□v (!□h (horiz-degen-square (ap-∘ switch left (glue (c , b)))))
      ⊡h !□v hid-square
      ⊡h !□v (horiz-degen-square (SwitchLeft.glue-β (c , b)))
      ⊡h horiz-degen-square (!-! _)

    module SwitchInvLeft = PushoutElim {d = *-span A B}
      {P = λ k → switch {A = C} (switch (left k)) == left k}
      (λ a → idp)
      (λ b → idp)
      (↓-='-from-square ∘ uncurry switch-inv-left-square)

    {- In very small steps, build up the cube -}
    module Coh (a : A) (b : B) (c : C) where

      step₁ : Cube
        (app=cst-square (ap switch ∘ SwitchCoh.f c) (glue (a , b)))
        (ap-square switch (app=cst-square (SwitchCoh.f c) (glue (a , b))))
        _ _ _ _
      step₁ = ap-∘-app=cst-square switch (SwitchCoh.f c) (glue (a , b))

      step₂ : Cube
        (ap-square switch (app=cst-square (SwitchCoh.f c) (glue (a , b))))
        (ap-square switch $ massage $
          app=cst-square (λ j → glue (j , a)) (glue (c , b)))
        _ _ _ _
      step₂ =
        cube-shift-left
          (! (ap (ap-square switch)
                 (app=cst-square-β (SwitchCoh.f c) (glue (a , b))
                                   (SwitchCoh.glue-β c (a , b)))))
          (ap-cube switch (snd (switch-coh-fill a b c)))

      step₃ : Cube
        (ap-square switch $ massage $
          app=cst-square (λ j → glue (j , a)) (glue (c , b)))
        (massage $ ap-square switch $
          app=cst-square (λ j → glue (j , a)) (glue (c , b)))
        _ _ _ _
      step₃ = ap-square-massage switch
                (app=cst-square (λ j → glue (j , a)) (glue (c , b)))

      step₄ : Cube
        (massage $ ap-square switch $
          app=cst-square (λ j → glue (j , a)) (glue (c , b)))
        (massage $
          app=cst-square (λ j → ap switch (glue (j , a))) (glue (c , b)))
        _ _ _ _
      step₄ = massage-cube $ cube-!-x $
        ap-∘-app=cst-square switch (λ j → glue (j , a)) (glue (c , b))

      step₅ : Cube
        (massage $
          app=cst-square (λ j → ap switch (glue (j , a))) (glue (c , b)))
        (massage $ app=cst-square (SwitchCoh.f a) (glue (c , b)))
        _ _ _ _
      step₅ = massage-cube $
        app=cst-square= (λ j → Switch.glue-β (j , a)) (glue (c , b))

      step₆ : Cube
        (massage $ app=cst-square (SwitchCoh.f a) (glue (c , b)))
        (massage $ massage $
          app=cst-square (λ k → glue (k , c)) (glue (a , b)))
        _ _ _ _
      step₆ = massage-cube $
        cube-shift-left
          (! (app=cst-square-β (SwitchCoh.f a) (glue (c , b))
                               (SwitchCoh.glue-β a (c , b))))
          (snd (switch-coh-fill c b a))

      step₇ : Cube
        (massage $ massage $
          app=cst-square (λ k → glue {d = *-span (A * B) C} (k , c))
                         (glue (a , b)))
        (app=cst-square (λ k → glue (k , c)) (glue (a , b)))
        _ _ _ _
      step₇ = massage-massage _

      switch-inv-cube : Cube
        (switch-inv-coh-left c a) (switch-inv-coh-right c b)
        (switch-inv-left-square a b)
        (app=cst-square (ap switch ∘ SwitchCoh.f c) (glue (a , b)))
        (app=cst-square (λ k → glue (k , c)) (glue (a , b)))
        ids
      switch-inv-cube = cube-rotate-x→z $
        step₁ ∙³x step₂ ∙³x step₃ ∙³x step₄ ∙³x step₅ ∙³x step₆ ∙³x step₇


    module SwitchInvCoh (c : C) = PushoutElim {d = *-span A B}
      {P = λ k → Square (SwitchInvLeft.f k) (ap switch (SwitchCoh.f c k))
                        (glue (k , c)) idp}
      (switch-inv-coh-left c)
      (switch-inv-coh-right c)
      (cube-to-↓-rtriangle ∘ λ {(a , b) →
        cube-shift-back
          (! (natural-square-β SwitchInvLeft.f (glue (a , b))
              (SwitchInvLeft.glue-β (a , b))))
          (Coh.switch-inv-cube a b c)})

    abstract
      switch-inv : (l : (A * B) * C) → switch (switch l) == l
      switch-inv = Pushout-elim
        SwitchInvLeft.f
        (λ c → idp)
        (↓-∘=idf-from-square switch switch ∘ λ {(k , c) →
          ap (ap switch) (Switch.glue-β (k , c)) ∙v⊡ SwitchInvCoh.f c k})

module _ {i j k} (A : Type i) (B : Type j) (C : Type k) where

  *-rearrange-equiv : (A * B) * C ≃ (C * B) * A
  *-rearrange-equiv = equiv switch switch switch-inv switch-inv

  *-assoc : (A * B) * C ≃ A * (B * C)
  *-assoc = *-emap (ide A) *-comm ∘e *-comm ∘e *-rearrange-equiv

module _ {i j k} (X : Ptd i) (Y : Ptd j) (Z : Ptd k) where

  ⊙*-rearrange-equiv : (X ⊙* Y) ⊙* Z ⊙≃ (Z ⊙* Y) ⊙* X
  ⊙*-rearrange-equiv =
    ≃-to-⊙≃ (*-rearrange-equiv (fst X) (fst Y) (fst Z)) (! (glue (left (snd Z), snd X)))
