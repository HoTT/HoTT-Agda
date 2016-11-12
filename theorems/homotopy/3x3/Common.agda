{-# OPTIONS --without-K --rewriting #-}

module homotopy.3x3.Common where

open import HoTT public hiding (↓-='-in'; ↓-='-out'; ↓-='-in; ↓-='-out; ↓-=-in; ↓-=-out; ↓-∘=idf-in')

!-∘-ap-inv : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) (g : A → B) {a b : A}
  (p : a == b)
  → ap-∘ f g p == ! (∘-ap f g p)
!-∘-ap-inv f g idp = idp

!-ap-∘-inv : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) (g : A → B) {a b : A}
  (p : a == b)
  → ∘-ap f g p == ! (ap-∘ f g p)
!-ap-∘-inv f g idp = idp

!-∘-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) (g : A → B) {a b : A}
  (p : a == b)
  → ! (∘-ap f g p) == ap-∘ f g p
!-∘-ap f g idp = idp

!-ap-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : B → C) (g : A → B) {a b : A}
  (p : a == b)
  → ! (ap-∘ f g p) == ∘-ap f g p
!-ap-∘ f g idp = idp

module _ {i} {A : Type i} where

  _,_=□_,_ : {a b b' c : A} (p : a == b) (q : b == c)
             (r : a == b') (s : b' == c) → Type i
  (idp , q =□ r , idp) = (q == r)

  idp□ : {a b : A} {p : a == b} → idp , p =□ idp , p
  idp□ {p = idp} = idp

  idp□-i : {a b : A} {p : a == b} → p , idp =□ idp , p
  idp□-i {p = idp} = idp

  idp,=□idp,-in : {a b : A} {p q : a == b}
                → p == q → idp , p =□ idp , q
  idp,=□idp,-in {q = idp} α = α

  idp,=□idp,-out : {a b : A} {p q : a == b}
                 → idp , p =□ idp , q → p == q
  idp,=□idp,-out {q = idp} α = α

  idp,=□idp,-β : {a b : A} {p q : a == b}
                 (α : p == q) → idp,=□idp,-out (idp,=□idp,-in α) == α
  idp,=□idp,-β {q = idp} α = idp

  idp,=□idp,-η : {a b : A} {p q : a == b}
                  (α : idp , p =□ idp , q) → idp,=□idp,-in (idp,=□idp,-out α) == α
  idp,=□idp,-η {q = idp} α = idp


  ,idp=□,idp-in : {a b : A} {p q : a == b}
                → p == q → p , idp =□ q , idp
  ,idp=□,idp-in {p = idp} α = α

  ,idp=□,idp-out : {a b : A} {p q : a == b}
                 → p , idp =□ q , idp → p == q
  ,idp=□,idp-out {p = idp} α = α

  ,idp=□,idp-β : {a b : A} {p q : a == b}
                 (α : p == q) → ,idp=□,idp-out (,idp=□,idp-in α) == α
  ,idp=□,idp-β {p = idp} α = idp

  ,idp=□,idp-η : {a b : A} {p q : a == b}
                 (α : p , idp =□ q , idp) → ,idp=□,idp-in (,idp=□,idp-out α) == α
  ,idp=□,idp-η {p = idp} α = idp


  ,idp=□idp,-in : {a b : A} {p q : a == b}
                → p == q → p , idp =□ idp , q
  ,idp=□idp,-in {p = idp} = idp,=□idp,-in

  ,idp=□idp,-out : {a b : A} {p q : a == b}
                 → p , idp =□ idp , q → p == q
  ,idp=□idp,-out {p = idp} {q} α = idp,=□idp,-out α

  ,idp=□idp,-β : {a b : A} {p q : a == b}
                 (α : p == q) → ,idp=□idp,-out (,idp=□idp,-in α) == α
  ,idp=□idp,-β {p = idp} α = idp,=□idp,-β α

  ,idp=□idp,-η : {a b : A} {p q : a == b}
                 (α : p , idp =□ idp , q) → ,idp=□idp,-in (,idp=□idp,-out α) == α
  ,idp=□idp,-η {p = idp} α = idp,=□idp,-η α

  infix 40 _∙□-i/_/_/ _∙□-o/_/_/
  _∙□-i/_/_/ : {a b b' c : A} {p : a == b} {q q' : b == c}
         {r r' : a == b'} {s : b' == c}
         → (p , q =□ r , s) → (q' == q) → (r == r')
         → (p , q' =□ r' , s)
  α ∙□-i/ idp / idp / = α

  _∙□-o/_/_/ : {a b b' c : A} {p p' : a == b} {q : b == c}
         {r : a == b'} {s s' : b' == c}
         → (p , q =□ r , s) → (p' == p) → (s == s')
         → (p' , q =□ r , s')
  α ∙□-o/ idp / idp / = α

  infix 80 _∙□h_
  _∙□h_ : {a b b' c c' d : A} {p : a == b} {q : b == c} {r : a == b'}
    {s : b' == c} {t : c == d} {u : b' == c'} {v : c' == d}
    → (p , q =□ r , s) → (s , t =□ u , v) → (p , q ∙ t =□ r ∙ u , v)
  _∙□h_ {p = idp} {s = idp} {v = idp} idp idp = idp

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap□ : {a b b' c : A} {p : a == b} {q : b == c} {r : a == b'} {s : b' == c}
    → (p , q =□ r , s) → (ap f p , ap f q =□ ap f r , ap f s)
  ap□ {p = idp} {s = idp} α = ap (ap f) α

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap□-,idp=□idp,-in :  {a b : A} {p q : a == b}
                (α : p == q) → ap□ f (,idp=□idp,-in α) == ,idp=□idp,-in (ap (ap f) α)
  ap□-,idp=□idp,-in {p = idp} idp = idp

module _ {i j} {A : Type i} {B : A → Type j} where

  _,_=□d-i_,_ : {a b : A} {p : a == b} {u v : B a} {w x : B b}
           → (u == v) → (v == w [ B ↓ p ])
           → (u == x [ B ↓ p ]) → (x == w)
           → Type j
  _,_=□d-i_,_ idp α β idp = (α == β)
  -- _,_=□d-i_,_ {p = idp} = _,_=□_,_

  idp,=□d-iidp,-out : {a : A} {u w : B a} {α β : u == w}
    → (idp , α =□d-i idp , β) → α == β
  idp,=□d-iidp,-out {β = idp} x = x

  ,idp=□d-iidp,-out : {a : A} {u w : B a} {α β : u == w}
    → (α , idp =□d-i idp , β) → α == β
  ,idp=□d-iidp,-out {α = idp} x = idp,=□d-iidp,-out x

  idp,=□d-iidp,-in : {a : A} {u w : B a} {α β : u == w}
    → α == β → (idp , α =□d-i idp , β)
  idp,=□d-iidp,-in {β = idp} x = x

  ,idp=□d-iidp,-in : {a : A} {u w : B a} {α β : u == w}
    → α == β → (α , idp =□d-i idp , β)
  ,idp=□d-iidp,-in {α = idp} x = idp,=□d-iidp,-in x

  infix 40 _◃/_/_/
  _◃/_/_/ : {a b : A} {p : a == b} {u v : B a} {w x : B b}
          → (v == w [ B ↓ p ]) → (u == v) → (w == x)
          → (u == x [ B ↓ p ])
  α ◃/ idp / idp / = α

module _ {i} {A : Type i} where

  _,_,_=□□_,_,_ : {a0 b0 b'0 c0 a1 b1 b'1 c1 : A}
    {p0 : a0 == b0} {q0 : b0 == c0} {r0 : a0 == b'0} {s0 : b'0 == c0}
    {p1 : a1 == b1} {q1 : b1 == c1} {r1 : a1 == b'1} {s1 : b'1 == c1}
    {a* : a0 == a1} {b* : b0 == b1} {b'* : b'0 == b'1} {c* : c0 == c1}
    → (p0 , q0 =□ r0 , s0) → (s0 , c* =□ b'* , s1) → (r0 , b'* =□ a* , r1)
    → (q0 , c* =□ b* , q1) → (p0 , b* =□ a* , p1) → (p1 , q1 =□ r1 , s1)
    → Type i
  _,_,_=□□_,_,_ {p0 = idp} {s0 = idp} {p1 = idp} {s1 = idp} idp idp β γ idp idp = β == γ


{- Nondependent identity type -}

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  ↓-='-in' : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u , ap g p =□ ap f p , v)
    → (u == v [ (λ x → f x == g x) ↓ p ])
  ↓-='-in' {p = idp} α = ,idp=□idp,-out α

  ↓-='-out : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u == v [ (λ x → f x == g x) ↓ p ])
    → (u , ap g p =□ ap f p , v)
  ↓-='-out {p = idp} α = ,idp=□idp,-in α

↓-='-β : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  (α : (u , ap g p =□ ap f p , v))
  → ↓-='-out (↓-='-in' α) == α
↓-='-β {p = idp} α = ,idp=□idp,-η α

module _ {i j k} {A : Type i} {B : Type j} (C : Type k) {g h : B → C} (f : A → B) where

  lemma-a : {x y : A} (p : x == y) {u : g (f x) == h (f x)} {v : g (f y) == h (f y)} {q : f x == f y} (r : ap f p == q)
    (α : u == v [ (λ z → g z == h z) ↓ q ])
    → ↓-='-out (↓-ap-out= (λ z → g z == h z) f p r α) == ↓-='-out α ∙□-i/ ap-∘ h f p ∙ ap (ap h) r / ! (ap (ap g) r) ∙ ∘-ap g f p /
  lemma-a idp idp idp = idp

{- Dependent identity type -}

↓-=-in : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u , apd f p =□d-i apd g p , v)
  → (u == v [ (λ x → g x == f x) ↓ p ])
↓-=-in {B = B} {p = idp} {u} {v} α = ,idp=□d-iidp,-out α

↓-=-out : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u == v [ (λ x → g x == f x) ↓ p ])
  → (u , apd f p =□d-i apd g p , v)
↓-=-out {B = B} {p = idp} {u} {v} α = ,idp=□d-iidp,-in α

↓-=□-in : ∀ {i j} {A : Type i} {B : Type j} {f g g' h : A → B}
  {x y : A} {α : x == y} {p : (x : A) → f x == g x} {q : (x : A) → g x == h x}
  {r : (x : A) → f x == g' x} {s : (x : A) → g' x == h x}
  {u : (p x , q x =□ r x , s x)} {v : (p y , q y =□ r y , s y)}
  → (u , ↓-='-out (apd s α) , ↓-='-out (apd r α) =□□ ↓-='-out (apd q α) , ↓-='-out (apd p α) , v)
  → (u == v [ (λ x → (p x , q x =□ r x , s x)) ↓ α ])
↓-=□-in {α = idp} = ch _ _ where

  ch : ∀ {j} {B : Type j} {f g g' h : B} {p : f == g} {q : g == h}
       {r : f == g'} {s : g' == h} (u v : p , q =□ r , s)
       → u , ,idp=□idp,-in idp , ,idp=□idp,-in idp =□□ ,idp=□idp,-in idp , ,idp=□idp,-in idp , v
       → u == v
  ch {p = idp} {s = idp} u v = ,idp=□idp,-out ∘ ch2 u idp idp v   where

    ch2 : ∀ {i} {A : Type i} {a b : A}
          {q q' r r' : a == b}
          (p : q == r) (p' : r == r')
          (s' : q == q') (s : q' == r')
          → (p , idp , ,idp=□idp,-in p' =□□ ,idp=□idp,-in s' , idp , s) → (p , p' =□ s' , s)
    ch2 idp p' s' idp α = ! (,idp=□idp,-β p') ∙ ap ,idp=□idp,-out α ∙ ,idp=□idp,-β s'

-- Dependent path in a type of the form [λ x → x ≡ g (f x)]
module _ {i j} {A : Type i} {B : Type j} (g : B → A) (f : A → B) where
  ↓-idf=∘-in : {x y : A} {p : x == y} {u : x == g (f x)} {v : y == g (f y)}
    → (u , ap g (ap f p) =□ p , v)
    → (u == v [ (λ x → x == g (f x)) ↓ p ])
  ↓-idf=∘-in {p = idp} q = ,idp=□idp,-out q

  ↓-∘=idf-in' : {x y : A} {p : x == y} {u : g (f x) == x} {v : g (f y) == y}
    → (u , p =□ ap g (ap f p) , v)
    → (u == v [ (λ x → g (f x) == x) ↓ p ])
  ↓-∘=idf-in' {p = idp} q = ,idp=□idp,-out q

module _ {i i' j k} {A : Type i} {A' : Type i'} {B : Type j} {C : Type k}
  (f : B → C) (g : A → B) (h : A' → B) where

  ap-∙∙`∘`∘ : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : c == d)
    → ap f (ap g p ∙ q ∙ ap h r) == ap (f ∘ g) p ∙ ap f q ∙ ap (f ∘ h) r
  ap-∙∙`∘`∘ idp q idp = ap-∙ f q idp

  ap-∙∙!`∘`∘ : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : d == c)
    → ap f (ap g p ∙ q ∙ ap h (! r)) == ap (f ∘ g) p ∙ ap f q ∙ ! (ap (f ∘ h) r)
  ap-∙∙!`∘`∘ idp q idp = ap-∙ f q idp

  ap-∙∙!'`∘`∘ : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : d == c)
    → ap f (ap g p ∙ q ∙ ! (ap h r)) == ap (f ∘ g) p ∙ ap f q ∙ ! (ap (f ∘ h) r)
  ap-∙∙!'`∘`∘ idp q idp = ap-∙ f q idp

  ap-!∙∙`∘`∘ : {a b : A} {c d : A'} (p : b == a) (q : g b == h c) (r : c == d)
    → ap f (ap g (! p) ∙ q ∙ ap h r) == ! (ap (f ∘ g) p) ∙ ap f q ∙ ap (f ∘ h) r
  ap-!∙∙`∘`∘ idp q idp = ap-∙ f q idp

  ap-!'∙∙`∘`∘ : {a b : A} {c d : A'} (p : b == a) (q : g b == h c) (r : c == d)
    → ap f (! (ap g p) ∙ q ∙ ap h r) == ! (ap (f ∘ g) p) ∙ ap f q ∙ ap (f ∘ h) r
  ap-!'∙∙`∘`∘ idp q idp = ap-∙ f q idp

module _ {i i' j k} {A : Type i} {A' : Type i'} {B : Type j} {C : B → Type k}
  (f : Π B C) (g : A → B) (h : A' → B) where

  apd-∙∙`∘`∘ : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : c == d)
    → apd f (ap g p ∙ q ∙ ap h r) == ↓-ap-in _ _ (apd (f ∘ g) p) ∙ᵈ apd f q ∙ᵈ ↓-ap-in _ _ (apd (f ∘ h) r)
  apd-∙∙`∘`∘ idp q idp = ch q  where

    ch : {a b : B} (q : a == b)
         → apd f (q ∙ idp) == idp ∙ᵈ apd f q ∙ᵈ idp
    ch idp = idp

module _ {i i' j k} {A : Type i} {A' : Type i'} {B : Type j} {C : Type k} {f : A → B} {f' : A' → B} {g h : B → C} where

  lemma-b : {x y : A} {z t : A'} {p : x == y} {q : z == t} (r : f y == f' z)
    {a : g (f x) == h (f x)} {b : g (f y) == h (f y)}
    {c : g (f' z) == h (f' z)} {d : g (f' t) == h (f' t)}
    (u : a == b [ (λ x → g (f x) == h (f x)) ↓ p ]) (v : (b , ap h r =□ ap g r , c))
    (w : c == d [ (λ x → g (f' x) == h (f' x)) ↓ q ])
    → ↓-='-out (↓-ap-in _ f u ∙ᵈ ↓-='-in' v ∙ᵈ ↓-ap-in _ f' w) == (↓-='-out u ∙□h (v ∙□h ↓-='-out w))  ∙□-i/ ap-∙∙`∘`∘ h f f' p r q / ! (ap-∙∙`∘`∘ g f f' p r q) /
  lemma-b {p = idp} {q = idp} r idp v idp = ch r v  where

    ch : ∀ {a b : B} (r : a == b) {p : g a == h a} {q : g b == h b} (v : (p , ap h r =□ ap g r , q))
         → ↓-='-out (idp ∙ᵈ ↓-='-in' v ∙ᵈ idp)
           == (,idp=□idp,-in idp ∙□h (v ∙□h ,idp=□idp,-in idp))
              ∙□-i/ ap-∙ h r idp / ! (ap-∙ g r idp) /
    ch idp v = ch2 (,idp=□idp,-out v) ∙ (,idp=□idp,-η v |in-ctx (λ u → ,idp=□idp,-in idp ∙□h (u ∙□h ,idp=□idp,-in idp)))  where

      ch2 : ∀ {i} {A : Type i} {a b : A} {p q : a == b} (v' : p == q)
            → ,idp=□idp,-in (v' ∙ idp) == ,idp=□idp,-in idp ∙□h (,idp=□idp,-in v' ∙□h ,idp=□idp,-in idp)
      ch2 {p = idp} v' = ch3 v'  where

        ch3 : ∀ {i} {A : Type i} {a : A} {q : a == a} (v' : idp == q)
              → idp,=□idp,-in (v' ∙ idp) == (,idp=□idp,-in idp ∙□h (idp,=□idp,-in v' ∙□h ,idp=□idp,-in idp))
        ch3 idp = idp

module _ {i} {A : Type i} where

  pp-coh : {a b b' c c' d d' e : A}
           {p : a == b}  {q : b == c}   {r : c == d}   {s : e == d}
           {t : b' == a} {u : b' == c'} {v : c' == d'} {w : d' == e}
    → (p , (q ∙ r ∙ (! s)) =□ (! t ∙ u ∙ v) , w) → (u , (v ∙ w ∙ s) =□ (t ∙ p ∙ q) , r)
  pp-coh {p = idp} {q} {idp} {idp} {idp} {idp} {idp} {idp} α = (! α) ∙ (∙-unit-r q)

  pp-coh! : {a b b' c c' d d' e : A}
            {u : b' == c'} {v : c' == d'} {w : d' == e} {s : e == d}
            {t : b' == a}  {p : a == b}   {q : b == c}  {r : c == d}
    → (u , (v ∙ w ∙ s) =□ (t ∙ p ∙ q) , r) → (p , (q ∙ r ∙ (! s)) =□ ((! t) ∙ u ∙ v) , w)
  pp-coh! {u = idp} {idp} {idp} {idp} {idp} {idp} {q} {idp} α = ∙-unit-r q ∙ (! α)

  pp-coh-β : {a b b' c c' d d' e : A}
             {u : b' == c'} {v : c' == d'} {w : d' == e} {s : e == d}
             {t : b' == a}  {p : a == b}   {q : b == c}  {r : c == d}
             (α : (u , (v ∙ w ∙ s) =□ (t ∙ p ∙ q) , r))
             → pp-coh {p = p} {q = q} {r = r} {s = s} {t = t} {u = u} {v = v} {w = w}
               (pp-coh! {u = u} {v = v} {w = w} {s = s} {t = t} {p = p} {q = q} {r = r} α) == α
  pp-coh-β {u = idp} {idp} {idp} {idp} {idp} {idp} {.idp} {idp} idp = idp

  pp-coh!-β : {a b b' c c' d d' e : A}
              {p : a == b}  {q : b == c}   {r : c == d}   {s : e == d}
              {t : b' == a} {u : b' == c'} {v : c' == d'} {w : d' == e}
              (α : (p , (q ∙ r ∙ (! s)) =□ (! t ∙ u ∙ v) , w))
              → pp-coh! {u = u} {v} {w} {s} {t} {p} {q} {r}
                (pp-coh {p = p} {q} {r} {s} {t} {u} {v} {w} α) == α
  pp-coh!-β {p = idp} {idp} {idp} {idp} {idp} {idp} {.idp} {idp} idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  ap-∙∙ : (f : A → B) {x y z t : A} (p : x == y) (q : y == z) (r : z == t) → ap f (p ∙ q ∙ r) == ap f p ∙ ap f q ∙ ap f r
  ap-∙∙ f idp q idp = ap-∙ f q idp

  ap-∙∙! : (f : A → B) {x y z t : A} (p : x == y) (q : y == z) (r : t == z) → ap f (p ∙ q ∙ ! r) == ap f p ∙ ap f q ∙ ! (ap f r)
  ap-∙∙! f idp q idp = ap-∙ f q idp

  ap-!∙∙ : (f : A → B) {x y z t : A} (p : y == x) (q : y == z) (r : z == t) → ap f (! p ∙ q ∙ r) == ! (ap f p) ∙ ap f q ∙ ap f r
  ap-!∙∙ f idp q idp = ap-∙ f q idp

module _ {i j k} {A : Type i} {B : Type j} {C₁ C₂ C₃ C₄ : Type k} {g₁ : C₁ → A} {g₂ : C₂ → A} {g₃ : C₃ → A} {g₄ : C₄ → A} (f : A → B) where

  ap□-pp-coh : {a b b' c c' d d' e : A}
               {p : a == b}  {q : b == c}   {r : c == d}   {s : e == d}
               {t : b' == a} {u : b' == c'} {v : c' == d'} {w : d' == e}
               (α : (p , (q ∙ r ∙ (! s)) =□ (! t ∙ u ∙ v) , w))
               → ap□ f (pp-coh {p = p} {q} {r} {s} {t} {u} {v} {w} α) == 
                 pp-coh {p = ap f p} {ap f q} {ap f r} {ap f s} {ap f t} {ap f u} {ap f v} {ap f w}
                   (ap□ f α ∙□-i/ ! (ap-∙∙! f q r s) / ap-!∙∙ f t u v /)
                 ∙□-i/ ap-∙∙ f v w s / ! (ap-∙∙ f t p q) /
  ap□-pp-coh {p = idp} {q} {idp} {idp} {idp} {idp} {idp} {idp} α = c q idp α  where

    c : {a b : A} (q q' : a == b) (α : q ∙ idp == q')
        → ap (ap f) (! α ∙ ∙-unit-r q) ==
          (! (ap (ap f) α ∙□-i/ ! (ap-∙∙! f q idp idp) / idp /) ∙
          ∙-unit-r (ap f q))
          ∙□-i/ idp / ! (ap-∙∙ f idp idp q) /
    c idp q' α = d α  where

      d : {a b : A} {q q' : a == b} (α : q == q')
          → ap (ap f) (! α ∙ idp) == ! (ap (ap f) α) ∙ idp
      d idp = idp

  ap□-coh : {a₁ b₁ : C₁} {a₂ b₂ : C₂} {a₃ b₃ : C₃} {a₄ b₄ : C₄}
               {p : g₃ b₃ == g₁ a₁} {q : a₁ == b₁}       {r : g₁ b₁ == g₂ b₂} {s : a₂ == b₂}
               {t : a₃ == b₃}       {u : g₃ a₃ == g₄ a₄} {v : a₄ == b₄}       {w : g₄ b₄ == g₂ a₂}
               (α : (p , (ap g₁ q ∙ r ∙ (! (ap g₂ s))) =□ (! (ap g₃ t) ∙ u ∙ ap g₄ v) , w))
               → ap□ f (pp-coh {p = p} {ap g₁ q} {r} {ap g₂ s} {ap g₃ t} {u} {ap g₄ v} {w} α) == 
                 pp-coh {p = ap f p} {ap (f ∘ g₁) q} {ap f r} {ap (f ∘ g₂) s} {ap (f ∘ g₃) t} {ap f u} {ap (f ∘ g₄) v} {ap f w}
                   (ap□ f α ∙□-i/ ! (ap-∙∙!'`∘`∘ f g₁ g₂ q r s) / ap-!'∙∙`∘`∘ f g₃ g₄ t u v /)
                 ∙□-i/ ap-∙∙`∘`∘ f g₄ g₂ v w s / ! (ap-∙∙`∘`∘ f g₃ g₁ t p q) /
  ap□-coh {p = p} {idp} {r} {idp} {idp} {u} {idp} {w} α = ap□-pp-coh {p = p} {idp} {r} {idp} {idp} {u} {idp} {w} α

module _ {i j k} {A : Type i} {B : Type j} {C₁ C₂ C₃ C₄ : Type k} {g₁ : C₁ → A} {g₂ : C₂ → A} {g₃ : C₃ → A} {g₄ : C₄ → A} (f : A → B) where

  ap□-pp-coh! : {a b b' c c' d d' e : A}
               {u : b' == c'} {v : c' == d'} {w : d' == e} {s : e == d}
               {t : b' == a}  {p : a == b}   {q : b == c}  {r : c == d}
               (α : (u , (v ∙ w ∙ s) =□ (t ∙ p ∙ q) , r))
               → ap□ f (pp-coh! {u = u} {v} {w} {s} {t} {p} {q} {r} α) == 
                 pp-coh! {u = ap f u} {ap f v} {ap f w} {ap f s} {ap f t} {ap f p} {ap f q} {ap f r}
                   (ap□ f α ∙□-i/ ! (ap-∙∙ f v w s) / ap-∙∙ f t p q /)
                 ∙□-i/ ap-∙∙! f q r s / ! (ap-!∙∙ f t u v) /
  ap□-pp-coh! {u = idp} {idp} {idp} {idp} {idp} {idp} {.idp} {idp} idp = idp

  ap□-coh! : {a₁ b₁ : C₁} {a₂ b₂ : C₂} {a₃ b₃ : C₃} {a₄ b₄ : C₄}
               {u : g₃ a₃ == g₄ a₄} {v : a₄ == b₄}       {w : g₄ b₄ == g₂ a₂} {s : a₂ == b₂}
               {t : a₃ == b₃}       {p : g₃ b₃ == g₁ a₁} {q : a₁ == b₁}       {r : g₁ b₁ == g₂ b₂}
               (α : (u , (ap g₄ v ∙ w ∙ ap g₂ s) =□ (ap g₃ t ∙ p ∙ ap g₁ q) , r))
               → ap□ f (pp-coh! {u = u} {ap g₄ v} {w} {ap g₂ s} {ap g₃ t} {p} {ap g₁ q} {r} α) == 
                 pp-coh! {u = ap f u} {ap (f ∘ g₄) v} {ap f w} {ap (f ∘ g₂) s} {ap (f ∘ g₃) t} {ap f p} {ap (f ∘ g₁) q} {ap f r}
                   (ap□ f α ∙□-i/ ! (ap-∙∙`∘`∘ f g₄ g₂ v w s) / ap-∙∙`∘`∘ f g₃ g₁ t p q /)
                 ∙□-i/ ap-∙∙!'`∘`∘ f g₁ g₂ q r s / ! (ap-!'∙∙`∘`∘ f g₃ g₄ t u v) /
  ap□-coh! {u = u} {idp} {w} {idp} {idp} {p} {idp} {r} α = ap□-pp-coh! {u = u} {idp} {w} {idp} {idp} {p} {idp} {r} α

module _ {i} {A : Type i} where

  lemma : {a b b' c c' d d' e : A}
          {u u' : b' == c'} {v : c' == d'} {w w' : d' == e} {s : e == d}
          {t : b' == a}  {p p' : a == b}   {q : b == c}  {r r' : c == d}
          (β : u' == u) (γ : w' == w) (δ : p' == p) (ε : r' == r)
          (α : (u , (v ∙ w ∙ s) =□ (t ∙ p ∙ q) , r))
          → pp-coh {p = p'} {q} {r'} {s} {t} {u'} {v} {w'}
             (pp-coh! {u = u} {v} {w} {s} {t} {p} {q} {r} α
              ∙□-o/ δ / ! γ /
              ∙□-i/ ε |in-ctx (λ x → q ∙ x ∙ ! s) / (! β) |in-ctx (λ x → ! t ∙ x ∙ v) /) == α ∙□-o/ β / ! ε / ∙□-i/ γ |in-ctx (λ x → v ∙ x ∙ s) / (! δ) |in-ctx (λ x → t ∙ x ∙ q) /
  lemma {u = u} {v = v} {w = w} {s = s} {t = t} {p = p} {q = q} {r = r} idp idp idp idp α = pp-coh-β {u = u} {v = v} {w = w} {s = s} {t = t} {p = p} {q = q} {r = r} α

  lemma! : {a b b' c c' d d' e : A}
           {p p' : a == b} {q : b == c}      {r r' : c == d} {s : e == d}
           {t : b' == a}   {u u' : b' == c'} {v : c' == d'}  {w w' : d' == e}
           (β : p' == p) (γ : r' == r) (δ : u' == u) (ε : w' == w)
           (α : (p , (q ∙ r ∙ (! s)) =□ (! t ∙ u ∙ v) , w))
           → pp-coh! {u = u'} {v} {w'} {s} {t} {p'} {q} {r'}
               (pp-coh {p = p} {q} {r} {s} {t} {u} {v} {w} α
                ∙□-o/ δ / ! γ /
                ∙□-i/ ε |in-ctx (λ w → v ∙ w ∙ s) / (! β) |in-ctx (λ p → t ∙ p ∙ q) /) == α ∙□-o/ β / ! ε / ∙□-i/ γ |in-ctx (λ r → q ∙ r ∙ ! s) / (! δ) |in-ctx (λ u → ! t ∙ u ∙ v) /
  lemma! {p = p} {q = q} {r = r} {s = s} {t = t} {u = u} {v = v} {w = w} idp idp idp idp α = pp-coh!-β {p = p} {q} {r} {s} {t} {u} {v} {w} α

module _ {i j} {A : Type i} {B : A → Type j} where

  coh1 : {a b : A} {α : a == b} {u v : B a} {w x : B b}
         {p : u == w [ B ↓ α ]} {q : w == x} {r : u == v} {s : v == x [ B ↓ α ]}
         → (r , s =□d-i p , q) → p == s ◃/ r / ! q /
  coh1 {α = idp} {p = idp} {idp} {idp} {s} β = ! β

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f g : A → B) (h : B → C) where

  ap↓-↓-='-in-β : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    (α : (u , ap g p =□ ap f p , v))
    → ap↓ (ap h) {p = p} {u = u} {v = v} (↓-='-in' {p = p} α)
    == ↓-='-in' ((ap□ h α) ∙□-i/ (ap-∘ h g p) / (∘-ap h f p) /)
  ap↓-↓-='-in-β {p = idp} = t  where

    t : {x y : B} {u v : x == y} (α : (u , idp =□ idp , v))
        → ap (ap h) (,idp=□idp,-out α) == ,idp=□idp,-out (ap□ h α)
    t {u = idp} {v} = t'  where

      t' : {x y : B} {u v : x == y} (α : (idp , u =□ idp , v))
         → ap (ap h) (idp,=□idp,-out α) == idp,=□idp,-out (ap□ h α)
      t' {u} {v = idp} α = idp

  ap□-↓-='-out-β : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    (α : u == v [ (λ x → f x == g x) ↓ p ])
    → ap□ h (↓-='-out α) == ↓-='-out (ap↓ (ap h) α) ∙□-i/ ∘-ap h g p / ap-∘ h f p /
  ap□-↓-='-out-β {p = idp} idp = ap□-,idp=□idp,-in h idp

thing : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
        {x y : A} {p : x == y} {u u' : f x == g x} {v v' : f y == g y}
        (α : (u , ap g p =□ ap f p , v)) (r : u' == u) (s : v == v')
        → ↓-='-out (↓-='-in' α ◃/ r / s /) == α ∙□-o/ r / s /
thing α idp idp = ↓-='-β α

ap↓-∘ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : A → Type k} {D : A → Type l}
  (f : {a : A} → C a → D a) (g : {a : A} → B a → C a)
  {x y : A} {p : x == y} {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → ap↓ (f ∘ g) q == ap↓ f (ap↓ g q)
ap↓-∘ f g {p = idp} idp = idp

ap↓-◃/ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : {a : A} → B a → C a) {x y : A} {p : x == y} {u u' : B x} {v v' : B y}
  (q : u == v [ B ↓ p ]) (r : u' == u) (s : v == v')
  → ap↓ f (q ◃/ r / s /) == ap↓ f q ◃/ ap f r / ap f s /
ap↓-◃/ f {p = idp} idp idp idp = idp

ap□-∙□-i/ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  {a b b' c : A} {p : a == b} {q q' : b == c} {r r' : a == b'} {s : b' == c}
  (α : (p , q =□ r , s)) (t : q' == q) (u : r == r')
  → ap□ f (α ∙□-i/ t / u /) == ap□ f α ∙□-i/ ap (ap f) t / ap (ap f) u /
ap□-∙□-i/ f {p = idp} {s = idp} idp idp idp = idp

ap-∘^3-coh : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (h : C → D) (g : B → C) (f : A → B) {a b : A} (p : a == b)
  → ap (ap h) (∘-ap g f p) ∙ ∘-ap h (g ∘ f) p ∙ ap-∘ (h ∘ g) f p == ∘-ap h g (ap f p)
ap-∘^3-coh h g f idp = idp

ap-∘^3-coh' : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (h : C → D) (g : B → C) (f : A → B) {a b : A} (p : a == b)
  → ∘-ap (h ∘ g) f p ∙ ap-∘ h (g ∘ f) p ∙ ap (ap h) (ap-∘ g f p) == ap-∘ h g (ap f p)
ap-∘^3-coh' h g f idp = idp

ap-∘-ap-coh : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) {a b : A} {p q : a == b} (α : p == q)
  → ap (ap g) (! α |in-ctx (ap f)) ∙ ∘-ap g f p ∙ (α |in-ctx (ap (g ∘ f)))
  == ∘-ap g f q
ap-∘-ap-coh g f idp = ∙-unit-r _

ap-∘-ap-coh' : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) {a b : A} {p q : a == b} (α : p == q)
  → (! α |in-ctx (ap (g ∘ f))) ∙ ap-∘ g f p ∙ ap (ap g) (α |in-ctx (ap f))
  == ap-∘ g f q
ap-∘-ap-coh' g f idp = ∙-unit-r _

ap-∘-ap-coh'2 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) {a b : A} {p q : a == b} (α : p == q)
  → (! (α |in-ctx (ap (g ∘ f)))) ∙ ap-∘ g f p ∙ ap (ap g) (α |in-ctx (ap f))
  == ap-∘ g f q
ap-∘-ap-coh'2 g f {p = idp} idp = idp


module _ {i i' j k l} {A : Type i} {A' : Type i'} {B : Type j} {C : Type k} {D : Type l}
  (f2 : C → D) (f1 : B → C) (g : A → B) (h : A' → B) where

  ap-∘-ap-∙∙!`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : d == c)
    → ! (ap-∙∙!'`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p (ap f1 q) r)
      ∙ ap (ap f2) (! (ap-∙∙!`∘`∘ f1 g h p q r))
      ∙ ∘-ap f2 f1 (ap g p ∙ q ∙ ap h (! r))
      ∙ ap-∙∙!`∘`∘ (f2 ∘ f1) g h p q r
      == ((∘-ap f2 f1 q) |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ! (ap (f2 ∘ f1 ∘ h) r)))
  ap-∘-ap-∙∙!`∘`∘-coh idp q idp = coh q  where

    coh : {a b : B} (q : a == b) →
          ! (ap-∙ f2 (ap f1 q) idp)
          ∙ ap (ap f2) (! (ap-∙ f1 q idp))
          ∙ ∘-ap f2 f1 (q ∙ idp)
          ∙ ap-∙ (f2 ∘ f1) q idp
          == ap (λ u → u ∙ idp) (∘-ap f2 f1 q)
    coh idp = idp

  ap-∘-ap-!∙∙`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) (q : g a == h c) (r : c == d)
    → ! (ap-!∙∙`∘`∘ (f2 ∘ f1) g h p q r)
      ∙ ap-∘ f2 f1 (ap g (! p) ∙ q ∙ ap h r)
      ∙ ap (ap f2) (ap-!∙∙`∘`∘ f1 g h p q r)
      ∙ ap-!'∙∙`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p (ap f1 q) r
      == ((ap-∘ f2 f1 q) |in-ctx (λ u → ! (ap (f2 ∘ f1 ∘ g) p) ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
  ap-∘-ap-!∙∙`∘`∘-coh idp q idp = coh q where

    coh : {a b : B} (q : a == b)
          → ! (ap-∙ (f2 ∘ f1) q idp) ∙ ap-∘ f2 f1 (q ∙ idp) ∙ ap (ap f2) (ap-∙ f1 q idp) ∙ ap-∙ f2 (ap f1 q) idp
          == ap (λ u → u ∙ idp) (ap-∘ f2 f1 q)
    coh idp = idp

  ap-∘-ap-∙∙2`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : c == d)
    → ! (ap-∙∙`∘`∘ (f2 ∘ f1) g h p q r)
      ∙ ap-∘ f2 f1 (ap g p ∙ q ∙ ap h r)
      ∙ ap (ap f2) (ap-∙∙`∘`∘ f1 g h p q r)
      ∙ ap-∙∙`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p (ap f1 q) r
      == ((ap-∘ f2 f1 q) |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
  ap-∘-ap-∙∙2`∘`∘-coh idp q idp = coh q where

    coh : {a b : B} (q : a == b)
          → ! (ap-∙ (f2 ∘ f1) q idp) ∙ ap-∘ f2 f1 (q ∙ idp) ∙ ap (ap f2) (ap-∙ f1 q idp) ∙ ap-∙ f2 (ap f1 q) idp
          == ap (λ u → u ∙ idp) (ap-∘ f2 f1 q)
    coh idp = idp

  ap-∘-ap-∙∙3`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) (q : g b == h c) (r : c == d)
    → ! (ap-∙∙`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p (ap f1 q) r)
      ∙ ap (ap f2) (! (ap-∙∙`∘`∘ f1 g h p q r))
      ∙ ∘-ap f2 f1 (ap g p ∙ q ∙ ap h r)
      ∙ ap-∙∙`∘`∘ (f2 ∘ f1) g h p q r
      == ((∘-ap f2 f1 q) |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
  ap-∘-ap-∙∙3`∘`∘-coh idp q idp = coh q  where

    coh : {a b : B} (q : a == b) →
          ! (ap-∙ f2 (ap f1 q) idp)
          ∙ ap (ap f2) (! (ap-∙ f1 q idp))
          ∙ ∘-ap f2 f1 (q ∙ idp)
          ∙ ap-∙ (f2 ∘ f1) q idp
          == ap (λ u → u ∙ idp) (∘-ap f2 f1 q)
    coh idp = idp

  ap-∘-ap-∙∙4`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) {q : g b == h c} {q' : f1 (g b) == f1 (h c)} (α : ap f1 q == q') (r : c == d)
    → ap-∘ f2 f1 (ap g p ∙ q ∙ ap h r)
      ∙ ap (ap f2) (ap-∙∙`∘`∘ f1 g h p q r)
      ∙ ap (ap f2) (α |in-ctx (λ u → ap (f1 ∘ g) p ∙ u ∙ ap (f1 ∘ h) r))
      ∙ ap-∙∙`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p q' r
      ==
      ap-∙∙`∘`∘ (f2 ∘ f1) g h p q r
      ∙ (ap-∘ f2 f1 q |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
      ∙ (ap (ap f2) α |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
  ap-∘-ap-∙∙4`∘`∘-coh idp {q = q} idp idp = coh q  where

    coh : {a b : B} (q : a == b)
          → ap-∘ f2 f1 (q ∙ idp) ∙ ap (ap f2) (ap-∙ f1 q idp) ∙ ap-∙ f2 (ap f1 q) idp
          == ap-∙ (f2 ∘ f1) q idp ∙ ap (λ u → u ∙ idp) (ap-∘ f2 f1 q) ∙ idp
    coh idp = idp

  ap-∘-ap-∙∙5`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) {q : g a == h c} {q' : f1 (g a) == f1 (h c)} (α : ap f1 q == q') (r : c == d)
    → ap-∘ f2 f1 (ap g (! p) ∙ q ∙ ap h r)
      ∙ ap (ap f2) (ap-!∙∙`∘`∘ f1 g h p q r)
      ∙ ap (ap f2) (α |in-ctx (λ u → ! (ap (f1 ∘ g) p) ∙ u ∙ ap (f1 ∘ h) r))
      ∙ ap-!'∙∙`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p q' r
      ==
      ap-∙∙`∘`∘ (f2 ∘ f1) g h (! p) q r
      ∙ (ap-∘ f2 f1 q |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) (! p) ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
      ∙ (ap (ap f2) α |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) (! p) ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
      ∙ (ap-! (f2 ∘ f1 ∘ g) p |in-ctx (λ u → u ∙ ap f2 q' ∙ ap (f2 ∘ f1 ∘ h) r))
  ap-∘-ap-∙∙5`∘`∘-coh idp {q = q} idp idp = coh q  where

    coh : {a b : B} (q : a == b)
          → ap-∘ f2 f1 (q ∙ idp) ∙ ap (ap f2) (ap-∙ f1 q idp) ∙ ap-∙ f2 (ap f1 q) idp
          == ap-∙ (f2 ∘ f1) q idp ∙ ap (λ u → u ∙ idp) (ap-∘ f2 f1 q) ∙ idp
    coh idp = idp

  ap-∘-ap-∙∙`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) {q : g b == h c} {q' : f1 (g b) == f1 (h c)} (α : ap f1 q == q') (r : c == d)
    → ap (ap f2) (ap-∙∙`∘`∘ f1 g h p q r)
      ∙ ap (ap f2) (α |in-ctx (λ u → ap (f1 ∘ g) p ∙ u ∙ ap (f1 ∘ h) r))
      ∙ ap-∙∙`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p q' r
      ==
      ∘-ap f2 f1 (ap g p ∙ q ∙ ap h r)
      ∙ ap-∙∙`∘`∘ (f2 ∘ f1) g h p q r
      ∙ (ap-∘ f2 f1 q |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
      ∙ (ap (ap f2) α |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ap (f2 ∘ f1 ∘ h) r))
  ap-∘-ap-∙∙`∘`∘-coh idp {q = q} idp idp = coh q  where

    coh : {a b : B} (q : a == b)
          → ap (ap f2) (ap-∙ f1 q idp) ∙ ap-∙ f2 (ap f1 q) idp
          == ∘-ap f2 f1 (q ∙ idp) ∙ ap-∙ (f2 ∘ f1) q idp ∙ ap (λ u → u ∙ idp) (ap-∘ f2 f1 q) ∙ idp
    coh idp = idp

  ap-∘-ap-∙∙!'`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) {q : g b == h c} {q' : f1 (g b) == f1 (h c)} (α : ap f1 q == q') (r : d == c)
    → ap (ap f2) (ap-∙∙!`∘`∘ f1 g h p q r)
      ∙ ap (ap f2) (α |in-ctx (λ u → ap (f1 ∘ g) p ∙ u ∙ ! (ap (f1 ∘ h) r)))
      ∙ ap-∙∙!'`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p q' r
      ==
      ∘-ap f2 f1 (ap g p ∙ q ∙ ap h (! r))
      ∙ ap-∙∙!`∘`∘ (f2 ∘ f1) g h p q r
      ∙ (ap-∘ f2 f1 q |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ! (ap (f2 ∘ f1 ∘ h) r)))
      ∙ (ap (ap f2) α |in-ctx (λ u → ap (f2 ∘ f1 ∘ g) p ∙ u ∙ ! (ap (f2 ∘ f1 ∘ h) r)))
  ap-∘-ap-∙∙!'`∘`∘-coh idp {q = q} idp idp = coh q  where

    coh : {a b : B} (q : a == b)
          → ap (ap f2) (ap-∙ f1 q idp) ∙ ap-∙ f2 (ap f1 q) idp
          == ∘-ap f2 f1 (q ∙ idp) ∙ ap-∙ (f2 ∘ f1) q idp ∙ ap (λ u → u ∙ idp) (ap-∘ f2 f1 q) ∙ idp
    coh idp = idp

  ap-∘-ap-∙∙!'2`∘`∘-coh : {a b : A} {c d : A'} (p : a == b) {q : g b == h c} {q' : f1 (g b) == f1 (h c)} (α : ap f1 q == q') (r : d == c)
    → ap (ap f2) (ap-∙∙!`∘`∘ f1 g h p q r)
      ∙ ap (ap f2) (α |in-ctx (λ u → ap (f1 ∘ g) p ∙ u ∙ ! (ap (f1 ∘ h) r)))
      ∙ ap-∙∙!'`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p q' r
      ==
      ap (ap f2) (ap-∙∙`∘`∘ f1 g h p q (! r))
      ∙ ap (ap f2) (α |in-ctx (λ u → ap (f1 ∘ g) p ∙ u ∙ ap (f1 ∘ h) (! r)))
      ∙ ap-∙∙!`∘`∘ f2 (f1 ∘ g) (f1 ∘ h) p q' r
  ap-∘-ap-∙∙!'2`∘`∘-coh idp {q = q} idp idp = idp

module _ {i i' j k} {A : Type i} {A' : Type i'} {B : Type j} {C : Type k}
  (f : B → C) (g : A → B) (h : A' → B) where

  ap-!∙∙`∘`∘-coh : {a b : A} {c d : A'} (p : b == a) {q : g b == h c} {q' : f (g b) == f (h c)} (α : ap f q == q') (r : c == d)
    → ap-!∙∙`∘`∘ f g h p q r
      ∙ ap (λ u → ! (ap (f ∘ g) p) ∙ u ∙ ap (f ∘ h) r) α
      ∙ ! (ap-! (f ∘ g) p |in-ctx (λ u → u ∙ q' ∙ ap (f ∘ h) r))
      ==
      ap-∙∙`∘`∘ f g h (! p) q r
      ∙' ap (λ u → ap (f ∘ g) (! p) ∙ u ∙ ap (f ∘ h) r) α
  ap-!∙∙`∘`∘-coh idp {q = q} idp idp = ∙-unit-r (ap-∙ f q idp)

  ap-∙∙!`∘`∘-coh1 : {a b : A} {c d : A'} (p : a == b) {q : g b == h c} {q' : f (g b) == f (h c)} (α : ap f q == q') (r : d == c)
    → ap-∙∙!`∘`∘ f g h p q r
      ∙ ap (λ u → ap (f ∘ g) p ∙ u ∙ ! (ap (f ∘ h) r)) α
      ==
      ap-∙∙`∘`∘ f g h p q (! r)
      ∙ ap (λ u → ap (f ∘ g) p ∙ u ∙ ap (f ∘ h) (! r)) α
      ∙ (ap-! (f ∘ h) r |in-ctx (λ u → ap (f ∘ g) p ∙ q' ∙ u))
  ap-∙∙!`∘`∘-coh1 idp {q = q} idp idp = idp

  ap-∙∙!`∘`∘-coh2 : {a b : A} {c d : A'} (p : a == b) {q : g b == h c} (r : d == c)
      → (ap-! (f ∘ h) r |in-ctx (λ u → ap (f ∘ g) p ∙ ap f q ∙ u))
        ∙ ! (ap-∙∙!`∘`∘ f g h p q r)
        ==
        ! (ap-∙∙`∘`∘ f g h p q (! r))
  ap-∙∙!`∘`∘-coh2 idp {q} idp = idp

ap-∘-coh : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (f : C → D) (g : B → C) (h : A → B) {a b : A} (p : a == b) {p' : h a == h b} (α : ap h p == p')
  → ap-∘ f (g ∘ h) p ∙ ap (ap f) (ap-∘ g h p) ∙ ap (ap f) (α |in-ctx (ap g)) ∙ ∘-ap f g p'
    == ap-∘ (f ∘ g) h p ∙ ap (ap (f ∘ g)) α
ap-∘-coh f g h idp idp = idp

ap-∘-coh2 : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (f : C → D) (g : B → C) (h : A → B) {a b : A} (p : a == b) {p' : h a == h b} (α : ap h p == p')
  → ap-∘ f (g ∘ h) p ∙ ap (ap f) (ap-∘ g h p) ∙ ap (ap f) (α |in-ctx (ap g))
    == ap-∘ (f ∘ g) h p ∙ ap (ap (f ∘ g)) α ∙ ap-∘ f g p'
ap-∘-coh2 f g h idp idp = idp

∙-|in-ctx : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c : A}
  (p : a == b) (q : b == c)
  → (p |in-ctx f) ∙ (q |in-ctx f) == ((p ∙ q) |in-ctx f)
∙-|in-ctx f idp idp = idp

∙□-i/-rewrite : ∀ {i} {A : Type i} {a b b' c : A} {p : a == b} {q q' : b == c}
  {r r' : a == b'} {s : b' == c}
  (α : (p , q =□ r , s)) {β β' : q' == q} (eqβ : β == β') {γ γ' : r == r'}
  (eqγ : γ == γ')
  → (α ∙□-i/ β / γ / == α ∙□-i/ β' / γ' /)
∙□-i/-rewrite α idp idp = idp
