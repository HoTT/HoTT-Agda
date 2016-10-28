{-# OPTIONS --without-K #-}

open import HoTT

{-
This file contains three proofs of Ω(S¹) = ℤ and the fact that the circle is
a 1-type:
- Something closely related to Mike’s original proof
- Dan’s encode-decode proof
- Guillaume’s proof using the flattening lemma.
This file is divided in a lot of different parts so that common parts can be
factored:

1. Definition of the universal cover and the encoding map (this part is common
   to all three proofs)
2. Proof that [encode (loop^ n) == n] (this part is common to Mike’s proof and
   the encode-decode proof)
3. Dan’s encode-decode proof that [Ω S¹ ≃ ℤ]
4. Mike’s proof that [Σ S¹ Cover] is contractible
5. Proof with the flattening lemma that [Σ S¹ S¹Cover] is contractible
6. Proof of [Ω S¹ ≃ ℤ] using the fact that [Σ S¹ S¹Cover] is contractible (common
   to Mike’s proof and the flattening lemma proof)
7. Encode-decode proof of the whole equivalence
8. Proof that the circle is a 1-type (common to all three proofs)

Keep
- 1, 2, 3    for the encode-decode proof    (+ 7, 8 for S¹ is a 1-type)
- 1, 2, 4, 6 for Mike’s proof               (+ 8)
- 1, 5, 6    for the flattening lemma proof (+ 8)
-}

module homotopy.LoopSpaceCircle where

{- 1. Universal cover and encoding map (common to all three proofs) -}

module S¹Cover = S¹RecType ℤ succ-equiv

S¹Cover : S¹ → Type₀
S¹Cover = S¹Cover.f

encode : {x : S¹} (p : base == x) → S¹Cover x
encode p = transport S¹Cover p 0

{- 2. Encoding [loop^ n] (common to Mike’s proof and the encode-decode proof) -}

-- We define the element of [Ω S¹] which is supposed to correspond to an
-- integer [n], this is the loop winding around the circle [n] times.
-- This is easy by induction on [n]
loop^ : (n : ℤ) → base == base
loop^ (pos O) = idp
loop^ (pos (S n)) = loop^ (pos n) ∙ loop
loop^ (negsucc O) = ! loop
loop^ (negsucc (S n)) = loop^ (negsucc n) ∙ (! loop)

-- Compatibility of [loop^] with the successor function
-- This is again not difficult by induction on [n]
loop^succ : (n : ℤ) → loop^ n ∙ loop == loop^ (succ n)
loop^succ (pos n) = idp
loop^succ (negsucc O) = !-inv-l loop
loop^succ (negsucc (S n)) =
  (loop^ (negsucc n) ∙ ! loop) ∙ loop
        =⟨ ∙-assoc (loop^ (negsucc n)) (! loop) loop ⟩
   loop^ (negsucc n) ∙ (! loop ∙ loop)
        =⟨ !-inv-l loop |in-ctx (λ u → loop^ (negsucc n) ∙ u) ⟩
   loop^ (negsucc n) ∙ idp
        =⟨ ∙-unit-r _ ⟩
   loop^ (negsucc n) ∎

-- Now we check that encoding [loop^ n] gives indeed [n], again by induction
-- on [n]
encode-loop^ : (n : ℤ) → encode (loop^ n) == n
encode-loop^ (pos O) = idp
encode-loop^ (pos (S n)) =
  encode (loop^ (pos n) ∙ loop) =⟨ idp ⟩
  coe (ap S¹Cover (loop^ (pos n) ∙ loop)) 0
       =⟨ ap-∙ S¹Cover (loop^ (pos n)) loop |in-ctx (λ u → coe u 0) ⟩
  coe (ap S¹Cover (loop^ (pos n)) ∙ ap S¹Cover loop) 0
       =⟨ coe-∙ (ap S¹Cover (loop^ (pos n)))
                (ap S¹Cover loop) 0 ⟩
  coe (ap S¹Cover loop) (coe (ap S¹Cover (loop^ (pos n))) 0)
       =⟨ encode-loop^ (pos n) |in-ctx coe (ap S¹Cover loop) ⟩
  coe (ap S¹Cover loop) (pos n)
       =⟨ S¹Cover.coe-loop-β (pos n) ⟩
  pos (S n) ∎
encode-loop^ (negsucc O) =
  coe (ap S¹Cover (! loop)) 0 =⟨ coe-ap-! S¹Cover loop 0 ⟩
  coe! (ap S¹Cover loop) 0 =⟨ S¹Cover.coe!-loop-β 0 ⟩
  negsucc O ∎
encode-loop^ (negsucc (S n)) =
  encode (loop^ (negsucc n) ∙ ! loop) =⟨ idp ⟩
  coe (ap S¹Cover (loop^ (negsucc n) ∙ ! loop)) 0
       =⟨ ap-∙ S¹Cover (loop^ (negsucc n)) (! loop)
          |in-ctx (λ u → coe u 0) ⟩
  coe (ap S¹Cover (loop^ (negsucc n)) ∙ ap S¹Cover (! loop)) 0
       =⟨ coe-∙ (ap S¹Cover (loop^ (negsucc n)))
                (ap S¹Cover (! loop)) 0 ⟩
  coe (ap S¹Cover (! loop)) (coe (ap S¹Cover (loop^ (negsucc n))) 0)
       =⟨ encode-loop^ (negsucc n) |in-ctx coe (ap S¹Cover (! loop)) ⟩
  coe (ap S¹Cover (! loop)) (negsucc n)
       =⟨ coe-ap-! S¹Cover loop (negsucc n) ⟩
  coe! (ap S¹Cover loop) (negsucc n)
       =⟨ S¹Cover.coe!-loop-β (negsucc n) ⟩
  negsucc (S n) ∎

{- 3. Dan’s encode-decode proof -}

-- The decoding function at [base] is [loop^], but we extend it to the whole
-- of [S¹] so that [decode-encode] becomes easier (and we need [loop^succ] to
-- be able to extend it)
decode : (x : S¹) → (S¹Cover x → base == x)
decode =
  S¹-elim loop^ (↓-→-in (λ {n} q →
                 ↓-cst=idf-in'
                   (loop^succ n ∙ ap loop^ (S¹Cover.↓-loop-out q))))

decode-encode : (x : S¹) (p : base == x) → decode x (encode p) == p
decode-encode _ p = J (λ x p → decode x (encode p) == p) idp p  -- Magic!

-- And we get the theorem
ΩS¹≃ℤ : (base == base) ≃ ℤ
ΩS¹≃ℤ = equiv encode (decode base) encode-loop^ (decode-encode base)

{- 4. Mike’s proof that [Σ S¹ Cover] is contractible -}

-- We want to prove that every point of [Σ S¹ S¹Cover] is equal to [(base , O)]
paths-mike : (xt : Σ S¹ S¹Cover) → (base , 0) == xt
paths-mike (x , t) = paths-mike-c x t where

  -- We do it by circle-induction on the first component. When it’s [base],
  -- we use the [↓-loop^] below (which is essentially [encode-loop^]) and
  -- for [loop] we use [loop^succ] and the fact that [ℤ] is a set.
  paths-mike-c : (x : S¹) (t : S¹Cover x) → (base , 0) == (x , t) :> Σ S¹ S¹Cover
  paths-mike-c = S¹-elim
    (λ n → pair= (loop^ n) (↓-loop^ n))
    (↓-Π-in (λ {n} {n'} q →
     ↓-cst=idf-in'
       (pair= (loop^ n) (↓-loop^ n) ∙ pair= loop q
                  =⟨ Σ-∙ (↓-loop^ n) q ⟩
        pair= (loop^ n ∙ loop) (↓-loop^ n ∙ᵈ q)
                  =⟨ pair== (loop^succ n ∙ ap loop^ (S¹Cover.↓-loop-out q))
                            (set-↓-has-all-paths-↓ ℤ-is-set) ⟩
        pair= (loop^ n') (↓-loop^ n') ∎))) where

    ↓-loop^ : (n : ℤ) → 0 == n [ S¹Cover ↓ loop^ n ]
    ↓-loop^ n = from-transp _ _ (encode-loop^ n)

contr-mike : is-contr (Σ S¹ S¹Cover)
contr-mike = ((base , 0) , paths-mike)

{- 5. Flattening lemma proof that [Σ S¹ Cover] is contractible -}

--We import the flattening lemma for the universal cover of the circle
--open FlatteningS¹ ℤ succ-equiv
open S¹Cover using (module Wt; Wt; cct; ppt; flattening-S¹)

-- We prove that the flattened HIT corresponding to the universal cover of the
-- circle (the real line) is contractible
Wt-is-contr : is-contr Wt
Wt-is-contr = (cct tt 0 , Wt.elim (base* ∘ snd) (loop* ∘ snd)) where

  -- This is basically [loop^]
  base* : (n : ℤ) → cct tt 0 == cct tt n
  base* (pos O) = idp
  base* (pos (S n)) = base* (pos n) ∙ ppt tt (pos n)
  base* (negsucc O) = ! (ppt tt (negsucc O))
  base* (negsucc (S n)) = base* (negsucc n) ∙ ! (ppt tt (negsucc (S n)))

  loop* : (n : ℤ)
    → base* n == base* (succ n) [ (λ x → cct tt 0 == x) ↓ ppt tt n ]
  loop* n = ↓-cst=idf-in' (aux n) where

    -- This is basically [loop^succ]
    aux : (n : ℤ) → base* n ∙ ppt tt n == base* (succ n)
    aux (pos n) = idp
    aux (negsucc O) = !-inv-l (ppt tt (negsucc O))
    aux (negsucc (S n)) =
      base* (negsucc (S n)) ∙ ppt tt (negsucc (S n))
                =⟨ idp ⟩
      (base* (negsucc n) ∙ ! (ppt tt (negsucc (S n)))) ∙ ppt tt (negsucc (S n))
                =⟨ ∙-assoc (base* (negsucc n)) _ _ ⟩
      base* (negsucc n) ∙ (! (ppt tt (negsucc (S n))) ∙ ppt tt (negsucc (S n)))
                =⟨ !-inv-l (ppt tt (negsucc (S n)))
                       |in-ctx (λ u → base* (negsucc n) ∙ u) ⟩
      base* (negsucc n) ∙ idp
                =⟨ ∙-unit-r _ ⟩
      base* (negsucc n) ∎

-- Then, using the flattening lemma we get that the total space of [Cover] is
-- contractible
contr-flattening : is-contr (Σ S¹ S¹Cover)
contr-flattening = transport! is-contr flattening-S¹ Wt-is-contr

{- 6. Proof that [Ω S¹ ≃ ℤ] using the fact that [Σ S¹ Cover] is contractible -}

tot-encode : Σ S¹ (λ x → base == x) → Σ S¹ S¹Cover
tot-encode (x , y) = (x , encode y)

-- The previous map induces an equivalence on the total spaces, because both
-- total spaces are contractible
total-is-equiv : is-equiv tot-encode
total-is-equiv = contr-to-contr-is-equiv _ (pathfrom-is-contr base) contr-flattening

-- Hence it’s an equivalence fiberwise
encode-is-equiv : (x : S¹) → is-equiv (encode {x})
encode-is-equiv = total-equiv-is-fiber-equiv (λ _ → encode) total-is-equiv

-- We can then conclude that the loop space of the circle is equivalent to [ℤ]
ΩS¹≃ℤ' : (base == base) ≃ ℤ
ΩS¹≃ℤ' = (encode {base} , encode-is-equiv base)

{- 7. Encode-decode proof of the whole fiberwise equivalence -}

-- This is quite similar to [paths-mike], we’re doing it by circle-induction,
-- the base case is [encode-loop^] and the loop case is using the fact that [ℤ]
-- is a set (and [loop^succ] is already used in [decode])
encode-decode : (x : S¹) (t : S¹Cover x) → encode (decode x t) == t
encode-decode =
  S¹-elim {P = λ x → (t : S¹Cover x) → encode (decode x t) == t}
    encode-loop^ (↓-Π-in (λ q → prop-has-all-paths-↓ (ℤ-is-set _ _)))

encode-is-equiv' : (x : S¹) → is-equiv (encode {x})
encode-is-equiv' x = is-eq encode (decode x) (encode-decode x) (decode-encode x)

{- 8. Proof that the circle is a 1-type -}

S¹Cover-is-set : (y : S¹) → is-set (S¹Cover y)
S¹Cover-is-set = S¹-elim ℤ-is-set (prop-has-all-paths-↓ is-set-is-prop)

ΩS¹-is-set : (y : S¹) → is-set (base == y)
ΩS¹-is-set y = equiv-preserves-level ((encode {y} , encode-is-equiv y) ⁻¹)
                                     (S¹Cover-is-set y)

S¹-level : has-level 1 S¹
S¹-level =
  S¹-elim ΩS¹-is-set (prop-has-all-paths-↓ (Π-level (λ x → is-set-is-prop)))
