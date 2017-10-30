{-# OPTIONS --without-K --rewriting #-}

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

{- 2017/02/09 favonia:

  1. [loop^] is defined in terms of [Group.exp], and the lemma
     [encode'-decode] is changed accordingly.  Although the original
     [encode-decode] can be proved without the generalized [encode'],
     [encode'] seems useful in proving the isomorphism (not just
     type equivalence) without flipping the two sides [Ω S¹] and [ℤ].

  2. Part 9 is added for further results.
-}

module homotopy.LoopSpaceCircle where

{- 1. Universal cover and encoding map (common to all three proofs) -}

module S¹Cover = S¹RecType ℤ succ-equiv

S¹Cover : S¹ → Type₀
S¹Cover = S¹Cover.f

encode' : {x₁ x₂ : S¹} (p : x₁ == x₂) → S¹Cover x₁ → S¹Cover x₂
encode' p n = transport S¹Cover p n

encode : {x : S¹} (p : base == x) → S¹Cover x
encode p = encode' p 0

{- 2. Encoding [loop^ n] (common to Mike’s proof and the encode-decode proof) -}

ΩS¹-group-structure : GroupStructure (base == base)
ΩS¹-group-structure = Ω^S-group-structure 0 ⊙S¹

module ΩS¹GroupStruct = GroupStructure ΩS¹-group-structure

-- We define the element of [Ω S¹] which is supposed to correspond to an
-- integer [n], this is the loop winding around the circle [n] times.
loop^ : (n : ℤ) → base == base
loop^ = ΩS¹GroupStruct.exp loop

-- Compatibility of [loop^] with the addition function
abstract
  loop^+ : (n₁ n₂ : ℤ) → loop^ (n₁ ℤ+ n₂) == loop^ n₁ ∙ loop^ n₂
  loop^+ = ΩS¹GroupStruct.exp-+ loop

-- Now we check that encoding [loop^ n] gives indeed [n], again by induction
-- on [n]
abstract
  encode'-∙ : ∀ {x₀ x₁ x₂} (p₀ : x₀ == x₁) (p₁ : x₁ == x₂) n
    → encode' (p₀ ∙ p₁) n == encode' p₁ (encode' p₀ n)
  encode'-∙ idp _ _ = idp

  encode'-loop : ∀ n → encode' loop n == succ n
  encode'-loop = S¹Cover.coe-loop-β

  encode'-!loop : ∀ n → encode' (! loop) n == pred n
  encode'-!loop n = coe-ap-! S¹Cover loop n ∙ S¹Cover.coe!-loop-β n

abstract
  encode'-loop^ : (n₁ n₂ : ℤ) → encode' (loop^ n₁) n₂ == n₁ ℤ+ n₂
  encode'-loop^ (pos 0) n₂ = idp
  encode'-loop^ (pos 1) n₂ = encode'-loop n₂
  encode'-loop^ (pos (S (S n₁))) n₂ =
    encode' (loop ∙ loop^ (pos (S n₁))) n₂
         =⟨ encode'-∙ loop (loop^ (pos (S n₁))) n₂ ⟩
    encode' (loop^ (pos (S n₁))) (encode' loop n₂)
         =⟨ encode'-loop n₂ |in-ctx encode' (loop^ (pos (S n₁))) ⟩
    encode' (loop^ (pos (S n₁))) (succ n₂)
         =⟨ encode'-loop^ (pos (S n₁)) (succ n₂) ⟩
    pos (S n₁) ℤ+ succ n₂
         =⟨ ℤ+-succ (pos (S n₁)) n₂ ⟩
    pos (S (S n₁)) ℤ+ n₂ =∎
  encode'-loop^ (negsucc 0) n₂ = encode'-!loop n₂
  encode'-loop^ (negsucc (S n₁)) n₂ =
    encode' (! loop ∙ loop^ (negsucc n₁)) n₂
         =⟨ encode'-∙ (! loop) (loop^ (negsucc n₁)) n₂ ⟩
    encode' (loop^ (negsucc n₁)) (encode' (! loop) n₂)
         =⟨ encode'-!loop n₂ |in-ctx encode' (loop^ (negsucc n₁)) ⟩
    encode' (loop^ (negsucc n₁)) (pred n₂)
         =⟨ encode'-loop^ (negsucc n₁) (pred n₂) ⟩
    negsucc n₁ ℤ+ pred n₂
         =⟨ ℤ+-pred (negsucc n₁) n₂ ⟩
    negsucc (S n₁) ℤ+ n₂
         =∎

  encode-loop^ : (n : ℤ) → encode (loop^ n) == n
  encode-loop^ n = encode'-loop^ n 0 ∙ ℤ+-unit-r n

{- 3. Dan’s encode-decode proof -}

-- The decoding function at [base] is [loop^], but we extend it to the whole
-- of [S¹] so that [decode-encode] becomes easier (and we need [loop^+] to
-- be able to extend it)
decode : (x : S¹) → (S¹Cover x → base == x)
decode =
  S¹-elim loop^ (↓-→-in λ {n} q →
                 ↓-cst=idf-in' $
                   ! (loop^+ n 1) ∙ ap loop^ (ℤ+-comm n 1 ∙ S¹Cover.↓-loop-out q))

abstract
  decode-encode : (x : S¹) (p : base == x) → decode x (encode p) == p
  decode-encode _ idp = idp  -- Magic!

-- And we get the theorem
ΩS¹≃ℤ : (base == base) ≃ ℤ
ΩS¹≃ℤ = equiv encode (decode base) encode-loop^ (decode-encode base)

{- 4. Mike’s proof that [Σ S¹ Cover] is contractible -}

-- We want to prove that every point of [Σ S¹ S¹Cover] is equal to [(base , O)]
paths-mike : (xt : Σ S¹ S¹Cover) → (base , 0) == xt
paths-mike (x , t) = paths-mike-c x t where

  abstract
    -- We do it by circle-induction on the first component. When it’s [base],
    -- we use the [↓-loop^] below (which is essentially [encode-loop^]) and
    -- for [loop] we use [loop^+] and the fact that [ℤ] is a set.
    paths-mike-c : (x : S¹) (t : S¹Cover x) → (base , 0) == (x , t) :> Σ S¹ S¹Cover
    paths-mike-c = S¹-elim
      (λ n → pair= (loop^ n) (↓-loop^ n))
      (↓-Π-in (λ {n} {n'} q →
       ↓-cst=idf-in'
         (pair= (loop^ n) (↓-loop^ n) ∙ pair= loop q
                    =⟨ Σ-∙ (↓-loop^ n) q ⟩
          pair= (loop^ n ∙ loop) (↓-loop^ n ∙ᵈ q)
                    =⟨ pair== (! (loop^+ n 1) ∙ ap loop^ (ℤ+-comm n 1 ∙ S¹Cover.↓-loop-out q))
                              set-↓-has-all-paths-↓ ⟩
          pair= (loop^ n') (↓-loop^ n') ∎))) where

      ↓-loop^ : (n : ℤ) → 0 == n [ S¹Cover ↓ loop^ n ]
      ↓-loop^ n = from-transp _ _ (encode-loop^ n)

abstract
  contr-mike : is-contr (Σ S¹ S¹Cover)
  contr-mike = has-level-make ((base , 0) , paths-mike)

{- 5. Flattening lemma proof that [Σ S¹ Cover] is contractible -}

--We import the flattening lemma for the universal cover of the circle
--open FlatteningS¹ ℤ succ-equiv
open S¹Cover using (module Wt; Wt; cct; ppt; flattening-S¹)

-- We prove that the flattened HIT corresponding to the universal cover of the
-- circle (the real line) is contractible
Wt-is-contr : is-contr Wt
Wt-is-contr = has-level-make (cct tt 0 , Wt.elim (base* ∘ snd) (loop* ∘ snd)) where

  -- This is basically [loop^] using a different composition order
  base* : (n : ℤ) → cct tt 0 == cct tt n
  base* (pos 0) = idp
  base* (pos 1) = ppt tt 0
  base* (pos (S (S n))) = base* (pos (S n)) ∙ ppt tt (pos (S n))
  base* (negsucc 0) = ! (ppt tt (negsucc O))
  base* (negsucc (S n)) = base* (negsucc n) ∙ ! (ppt tt (negsucc (S n)))

  abstract
    loop* : (n : ℤ)
      → base* n == base* (succ n) [ (λ x → cct tt 0 == x) ↓ ppt tt n ]
    loop* n = ↓-cst=idf-in' (aux n) where

      -- This is basically [loop^+ 1 n]
      aux : (n : ℤ) → base* n ∙ ppt tt n == base* (succ n)
      aux (pos 0) = idp
      aux (pos (S n)) = idp
      aux (negsucc 0) = !-inv-l (ppt tt (negsucc O))
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
abstract
  contr-flattening : is-contr (Σ S¹ S¹Cover)
  contr-flattening = transport! is-contr flattening-S¹ Wt-is-contr

{- 6. Proof that [Ω S¹ ≃ ℤ] using the fact that [Σ S¹ Cover] is contractible -}

tot-encode : Σ S¹ (λ x → base == x) → Σ S¹ S¹Cover
tot-encode (x , y) = (x , encode y)

-- The previous map induces an equivalence on the total spaces, because both
-- total spaces are contractible
abstract
  total-is-equiv : is-equiv tot-encode
  total-is-equiv = contr-to-contr-is-equiv _ (pathfrom-is-contr base) contr-flattening

-- Hence it’s an equivalence fiberwise
abstract
  encode-is-equiv : (x : S¹) → is-equiv (encode {x})
  encode-is-equiv = total-equiv-is-fiber-equiv (λ _ → encode) total-is-equiv

-- We can then conclude that the loop space of the circle is equivalent to [ℤ]
ΩS¹≃ℤ' : (base == base) ≃ ℤ
ΩS¹≃ℤ' = (encode {base} , encode-is-equiv base)

{- 7. Encode-decode proof of the whole fiberwise equivalence -}

-- This is quite similar to [paths-mike], we’re doing it by circle-induction,
-- the base case is [encode-loop^] and the loop case is using the fact that [ℤ]
-- is a set (and [loop^+] is already used in [decode])
encode-decode : (x : S¹) (t : S¹Cover x) → encode (decode x t) == t
encode-decode =
  S¹-elim {P = λ x → (t : S¹Cover x) → encode (decode x t) == t}
    encode-loop^ (↓-Π-in (λ q → prop-has-all-paths-↓))

encode-is-equiv' : (x : S¹) → is-equiv (encode {x})
encode-is-equiv' x = is-eq encode (decode x) (encode-decode x) (decode-encode x)

{- 8. Proof that the circle is a 1-type -}

abstract
  S¹Cover-is-set : {y : S¹} → is-set (S¹Cover y)
  S¹Cover-is-set {y} = S¹-elim {P = λ y → is-set (S¹Cover y)}
    ℤ-is-set prop-has-all-paths-↓ y

  ΩS¹-is-set : {y : S¹} → is-set (base == y)
  ΩS¹-is-set {y} = equiv-preserves-level ((encode {y} , encode-is-equiv y) ⁻¹)
                                         {{S¹Cover-is-set {y}}}

S¹-level : has-level 1 S¹
S¹-level = has-level-make (S¹-elim ⟨⟩ prop-has-all-paths-↓) where instance _ = ΩS¹-is-set

instance S¹-level-instance = S¹-level

{- 9. More stuff -}

ΩS¹-iso-ℤ : Ω^S-group 0 ⊙S¹ ≃ᴳ ℤ-group
ΩS¹-iso-ℤ = ≃-to-≃ᴳ ΩS¹≃ℤ encode-pres-∙ where
  abstract
    encode-∙ : ∀ {x₁ x₂} (loop₁ : base == x₁) (loop₂ : x₁ == x₂)
      → encode (loop₁ ∙ loop₂) == encode' loop₂ (encode loop₁)
    encode-∙ idp _ = idp

    encode-pres-∙ : ∀ (loop₁ loop₂ : base == base)
      → encode (loop₁ ∙ loop₂) == encode loop₁ ℤ+ encode loop₂
    encode-pres-∙ loop₁ loop₂ =
        encode (loop₁ ∙ loop₂)
          =⟨ encode'-∙ loop₁ loop₂ 0 ⟩
        encode' loop₂ (encode loop₁)
          =⟨ ! $ decode-encode _ loop₂ |in-ctx (λ loop₂ → encode' loop₂ (encode loop₁)) ⟩
        encode' (loop^ (encode loop₂)) (encode loop₁)
          =⟨ encode'-loop^ (encode loop₂) (encode loop₁) ⟩
        encode loop₂ ℤ+ encode loop₁
          =⟨ ℤ+-comm (encode loop₂) (encode loop₁) ⟩
        encode loop₁ ℤ+ encode loop₂
          =∎

abstract
  ΩS¹-is-abelian : is-abelian (Ω^S-group 0 ⊙S¹)
  ΩS¹-is-abelian = iso-preserves-abelian (ΩS¹-iso-ℤ ⁻¹ᴳ) ℤ-group-is-abelian
