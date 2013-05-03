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
5. Proof with the flattening lemma that [Σ S¹ Cover] is contractible
6. Proof of [Ω S¹ ≃ ℤ] using the fact that [Σ S¹ Cover] is contractible (common
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

succ-path : ℤ == ℤ
succ-path = ua succ-equiv

Cover : S¹ → Type₀
Cover = S¹-rec ℤ succ-path

encode : {x : S¹} (p : base == x) → Cover x
encode p = transport Cover p O

{- 2. Encoding [loop^ n] (common to Mike’s proof and the encode-decode proof) -}

-- We define the element of [Ω S¹] which is supposed to correspond to an
-- integer [n], this is the loop winding around the circle [n] times.
-- This is easy by induction on [n]
loop^ : (n : ℤ) → base == base
loop^ O = idp
loop^ (pos O) = loop
loop^ (pos (S n)) = loop^ (pos n) ∙ loop
loop^ (neg O) = ! loop
loop^ (neg (S n)) = loop^ (neg n) ∙ (! loop)

-- Compatibility of [loop^] with the successor function
-- This is again not difficult by induction on [n]
loop^succ : (n : ℤ) → loop^ n ∙ loop == loop^ (succ n)
loop^succ O = idp
loop^succ (pos n) = idp
loop^succ (neg O) = !-inv-l loop
loop^succ (neg (S n)) =
  (loop^ (neg n) ∙ ! loop) ∙ loop
        =⟨ ∙-assoc (loop^ (neg n)) (! loop) loop ⟩
   loop^ (neg n) ∙ (! loop ∙ loop)
        =⟨ !-inv-l loop |in-ctx (λ u → loop^ (neg n) ∙ u) ⟩
   loop^ (neg n) ∙ idp
        =⟨ ∙-unit-r _ ⟩
   loop^ (neg n) ∎

-- Now we check that encoding [loop^ n] gives indeed [n], again by induction
-- on [n]
encode-loop^ : (n : ℤ) → encode (loop^ n) == n
encode-loop^ O = idp
encode-loop^ (pos O) = loop-path succ-equiv O
encode-loop^ (pos (S n)) =
  encode (loop^ (pos n) ∙ loop) =⟨ idp ⟩
  coe (ap Cover (loop^ (pos n) ∙ loop)) O
       =⟨ ap-∙ Cover (loop^ (pos n)) loop |in-ctx (λ u → coe u O) ⟩
  coe (ap Cover (loop^ (pos n)) ∙ ap Cover loop) O
       =⟨ coe-∙ (ap Cover (loop^ (pos n)))
                (ap Cover loop) O ⟩
  coe (ap Cover loop) (coe (ap Cover (loop^ (pos n))) O)
       =⟨ encode-loop^ (pos n) |in-ctx coe (ap Cover loop) ⟩
  coe (ap Cover loop) (pos n)
       =⟨ loop-path succ-equiv (pos n) ⟩
  pos (S n) ∎
encode-loop^ (neg O) =
  coe (ap Cover (! loop)) O =⟨ coe-ap-! Cover loop O ⟩
  coe! (ap Cover loop) O =⟨ !loop-path succ-equiv O ⟩
  neg O ∎
encode-loop^ (neg (S n)) =
  encode (loop^ (neg n) ∙ ! loop) =⟨ idp ⟩
  coe (ap Cover (loop^ (neg n) ∙ ! loop)) O
       =⟨ ap-∙ Cover (loop^ (neg n)) (! loop)
          |in-ctx (λ u → coe u O) ⟩
  coe (ap Cover (loop^ (neg n)) ∙ ap Cover (! loop)) O
       =⟨ coe-∙ (ap Cover (loop^ (neg n)))
                (ap Cover (! loop)) O ⟩
  coe (ap Cover (! loop)) (coe (ap Cover (loop^ (neg n))) O)
       =⟨ encode-loop^ (neg n) |in-ctx coe (ap Cover (! loop)) ⟩
  coe (ap Cover (! loop)) (neg n)
       =⟨ coe-ap-! Cover loop (neg n) ⟩
  coe! (ap Cover loop) (neg n)
       =⟨ !loop-path succ-equiv (neg n) ⟩
  neg (S n) ∎

{- 3. Dan’s encode-decode proof -}

-- The decoding function at [base] is [loop^], but we extend it to the whole
-- of [S¹] so that [decode-encode] becomes easier (and we need [loop^succ] to
-- be able to extend it)
decode : {x : S¹} → (Cover x → base == x)
decode {x} =
  S¹-elim loop^ (↓-→-in (λ {n} q →
                 ↓-cst=idf-in
                   (loop^succ n ∙ ap loop^ (↓-loop-out succ-equiv q)))) x

decode-encode : {x : S¹} (t : base == x) → decode (encode t) == t
decode-encode idp = idp  -- Magic!

-- And we get the theorem
ΩS¹≃ℤ : (base == base) ≃ ℤ
ΩS¹≃ℤ = equiv encode decode encode-loop^ decode-encode

{- 4. Mike’s proof that [Σ S¹ Cover] is contractible (or at least something
      similar) -}

-- We want to prove that every point of [Σ S¹ Cover] is equal to [(base , O)]
paths-mike : (xt : Σ S¹ Cover) → (base , O) == xt
paths-mike (x , t) = paths-mike-curr x t where

  ↓-loop^ : (n : ℤ) → O == n [ Cover ↓ loop^ n ]
  ↓-loop^ n = from-transp _ _ (encode-loop^ n)

  -- So we do it by circle-induction on the first component. When it’s [base],
  -- we use the [↓-loop^] above (which is essentially [encode-loop^]) and
  -- around [loop] we need to use [loop^succ] and the fact that [ℤ] is a set.
  paths-mike-curr : (x : S¹) (t : Cover x) → (base , O) == (x , t) :> Σ S¹ Cover
  paths-mike-curr = S¹-elim
    (λ n → pair= (loop^ n) (↓-loop^ n))
    (↓-Π-in (λ {n} {n'} q →
     ↓-cst=idf-in
       (pair= (loop^ n) (↓-loop^ n) ∙ pair= loop q
                  =⟨ Σ-∙ (↓-loop^ n) q ⟩
        pair= (loop^ n ∙ loop) (↓-loop^ n ∙dep q)
                  =⟨ ap (uncurry (λ p q → pair= p q))
                        (pair= (loop^succ n ∙ ap loop^ (↓-loop-out succ-equiv q))
                               (from-transp _ _
                                 (<– (equiv-ap (to-transp-equiv Cover (loop^ n')) _ _)
                                     (fst (ℤ-is-set _ _ _ _))))) ⟩
        pair= (loop^ n') (↓-loop^ n') ∎)))

contr-mike : is-contr (Σ S¹ Cover)
contr-mike = ((base , O) , paths-mike)

{- 5. Flattening lemma proof that [Σ S¹ Cover] is contractible -}

-- We import the flattening lemma for the universal cover of the circle
open import homotopy.Flattening
  Unit Unit (idf _) (idf _) (cst ℤ) (cst succ-equiv)
  renaming (eqv to flattening-eqv)

-- We prove that the flattened HIT corresponding to the universal cover of the
-- circle (the real line) is contractible
Wt-is-contr : is-contr Wt
Wt-is-contr = (cct tt O , Wt-elim (base* ∘ snd) (loop* ∘ snd)) where

  -- This is basically [loop^]
  base* : (n : ℤ) → cct tt O == cct tt n
  base* O = idp
  base* (pos O) = ppt tt O
  base* (pos (S n)) = base* (pos n) ∙ ppt tt (pos n)
  base* (neg O) = ! (ppt tt (neg O))
  base* (neg (S n)) = base* (neg n) ∙ ! (ppt tt (neg (S n)))

  loop* : (n : ℤ)
    → base* n == base* (succ n) [ (λ x → cct tt O == x) ↓ ppt tt n ]
  loop* n = ↓-cst=idf-in (aux n) where

    -- This is basically [loop^succ]
    aux : (n : ℤ) → base* n ∙ ppt tt n == base* (succ n)
    aux O = idp
    aux (pos n) = idp
    aux (neg O) = !-inv-l (ppt tt (neg O))
    aux (neg (S n)) =
      base* (neg (S n)) ∙ ppt tt (neg (S n))
                =⟨ idp ⟩
      (base* (neg n) ∙ ! (ppt tt (neg (S n)))) ∙ ppt tt (neg (S n))
                =⟨ ∙-assoc (base* (neg n)) _ _ ⟩
      base* (neg n) ∙ (! (ppt tt (neg (S n))) ∙ ppt tt (neg (S n)))
                =⟨ !-inv-l (ppt tt (neg (S n)))
                       |in-ctx (λ u → base* (neg n) ∙ u) ⟩
      base* (neg n) ∙ idp
                =⟨ ∙-unit-r _ ⟩
      base* (neg n) ∎

-- Then, using the flattening lemma we get that the total space of [Cover] is
-- contractible
contr-flattening : is-contr (Σ S¹ Cover)
contr-flattening = transport! is-contr
  (S¹-generic.eqv-tot succ-equiv ∙ ua flattening-eqv) Wt-is-contr

{- 6. Proof that [Ω S¹ ≃ ℤ] using the fact that [Σ S¹ Cover] is contractible -}

tot-encode : Σ S¹ (λ y → base == y) → Σ S¹ Cover
tot-encode (x , y) = (x , encode y)

-- The previous map induces an equivalence on the total spaces, because both
-- total spaces are contractible
total-is-equiv : is-equiv tot-encode
total-is-equiv = contr-to-contr-is-equiv _ (pathfrom-is-contr base) contr-flattening

-- Hence it’s an equivalence fiberwise
postulate  -- TODO, will be only one line using the fact that an equivalence on
           -- total spaces induces an equivalence fiberwise
  encode-is-equiv : (x : S¹) → is-equiv (encode {x})

-- We can then conclude that the loop space of the circle is equivalent to [ℤ]
ΩS¹≃ℤ' : (base == base) ≃ ℤ
ΩS¹≃ℤ' = (encode {base} , encode-is-equiv base)

{- 7. Encode-decode proof of the whole fiberwise equivalence -}

-- This is quite similar to [paths-mike], we’re doing it by circle-induction,
-- the base case is [encode-loop^] and the loop case is using the fact that [ℤ]
-- is a set (and [loop^succ] is already used in [decode])
encode-decode : {x : S¹} (t : Cover x) → encode (decode {x} t) == t
encode-decode {x} =
  S¹-elim {A = λ x → (t : Cover x) → encode (decode {x} t) == t}
    encode-loop^ (↓-Π-in (λ q → from-transp _ _ (fst (ℤ-is-set _ _ _ _)))) x

encode-is-equiv' : (x : S¹) → is-equiv (encode {x})
encode-is-equiv' x = is-eq encode decode (encode-decode {x}) decode-encode

{- 8. Proof that the circle is a 1-type -}

Cover-is-set : (y : S¹) → is-set (Cover y)
Cover-is-set = S¹-elim ℤ-is-set (from-transp _ _ (fst (is-set-is-prop _ _)))

ΩS¹-is-set : (y : S¹) → is-set (base == y)
ΩS¹-is-set y = equiv-preserves-level ((encode {y} , encode-is-equiv y) ⁻¹)
                                     (Cover-is-set y)

S¹-level : has-level ⟨1⟩ S¹
S¹-level =
  S¹-elim ΩS¹-is-set (from-transp _ _ (funext (λ _ → fst (is-set-is-prop _ _))))
