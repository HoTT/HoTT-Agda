{-# OPTIONS --without-K #-}

open import HoTT

{-
This file contains two proofs of Ω(S¹) = ℤ, the encode-decode proof and
the proof via the flattening lemma.
-}

module homotopy.LoopSpaceCircle where

-- Universal cover and encoding map (common to both proofs)

succ-path : ℤ == ℤ
succ-path = ua succ-equiv

Cover : S¹ → Type₀
Cover = S¹-rec ℤ succ-path

encode : {x : S¹} (p : base == x) → Cover x
encode p = transport Cover p O

{- Encode-decode proof -}

loop^ : (n : ℤ) → base == base
loop^ O = idp
loop^ (pos O) = loop
loop^ (pos (S n)) = loop^ (pos n) ∙ loop
loop^ (neg O) = ! loop
loop^ (neg (S n)) = loop^ (neg n) ∙ (! loop)

-- Compatibility of [loop^] with the successor function

loop^S : (n : ℤ) → loop^ n ∙ loop == loop^ (succ n)
loop^S O = idp
loop^S (pos n) = idp
loop^S (neg O) = !-inv-l loop
loop^S (neg (S n)) =
  (loop^ (neg n) ∙ ! loop) ∙ loop =⟨ ∙-assoc (loop^ (neg n)) (! loop) loop ⟩
   loop^ (neg n) ∙ (! loop ∙ loop)
        =⟨ !-inv-l loop |in-ctx (λ u → loop^ (neg n) ∙ u) ⟩
   loop^ (neg n) ∙ idp =⟨ ∙-unit-r _ ⟩
   loop^ (neg n) ∎

encode-decode' : (n : ℤ) → encode (loop^ n) == n
encode-decode' O = idp
encode-decode' (pos O) = loop-path succ-equiv O
encode-decode' (pos (S n)) =
  encode (loop^ (pos n) ∙ loop) =⟨ idp ⟩
  coe (ap Cover (loop^ (pos n) ∙ loop)) O
       =⟨ ap-∙ Cover (loop^ (pos n)) loop |in-ctx (λ u → coe u O) ⟩
  coe (ap Cover (loop^ (pos n)) ∙ ap Cover loop) O
       =⟨ coe-∙ (ap Cover (loop^ (pos n)))
                (ap Cover loop) O ⟩
  coe (ap Cover loop) (coe (ap Cover (loop^ (pos n))) O)
       =⟨ encode-decode' (pos n) |in-ctx coe (ap Cover loop) ⟩
  coe (ap Cover loop) (pos n)
       =⟨ loop-path succ-equiv (pos n) ⟩
  pos (S n) ∎
encode-decode' (neg O) =
  coe (ap Cover (! loop)) O =⟨ coe-ap-! Cover loop O ⟩
  coe! (ap Cover loop) O =⟨ !loop-path succ-equiv O ⟩
  neg O ∎
encode-decode' (neg (S n)) =
  encode (loop^ (neg n) ∙ ! loop) =⟨ idp ⟩
  coe (ap Cover (loop^ (neg n) ∙ ! loop)) O
       =⟨ ap-∙ Cover (loop^ (neg n)) (! loop)
          |in-ctx (λ u → coe u O) ⟩
  coe (ap Cover (loop^ (neg n)) ∙ ap Cover (! loop)) O
       =⟨ coe-∙ (ap Cover (loop^ (neg n)))
                (ap Cover (! loop)) O ⟩
  coe (ap Cover (! loop)) (coe (ap Cover (loop^ (neg n))) O)
       =⟨ encode-decode' (neg n) |in-ctx coe (ap Cover (! loop)) ⟩
  coe (ap Cover (! loop)) (neg n)
       =⟨ coe-ap-! Cover loop (neg n) ⟩
  coe! (ap Cover loop) (neg n)
       =⟨ !loop-path succ-equiv (neg n) ⟩
  neg (S n) ∎

decode : {x : S¹} (t : Cover x) → base == x
decode {x} =
  S¹-elim loop^ (↓-→-in (λ {n} q →
                 ↓-cst=idf-in
                   (loop^S n ∙ ap loop^ (↓-loop-out succ-equiv q)))) x

decode-encode : {x : S¹} (t : base == x) → decode (encode t) == t
decode-encode idp = idp  -- Magic!

theorem : (base == base) ≃ ℤ
theorem = equiv encode decode encode-decode' decode-encode

-- This is the whole fiberwise equivalence, this is not needed for the theorem.
encode-decode : {x : S¹} (t : Cover x) → encode (decode {x} t) == t
encode-decode {x} =
  S¹-elim {A = λ x → (t : Cover x) → encode (decode {x} t) == t}
    encode-decode' (↓-Π-in (λ q → from-transp _ _ (fst (ℤ-is-set _ _ _ _)))) x


{- Flattening lemma proof -}

-- We import the flattening lemma for the universal cover of the circle
open import homotopy.Flattening
  Unit Unit (idf _) (idf _) (cst ℤ) (cst succ-equiv)
  renaming (eqv to flattening-eqv)

Wt-is-contr : is-contr Wt
Wt-is-contr = (cct tt O , Wt-elim (base-case ∘ snd) (loop-case ∘ snd)) where

  -- This is basically [loop^]
  base-case : (n : ℤ) → cct tt O == cct tt n
  base-case O = idp
  base-case (pos O) = ppt tt O
  base-case (pos (S n)) = base-case (pos n) ∙ ppt tt (pos n)
  base-case (neg O) = ! (ppt tt (neg O))
  base-case (neg (S n)) = base-case (neg n) ∙ ! (ppt tt (neg (S n)))

  -- This is basically [loop^S]
  loop-case : (n : ℤ)
    → base-case n == base-case (succ n) [ (λ x → cct tt O == x) ↓ ppt tt n ]
  loop-case n = ↓-cst=idf-in (aux n) where

    aux : (n : ℤ) → base-case n ∙ ppt tt n == base-case (succ n)
    aux O = idp
    aux (pos n) = idp
    aux (neg O) = !-inv-l (ppt tt (neg O))
    aux (neg (S n)) =
      base-case (neg (S n)) ∙ ppt tt (neg (S n))
                =⟨ idp ⟩
      (base-case (neg n) ∙ ! (ppt tt (neg (S n)))) ∙ ppt tt (neg (S n))
                =⟨ ∙-assoc (base-case (neg n)) _ _ ⟩
      base-case (neg n) ∙ (! (ppt tt (neg (S n))) ∙ ppt tt (neg (S n)))
                =⟨ !-inv-l (ppt tt (neg (S n)))
                       |in-ctx (λ u → base-case (neg n) ∙ u) ⟩
      base-case (neg n) ∙ idp
                =⟨ ∙-unit-r _ ⟩
      base-case (neg n) ∎

-- Using the flattening lemma we get that the total space of [Cover]
-- is contractible
tot-is-contr : is-contr (Σ S¹ Cover)
tot-is-contr = transport! is-contr
  (S¹-generic.eqv-tot succ-equiv ∙ ua flattening-eqv) Wt-is-contr

tot-encode : Σ S¹ (λ y → base == y) → Σ S¹ Cover
tot-encode (x , y) = (x , encode y)

-- This induces an equivalence on the total spaces, because both total spaces
-- are contractible
total-is-equiv : is-equiv tot-encode
total-is-equiv = contr-to-contr-is-equiv _ (pathfrom-is-contr base) tot-is-contr

-- Hence an equivalence fiberwise
postulate  -- TODO
  encode-is-equiv : (x : S¹) → is-equiv (encode {x})
--encode-is-equiv x = {!!}

-- We can then conclude that the based loop space of the circle is equivalent to
-- the type of the integers
ΩS¹≃ℤ : (base == base) ≃ ℤ
ΩS¹≃ℤ = (encode {base} , encode-is-equiv base)

{- Unfinished attempt to get something similar to Mike’s original proof
tot : Type₀
tot = Σ S¹ Cover

x : (n : ℤ) → O == n [ Cover ↓ loop^ n ]
x n = to-transp-in Cover (loop^ n) (encode-decode' n)

postulate
  xx : {n n' : ℤ} → (n == n') == (O == n [ Cover ↓ loop^ n ])

contr-curryfied : (x : S¹) (t : Cover x) → (base , O) == (x , t) :> tot
contr-curryfied = S¹-elim (λ n → pair= (loop^ n) (x n)) (↓-Π-in (λ {n} {n'} q →
  ↓-cst=idf-in
    (pair= (loop^ n) (x n) ∙ pair= loop q =⟨ Σ-∙ (x n) q ⟩
    pair= (loop^ n ∙ loop) (x n ∙dep q)
      =⟨ ap (uncurry (λ p q → pair= p q))
            (pair= (loop^S' {n} (↓-loop-out succ-equiv q))
              (to-transp-in _ _ {!fst (ℤ-is-set _ _ _ _)!})) ⟩
    pair= (loop^ n') (x n') ∎)))

contr : (xt : tot) → (base , O) == xt
contr (x , t) = contr-curryfied x t
-}

-- -- Path fibration

-- path-fib : S¹ → Type₀
-- path-fib t = (t == base)

-- tot-path-fib : Type₀
-- tot-path-fib = Σ S¹ path-fib

-- tot-path-fib-is-contr : is-contr tot-path-fib
-- tot-path-fib-is-contr = pathto-is-contr base


-- tot-cover-is-contr : is-contr tot-cover
-- tot-cover-is-contr = (R-z O , λ x → ! (R-contr x))

-- -- We define now a fiberwise map between the two fibrations [path-fib]
-- -- and [Cover]
-- fiberwise-map : (x : S¹) → (path-fib x → Cover x)
-- fiberwise-map x p = transport Cover (! p) O

-- -- This induces an equivalence on the total spaces, because both total spaces
-- -- are contractible
-- total-is-equiv : is-equiv (total-map fiberwise-map)
-- total-is-equiv = contr-to-contr-is-equiv (total-map fiberwise-map)
--                                          tot-path-fib-is-contr
--                                          tot-cover-is-contr

-- -- Hence an equivalence fiberwise
-- fiberwise-map-is-equiv : (x : S¹) → is-equiv (fiberwise-map x)
-- fiberwise-map-is-equiv x = fiberwise-is-equiv fiberwise-map total-is-equiv x

-- -- We can then conclude that the based loop space of the circle is equivalent to
-- -- the type of the integers
-- ΩS¹≃ℤ : (base == base) ≃ ℤ
-- ΩS¹≃ℤ = (fiberwise-map base , fiberwise-map-is-equiv base)

-- -- We can also deduce that the circle is 1-truncated

-- ΩS¹-is-set : is-set (base == base)
-- ΩS¹-is-set = equiv-types-truncated _ (ΩS¹≃ℤ ⁻¹) ℤ-is-set

-- S¹-is-gpd : is-gpd S¹
-- S¹-is-gpd =
--   S¹-rec _
--     (S¹-rec _
--       ΩS¹-is-set  -- [base == base] is a set
--       (π₁ (is-truncated-is-prop _ _ _)))
--     (funext
--       (S¹-rec _
--         (π₁ (is-truncated-is-prop _ _ _))
--         (prop-has-all-paths (==-is-truncated _ (is-truncated-is-prop _)) _ _)))
