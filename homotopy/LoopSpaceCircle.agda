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

ΩS¹≃ℤ : (base == base) ≃ ℤ
ΩS¹≃ℤ = equiv encode decode encode-decode' decode-encode

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

  -- This is basically [loop^S]
  loop* : (n : ℤ)
    → base* n == base* (succ n) [ (λ x → cct tt O == x) ↓ ppt tt n ]
  loop* n = ↓-cst=idf-in (aux n) where

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

-- Using the flattening lemma we get that the total space of [Cover]
-- is contractible
tot-is-contr : is-contr (Σ S¹ Cover)
tot-is-contr = transport! is-contr
  (S¹-generic.eqv-tot succ-equiv ∙ ua flattening-eqv) Wt-is-contr

tot-encode : Σ S¹ (λ y → base == y) → Σ S¹ Cover
tot-encode (x , y) = (x , encode y)

-- The previous map induces an equivalence on the total spaces, because both
-- total spaces are contractible
total-is-equiv : is-equiv tot-encode
total-is-equiv = contr-to-contr-is-equiv _ (pathfrom-is-contr base) tot-is-contr

-- Hence it’s an equivalence fiberwise
postulate  -- TODO, will be only one line
  encode-is-equiv : (x : S¹) → is-equiv (encode {x})

private
  -- We can then conclude that the loop space of the circle is equivalent
  -- to the type of the integers
  ΩS¹≃ℤ' : (base == base) ≃ ℤ
  ΩS¹≃ℤ' = (encode {base} , encode-is-equiv base)

-- We can also deduce that the circle is a 1-type (WIP)

ΩS¹-is-set : is-set (base == base)
ΩS¹-is-set = equiv-preserves-level (ΩS¹≃ℤ ⁻¹) ℤ-is-set

-- TODO
-- S¹-level : has-level ⟨1⟩ S¹
-- S¹-level =
--   S¹-elim
--     (S¹-elim
--       ΩS¹-is-set  -- [base == base] is a set
--       (from-transp _ loop (fst (has-level-is-prop _ _))))
--  -- (π₁ (is-truncated-is-prop _ _ _)))
--     (↓-cst→app-in
--       (S¹-elim
--         (from-transp _ loop (fst (has-level-is-prop _ _)))
--         (from-transp _ loop {!!})))
-- --     (funext
-- --       (S¹-elim
-- --         ? -- (π₁ (is-truncated-is-prop _ _ _))
-- --         ?))
-- -- --(prop-has-all-paths (==-is-truncated _ (is-truncated-is-prop _)) _ _)))

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
