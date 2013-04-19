{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.LoopSpaceCircle where

-- Universal cover

succ-path : ℤ == ℤ
succ-path = ua succ-equiv

Cover : S¹ → Type₀
Cover = S¹-rec ℤ succ-path

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

loop^S' : {n n' : ℤ} (p : succ n == n') → loop^ n ∙ loop == loop^ n'
loop^S' {n} p = loop^S n ∙ ap loop^ p

encode : {x : S¹} (p : base == x) → Cover x
encode p = coe (ap Cover p) O

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
encode-loop^ (neg O) = !loop-path succ-equiv O
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
       =⟨ !loop-path succ-equiv (neg n) ⟩
  neg (S n) ∎

decode : {x : S¹} (t : Cover x) → base == x
decode {x} =
  S¹-elim loop^ (↓-→-in (λ {n} q →
                 ↓-cst=idf-in
                   (loop^S' {n} (↓-loop-out succ-equiv q)))) x

decode-encode : {x : S¹} (t : base == x) → decode (encode t) == t
decode-encode idp = idp

encode-decode : {x : S¹} (t : Cover x) → encode (decode {x} t) == t
encode-decode {x} =
  S¹-elim {A = λ x → (t : Cover x) → encode (decode {x} t) == t}
    encode-loop^ (↓-Π-in (λ q → to-transp-in _ _ (fst (ℤ-is-set _ _ _ _)))) x


theorem : (base == base) ≃ ℤ
theorem = equiv encode decode (encode-decode {base}) decode-encode


{- Unfinished attempt to get something similar to Mike’s original proof
tot : Type₀
tot = Σ S¹ Cover

x : (n : ℤ) → O == n [ Cover ↓ loop^ n ]
x n = to-transp-in Cover (loop^ n) (encode-loop^ n)

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

-- {- The flattening lemma

-- Here is an HIT declaration for the CW-complex of real numbers:

-- data ℝ : Type₀ where
--   z : ℤ → ℝ
--   e : (n : ℤ) → z n == z (succ n)

-- We want to show that [tot-cover] has the same introduction and elimination
-- rules.
-- -}

-- -- Introduction rules

-- R-z : ℤ → tot-cover
-- R-z n = (base , n)

-- R-e : (n : ℤ) → R-z n == R-z (succ n)
-- R-e n = Σ-eq loop (loop-to-succ n)

-- -- Elimination rule
-- module Tot-cover-is-ℝ
--   {i}
--   (P : tot-cover → Type i)
--   (z : (n : ℤ) → P (R-z n))
--   (e : (n : ℤ) → transport P (R-e n) (z n) == z (succ n)) where

--   -- I redefine [R-e] and [e] to have something involving
--   -- [transport Cover loop] instead of [succ]
--   R-e' : (n : ℤ) → R-z n == R-z (transport Cover loop n)
--   R-e' n = Σ-eq loop refl

--   e' : (n : ℤ) → transport P (R-e' n) (z n)
--                  == z (transport Cover loop n)
--   e' n = (trans-totalpath Cover P {x = (base , n)}
--                           {y = (base , transport Cover loop n)}
--                           loop refl z
--          ∘ move!-transp-left (λ z → P (base , z)) _ (loop-to-succ n)
--            (z (succ n))
--            (! (trans-totalpath Cover P {x = (base , n)}
--                                {y = (base , succ n)} loop (loop-to-succ n) z)
--             ∘ e n))
--           ∘ apd z (! (loop-to-succ n))

--   -- Now I can prove what I want by induction on the circle

--   P-base : (t : Cover base) → P (base , t)
--   P-base t = z t

--   P-loop : (t : Cover base)
--     → transport (λ x → (u : Cover x) → P (x , u)) loop P-base t
--       == P-base t
--   P-loop t = transport (λ t → transport
--                                 (λ x → (u : Cover x) → P (x , u))
--                                 loop P-base t == P-base t)
--                (trans-trans-opposite Cover loop t)
--                (! (trans-totalpath Cover P
--                                    loop refl z)
--                ∘ e' (transport Cover (! loop) t))

--   P-R-rec : (x : S¹) → (t : Cover x) → P (x , t)
--   P-R-rec = S¹-rec (λ x → (t : Cover x) → P (x , t))
--                    P-base (funext P-loop)

--   -- Here is the conclusion of the elimination rule
--   R-rec : (t : tot-cover) → P t
--   R-rec (x , y) = P-R-rec x y

-- -- We can now prove that [tot-cover] is contractible using [R-rec], that’s a
-- -- little tedious but not difficult

-- P-R-contr : (x : tot-cover) → Type _
-- P-R-contr x = R-z O == x

-- R-contr-base : (n : ℤ) → P-R-contr (R-z n)
-- R-contr-base O = refl
-- R-contr-base (pos O) = R-e O
-- R-contr-base (pos (S y)) = R-contr-base (pos y) ∘ R-e (pos y)
-- R-contr-base (neg O) = ! (R-e (neg O))
-- R-contr-base (neg (S y)) = R-contr-base (neg y) ∘ ! (R-e (neg (S y)))

-- R-contr-loop : (n : ℤ)
--   → transport P-R-contr (R-e n) (R-contr-base n) == (R-contr-base (succ n))
-- R-contr-loop O = trans-cst==id (R-e O) refl
-- R-contr-loop (pos O) = trans-cst==id (R-e (pos O)) (R-e O)
-- R-contr-loop (pos (S y)) = trans-cst==id (R-e (pos (S y)))
--   (R-contr-base (pos y) ∘ R-e (pos y))
-- R-contr-loop (neg O) = trans-cst==id (R-e (neg O))
--   (! (R-e (neg O))) ∘ opposite-left-inverse (R-e (neg O))
-- R-contr-loop (neg (S y)) =
--   ((trans-cst==id (R-e (neg (S y))) (R-contr-base (neg y) ∘ ! (R-e (neg (S y))))
--    ∘ concat-assoc (R-contr-base (neg y)) (! (R-e (neg (S y))))
--                   (R-e (neg (S y))))
--    ∘ (whisker-left (R-contr-base (neg y))
--                    (opposite-left-inverse (R-e (neg (S y))))))
--    ∘ refl-right-unit (R-contr-base (neg y))

-- R-contr : (x : tot-cover) → P-R-contr x
-- R-contr = Tot-cover-is-ℝ.R-rec P-R-contr R-contr-base R-contr-loop

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
