{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.cubical.Square
open import lib.types.Nat
open import lib.types.Pointed
open import lib.types.TLevel
open import lib.types.Truncation

{- Sequential colimits -}

module lib.types.NatColim where

module _ {i} {D : ℕ → Type i} where

  private
    data #ℕColim-aux (d : (n : ℕ) → D n → D (S n)) : Type i where
      #ncin : (n : ℕ) → D n → #ℕColim-aux d

    data #ℕColim (d : (n : ℕ) → D n → D (S n)) : Type i where
      #ncolim : #ℕColim-aux d → (Unit → Unit) → #ℕColim d

  ℕColim : (d : (n : ℕ) → D n → D (S n)) → Type i
  ℕColim d = #ℕColim d

  ncin : {d : (n : ℕ) → D n → D (S n)} → (n : ℕ) → D n → ℕColim d
  ncin n x = #ncolim (#ncin n x) _

  postulate  -- HIT
    ncglue : {d : (n : ℕ) → D n → D (S n)}
      (n : ℕ) → (x : D n) → ncin {d = d} n x == ncin (S n) (d n x)

  module ℕColimElim (d : (n : ℕ) → D n → D (S n))
    {j} {P : ℕColim d → Type j}
    (ncin* : (n : ℕ) (x : D n) → P (ncin n x))
    (ncglue* : (n : ℕ) (x : D n)
      → ncin* n x == ncin* (S n) (d n x) [ P ↓ ncglue n x ])
    where

    f : Π (ℕColim d) P
    f = f-aux phantom where

      f-aux : Phantom ncglue* → Π (ℕColim d) P
      f-aux phantom (#ncolim (#ncin n x) _) = ncin* n x

    postulate  -- HIT
      ncglue-β : (n : ℕ) (x : D n) → apd f (ncglue n x) == ncglue* n x

  open ℕColimElim public using () renaming (f to ℕColim-elim)

  module ℕColimRec (d : (n : ℕ) → D n → D (S n))
    {j} {A : Type j}
    (ncin* : (n : ℕ) → D n → A)
    (ncglue* : (n : ℕ) → (x : D n) → ncin* n x == ncin* (S n) (d n x))
    where

    private
      module M = ℕColimElim d ncin* (λ n x → ↓-cst-in (ncglue* n x))

    f : ℕColim d → A
    f = M.f

    ncglue-β : (n : ℕ) (x : D n) → ap f (ncglue n x) == ncglue* n x
    ncglue-β n x = apd=cst-in {f = f} (M.ncglue-β n x)

⊙ℕColim : ∀ {i} {D : ℕ → Ptd i} (d : (n : ℕ) → fst (D n ⊙→ D (S n))) → Ptd i
⊙ℕColim {D = D} d = ⊙[ ℕColim (fst ∘ d) , ncin 0 (snd (D 0)) ]

{- Can define a function [nc-raise d : ℕColim d → ℕColim d]
   so that [inn (S n) ∘ d = nc-raise d ∘ inn n] -}

module ℕCRaise {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) =
  ℕColimRec d {A = ℕColim d}
    (λ n x → ncin (S n) (d n x))
    (λ n x → ncglue (S n) (d n x))

nc-raise : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n))
  → ℕColim d → ℕColim d
nc-raise d = ℕCRaise.f d

nc-raise-= : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) (c : ℕColim d)
  → c == nc-raise d c
nc-raise-= d = ℕColimElim.f d
  (λ n x → ncglue n x)
  (λ n x → ↓-='-from-square $
    ap-idf (ncglue n x) ∙v⊡ connection2 ⊡v∙ (! (ℕCRaise.ncglue-β d n x)))

{- Lift an element of D₀ to any level -}

nc-lift : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n))
  (n : ℕ) → D O → D n
nc-lift d O x = x
nc-lift d (S n) x = d n (nc-lift d n x)

nc-lift-= : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n))
  (n : ℕ) (x : D O)
  → ncin {d = d} O x == ncin n (nc-lift d n x)
nc-lift-= d O x = idp
nc-lift-= d (S n) x = nc-lift-= d n x ∙ ncglue n (nc-lift d n x)

{- Lift an element of D₀ to the 'same level' as some element of ℕColim d -}

module ℕCMatch {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) (x : D O) =
  ℕColimRec d {A = ℕColim d}
    (λ n _ → ncin n (nc-lift d n x))
    (λ n _ → ncglue n (nc-lift d n x))

nc-match = ℕCMatch.f

nc-match-=-base : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n))
  (x : D O) (c : ℕColim d)
  → ncin O x == nc-match d x c
nc-match-=-base d x = ℕColimElim.f d
  (λ n _ → nc-lift-= d n x)
  (λ n y → ↓-cst=app-from-square $
    disc-to-square idp ⊡v∙ ! (ℕCMatch.ncglue-β d x n y))

{- If all Dₙ are m-connected, then the colim is m-connected -}

ncolim-conn : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) (m : ℕ₋₂)
  → ((n : ℕ) → is-connected m (D n))
  → is-connected m (ℕColim d)
ncolim-conn {D = D} d ⟨-2⟩ cD = -2-conn (ℕColim d)
ncolim-conn {D = D} d (S m) cD =
  Trunc-rec (prop-has-level-S is-contr-is-prop)
    (λ x → ([ ncin O x ] ,
            (Trunc-elim (λ _ → =-preserves-level _ Trunc-level) $
              λ c → ap [_] (nc-match-=-base d x c) ∙ nc-match-=-point x c)))
    (fst (cD O))
  where
  nc-match-=-point : (x : D O) (c : ℕColim d)
    → [_] {n = S m} (nc-match d x c) == [ c ]
  nc-match-=-point x = ℕColimElim.f d
    (λ n y → ap (Trunc-fmap (ncin n))
                (contr-has-all-paths (cD n) [ nc-lift d n x ] [ y ]))
      (λ n y → ↓-='-from-square $
        (ap-∘ [_] (nc-match d x) (ncglue n y)
         ∙ ap (ap [_]) (ℕCMatch.ncglue-β d x n y))
        ∙v⊡
        ! (ap-idf _)
        ∙h⊡
        (square-symmetry $
          natural-square
            (Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
               (λ c → ap [_] (nc-raise-= d c)))
            (ap (Trunc-fmap (ncin n))
                (contr-has-all-paths (cD n) [ nc-lift d n x ] [ y ])))
        ⊡h∙
        (∘-ap (Trunc-fmap (nc-raise d)) (Trunc-fmap (ncin n))
              (contr-has-all-paths (cD n) [ nc-lift d n x ] [ y ])
         ∙ vert-degen-path
             (natural-square
               (λ t → Trunc-fmap-∘ (nc-raise d) (ncin n) t
                      ∙ ! (Trunc-fmap-∘ (ncin (S n)) (d n) t))
               (contr-has-all-paths (cD n) [ nc-lift d n x ] [ y ]))
         ∙ ap-∘ (Trunc-fmap (ncin (S n))) (Trunc-fmap (d n))
                (contr-has-all-paths (cD n) [ nc-lift d n x ] [ y ])
         ∙ ap (ap (Trunc-fmap (ncin (S n))))
              (contr-has-all-paths (=-preserves-level _ (cD (S n))) _ _)))

{- Type of finite tuples -}

FinTuplesType : ∀ {i} → (ℕ → Ptd i) → ℕ → Ptd i
FinTuplesType F O = F O
FinTuplesType F (S n) = F O ⊙× FinTuplesType (F ∘ S) n

fin-tuples-map : ∀ {i} (F : ℕ → Ptd i) (n : ℕ)
  → fst (FinTuplesType F n ⊙→ FinTuplesType F (S n))
fin-tuples-map F O = ((λ r → r , snd (F 1)) , idp)
fin-tuples-map F (S n) =
  ((λ {(x , r) → (x , fst (fin-tuples-map (F ∘ S) n) r)}) ,
   pair×= idp (snd (fin-tuples-map (F ∘ S) n)))

⊙FinTuples : ∀ {i} → (ℕ → Ptd i) → Ptd i
⊙FinTuples {i} F = ⊙ℕColim (fin-tuples-map F)

fin-tuples-cons : ∀ {i} (F : ℕ → Ptd i)
  → F O ⊙× ⊙FinTuples (F ∘ S) ⊙≃ ⊙FinTuples F
fin-tuples-cons {i} F =
  ⊙ify-eq (equiv into out into-out out-into) (! (ncglue O (snd (F O))))
  where
  module Into (x : fst (F O)) =
    ℕColimRec (fst ∘ fin-tuples-map (F ∘ S)) {A = fst (⊙FinTuples F)}
      (λ n r → ncin (S n) (x , r))
      (λ n r → ncglue (S n) (x , r))

  into = uncurry Into.f

  out-ncin : (n : ℕ)
    → fst (FinTuplesType F n) → fst (F O ⊙× ⊙FinTuples (F ∘ S))
  out-ncin O x = (x , ncin O (snd (F 1)))
  out-ncin (S n) (x , r) = (x , ncin n r)

  out-ncglue : (n : ℕ) (r : fst (FinTuplesType F n))
    → out-ncin n r == out-ncin (S n) (fst (fin-tuples-map F n) r)
  out-ncglue O x = idp
  out-ncglue (S n) (x , r) = pair= idp (ncglue n r)

  module Out = ℕColimRec _ out-ncin out-ncglue
  out = Out.f

  into-out-ncin : (n : ℕ) (r : fst (FinTuplesType F n))
    → into (out-ncin n r) == ncin n r
  into-out-ncin O x = ! (ncglue O x)
  into-out-ncin (S n) (x , r) = idp

  into-out-ncglue : (n : ℕ) (r : fst (FinTuplesType F n))
    → into-out-ncin n r == into-out-ncin (S n) (fst (fin-tuples-map F n) r)
      [ (λ s → into (out s) == s) ↓ ncglue n r ]
  into-out-ncglue O x =
    ↓-∘=idf-from-square into out $
      ap (ap into) (Out.ncglue-β O x)
      ∙v⊡ bl-square (ncglue O x)
  into-out-ncglue (S n) (x , r) =
    ↓-∘=idf-from-square into out $
      (ap (ap into) (Out.ncglue-β (S n) (x , r))
       ∙ ∘-ap into (_,_ x) (ncglue n r)
       ∙ Into.ncglue-β x n r)
      ∙v⊡ vid-square

  into-out : (r : fst (⊙FinTuples F)) → into (out r) == r
  into-out = ℕColimElim.f _
    into-out-ncin
    into-out-ncglue

  out-into : (t : fst (F O ⊙× ⊙FinTuples (F ∘ S))) → out (into t) == t
  out-into = uncurry $ λ x → ℕColimElim.f _
    (λ n r → idp)
    (λ n r → ↓-='-from-square $
      (ap-∘ out (Into.f x) (ncglue n r)
       ∙ ap (ap out) (Into.ncglue-β x n r)
       ∙ Out.ncglue-β (S n) (x , r))
      ∙v⊡ vid-square)
