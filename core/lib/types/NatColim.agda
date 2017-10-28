{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.cubical.Square
open import lib.types.Lift
open import lib.types.Nat
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Unit

{- Sequential colimits -}

module lib.types.NatColim where

module _ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) where

  postulate  -- HIT
    ℕColim : Type i
    ncin' : (n : ℕ) → D n → ℕColim
    ncglue' : (n : ℕ) → (x : D n) → ncin' n x == ncin' (S n) (d n x)

module _ {i} {D : ℕ → Type i} {d : (n : ℕ) → D n → D (S n)} where

  ncin = ncin' d
  ncglue = ncglue' d

module _ {i} {D : ℕ → Ptd i} where

  ⊙ℕColim : (d : (n : ℕ) → (D n ⊙→ D (S n))) → Ptd i
  ⊙ℕColim d = ⊙[ ℕColim (fst ∘ d) , ncin 0 (pt (D 0)) ]

module _ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) where

  module ℕColimElim {j} {P : ℕColim d → Type j}
    (ncin* : (n : ℕ) (x : D n) → P (ncin n x))
    (ncglue* : (n : ℕ) (x : D n)
      → ncin* n x == ncin* (S n) (d n x) [ P ↓ ncglue n x ])
    where

    postulate  -- HIT
      f : Π (ℕColim d) P
      ncin-β : ∀ n x → f (ncin n x) ↦ ncin* n x
    {-# REWRITE ncin-β #-}

    postulate  -- HIT
      ncglue-β : (n : ℕ) (x : D n) → apd f (ncglue n x) == ncglue* n x

  open ℕColimElim public using () renaming (f to ℕColim-elim)

  module ℕColimRec {j} {A : Type j}
    (ncin* : (n : ℕ) → D n → A)
    (ncglue* : (n : ℕ) → (x : D n) → ncin* n x == ncin* (S n) (d n x))
    where

    private
      module M = ℕColimElim ncin* (λ n x → ↓-cst-in (ncglue* n x))

    f : ℕColim d → A
    f = M.f

    ncglue-β : (n : ℕ) (x : D n) → ap f (ncglue n x) == ncglue* n x
    ncglue-β n x = apd=cst-in {f = f} (M.ncglue-β n x)

{- Raising and lifting -}
module _ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) where

  {- Can define a function [nc-raise d : ℕColim d → ℕColim d]
     so that [inn (S n) ∘ d = nc-raise d ∘ inn n] -}

  module ℕCRaise = ℕColimRec d {A = ℕColim d}
    (λ n x → ncin (S n) (d n x))
    (λ n x → ncglue (S n) (d n x))

  nc-raise : ℕColim d → ℕColim d
  nc-raise = ℕCRaise.f

  nc-raise-= : (c : ℕColim d) → c == nc-raise c
  nc-raise-= = ℕColimElim.f d
    (λ n x → ncglue n x)
    (λ n x → ↓-='-from-square $
      ap-idf (ncglue n x) ∙v⊡ (connection2 ⊡v∙ (! (ℕCRaise.ncglue-β n x))))

  {- Lift an element of D₀ to any level -}

  nc-lift : (n : ℕ) → D O → D n
  nc-lift O x = x
  nc-lift (S n) x = d n (nc-lift n x)

  nc-lift-= : (n : ℕ) (x : D O)
    → ncin' d O x == ncin n (nc-lift n x)
  nc-lift-= O x = idp
  nc-lift-= (S n) x = nc-lift-= n x ∙ ncglue n (nc-lift n x)

  {- Lift an element of D₀ to the 'same level' as some element of ℕColim d -}

  module ℕCMatch (x : D O) = ℕColimRec d {A = ℕColim d}
    (λ n _ → ncin n (nc-lift n x))
    (λ n _ → ncglue n (nc-lift n x))

  nc-match = ℕCMatch.f

  nc-match-=-base : (x : D O) (c : ℕColim d) → ncin O x == nc-match x c
  nc-match-=-base x = ℕColimElim.f d
    (λ n _ → nc-lift-= n x)
    (λ n y → ↓-cst=app-from-square $
      disc-to-square idp ⊡v∙ ! (ℕCMatch.ncglue-β x n y))

{- If all Dₙ are m-connected, then the colim is m-connected -}

ncolim-conn : ∀ {i} {D : ℕ → Type i} (d : (n : ℕ) → D n → D (S n)) (m : ℕ₋₂)
  {{_ : {n : ℕ} → is-connected m (D n)}}
  → is-connected m (ℕColim d)
ncolim-conn {D = D} d ⟨-2⟩ = -2-conn (ℕColim d)
ncolim-conn {D = D} d (S m) {{cD}} =
  Trunc-rec
    (λ x → has-level-make ([ ncin O x ] ,
            (Trunc-elim $
              λ c → ap [_] (nc-match-=-base d x c) ∙ nc-match-=-point x c)))
    (contr-center (cD {O}))
  where
  nc-match-=-point : (x : D O) (c : ℕColim d)
    → [_] {n = S m} (nc-match d x c) == [ c ]
  nc-match-=-point x = ℕColimElim.f d
    (λ n y → ap (Trunc-fmap (ncin n))
                (contr-has-all-paths [ nc-lift d n x ] [ y ]))
      (λ n y → ↓-='-from-square $
        (ap-∘ [_] (nc-match d x) (ncglue n y)
         ∙ ap (ap [_]) (ℕCMatch.ncglue-β d x n y))
        ∙v⊡
        ! (ap-idf _)
        ∙h⊡
        square-symmetry
          (natural-square
            (Trunc-elim
               (λ c → ap [_] (nc-raise-= d c)))
            (ap (Trunc-fmap (ncin n))
                (contr-has-all-paths [ nc-lift d n x ] [ y ])))
        ⊡h∙
        ∘-ap (Trunc-fmap (nc-raise d)) (Trunc-fmap (ncin n))
          (contr-has-all-paths [ nc-lift d n x ] [ y ])
        ⊡h∙
        vert-degen-path
          (natural-square
            (λ t → Trunc-fmap-∘ (nc-raise d) (ncin n) t
                   ∙ ! (Trunc-fmap-∘ (ncin (S n)) (d n) t))
            (contr-has-all-paths [ nc-lift d n x ] [ y ]))
        ⊡h∙
        ap-∘ (Trunc-fmap (ncin (S n))) (Trunc-fmap (d n))
             (contr-has-all-paths [ nc-lift d n x ] [ y ])
        ⊡h∙
        ap (ap (Trunc-fmap (ncin (S n))))
           (contr-has-all-paths _ _))

{- Type of finite tuples -}

⊙FinTuplesType : ∀ {i} → (ℕ → Ptd i) → ℕ → Ptd i
⊙FinTuplesType F O = ⊙Lift ⊙Unit
⊙FinTuplesType F (S n) = F O ⊙× ⊙FinTuplesType (F ∘ S) n

FinTuplesType : ∀ {i} → (ℕ → Ptd i) → ℕ → Type i
FinTuplesType F n = de⊙ (⊙FinTuplesType F n)

fin-tuples-map : ∀ {i} (F : ℕ → Ptd i) (n : ℕ)
  → (⊙FinTuplesType F n ⊙→ ⊙FinTuplesType F (S n))
fin-tuples-map F O = (_ , idp)
fin-tuples-map F (S n) =
  ((λ {(x , r) → (x , fst (fin-tuples-map (F ∘ S) n) r)}) ,
   pair×= idp (snd (fin-tuples-map (F ∘ S) n)))

⊙FinTuples : ∀ {i} → (ℕ → Ptd i) → Ptd i
⊙FinTuples {i} F = ⊙ℕColim (fin-tuples-map F)

FinTuples : ∀ {i} → (ℕ → Ptd i) → Type i
FinTuples = de⊙ ∘ ⊙FinTuples

fin-tuples-cons : ∀ {i} (F : ℕ → Ptd i)
  → de⊙ (F O) × FinTuples (F ∘ S) ≃ FinTuples F
fin-tuples-cons {i} F = equiv into out into-out out-into
  where
    module Into (x : de⊙ (F O)) =
      ℕColimRec (fst ∘ fin-tuples-map (F ∘ S)) {A = FinTuples F}
        (λ n r → ncin (S n) (x , r))
        (λ n r → ncglue (S n) (x , r))

    into = uncurry Into.f

    out-ncin : (n : ℕ)
      → FinTuplesType F n → de⊙ (F O) × FinTuples (F ∘ S)
    out-ncin O x = (pt (F O) , ncin O _)
    out-ncin (S n) (x , r) = (x , ncin n r)

    out-ncglue : (n : ℕ) (r : FinTuplesType F n)
      → out-ncin n r == out-ncin (S n) (fst (fin-tuples-map F n) r)
    out-ncglue O x = idp
    out-ncglue (S n) (x , r) = pair= idp (ncglue n r)

    module Out = ℕColimRec _ out-ncin out-ncglue
    out = Out.f

    abstract
      into-out-ncin : (n : ℕ) (r : FinTuplesType F n)
        → into (out-ncin n r) == ncin n r
      into-out-ncin O x = ! (ncglue O x)
      into-out-ncin (S n) (x , r) = idp

      into-out-ncglue : (n : ℕ) (r : FinTuplesType F n)
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

      into-out : (r : FinTuples F) → into (out r) == r
      into-out = ℕColimElim.f _
        into-out-ncin
        into-out-ncglue

      out-into : (t : de⊙ (F O) × FinTuples (F ∘ S)) → out (into t) == t
      out-into = uncurry $ λ x → ℕColimElim.f _
        (λ n r → idp)
        (λ n r → ↓-='-from-square $
          (ap-∘ out (Into.f x) (ncglue n r)
           ∙ ap (ap out) (Into.ncglue-β x n r)
           ∙ Out.ncglue-β (S n) (x , r))
          ∙v⊡ vid-square)

⊙fin-tuples-cons : ∀ {i} (F : ℕ → Ptd i)
  → (F O ⊙× ⊙FinTuples (F ∘ S)) ⊙≃ ⊙FinTuples F
⊙fin-tuples-cons F = ≃-to-⊙≃ (fin-tuples-cons F) (! (ncglue O _))
