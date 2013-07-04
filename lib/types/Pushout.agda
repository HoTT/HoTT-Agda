{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Paths
import lib.types.Generic1HIT as Generic1HIT

module lib.types.Pushout where
-- Cannot be parametrized by i j k because we use different values in the
-- flattening lemma. This should be fixed somehow.

module Pushout {i} {j} {k} {d : Span {i} {j} {k}} where

  open Span d renaming (f to g; g to h)

  module _ where

    private
      data #Pushout : Type (lmax (lmax i j) k) where
        #left : A → #Pushout
        #right : B → #Pushout

    Pushout : Type _
    Pushout = #Pushout

    left : A → Pushout
    left = #left

    right : B → Pushout
    right = #right

    postulate  -- HIT
      glue : (c : C) → left (g c) == right (h c)

    module PushoutElim {l} {P : Pushout → Type l} (left* : (a : A) → P (left a))
      (right* : (b : B) → P (right b))
      (glue* : (c : C) → left* (g c) == right* (h c) [ P ↓ glue c ]) where

      f : (x : Pushout) → P x
      f (#left y) = left* y
      f (#right y) = right* y

      postulate  -- HIT
        glue-β : (c : C) → apd f (glue c) == glue* c

  open PushoutElim public using () renaming (f to Pushout-elim)

  module PushoutRec {l} {D : Type l} (left* : A → D) (right* : B → D)
    (glue* : (c : C) → left* (g c) == right* (h c)) where

    private
      module M = PushoutElim left* right* (λ c → ↓-cst-in (glue* c))

    f : Pushout → D
    f = M.f

    glue-β : (c : C) → ap f (glue c) == glue* c
    glue-β c = apd=cst-in (M.glue-β c)

  module PushoutGeneric where

    open Generic1HIT (Coprod A B) C (inl ∘ g) (inr ∘ h) public

    generic-pushout : Pushout ≃ T
    generic-pushout = equiv to from to-from from-to  module _ where

      module To = PushoutRec (cc ∘ inl) (cc ∘ inr) pp

      to : Pushout → T
      to = To.f

      from-cc : Coprod A B → Pushout
      from-cc (inl a) = left a
      from-cc (inr b) = right b

      module From = Rec from-cc glue

      from : T → Pushout
      from = From.f

      to-from : (x : T) → to (from x) == x
      to-from = elim to-from-cc to-from-pp where

        to-from-cc : (x : Coprod A B)
          → to (from (cc x)) == cc x
        to-from-cc (inl a) = idp
        to-from-cc (inr b) = idp

        to-from-pp :
          (c : C) → idp == idp [ (λ z → to (from z) == z) ↓ pp c ]
        to-from-pp c = ↓-∘=id-in from to
          (ap to (ap from (pp c))   =⟨ From.pp-β c |in-ctx ap to ⟩
           ap to (glue c)                    =⟨ To.glue-β c ⟩
           pp c ∎)

      from-to : (x : Pushout) → from (to x) == x
      from-to = Pushout-elim (λ a → idp) (λ b → idp) (λ c → ↓-∘=id-in to from
        (ap from (ap to (glue c))   =⟨ To.glue-β c |in-ctx ap from ⟩
         ap from (pp c)    =⟨ From.pp-β c ⟩
         glue c ∎))

open Pushout public hiding (Pushout)

Pushout : ∀ {i j k} (d : Span {i} {j} {k}) → Type (lmax (lmax i j) k)
Pushout d = Pushout.Pushout {d = d}

module _  {i} {j} {k} {d : Span {i} {j} {k}} where

  open Span d renaming (f to g; g to h)

  module PushoutRecType {l} (left* : A → Type l) (right* : B → Type l)
    (glue* : (c : C) → left* (g c) ≃ right* (h c)) where

    open PushoutRec left* right* (ua ∘ glue*) public

    abstract
      coe-glue-β : (c : C) (a : left* (g c))
        → coe (ap f (glue c)) a == –> (glue* c) a
      coe-glue-β c a =
        coe (ap f (glue c)) a  =⟨ glue-β c |in-ctx (λ u → coe u a) ⟩
        coe (ua (glue* c)) a   =⟨ coe-β (glue* c) a ⟩
        –> (glue* c) a ∎

      coe!-glue-β : (c : C) (b : right* (h c))
        → coe! (ap f (glue c)) b == <– (glue* c) b
      coe!-glue-β c b =
        coe! (ap f (glue c)) b  =⟨ glue-β c |in-ctx (λ u → coe! u b) ⟩
        coe! (ua (glue* c)) b   =⟨ coe!-β (glue* c) b ⟩
        <– (glue* c) b ∎

      ↓-glue-out : (c : C) {a : left* (g c)} {b : right* (h c)}
        → a == b [ f ↓ glue c ]
        → –> (glue* c) a == b
      ↓-glue-out c {a} {b} p =
        –> (glue* c) a          =⟨ ! (coe-glue-β c a) ⟩
        coe (ap f (glue c)) a   =⟨ to-transp p ⟩
        b ∎

      ↓-glue-in : (c : C) {a : left* (g c)} {b : right* (h c)}
        → –> (glue* c) a == b
        → a == b [ f ↓ glue c ]
      ↓-glue-in c {a} {b} p = from-transp f (glue c) (coe-glue-β c a ∙ p)

    f-d : Span
    f-d = span fA fB fC fg fh  module _ where

      fA : Type _
      fA = Σ A left*

      fB : Type _
      fB = Σ B right*

      fC : Type _
      fC = Σ C (left* ∘ g)

      fg : fC → fA
      fg (c , c') = (g c , c')

      fh : fC → fB
      fh (c , c') = (h c , –> (glue* c) c')

    flattening : Σ (Pushout d) f == Pushout f-d
    flattening = ap (uncurry Σ) (pair= r r') ∙ q ∙ eq ∙ p  where

      module G = PushoutGeneric {d = d}
      module fG = PushoutGeneric {d = f-d}

      P-cc : Coprod A B → Type _
      P-cc (inl a) = left* a
      P-cc (inr b) = right* b

      module P = G.RecType P-cc glue*

      p : fG.T == Pushout f-d
      p = ! (ua fG.generic-pushout)

      import lib.types.Flattening as Flattening
      module FlatteningPushout = Flattening
        (Coprod A B) C (inl ∘ g) (inr ∘ h) P-cc glue*
      open FlatteningPushout public hiding (flattening-equiv; module P)

      module fG' = Generic1HIT At Bt ft gt

      q : Σ G.T P.f == fG'.T
      q = ua FlatteningPushout.flattening-equiv

      eq : fG'.T == fG.T
      eq = ua eqv  where

        to-cc : At → fG.T
        to-cc (inl a , a') = fG.cc (inl (a , a'))
        to-cc (inr b , b') = fG.cc (inr (b , b'))

        module To = fG'.Rec to-cc fG.pp

        to : fG'.T → fG.T
        to = To.f

        from-cc : Coprod fA fB → fG'.T
        from-cc (inl (a , a')) = fG'.cc (inl a , a')
        from-cc (inr (b , b')) = fG'.cc (inr b , b')

        module From = fG.Rec from-cc fG'.pp

        from : fG.T → fG'.T
        from = From.f

        to-from : (x : fG.T) → to (from x) == x
        to-from = fG.elim to-from-cc to-from-pp  where
          to-from-cc : (x : Coprod fA fB)
            → to (from (fG.cc x)) == fG.cc x
          to-from-cc (inl _) = idp
          to-from-cc (inr _) = idp

          to-from-pp : (c : fC)
            → idp == idp [ (λ x → to (from x) == x) ↓ fG.pp c ]
          to-from-pp c = ↓-∘=id-in from to
            (ap to (ap from (fG.pp c))   =⟨ From.pp-β c |in-ctx ap to ⟩
             ap to (fG'.pp c)            =⟨ To.pp-β c ⟩
             fG.pp c ∎)

        from-to : (x : fG'.T) → from (to x) == x
        from-to = fG'.elim from-to-cc from-to-pp  where
          from-to-cc : (a : At) → from (to (fG'.cc a)) == fG'.cc a
          from-to-cc (inl _ , _) = idp
          from-to-cc (inr _ , _) = idp

          from-to-pp : (b : Bt)
            → idp == idp [ (λ x → from (to x) == x) ↓ fG'.pp b ]
          from-to-pp b = ↓-∘=id-in to from
            (ap from (ap to (fG'.pp b))   =⟨ To.pp-β b |in-ctx ap from ⟩
             ap from (fG.pp b)            =⟨ From.pp-β b ⟩
             fG'.pp b ∎)

        eqv : fG'.T ≃ fG.T
        eqv = equiv to from to-from from-to

      r : Pushout d == G.T
      r = ua G.generic-pushout

      r' : f == P.f [ (λ X → (X → Type _)) ↓ r ]
      r' = ↓-app→cst-in (λ {t} {t'} q →
             Pushout-elim {P = λ t → f t == P.f (–> G.generic-pushout t)}
               (λ a → idp) (λ b → idp)
               (λ c → ↓-='-in
                 (ap (P.f ∘ (–> G.generic-pushout)) (glue c)    =⟨ ap-∘ P.f _ (glue c) ⟩
                  ap P.f (ap (–> G.generic-pushout) (glue c))   =⟨ G.To.glue-β c |in-ctx ap P.f ⟩
                  ap P.f (pp c)                                 =⟨ P.pp-β c ⟩
                  ua (glue* c)                                  =⟨ ! (glue-β c) ⟩
                  ap f (glue c) ∎))
           t ∙ ap P.f (↓-idf-ua-out _ q))

_⊔^[_]_/_ : ∀ {i j k} (A : Type i) (C : Type k) (B : Type j)
  (fg : (C → A) × (C → B)) → Type (lmax (lmax i j) k)
A ⊔^[ C ] B  / (f , g) = Pushout (span A B C f g)

_*_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A * B = A ⊔^[ (A × B) ] B  / (fst , snd)
