{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Paths
import lib.types.Generic1HIT as Generic1HIT
open import lib.types.Pushout

module lib.types.PushoutFlattening {i} {j} {k} {d : Span {i} {j} {k}} where

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

  private
    module _ where
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

    f-d : Span
    f-d = span fA fB fC fg fh  

  flattening : Σ (Pushout d) f == Pushout f-d
  flattening = Σ= p p' ∙ q ∙ r ∙ s  where

    module G = PushoutGeneric {d = d}

    P-cc : Coprod A B → Type _
    P-cc (inl a) = left* a
    P-cc (inr b) = right* b

    module P = G.RecType P-cc glue*

    import lib.types.Flattening as Flattening
    module FlatteningPushout = Flattening
      (Coprod A B) C (inl ∘ g) (inr ∘ h) P-cc glue*
    open FlatteningPushout public hiding (flattening-equiv; module P)

    p-equiv : Pushout d ≃ G.T
    p-equiv = G.generic-pushout

    p : Pushout d == G.T
    p = ua p-equiv

    p' : f == P.f [ (λ X → (X → Type _)) ↓ p ]
    p' = ↓-app→cst-in (λ {t} {t'} q →
           Pushout-elim {P = λ t → f t == P.f (–> p-equiv t)}
             (λ a → idp) (λ b → idp)
             (λ c → ↓-='-in
               (ap (P.f ∘ (–> p-equiv)) (glue c)    =⟨ ap-∘ P.f (–> p-equiv) (glue c) ⟩
                ap P.f (ap (–> p-equiv) (glue c))   =⟨ G.To.glue-β c |in-ctx ap P.f ⟩
                ap P.f (pp c)                       =⟨ P.pp-β c ⟩
                ua (glue* c)                        =⟨ ! (glue-β c) ⟩
                ap f (glue c) ∎))
         t ∙ ap P.f (↓-idf-ua-out _ q))

    --

    module fG' = Generic1HIT At Bt ft gt

    q : Σ G.T P.f == fG'.T
    q = ua FlatteningPushout.flattening-equiv

    --

    {-
    This part is basically [Generic1HIT=] applied to the flattening lemma
    for coproducts. Maybe it would make sense to refactor it that way.
    -}

    module fG = PushoutGeneric {d = f-d}

    r : fG'.T == fG.T
    r = ua (equiv to from to-from from-to)  where

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

      abstract
        to-from : (x : fG.T) → to (from x) == x
        to-from = fG.elim to-from-cc to-from-pp  where
          to-from-cc : (x : Coprod fA fB)
            → to (from (fG.cc x)) == fG.cc x
          to-from-cc (inl _) = idp
          to-from-cc (inr _) = idp

          to-from-pp : (c : fC)
            → idp == idp [ (λ x → to (from x) == x) ↓ fG.pp c ]
          to-from-pp c = ↓-∘=idf-in to from
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
          from-to-pp b = ↓-∘=idf-in from to
            (ap from (ap to (fG'.pp b))   =⟨ To.pp-β b |in-ctx ap from ⟩
             ap from (fG.pp b)            =⟨ From.pp-β b ⟩
             fG'.pp b ∎)

    --

    s : fG.T == Pushout f-d
    s = ! (ua fG.generic-pushout)
