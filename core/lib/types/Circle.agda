{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.Unit
open import lib.types.Bool
open import lib.types.Suspension
open import lib.types.IteratedSuspension

module lib.types.Circle where

{-
Idea :

data S¹ : Type₀ where
  base : S¹
  loop : base == base

I’m using Dan Licata’s trick to have a higher inductive type with definitional
reduction rule for [base]
-}

{-
  favonia (2016/05): Now [Circle] is defined as [Sphere 1].
-}

module _ where
  -- (already defined in IteratedSuspension.agda)
  -- S¹ : Type₀
  -- S¹ = Sphere 1

  base : S¹
  base = north

  loop : base == base
  loop = σloop ⊙Bool false

  module S¹Elim {i} {P : S¹ → Type i} (base* : P base)
    (loop* : base* == base* [ P ↓ loop ]) where

    private
      north* = base*
      south* = transport P (merid false) base*
      merid*-general :
        ∀ {x : S¹} (p q : base == x)
          (loop* :  base* == base* [ P ↓ p ∙ ! q ]) (b : Bool)
        → base* == transport P p base* [ P ↓ Bool-rec q p b ]
      merid*-general idp q loop* false = idp
      merid*-general idp q loop* true = !ᵈ' loop*

      merid* : ∀ (b : Bool) → north* == south* [ P ↓ merid b ]
      merid* false = merid*-general (merid false) (merid true) loop* false
      merid* true = merid*-general (merid false) (merid true) loop* true

      module SE = SuspElim north* south* merid*

    f : Π S¹ P
    f = SE.f

    private
      merid*-general-lemma :
        ∀ {x : S¹} (p q : base == x) (loop* :  base* == base* [ P ↓ p ∙ ! q ])
        → merid*-general p q loop* false ◃ !ᵈ (merid*-general p q loop* true) == loop*
      merid*-general-lemma idp q loop* = idp◃ _ ∙ !ᵈ-!ᵈ' loop*

    loop-β : apd f loop == loop*
    loop-β =
      apd f loop
        =⟨ apd-∙ f (merid false) (! (merid true)) ⟩
      apd f (merid false) ◃ apd f (! (merid true))
        =⟨ apd-! f (merid true) |in-ctx apd f (merid false) ◃_ ⟩
      apd f (merid false) ◃ !ᵈ (apd f (merid true))
        =⟨ SE.merid-β false |in-ctx _◃ !ᵈ (apd f (merid true)) ⟩
      merid* false ◃ !ᵈ (apd f (merid true))
        =⟨ SE.merid-β true |in-ctx (λ p → merid* false ◃ !ᵈ p) ⟩
      merid* false ◃ !ᵈ (merid* true)
        =⟨ merid*-general-lemma (merid false) (merid true) loop* ⟩
      loop*
        =∎

open S¹Elim public using () renaming (f to S¹-elim)

module S¹Rec {i} {A : Type i} (base* : A) (loop* : base* == base*) where

  private
    module M = S¹Elim base* (↓-cst-in loop*)

  f : S¹ → A
  f = M.f

  loop-β : ap f loop == loop*
  loop-β = apd=cst-in {f = f} M.loop-β

open S¹Rec public using () renaming (f to S¹-rec)

S¹-rec-η : ∀ {i} {A : Type i} (f : S¹ → A)
  → ∀ x → S¹-rec (f base) (ap f loop) x == f x
S¹-rec-η f = S¹-elim idp (↓-='-in' $ ! $ S¹Rec.loop-β (f base) (ap f loop))

module S¹RecType {i} (A : Type i) (e : A ≃ A) where

  open S¹Rec A (ua e) public

  coe-loop-β : (a : A) → coe (ap f loop) a == –> e a
  coe-loop-β a =
    coe (ap f loop) a   =⟨ loop-β |in-ctx (λ u → coe u a) ⟩
    coe (ua e) a        =⟨ coe-β e a ⟩
    –> e a =∎

  coe!-loop-β : (a : A) → coe! (ap f loop) a == <– e a
  coe!-loop-β a =
    coe! (ap f loop) a   =⟨ loop-β |in-ctx (λ u → coe! u a) ⟩
    coe! (ua e) a        =⟨ coe!-β e a ⟩
    <– e a =∎

  ↓-loop-out : {a a' : A} → a == a' [ f ↓ loop ] → –> e a == a'
  ↓-loop-out {a} {a'} p =
    –> e a              =⟨ ! (coe-loop-β a) ⟩
    coe (ap f loop) a   =⟨ to-transp p ⟩
    a' =∎

  import lib.types.Generic1HIT as Generic1HIT
  module S¹G = Generic1HIT Unit Unit (idf _) (idf _)
  module P = S¹G.RecType (cst A) (cst e)

  private
    generic-S¹ : Σ S¹ f == Σ S¹G.T P.f
    generic-S¹ = eqv-tot where

      module To = S¹Rec (S¹G.cc tt) (S¹G.pp tt)
      to = To.f

      module From = S¹G.Rec (cst base) (cst loop)
      from : S¹G.T → S¹
      from = From.f

      abstract
        to-from : (x : S¹G.T) → to (from x) == x
        to-from = S¹G.elim (λ _ → idp) (λ _ → ↓-∘=idf-in' to from
          (ap to (ap from (S¹G.pp tt)) =⟨ From.pp-β tt |in-ctx ap to ⟩
           ap to loop                  =⟨ To.loop-β ⟩
           S¹G.pp tt =∎))

        from-to : (x : S¹) → from (to x) == x
        from-to = S¹-elim idp (↓-∘=idf-in' from to
          (ap from (ap to loop)   =⟨ To.loop-β |in-ctx ap from ⟩
           ap from (S¹G.pp tt)    =⟨ From.pp-β tt ⟩
           loop =∎))

      eqv : S¹ ≃ S¹G.T
      eqv = equiv to from to-from from-to

      eqv-fib : f == P.f [ (λ X → (X → Type _)) ↓ ua eqv ]
      eqv-fib =
        ↓-app→cst-in (λ {t} p → S¹-elim {P = λ t → f t == P.f (–> eqv t)} idp
          (↓-='-in'
            (ap (P.f ∘ (–> eqv)) loop   =⟨ ap-∘ P.f to loop ⟩
             ap P.f (ap to loop)        =⟨ To.loop-β |in-ctx ap P.f ⟩
             ap P.f (S¹G.pp tt)         =⟨ P.pp-β tt ⟩
             ua e                       =⟨ ! loop-β ⟩
             ap f loop =∎))
        t ∙ ap P.f (↓-idf-ua-out eqv p))

      eqv-tot : Σ S¹ f == Σ S¹G.T P.f
      eqv-tot = ap (uncurry Σ) (pair= (ua eqv) eqv-fib)

  import lib.types.Flattening as Flattening
  module FlatteningS¹ = Flattening
    Unit Unit (idf _) (idf _) (cst A) (cst e)
  open FlatteningS¹ public hiding (flattening-equiv; module P)

  flattening-S¹ : Σ S¹ f == Wt
  flattening-S¹ = generic-S¹ ∙ ua FlatteningS¹.flattening-equiv

instance
  S¹-conn : is-connected 0 S¹
  S¹-conn = Sphere-conn 1
