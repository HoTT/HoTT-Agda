{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PushoutSplit

module cw.cohomology.grid.CofiberSplit {i j k}
  {A : Type i} {B : Type j} {C : Type k}
  (f : A → B) (g : B → C) where

  {-
    A -------> B -----------> C
    |          |           _/|
    |          |         _/  |
    |          |     __.D_   |
    v          v .--'   | `-.v
    1 ------> B/A ------|-> C/A
               |        |    |
               |        v    |
               |     __.E_   |
               v .--'     `-.v
               1 ---------> C/B
  -}

  open import cw.cohomology.grid.Map f g

  private
    B-to-B/A : B → B/A
    B-to-B/A = cfcod' f

    D-span : Span
    D-span = span B/A C B B-to-B/A g
    D : Type (lmax i (lmax j k))
    D = Pushout D-span

  private
    module VSplit = PushoutRSplit (λ _ → tt) f g
    module C/AToD = VSplit.Split
  C/A-to-D : C/A → D
  C/A-to-D = C/AToD.f

  B/A-to-D : B/A → D
  B/A-to-D = left

  private
    E : Type (lmax i (lmax j k))
    E = Cofiber B/A-to-D

  private
    module HSplit = PushoutLSplit B-to-B/A (λ _ → tt) g
    module C/BToE = HSplit.Split
  C/B-to-E : C/B → E
  C/B-to-E = C/BToE.f

  C/B-to-E-glue-β : ∀ x →
    ap C/B-to-E (glue x) == glue (cfcod x) ∙' ap cfcod (glue x)
  C/B-to-E-glue-β = HSplit.split-glue-β

  private
    module DToC/B = HSplit.Inner
    D-to-C/B : D → C/B
    D-to-C/B = DToC/B.f

    D-to-E : D → E
    D-to-E = cfcod

    C/A-to-D-to-C/B : ∀ c/a → D-to-C/B (C/A-to-D c/a) == C/A-to-C/B c/a
    C/A-to-D-to-C/B = Cofiber-elim
      idp
      (λ c → idp)
      (λ a → ↓-='-in' $ ! $
        ap (D-to-C/B ∘ C/A-to-D) (glue a)
          =⟨ ap-∘ D-to-C/B C/A-to-D (glue a) ⟩
        ap D-to-C/B (ap C/A-to-D (glue a))
          =⟨ C/AToD.glue-β a |in-ctx ap D-to-C/B ⟩
        ap D-to-C/B (ap left (glue a) ∙ glue (f a))
          =⟨ ap-∙ D-to-C/B (ap left (glue a)) (glue (f a)) ⟩
        ap D-to-C/B (ap left (glue a)) ∙ ap D-to-C/B (glue (f a))
          =⟨ ap2 _∙_ (∘-ap D-to-C/B left (glue a)) (DToC/B.glue-β (f a)) ⟩
        ap (λ _ → cfbase) (glue a) ∙ glue (f a)
          =⟨ ap-cst cfbase (glue a) |in-ctx _∙ glue (f a) ⟩
        glue (f a)
          =⟨ ! $ C/AToC/B.glue-β a ⟩
        ap C/A-to-C/B (glue a)
          =∎)

    D-to-C/B-to-E : ∀ d → C/B-to-E (D-to-C/B d) == D-to-E d
    D-to-C/B-to-E = HSplit.split-inner

  {- The public interface -}

  C/A-to-C/B-comm-square : CommSquare C/A-to-C/B D-to-E C/A-to-D C/B-to-E
  C/A-to-C/B-comm-square = comm-sqr λ c/a → ap C/B-to-E (! (C/A-to-D-to-C/B c/a))
                                     ∙ D-to-C/B-to-E (C/A-to-D c/a)

  B/A-to-C/A-comm-square : CommSquare B/A-to-C/A B/A-to-D (idf B/A) C/A-to-D
  B/A-to-C/A-comm-square = comm-sqr VSplit.split-inner

  C/A-to-D-is-equiv : is-equiv C/A-to-D
  C/A-to-D-is-equiv = snd VSplit.split-equiv

  C/B-to-E-is-equiv : is-equiv C/B-to-E
  C/B-to-E-is-equiv = snd HSplit.split-equiv
