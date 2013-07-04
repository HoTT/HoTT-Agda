{-# OPTIONS --without-K #-} 

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel

module lib.Group where

record Group i : Type (lsucc i) where
  field
    El : Type i
    El-level : has-level ⟨0⟩ El
    ident : El
    inv : El → El
    comp : El → El → El
    unitl : ∀ a → comp ident a == a
    unitr : ∀ a → comp a ident == a
    assoc   : ∀ a b c → comp (comp a b) c == comp a (comp b c)
    invr    : ∀ a → (comp a (inv a)) == ident
    invl    : ∀ a → (comp (inv a) a) == ident
open Group

record GroupHom {i j} (G : Group i) (H : Group j) : Type (lsucc (lmax i j)) where
  field
    f : El G → El H
    pres-ident : f (ident G) == ident H
    pres-comp  : ∀ g1 g2 → f (comp G g1 g2) == comp H (f g1) (f g2)

AbelianGroup : ∀ i → Type (lsucc i)
AbelianGroup i = Σ (Group i) 
                   (λ G → ∀ (g₁ g₂ : El G) → comp G g₁ g₂ == comp G g₂ g₁)

PathGroup : ∀ {i} (A : ⟨ 1 ⟩ -Type i) (a₀ : fst A) → Group i
PathGroup {i} A a₀ = record { El = (a₀ == a₀); El-level = snd A a₀ a₀;
                              ident = idp; inv = !; comp = _∙_;
                              unitl = λ _ → idp; unitr = ∙-unit-r;
                              assoc = ∙-assoc; 
                              invr = !-inv-r; invl = !-inv-l }