{-# OPTIONS --without-K #-} 

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel

module lib.Group where

record Group {i} (El : Type i) : Type i where
  field
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

record GroupHom {i j} {A : Type i} {B : Type j} (G : Group A) (H : Group B) : Type (lsucc (lmax i j)) where
  field
    f : A → B
    pres-ident : f (ident G) == ident H
    pres-comp  : ∀ g1 g2 → f (comp G g1 g2) == comp H (f g1) (f g2)

AbelianGroup : ∀ {i} → Type i → Type i
AbelianGroup A = Σ (Group A) 
                   (λ G → ∀ (g₁ g₂ : A) → comp G g₁ g₂ == comp G g₂ g₁)

PathGroup : ∀ {i} (A : ⟨ 1 ⟩ -Type i) (a₀ : fst A) → Group (a₀ == a₀)
PathGroup {i} A a₀ = record { El-level = snd A a₀ a₀;
                              ident = idp; inv = !; comp = _∙_;
                              unitl = λ _ → idp; unitr = ∙-unit-r;
                              assoc = ∙-assoc; 
                              invr = !-inv-r; invl = !-inv-l }