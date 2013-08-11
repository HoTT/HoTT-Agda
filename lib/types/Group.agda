{-# OPTIONS --without-K #-} 

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Group where

record Group {i} (El : Type i) : Type i where
  constructor group
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

record GroupHom {i j} {A : Type i} {B : Type j} 
  (G : Group A) (H : Group B) : Type (lsucc (lmax i j)) where
  field
    f : A → B
    pres-ident : f (ident G) == ident H
    pres-comp  : ∀ g1 g2 → f (comp G g1 g2) == comp H (f g1) (f g2)

grouphom-pres-inv : ∀ {i j} {A : Type i} {B : Type j}
  {G : Group A} {H : Group B} (f : GroupHom G H)
  (a : A) → GroupHom.f f (inv G a) == inv H (GroupHom.f f a)
grouphom-pres-inv {G = G} {H = H} f a = 
  h (inv G a)
    =⟨ ! (unitr H (h (inv G a))) ⟩
  comp H (h (inv G a)) (ident H)
    =⟨ ! (invr H (h a)) |in-ctx (λ w → comp H (h (inv G a)) w) ⟩
  comp H (h (inv G a)) (comp H (h a) (inv H (h a)))
    =⟨ ! (assoc H (h (inv G a)) (h a) (inv H (h a))) ⟩
  comp H (comp H (h (inv G a)) (h a)) (inv H (h a))
    =⟨ lemma |in-ctx (λ w → comp H w (inv H (h a))) ⟩
  comp H (ident H) (inv H (h a))
    =⟨ unitl H (inv H (h a)) ⟩
  inv H (h a) ∎
  where 
  h = GroupHom.f f

  lemma : comp H (GroupHom.f f (inv G a)) (GroupHom.f f a) == ident H
  lemma = ! (GroupHom.pres-comp f (inv G a) a) 
          ∙ ap (GroupHom.f f) (invl G a) 
          ∙ GroupHom.pres-ident f
  
abstract
  group= : ∀ {i} {A : Type i}
    {id₁ id₂ : A} {inv₁ inv₂ : A → A} {comp₁ comp₂ : A → A → A}
    → ∀ {level₁ level₂} → ∀ {unitl₁ unitl₂} → ∀ {unitr₁ unitr₂} → ∀ {assoc₁ assoc₂}
    → ∀ {invr₁ invr₂} → ∀ {invl₁ invl₂}
    → (id₁ == id₂) → (inv₁ == inv₂) → (comp₁ == comp₂)
    → group level₁ id₁ inv₁ comp₁ unitl₁ unitr₁ assoc₁ invr₁ invl₁
      == group level₂ id₂ inv₂ comp₂ unitl₂ unitr₂ assoc₂ invr₂ invl₂
  group= {id₁ = id} {inv₁ = inv} {comp₁ = comp} {level₁ = level} idp idp idp = ap6
    (λ level unitl unitr assoc invr invl →
       group level id inv comp unitl unitr assoc invr invl)
    (prop-has-all-paths has-level-is-prop _ _) 
    (prop-has-all-paths (Π-level (λ _ → level _ _)) _ _) 
    (prop-has-all-paths (Π-level (λ _ → level _ _)) _ _) 
    (prop-has-all-paths (Π-level (λ _ → Π-level (λ _ → Π-level (λ _ → level _ _)))) _ _) 
    (prop-has-all-paths (Π-level (λ _ → level _ _)) _ _) 
    (prop-has-all-paths (Π-level (λ _ → level _ _)) _ _)
    where 
    ap6 : ∀ {j} {C D E F G H J : Type j}
      {c₁ c₂ : C} {d₁ d₂ : D} {e₁ e₂ : E} {f₁ f₂ : F} {g₁ g₂ : G} {h₁ h₂ : H}
      (f : C → D → E → F → G → H → J)
      → (c₁ == c₂) → (d₁ == d₂) → (e₁ == e₂) → (f₁ == f₂) → (g₁ == g₂) → (h₁ == h₂)
      → f c₁ d₁ e₁ f₁ g₁ h₁ == f c₂ d₂ e₂ f₂ g₂ h₂
    ap6 f idp idp idp idp idp idp = idp

  ↓-group= : ∀ {i} {A B : Type i} {G : Group A} {H : Group B}
    (p : A == B) 
    → (ident G == ident H [ (λ C → C) ↓ p ]) 
    → (inv G == inv H [ (λ C → C → C) ↓ p ]) 
    → (comp G == comp H [ (λ C → C → C → C) ↓ p ])
    → G == H [ Group ↓ p ]
  ↓-group= idp = group=

  group-iso : ∀ {i} {A B : Type i} {G : Group A} {H : Group B} (h : GroupHom G H) 
    → is-equiv (GroupHom.f h) → Path {A = Σ (Type i) Group} (A , G) (B , H)
  group-iso {A = A} {G = G} {H = H} h e = 
    pair= (ua (f , e)) (↓-group= (ua (f , e)) ident= inv= comp=)
    where
    open GroupHom h

    ident= : ident G == ident H [ (λ C → C) ↓ ua (f , e) ]
    ident= = (↓-idf-ua-in _ pres-ident) 

    inv= : inv G == inv H [ (λ C → C → C) ↓ ua (f , e) ]
    inv= =
      coe (↓-→-is-square (inv G) (inv H) (ua (f , e))) $ λ= $ λ a → 
        transport (λ C → C) (ua (f , e)) (inv G a) 
          =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
        f (inv G a) 
          =⟨ grouphom-pres-inv h a ⟩
        inv H (f a)
          =⟨ ap (inv H) (! (to-transp (↓-idf-ua-in _ idp))) ⟩
        inv H (transport (λ C → C) (ua (f , e)) a) ∎

    comp=' : (a : A) → comp G a == comp H (f a) [ (λ C → C → C) ↓ ua (f , e) ]
    comp=' a = 
      coe (↓-→-is-square (comp G a) (comp H (f a)) (ua (f , e))) $ λ= $ λ b →
        transport (λ C → C) (ua (f , e)) (comp G a b)
          =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
        f (comp G a b)
          =⟨ pres-comp a b ⟩
        comp H (f a) (f b)
          =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → comp H (f a) w) ⟩
        comp H (f a) (transport (λ C → C) (ua (f , e)) b) ∎

    comp= : comp G == comp H [ (λ C → C → C → C) ↓ ua (f , e) ]
    comp= =
      coe (↓-→-is-square (comp G) (comp H) (ua (f , e))) $ λ= $ λ a → 
        transport (λ C → C → C) (ua (f , e)) (comp G a)
          =⟨ to-transp (comp=' a) ⟩
        comp H (f a)
          =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → comp H w) ⟩ 
        comp H (transport (λ C → C) (ua (f , e)) a) ∎


AbelianGroup : ∀ {i} → Type i → Type i
AbelianGroup A = Σ (Group A) 
                   (λ G → ∀ (g₁ g₂ : A) → comp G g₁ g₂ == comp G g₂ g₁)

PathGroup : ∀ {i} (A : ⟨ 1 ⟩ -Type i) (a₀ : fst A) → Group (a₀ == a₀)
PathGroup {i} A a₀ = record { El-level = snd A a₀ a₀;
                              ident = idp; inv = !; comp = _∙_;
                              unitl = λ _ → idp; unitr = ∙-unit-r;
                              assoc = ∙-assoc; 
                              invr = !-inv-r; invl = !-inv-l }