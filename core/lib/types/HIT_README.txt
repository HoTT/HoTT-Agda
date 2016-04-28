* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
*                                                           *
*   Implementation of higher inductive types in HoTT-Agda   *
*                                                           *
* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Introduction
============

Agda does not have higher inductive types (HITs) natively, so we need to use
some hack(s) to fake them. This file contains
- the precise description of a particular scheme of HITs (parametrized truncated
  1-HITs) and of the associated elimination and reduction rules,
- some technical explanations of the hack(s),
- the interface used in the HoTT-Agda library,
- a sample file showing all of that in action,
- some additional informations about 2-HITs.


Contents
========

* Introduction
* Contents
* Definition of 1pt-HITs
* Elimination and reduction rules for 1pt-HITs
* Explanations of the hacks needed in Agda
* Interface choosen in HoTT-Agda
* Sample I.agda file
* Higher dimensional HITs
* Mutually recursive HITs


Definition of 1pt-HITs
======================

We will give a precise description of parametrized higher inductive types with
only points and paths constructors (no constructor of dimension ≥ 2), and
possibly with an additional truncation constructor. Let’s call such higher
inductive types "1pt-HITs" ("1" for the restriction to constructors of dimension
≤ 1, "p" for "parametrized" and "t" for the truncation constructor)

A 1pt-HIT specification consists of:

- A telescope [Γ] of parameters split in two:
  
    Γ = (Γf , Γv)
  
  where the parameters in [Γf] are called the *fixed* (or uniform) parameters,
  and the parameters in [Γv] are called the *variable* (or nonuniform)
  parameters.

- The formation rule for the type constructor, with [i] a big enough (see below)
  universe level:

    I : (γf : Γf) (γv : Γv) → Type i

- The introduction rules for the points constructors:

    c_1 : {γf : Γf} {γv : Γv} → Γ_1 → I γf γv
    ⋮
    c_n : {γf : Γf} {γv : Γv} → Γ_n → I γf γv

  where each [Γ_i] is a telescope subject to the following strict positivity
  condition with respect to [I]:
  For every type [A] in [Γ_i], either
  - [I] does not occur in [A], or
  - [A = (Γ_A → I γf γv')] where [Γ_A] is a telescope where [I] does not
    occur, and [γv' : Γv] (note that the fixed parameters are not allowed to
    vary, hence their name)

- The introduction rules for the paths constructors:

    p_1 : {γf : Γf} {γv : Γv} → Δ_1 → u_1 == v_1
    ⋮
    p_m : {γf : Γf} {γv : Γv} → Δ_m → u_m == v_m

  where each [Δ_i] is a telescope subject to the strict positivity condition
  with respect to [I] as above, and where each [u_i] and [v_i] is an acceptable
  point in [Δ_i] of type [I γf γv]. An acceptable point in [Δ_i] is a term in
  the context [Δ_i] which is either
  - [x δ_A] where [x] is a variable in [Δ_i] of type [Δ_A → I γf γv'] and where
    we have [δ_A : Δ_A] (note that [I] doesn’t occur in [Δ_A]), or
  - [c_k γ_k] where each element of [γ_k] is either
    - an arbitrary term (when [I] does not occur in its type), or
    - of the form [λ (γ' : Γ_A) → u] where [u] is an acceptable point in [Δ_i]
      (when its type is [Γ_A → I γf γv'])
  (the term [I] is not allowed to appear in acceptable points)

- Optionally, the introduction rule for the truncation constructor:

    I-level : {γf : Γf} {γv : Γv} → has-level n (I γf γv)

  where [n] is of type [ℕ] (in the context [Γf , Γv], so in particular it can be
  a parameter).

The universe level [i] has to be at least of the size of [Γf], [Γv], [Γ_1], …,
[Γ_n], [Δ_1], … and [Δ_m].


In an ideal world, we would just write:

  data I (γf : Γf) (γv : Γv) : Type i where
    c_1 : Γ_1 → I γf γv
    ⋮
    c_n : Γ_n → I γf γv
    p_1 : Δ_1 → u_1 == v_1
    ⋮
    p_m : Δ_m → u_m == v_m
    I-level : has-level n (I γf γv)

and automatically get the formation and introduction rules, pattern matching on
elements of I, and the associated (definitional) reduction rules.

But we’re not (yet) in an ideal world and the best we can get so far in Agda is:
- The formation and introduction rules
- The dependent elimination rule
- Definitional reduction rules for the points constructors
- Propositional reduction rules for the paths constructors

Drawbacks:
- No pattern matching
- No definitional reduction rules for the paths constructors
- Much more verbose
- Less safety checks (if you screw up your elimination rule, you may not notice
  it)


Elimination and reduction rules for 1pt-HITs
============================================

Let’s now describe the elimination rule and reduction rules for 1pt-HITs.

The elimination rule is the following:

  I-elim : {γf : Γf} {j} {P : {γv : Γv} → I γf γv → Type j}
    (c_1* : {γv : Γv} (γ_1P : (Γ_1 & P)) → P (c_1 (γ_1P -)))
    ⋮
    (c_n* : {γv : Γv} (γ_nP : (Γ_n & P)) → P (c_n (γ_nP -)))
    (p_1* : {γv : Γv} (δ_1P : (Δ_1 & P))
            → (u_1 &* δ_1P) == (v_1 &* δ_1P) [ P ↓ p_1 (δ_1P -) ])
    ⋮
    (p_m* : {γv : Γv} (δ_mP : (Δ_m & P))
            → (u_m &* δ_mP) == (v_m &* δ_mP) [ P ↓ p_m (δ_mP -) ])

    -- Only if the [I-level] constructor is present:
    (P-level : {γv : Γv} (i : I γf γv) → has-level n (P i))

    {γv : Γv} (i : I γf γv) → P i

and the reduction rules are the following:
(for [elim = I-elim c_1* ⋯ c_n* p_1* ⋯ p_m*])

  elim (c_1 γ_1) = c_1* (γ_1 &+ elim)
  ⋮
  elim (c_n γ_n) = c_n* (γ_n &+ elim)

  apd elim (p_1 δ_1) = p_1* (δ_1 &+ elim)
  ⋮
  apd elim (p_m δ_m) = p_m* (δ_m &+ elim)


where the operations [(Γ & P)], [(γP -)], [(u &* δP)] and [(γ &+ f)] are defined
as follows:

- (arguments of the dependent elimination rule)
  For [Γ] a telescope satisfying the condition of strict positivity with respect
  to [I], values [γf : Γf] for the fixed parameters, and a dependent type
  [P : {γv : Γv} → I γf γv → Type i], we define a telescope [(Γ & P)] by:

    (() & P) = ()
    ((Γ, A) & P) = (Γ & P) , A  -- if I does not occur in A
    ((Γ, (Γ_A → I γf γv')) & P) = (Γ & P) , (f : Γ_A → I γf γv') ,
                                    (f_rec : (γ_A : Γ_A) → P (f γ_A))

- There is an obvious context morphism from [(Γ & P)] to [Γ] discarding the
  recursive calls (the "*_rec"s), if [γP : (Γ & P)], we write [(γP -)] for the
  associated element of [Γ].

- (output types of paths arguments of the elimination rule)
  If [u] is an acceptable point in a context [Δ] and if [δP : (Δ & P)], then we
  define a term [(u &* δP)] of type [P (u [ (δP -) / Δ ])] as follows:

  - if [u = x δ_A] where [x] a variable of [Δ] of type [Δ_A → I γf γv'] and
    [δ_A : Δ_A], then [(u &* δP)] is [x_rec δ_A], where [x_rec] is the
    associated recursive call of [x] in [δP]
  - if [u = c_k γ_k], then [(u &* δP)] is [c_k* (γ_k &** δP)]

  where

    ((γ_k , a) &** δP) = (γ_k &** δP) , a  -- If [I] does not occur in the type
                                           -- of [a]
    ((γ_k , (λ γ_A → u)) &** δP) = (γ_k &** δP) , (λ γ_A → u) ,
                                     (λ γ_A → (u &* δ P))

- (recursive calls for the reduction rules)
  If we have [γ : Γ] and [s : {γv : Γv} (i : I γf γv) → P i], then we define
  [(γ &+ s) : (Γ & P)] as follows:

    (() &+ s) = ()
    -- If [I] does not occur in the type of [f]:
    ((γ , f) &+ s) = (γ &+ s) , f
    -- If [f : Γ_A → I γf γv']:
    ((γ , f) &+ s) = (γ &+ s) , f , (λ γ_A → s (f γ_A))


The nondependent elimination rule (recursion rule) is the following:

  I-rec : {γf : Γf} {j} {A : (γv : Γv) → Type j}
    (c_1* : {γv : Γv} → Γ_1 [ A / I γf ] → A γv)
    ⋮
    (c_n* : {γv : Γv} → Γ_n [ A / I γf ] → A γv)
    (p_1* : {γv : Γv} → Δ_1 [ A / I γf ]
            → u_1 [ (c_k* / c_k)_k ] == v_1 [ (c_k* / c_k)_k ])
    ⋮
    (p_m* : {γv : Γv} → Δ_m [ A / I γf ]
            → u_m [ (c_k* / c_k)_k ] == v_m [ (c_k* / c_k)_k ])

    -- Only if the [I-level] constructor is present:
    (A-level : {γv : Γv} → has-level n (A γv))

    {γv : Γv} → (I γf γv → A γv)

and the reduction rules are the following:
(for [rec = I-rec c_1* ⋯ c_n* p_1* ⋯ p_m*])

  rec (c_1 γ_1) = c_1* (γ_1 &+' rec)
  ⋮
  rec (c_n γ_n) = c_n* (γ_n &+' rec)

  ap rec (p_1 δ_1) == p_1* (δ_1 &+' rec)
  ⋮
  ap rec (p_m δ_m) == p_m* (δ_m &+' rec)

where:

- [Γ [ A / I γf] ] is [Γ] where all [I γf] have been replaced by [A]

- [u (c_k* / c_k)_k] is [u] where all [c_k] (for all [k]) have been replaced by
  [c_k*]

- If [γ : Γ] and [s : {γv : Γv} → (I γf γv → A γv)], then we define
  [(γ &+' s) : Γ [ A / I γf ]] as follows:

    (() &+' s) = ()
    -- If [I] does not occur in the type of [f]:
    ((γ , f) &+' s) = (γ &+' s) , f
    -- If [f : Γ_A → I γf γv']:
    ((γ , f) &+' s) = (γ &+' s) , (λ γ_A → s (f γ_A))


The recursion rule can be deduced from the elimination rule as follows:

  I-rec {A = A} c_1* ⋯ c_n* p_1* ⋯ p_m*
    = I-elim {P = λ {γv} _ → A γv} (λ γ_1P → c_1* (γ_1P -'))
                                   ⋮
                                   (λ γ_nP → c_n* (γ_nP -'))
                                   (λ δ_1P → ↓-cst-in (p_1* (δ_1P -')))
                                   ⋮
                                   (λ δ_mP → ↓-cst-in (p_m* (δ_mP -')))

where

- There is a context morphism from [(Γ & (λ {γv} _ → A {γv}))] to
  [Γ [ A / I γv ]] written [(γP -')] and defined by:

    (() -') = ()
    ((γ , a) -') = (γ -') , a
    ((γ , f , f_rec) -') = (γ -') , f_rec


Explanations of the hacks needed in Agda
========================================

The main hack used to implement HITs in Agda (known as Dan Licata’s trick)
consists in:
- defining a private inductive type [#I] containing only the points constructors
  of the HIT and defining [I] to be equal to [#I] and the points constructors to
  be equal to those of [#I]
- postulating the paths constructors
- "defining" the elimination rule by pattern matching on [#I] but with the
  correct arguments (taking the paths constructors into account)
- postulating the propositional β-reduction rules for paths

The idea is that outside this module, the inductive type [#I] is completely
hidden. In order to use the fact that [I = #I] is an inductive type, you would
need to pattern match on it, hence to know the names of the constructors, but
you can’t because they are private. But the elimination rule is defined by
pattern matching on [#I] (before [#I] is made private) hence the definitional
behaviour for the points constructors is preserved.

Here is some code showing (for the interval type) that the reduction rule for
points is definitional and that reasonable attempts to pattern match on [#I]
fail.

--------------------------------------------------------------------------------
module _ where

  private
    data #I : Type₀ where
      #zero : #I
      #one : #I

  I : Type₀
  I = #I

  zero : I
  zero = #zero

  one : I
  one = #one

  postulate
    seg : zero == one

  I-elim : ∀ {i} {P : I → Type i} (zero* : P zero) (one* : P one)
           (seg* : zero* == one* [ P ↓ seg ]) → Π I P
  I-elim zero* one* seg* #zero = zero*
  I-elim zero* one* seg* #one = one*

  postulate
    I-seg-β : ∀ {i} {P : I → Type i} (zero* : P zero) (one* : P one)
              (seg* : zero* == one* [ P ↓ seg ])
              → apd (I-elim zero* one* seg*) seg == seg*

-- Works (see [test.succeed.Test0])
test1 : ∀ {i} {P : I → Type i} (zero* : P zero) (one* : P one)
           (seg* : zero* == one* [ P ↓ seg ]) → 
       (I-elim zero* one* seg*) zero == zero*
test1 zero* one* seg* = idp

-- Fails (see [test.fail.Test0])
test2 : I → Bool
test2 zero = true
test2 one = false

-- Fails (see [test.fail.Test0'])
test3 : I → Bool
test3 #zero = true
test3 #one = false
--------------------------------------------------------------------------------

Unfortunately, there are two things that are not properly hidden, so we need two
more hacks to workaround them.

The first one is that if there are several points constructors, then you can
still prove that they are disjoint using absurd patterns:

------------------------------[test.succeed.Test1]------------------------------
module _ where

  private
    data #I : Type₀ where
      #zero : #I
      #one : #I

  I : Type₀
  I = #I

  zero : I
  zero = #zero

  one : I
  one = #one

  postulate
    seg : zero == one

-- Works
absurd : zero ≠ one
absurd ()
--------------------------------------------------------------------------------

This is worked around by the (Unit → Unit) hack. Essentially we take the
cartesian product of the inductive type #I with (Unit → Unit). The type
(Unit → Unit) being definitionally contractible, it doesn’t change anything
mathematically, but we cannot pattern match against a function type anymore, so
the absurd pattern above does not work anymore. The code is:

-------------------------------[test.fail.Test1]--------------------------------
module _ where

  private
    data #I-aux : Type₀ where
      #zero : #I-aux
      #one : #I-aux

    data #I : Type₀ where
      #i : #I-aux → (Unit → Unit) → #I

  I : Type₀
  I = #I

  zero : I
  zero = #i #zero _

  one : I
  one = #i #one _

  postulate
    seg : zero == one

-- Fails
absurd : zero ≠ one
absurd ()
--------------------------------------------------------------------------------

The second problem is that since Agda 2.3.2 there is a special treatment of
unused arguments and Agda detects that the arguments of the elimination rule
corresponding to the paths constructors are not used, hence they are not
compared at all when checking whether two applications of the elimination rule
are equal or not:

------------------------------[test.succeed.Test2]------------------------------
module _ where

  private
    data #I : Type₀ where
      #zero : #I
      #one : #I

  I : Type₀
  I = #I

  zero : I
  zero = #zero

  one : I
  one = #one

  postulate
    seg : zero == one

  I-elim : ∀ {i} {P : I → Type i} (zero* : P zero) (one* : P one)
           (seg* : zero* == one* [ P ↓ seg ]) → Π I P
  I-elim zero* one* seg* #zero = zero*
  I-elim zero* one* seg* #one = one*

postulate
  P : I → Type₀
  z : P zero
  o : P one
  s s' : z == o [ P ↓ seg ]

-- Works
absurd : I-elim z o s == I-elim z o s'
absurd = idp
--------------------------------------------------------------------------------

This is worked around by the Phantom hack: parameters of parametrized datatypes
on which you pattern match are always considered to be used (even if they’re not
actually used). Hence we defined [Phantom a] which is a (positive) Unit type
(with constructor [phantom]) parametrized by an arbitrary term, and the
elimination rule should now be defined with an additional [Phantom a] argument,
where [a] contains everything you want to mark as used:

-------------------------------[test.fail.Test2]--------------------------------
module _ where

  private
    data #I : Type₀ where
      #zero : #I
      #one : #I

  I : Type₀
  I = #I

  zero : I
  zero = #zero

  one : I
  one = #one

  postulate
    seg : zero == one

  I-elim : ∀ {i} {P : I → Type i} (zero* : P zero) (one* : P one)
           (seg* : zero* == one* [ P ↓ seg ]) → Π I P
  I-elim {i} {P} zero* one* seg* = I-elim-aux phantom  where

    I-elim-aux : Phantom seg* → Π I P
    I-elim-aux phantom #zero = zero*
    I-elim-aux phantom #one = one*

postulate
  P : I → Type₀
  z : P zero
  o : P one
  s s' : z == o [ P ↓ seg ]

-- Fails
absurd : I-elim z o s == I-elim z o s'
absurd = idp
--------------------------------------------------------------------------------


Interface chosen in HoTT-Agda
=============================

In practice, something annoying happens with propositional reduction rules for
paths, which is that when you want to use such a reduction rule, you need to
write again the arguments to the elimination rule (the [c_1*], …, [c_n*],
[p_1*], …, [p_m*]), which is quite verbose and sometimes really annoying.

Here is a solution to this problem (but with other drawbacks): instead of having
independent functions for the elimination and reduction rules, they are all
packed together in a parametrized module. For instance, if you want to define a
map [to : I → A] by recursion on I, instead of writing

  to : I → A
  to = I-rec args-of-to

  -- When you need to use some propositional β-reduction
  […] I-p-β args-of-to […]

you will now write

  module To = IRec args-of-to

  to : I → A
  to = To.f

  -- When you need to use some propositional β-reduction
  […] To.p-β […]

We’re using that interface in HoTT-Agda.

Moreover, the nondependent elimination and reduction rules are significantly
different from the dependent ones and often useful, so we want a similar
parametrized module for the nondependent rules.

Another advantage of this module system is that we don’t need to find different
names for the dependent and nondependent β-reduction rules for paths.

It actually often happens that you need the dependent elimination rule without
needing the associated reduction rules (for instance when proving that two HITs
are equivalent by defining two maps back and forth and proving that they are
inverse to each other), hence it can be useful to be able to use the dependent
eliminator directly without the overhead of parametrized modules.

For nonrecursive HITs, the flattening lemma is a fundamental property of the
HIT, so we also want it in the interface.


So we get the following interface:

For every HIT [I] as above, we want to write a file called [I.agda] exporting:
- The formation rule [I] and the introduction rules [c_1], …, [c_n], [p_1], …,
  [p_m], ([I-level])
- A module [IElim] parametrized by a dependent type over [I] (implicit) and the
  arguments of the dependent elimination rule, containing:
  - The elimination rule, called [f]
  - The β-reduction rules for the paths constructor, called [p_1-β], …, [p_m-β]
- A module [IRec] parametrized by a type (implicit) and the arguments of the
  nondependent elimination rule, containing:
  - The elimination rule, called [f]
  - The β-reduction rules for each paths constructor, called [p_1-β], …, [p_m-β]
- The dependent elimination rule, called [I-elim],
- For nonrecursive HITs, an additional module IRecType for the recursion rule
  applied to a universe, where the paths constructors are sent to equivalences,
  and containing the flattening lemma for [I] called [flattening] (for the
  circle I also defined additional rules called [coe-loop-β], [coe!-loop-β],
  [↓-loop-out], but I’m not sure how useful they are in general)

The nondependent elimination and reduction rules should be proved from the
dependent ones.


Sample I.agda file
==================

Here is what you would write in the file defining the 1pt-HIT [I]

---------------------------------[lib.types.I]----------------------------------
open import lib.Basics

module lib.types.I where

-- This section is the part where you can screw up everything. Outside you are
-- safe (but you can still screw up the interface, of course).
module _ where
  private
    data #I-aux (γf : Γf) (γv : Γv) : Type i where
      #c_1 : Γ_1 → #I-aux γf γv
      ⋮
      #c_n : Γ_n → #I-aux γf γv

    data #I (γf : Γf) (γv : Γv) : Type₀ where
      #i : #I-aux γf γv → (Unit → Unit) → #I γf γv

  I : (γf : Γf) (γv : Γv) → Type i
  I = #I

  c_1 : {γf : Γf} {γv : Γv} → Γ_1 → I
  c_1 γ_1 = #i (#c_1 γ_1) _

  ⋮

  c_n : {γf : Γf} {γv : Γv} → Γ_n → I
  c_n γ_n = #i (#c_n γ_n) _  

  postulate  -- HIT
    p_1 : {γf : Γf} {γv : Γv} → Δ_1 → u_1 == v_1
    ⋮
    p_m : {γf : Γf} {γv : Γv} → Δ_m → u_m == v_m

    -- Only when appropriate
    I-level : {γf : Γf} {γv : Γv} → has-level n (I γf γv)

  module IElim {γf : Γf} {j} {P : {γv : Γv} → I γf γv → Type j}
    (c_1* : {γv : Γv} (γ_1P : (Γ_1 & P)) → P (c_1 (γ_1P -)))
    ⋮
    (c_n* : {γv : Γv} (γ_nP : (Γ_n & P)) → P (c_n (γ_nP -)))
    (p_1* : {γv : Γv} (δ_1P : (Δ_1 & P))
            → (u_1 &* δ_1P) == (v_1 &* δ_1P) [ P ↓ p_1 (δ_1P -) ])
    ⋮
    (p_m* : {γv : Γv} (δ_mP : (Δ_m & P))
            → (u_m &* δ_mP) == (v_m &* δ_mP) [ P ↓ p_m (δ_mP -) ])

    -- Only if the [I-level] constructor is present:
    (P-level : {γv : Γv} (i : I γf γv) → has-level n (P i))
    where

    f : {γv : Γv} (i : I γf γv) → P i
    f = f-aux phantom where

     f-aux : Phantom (p_1* , … , p_m*) → {γv : Γv} (i : I γf γv) → P i
     f-aux phantom (#i (#c_1 γ_1) _) = c_1* (γ_1 &+ f)
     ⋮
     f-aux phantom (#i (#c_n γ_n) _) = c_n* (γ_n &+ f)

    postulate  -- HIT
      p_1-β : {γv : Γv} (δ_1 : Δ_1) → apd f (p_1 δ_1) == p_1* (δ_1 &+ f)
      ⋮
      p_m-β : {γv : Γv} (δ_m : Δ_m) → apd f (p_m δ_m) == p_m* (δ_m &+ f)

open IElim public using () renaming (f to I-elim)

module IRec {γf : Γf} {j} {A : (γv : Γv) → Type j}
  (c_1* : {γv : Γv} → Γ_1 [ A / I γf ] → A γv)
  ⋮
  (c_n* : {γv : Γv} → Γ_n [ A / I γf ] → A γv)
  (p_1* : {γv : Γv} → Δ_1 [ A / I γf ]
          → u_1 [ (c_k* / c_k)_k ] == v_1 [ (c_k* / c_k)_k ])
  ⋮
  (p_m* : {γv : Γv} → Δ_m [ A / I γf ]
          → u_m [ (c_k* / c_k)_k ] == v_m [ (c_k* / c_k)_k ])

  -- Only if the [I-level] constructor is present:
  (A-level : {γv : Γv} → has-level n (A γv))
  where

  private
    module M = IElim (λ γ_1P → c_1* (γ_1P -'))
                     ⋮
                     (λ γ_nP → c_n* (γ_nP -'))
                     (λ δ_1P → ↓-cst-in (p_1* (δ_1P -')))
                     ⋮
                     (λ δ_mP → ↓-cst-in (p_m* (δ_mP -')))
                     
                     -- Only if the [I-level] constructor is present:
                     (λ _ → A-level)

  f : I → A
  f = M.f

  p_1-β : {γv : Γv} (δ_1 : Δ_1) → ap f (p_1 δ_1) == p_1* (δ_1 &+' f)
  p_1-β δ_1 = apd=cst-in (M.p_1-β δ_1)

  ⋮

  p_m-β : {γv : Γv} (δ_m : Δ_m) → ap f (p_m δ_m) == p_m* (δ_m &+' f)
  p_m-β δ_m = apd=cst-in (M.p_m-β δ_m)

-- For nonrecursive HITs
--
-- If the constructor [I-level] is present and is of the form
-- [has-level (S m) (I γf γv)], then all [Type j] should be replaced by
-- [m -Type j], and the argument [(m -Type-level j)] should be added to the
-- application of [IRec].

module IRecType {γf : Γf} {j}
  (c_1* : {γv : Γv} → Γ_1 [ Type j / I γf γv' ] → Type j)
  ⋮
  (c_n* : {γv : Γv} → Γ_n [ Type j / I γf γv' ] → Type j)
  (p_1* : {γv : Γv} → Δ_1 [ Type j / I γf γv' ]
          → u_1 [ (c_k* / c_k)_k ] ≃ v_1 [ (c_k* / c_k)_k ])
  ⋮
  (p_m* : {γv : Γv} → Δ_m [ Type j / I γf γv' ]
          → u_m [ (c_k* / c_k)_k ] ≃ v_m [ (c_k* / c_k)_k ])
  where

  open IRec c_1* ⋯ c_n* (λ δ_1 → ua (p_1* δ_1)) ⋯ (λ δ_m → ua (p_m* δ_m))
             public

  flattening : (γv : Γv) → Σ (I γf γv) f ≃ [⋯]
  flattening = [⋯]
--------------------------------------------------------------------------------


Higher dimensional HITs
=======================

Here are some informations about 2-HITs (with constructors of dimension 2).

The introduction rules for 2-paths constructors are of the form:

  α : {γf : Γf} {γv : Γv} → Δ → p == q

where [p] and [q] are acceptable paths in [Δ] of type [u == v], where [u] and
[v] are acceptable points in [Δ] of type [I γf γv]. An acceptable path in [Δ] is
a term which is either
- a variable in [Δ] applied to some arguments, or
- a path constructor applied to some arguments, or
- an operation of the ∞-groupoid structure applied to acceptable things, so in
  particular we can have:
  - the identity path on an acceptable point, or
  - the opposite of an acceptable path, or
  - the concatenation of two acceptable paths.

(note that there is no (useful) operation of ∞-groupoids producing points, which
is why there are only two cases for acceptable points)

The elimination rule will be computed using the dependent ∞-groupoid structure
of fibrations: idpᵈ, !ᵈ and _∙ᵈ_

The reduction rules for the 2-paths constructors are quite annoying to write,
because the well-typedness would require the definitional reduction rules for
paths constructors and rules like [apd f (p ∙ q) = (apd f p) ∙ᵈ (apd f q)]. So
you have to write a lot of code just to have something well typed. Using them is
even more difficult.

As a useful special case, though, for 1-truncated 2-HITs (e.g. K(G,1)), the
reduction rules for the 2-paths constructors are not actually needed, so you can
just leave them out.


Mutually recursive HITs
=======================

You’re on your own.
