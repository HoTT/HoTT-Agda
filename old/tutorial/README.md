Agda for homotopy type theory
=============================

Introduction
------------

This is a basic introduction to Agda, principally aimed at people who want to use Agda for homotopy
type theory. It will not cover every feature of Agda, but only what I found to be useful for
homotopy type theory. It will suppose some knowledge of dependent type theory.

Disclaimer : I am far from a specialist in Agda, so everything here might be false.

The main goal of this text is to explain enough of Agda so that you can understand everything in
this library (everything Agda-related, I’ll not explain the content of the library). You should
not have to guess anything or have to refer to another documentation/tutorial. But it is of course
highly advised to also look at any other documentation you can find about Agda.

Don’t hesitate to tell me if you think there is anything missing (or wrong) here, my email address
is `guillaume.brunerie(at)gmail.com`.

Documentation
-------------

Documentation for Agda is rather sparse. The official wiki is available
[here](http://wiki.portal.chalmers.se/agda), you may in particular want to look at the Reference
manual (there are a lot of things missing, but there are also parts well explained), and at the
release notes of the various versions of Agda, which often contain useful informations.

Installation
------------

In order to use the HoTT-Agda library, you need at least Agda 2.3.2.

You need GHC 7.x, cabal and darcs, and you should be able to download and compile Agda with the
following commands:

    darcs get --lazy http://code.haskell.org/Agda
    cd Agda
    cabal install

Basic theory
------------

The theory behind Agda is very rich and has (as far as I know) never been studied theoretically. For
homotopy type theory, I restrict myself to a small understandable subset of Agda. The theory behind
this subset is a dependent type theory with

- an infinite (ℕ-indexed) hierarchy of universes, more precisely you can see it as a pure type
system with sorts (`Set n` | n ∈ ℕ), axioms (`Set n : Set (suc n)` | n ∈ ℕ) and relations (`(Set n,
Set m, Set (max n m))` | n, m ∈ ℕ). Note that `(Set n, Set m, Set k)` for `k > max n m` is not a
relation, and there is no subtyping rule (if `A : Set n`, then `A` is *not* of type `Set (suc
n)`). If you don’t know what a pure type system is, this means that everything is a term and has a
type (which is itself a term), that the terms that can be called “types” are the terms whose type is
`Set n` for some universe level (natural number) `n` (universes “à la Russel”), and that if `A : Set
n` and `x : A ⊢ B : Set m`, then the dependent function type `(x : A) → B` is a term of type `Set
(max n m)`.

- definitional βη-equality for (dependent) functions

- inductive types and inductive families. The default pattern matching algorithm allows more than
dependent eliminators, for example you can prove axiom K easily by pattern matching. But using the
`--without-K` flag, you can restrict dependent pattern matching to something that should not allow
you to prove K. I’m trying to use pattern matching in a minimal way, every pattern matching should
be directly translatable into a single dependent eliminator use.

- records. The main difference between records and one-constructor inductive types is that records
enjoy definitional η-equality. In particular, this gives definitional η-equality for dependent sums
and for unit. Also, records are negative types and inductive types are positive (as far as I
understand the difference between positive and negative types).

There is a lot of other features in Agda like coinductive definitions, irrelevant and erasable
arguments, first class universe polymorphic definitions (see the part about universe polymorphism),
induction-recursion, termination checking, etc. that I’m not sure if they are consistent with
homotopy type theory, so I’m trying not to use them.

Basic syntax
------------

Agda source files are UTF-8 encoded plain text files, ending with `.agda`. The only supported way to
edit Agda source files is in emacs, using the Agda mode. You can also edit Agda source files with
another text editor and compile them with the `agda` command, but you will loose interactivity.  The
Agda mode also contains an input method to enter Unicode characters easily, and this is usually
extensively used in Agda. There is a description of the Agda mode at the end of this tutorial.

There are two types of comments. Single-line comments start with `--` and ends at the end of the
line, and multi-line comments are delimited by `{-` and `-}` (these comments can be nested).

Whitespace is much more important in Agda than in most others programming languages. For example
`1+1` is recognized a a single token, something called `1+1`, but `1 + 1` is recognized as three
tokens. Similarly, if you write `(x, y)` it will be recognized as two tokens `x,` and `y` (the
parenthesis are special, but the comma is not), so if you want to write a pair, you will need to
write `(x , y)` instead (this notation is defined in `Types.agda` or in Agda’s standard
library). Moreover, the underscore character is special, it is used for mixfix operators (see the
section about fixity declaration), so if in Coq you have something called `opposite_right_inverse`,
you will rather want to call it `opposite-right-inverse` in Agda (this is recognized as a single
token). Also, a typing declaration is `a : A`, not `a:A` (which will be parsed as a single token).

Indentation matters, you have to indent properly (the convention is to use two spaces for
indentation), I’ll explain what it means in the appropriate sections.

Special comments
----------------

Special comments are comments of the form `{-# [special comment] #-}`. The special comments that I
understand (and use) are

- Options. If you have at the beginning of your file the special comment
  `{-# OPTIONS --something #-}`, Agda will be called with the command-line option `--something`.
  This is not inherited by imported modules, so homotopy type theorists should begin *every* Agda
  file with the special comment `{-# OPTIONS --without-K #-}`.

- Builtins. A builtin command is used to register some type as a builtin type that is handled
  specially by Agda. I’m using two of them : universe levels (see the part about universe
  polymorphism) and natural numbers (see the part about inductive types, this allows using `3` as a
  shorthand for `S (S (S O))`.

Structure of the source files
-----------------------------

An Agda source file *must* contain a module (the global module) named after the name of the file
(see the section about modules for more). For example a source file named `Test.agda` will start
with the following :

    {-# OPTIONS --without-K #-}
    
    module Test where
    -- Interesting stuff, that does not need to be indented

If `Test.agda` is in the directory `/toplevel/Mysublibrary/`, the global module should be called
`Mysublibrary.Test`, this will tell Agda that the toplevel of the library is `/toplevel/`, and every
module importation is understood with respect to `/toplevel/`.

Importation of other modules/files is done with `open import Myothermodule` or `open import
Mysublibrary.Myothermodule` if `Myothermodule.agda` is in the directory `Myotherlibrary`. The
command `open import Myothermodule public` means that every module importing the one containing this
line will also automatically import `myothermodule` (this is the equivalent of `Require Export
myothermodule` in Coq). Importation of other modules can be done before the line `module Test
where`.

λ-terms
-------

Here is the syntax of λ-terms.

The underscore is used as a wildcard for something that should be automatically inferred by Agda.

Parenthesis are used for grouping.

Application is written by concatenation (with whitespace between the tokens, `!p` will be recognized
as a single token and `! p` as the application of `!` to `p`).

λ-abstraction is written `λ x → u` or `λ (x : A) → u`. If there is not type annotation, the type of
`x` is inferred. As a shorthand, you can write `λ x y → u` for `λ x → (λ y → u)`. The characters `λ`
and `→` are Unicode characters written by typing `\Gl` (`G` for greek letter and `l` for λ) and
`\to` respectively (see the section about the emacs mode). You can also replace `λ` by `\` and `→`
by `->` if you don’t like Unicode.

Universes are written `Set` or `Set₀` or `Set0` for the first one and `Set₁`, `Set₂`, `Set₃`, … for
the next ones (or `Set1`, `Set2`, `Set3`, …). Subscripts are obtained by typing `\_0` for `₀`, for
example. There is also universe polymorphism, that allows you to write `Set i` where `i : Level` is
a universe level. See the section about universe polymorphism for more about this.

Dependent product is written `(x : A) → B` or `A → B` if `B` does not depend on `x`. You can also
write `∀ (x : A) → B` or `∀ x → B` (the type of `x` will only be inferred if you are using the `∀`
symbol, because `A → B` would be ambiguous (it could mean `(A : Set) → B` which is completely
different)). The `∀` symbol is obtained by typing `\forall`, and you can replace it by `forall` if
you want. I’m using it in particular for implicit universe levels, see the examples in the section
about universe polymorphism.

Function declaration, pattern matching
--------------------------------------

Function (or term) declaration use an Haskell-like syntax. The general syntax is

    function-name : (arg1 : type-of-arg1) (arg2 : type-of-arg2) (arg3 : type-of-arg3) → return-type
    function-name arg1 arg2 arg3 = return-value

The first line is the typing declaration and the second line is the function definition. If two
arguments have the same type, you can write `(arg1 arg2 : type-of-arg1-and-arg2)` in the typing
declaration. For example the polymorphic identity function can be written

    identity : (A : Set) → (A → A)
    identity A x = x

If the type or the code of the function spans several lines, the lines must be indented to tell Agda
that it’s still the same function that we’re defining.

The same syntax is used for pattern matching. For example, if the type `ℕ` is the inductive type
with constructors `O` and `S`, then the addition is defined by induction on the first argument with
the following syntax :

    add : ℕ → ℕ → ℕ
    add 0 m = m
    add (S n) m = S (add n m)

Pattern matching for inductive families is a little more subtle. For example if `Id` is the family
of identity types inductively generated by `refl a : Id A a a` for all `a : A` (we will see
implicit arguments and infix notations later), the opposite of a path is defined by

    opposite : (A : Set) (x y : A) (p : Id A x y) → Id A y x
    opposite A .a .a (refl a) = refl a

The leading dot in `.a` means that these values have been automatically deduced from the pattern
matching. With implicit arguments and the wildcard, we will be able to simply write

    opposite : {A : Set} {x y : A} (p : Id x y) → Id y x
    opposite (refl _) = refl _

For pattern matching for an empty inductive type, you have to write `()` where the (non-existent)
argument is supposed to be and to remove the `= return-value` part. For example if `empty` is the
inductive type with zero constructors, we have

    abort : (A : Set) (x : empty) → A
    abort A ()

Beware that such so-called absurd patterns are known to be unsound when combined to Dan Licata’s
trick for higher inductive types, so use them wisely.

There is also anonymous pattern matching with the following syntax

    pred : ℕ → ℕ
    pred = λ {0 → 0; S n → n}

Another form of pattern matching is the `with` syntax. Say you want to prove the following by
matching against `f x` :

    lemma : (f : A → ℕ) (x : A) → B

The first form of pattern matching will obviously not work (because it can only match against
arguments, not against arbitrary expressions), but you can write something like this :

    lemma : (f : A → ℕ) (x : A) → B
    lemma f x with (f x)
    lemma f x | 0 = […]
    lemma f x | S n = […]

The second line is there to announce that you are going to do a pattern matching against `f x`, and
then a vertical line separates the arguments of the function and the result of the pattern matching.

Implicit arguments
------------------

Implicit arguments are introduced with braces instead of parentheses in a function
declaration. Let’s consider the following function

    f : {a : A} {b : B} (c : C) {d : D} (e : E) → F
    f c e = […]

In order to use `f`, the simpler way is to write `f c e`. This tell Agda to infer the values of `a`,
`b` and `d`. If Agda does not know how to infer one of them, your code will be highlighted in yellow
in emacs (after loading the file). You can give explicitely the value of all implicit arguments with
`f {a} {b} c {d} e`, or only of some implicit arguments with `f {b = b} c e` (here the first `b` is
the name of the variable given in the definition of `f` and the second `b` is the value you want to
give). The order must be respected, for example `f {d = d} c e` will not work.

Instance arguments
------------------

Instance arguments are a different sort of implicit arguments. They are introduced with the symbols
`⦃` and `⦄` or `{{` and `}}` (the unicode symbols are obtained by typing `\{{` and `\}}`).

The difference with implicit arguments is that when they are not explicitely given, Agda try to
guess instance arguments by looking at the context. More precisely, if `f` is a function with an
instance argument of type `A`, Agda will search for variables of type `A` in the context and insert
it if there is exactly one such variable.

Local definitions
-----------------

You can define functions whose scope is only another function with the keyword `where` :

    f : (x : A) → type-of-f
    f x = u x x where
      u : (x y : A) → type-of-u
      u x y = something

The local definition needs to be indented.

Fixity declaration
------------------

To define an infix or mixfix operator, you just have to define a function whose name contains
underscores. Every underscore represents the position of an argument. For exemple you can define the
addition of natural numbers with:

    _+_ : ℕ → ℕ → ℕ
    0 + m = m
    (S n) + m = S (n + m)

`_+_` is of type `ℕ → ℕ → ℕ` and can be used either as `_+_ 1 1` or infix as in `1 + 1` (spaces are
mandatory, because `1+1` would be a single token that has nothing to do with `_+_`). This is very
flexible, you can use almost any syntax you like, not only binary infix operators. For example you
can define

    if_then_else_ : {A : Set} → bool → A → A → A
    if true then x else y = x
    if false then x else y = y

For infix binary operators, you can declare the precedence and the associativity with

    infix  precedence _binop_  -- non associative
    infixl precedence _binop_  -- left associative
    infixr precedence _binop_  -- right associative

`precedence` is a natural number and application (by juxtaposition) seems to have infinite
precedence.

Postulates
----------

You can postulate anything with the following syntax:

    postulate
      something : sometype

The line following `postulate` has to be indented.

Of course, this can make Agda inconsistent.

Abstract definitions
--------------------

A definition can be declared as abstract in this way:

    abstract
      something : sometype
      something = somevalue

(the lines following `abstract` have to be indented). This is roughly equivalent to `Qed.` in Coq,
this means that the definition will not be expanded. This can be used to help with performance
issues.

Universe polymorphism
---------------------

Universe polymorphism needs a special type named (usually) `Level` whose terms represent universe
levels. You have to postulate the type `Level` and the constructors of the first level, of the
successor of a level and of the maximum of two levels. Then you have to use BUILTINs to register it
with Agda. The following is extracted from `Types.agda` :

    postulate  -- Universe levels
      Level : Set
      zero : Level
      suc : Level → Level
      max : Level → Level → Level
    
    {-# BUILTIN LEVEL Level #-}
    {-# BUILTIN LEVELZERO zero #-}
    {-# BUILTIN LEVELSUC suc #-}
    {-# BUILTIN LEVELMAX max #-}

After that, if you have `i : Level`, you can use the universe `Set i` (which is of type `Set (suc i)`). For
example, composition of functions can then be defined as

    _◯_ : {i j k : Level} {A : Set i} {B : Set j} {C : Set k} (f : B → C) (g : A → B) → (A → C)
    f ◯ g = λ x → f (g x)

The typing declaration can be written more consisely using `∀` :

    _◯_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (f : B → C) (g : A → B) → (A → C)

The dependent product can be defined as

    Π : ∀ {i j} (A : Set i) (P : A → Set j) → Set (max i j)
    Π A P = (x : A) → P x

I’m seeing universe polymorphism only as a convenience to have definitions automatically copy-pasted
to every universe level. Agda seems to take it a little more seriously, for example you can write
something like 

    s : ℕ → Level
    s O = zero-u
    s (S n) = suc (s n)

and

    strange : (too-big : (i : Level) → Set i) (n : ℕ) → Set (s n)
    strange too-big n = too-big (s n)

This does not seem to be easily translatable to the basic theory I’m considering, because for me
`too-big` is not a first class object, but only a macro returing something of type `Set i` for every
universe level `i`. Moreover, if you ask Agda the type of `(i : Level) → Set i`, the answer will be
that `Setω` is not a valid type, so there are terms that do not have a type in Agda.

In order to be safe, I’m trying not to use universe polymorphic terms as arguments to functions or
modules.

Inductive types and inductive families
--------------------------------------

The general syntax for declaring inductive families is

    data name (param1 : type-of-param1) : (indice1 : type-of-indice1) → Set level where
      constr1 : type-of-constr1
      constr2 : type-of-constr2

The parameters are automatically declared as implicit arguments of every constructor. If the type of
an argument to a function is an inductive type (or family), you can use pattern matching to define
the function (see above). Given that you can potentially have very involved pattern matching that
will not easily be translatable to a type theory with only dependent eliminators, I’m trying to use
pattern matching only when it is just an application of the corresponding dependent eliminator.

For example, the family of identity types is defined by

    data _≡_ {i} {A : Set i} : A → A → Set i where
      refl : (a : A) → a ≡ a

And the type of natural numbers is defined by

    data ℕ : Set where
      O : ℕ
      S : ℕ → ℕ

If you define an inductive type corresponding to the natural numbers (with a zero-ary constructor
and a unary constructor), you can use the following builtins

    {-# BUILTIN NATURAL ℕ #-}
    {-# BUILTIN ZERO O #-}
    {-# BUILTIN SUC S #-}

(where `ℕ`, `O` and `S` are replaced by your constructors). This will allow the use of literal
natural numbers as a shorthand for `S (S … (S O) …)`.

Records
-------

In Coq, records are implemented with inductive types with only one constructor, together with named
(dependent) projections. In Agda, the main difference between records and one-constructor inductive
types is that records enjoy definitional η-equality. For example if you define dependent sums as a
record, then any `u : Σ A P` is definitionally equal to `(π₁ u , π₂ u)` (in Coq you can just prove
that they are propositionally equal by induction on `u`).

The syntax for records is the following

    record name (arg1 : type-of-arg1) : Set level where
      constructor name-constructor
      field
        field1 : type-of-field1
        field2 : type-of-field2

This will create a module called `name` and containing `field1` and `field2`. You can use them with
either `name.field1` or open `name` and use only `field1`.

For example, the type of dependent sums is defined with

    record Σ {i j} (A : Set i) (P : A → Set j) : Set (max i j) where
      constructor _,_
      field
        π₁ : A
        π₂ : P (π₁)
    open Σ public

The `open Σ public` line is used in order to be able to use `π₁` and `π₂` instead of `Σ.π₁` and
`Σ.π₂`, in every module importing this module.

Modules
-------

Aside from the module containing the whole file, you can define sub-modules with the syntax

    module SubModule where
      -- stuff

Note that everything defined in the sub-module must indented, but this is not the case for the
global module.

If you want to access something defined in SubModule from outside SubModule, you have to use a
qualified name `SubModule.thing` or use `open SubModule` and then `thing`.

You can have parametrized modules with (for example)

    module SubModule {param1 : type-of-param1} (param2 : type-of-param2) where
      -- stuff

This is the equivalent of `Section` in Coq, the parameters of the module will be abstracted over
everything defined in `SubModule`. You can also use parametrized modules as (Coq’s) functors:

    module NewModule = SubModule value-of-param2

This will create a new module called `NewModule` whose definitions use `value-of-param2` (and the
inferred value of the first parameter). You can also open it directly with

    open module NewModule = SubModule value-of-param2

You can also open parametrized modules with the syntax

    open SubModule value-of-param2

When opening modules, you can rename or hide some of the definitions exported in the module. The
syntax is the following (`to` is a keyword):

    open SubModule hiding (def1; def2)
    open SubModule2 renaming (def3 to newdef3; def4 to newdef4)

Private definitions
-------------------

Modules can have private definitions with the syntax

    private
      something : sometype
      something = somevalue

The value `somevalue` will be accessible only in the current module and never from the outside. This
is used in particular in Dan Licata’s trick to get higher inductive types with definitional
computation rules.

Emacs mode
----------

The emacs mode is used to edit interactively Agda source files. The input method is very easy to
use, just write as if you were typing LaTeX and the input method will automatically replace LaTeX
macros with Unicode characters, for example if you type `\alpha` this will be replaced by `α`. There
are a few shortcuts, for example greek letters are obtained with `\G` followed by another letter
(`α` is `\Ga`), `∘` is obtained with `\o`, and so on. See `M-x describe-input-method Agda` for a
complete list. In this HoTT library, I will write in a comment the Agda input method code of every
non-ASCII symbol used (after the first occurrence of the symbol).

The main keybindings of the emacs mode are the following

- `C-c C-l` (load) loads (recompiles) the whole file. You can have holes in it, represented by
  question marks.
  
For example if you load a file called `Test.agda` containing the following

    module Test where
    identity : (A : Set) → (A → A)
    identity A x = ?

the question mark will be replaced by something looking like `{ }0` meaning that it is now an
unsolved goal. In the goal, you can then use the other commands described below.

There is nothing like incremental compilation as in Coq. Either you recompile the whole file, or
you use the “refine” and “give” commands below (but this is not always possible, so you should
keep your files small enough for when you have to load them).

When you are in a goal :

- `C-c C-SPC` (give) will ask for a term (perhaps with holes) to fill the current goal. If the term is
  well typed, the goal is replaced by your term, possibly creating new goals. This is the main way
  term are written.

- `C-c C-r` (refine) will apply the introduction rule (if there is one) of the type of the goal. For
  example if the type of the goal is a dependent product, this will introduce a lambda abstraction
  (or several), if the type of the goal is a record, this will introduce the constructor of the
  record.

- `C-c C-c` (case) will ask for a variable and will do a pattern matching on this variable.

For example, suppose you have the following (not yet complete) program

    f : ℕ → A
    f n = { }0

and you do a case analysis on `n`, this will transform the source code into

    f : ℕ → A
    f O = { }0
    f (S n) = { }1

Beware that this will load the whole file, so this can be slow.

- `C-c C-a` (auto) will try to guess the term in this goal.

- `C-c C-t` (type) shows the type of the current goal.

- `C-u C-c C-t` (unnormalized type) shows the type of the current goal before normalization

- `C-c C-d` (deduce) asks for a term and return its type in the current context.

- `C-u C-c C-d` (unnormalized deduce) asks for a term and return its type in the current context
  before normalization.

- `C-c C-e` (environment) shows the current context.

Beware that “auto” and “refine” can give terms that will not be accepted by Agda. For example if you
try auto in the following :

    ! : ∀ {i} {A : Set i} {x y : A} (p : x ≡ y) → y ≡ x
    ! (refl _) = ?

(where `_≡_` is the family of identity types), this will give

    ! : ∀ {i} {A : Set i} {x y : A} (p : x ≡ y) → y ≡ x
    ! (refl _) = refl .a

which is not syntactically correct. You’ll have to try to circumvent those problems (in this case by
replacing the `.a` by an underscore, for example).
