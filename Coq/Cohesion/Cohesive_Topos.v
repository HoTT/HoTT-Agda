Add LoadPath "..".

Require Import Homotopy.

(* There is a full subcategory of objects called *discrete* *)
Parameter is_discrete : Type -> Type.
Axiom is_discrete_is_prop : forall X, is_prop (is_discrete X).

(* Every object has a reflection into a discrete object *)
Axiom pi : Type -> Type.
Axiom pi_is_discrete : forall X, is_discrete (pi X).
Axiom map_to_pi : forall X, X -> pi X.
Axiom pi_is_reflection :
  forall X Y, is_discrete Y -> is_equiv (fun f : pi X -> Y => compose f (map_to_pi X)).

(* The reflector preserves the terminal object *)
Axiom pi_preserve_terminal : is_equiv (map_to_pi unit).

(* Every object has a coreflection from a discrete object *)
Axiom flat : Type -> Type.
Axiom flat_is_discrete : forall X : Type, is_discrete (flat X).
Axiom map_from_flat : forall X, flat X -> X.
Axiom flat_is_coreflection :
  forall X Y, is_discrete Y -> is_equiv (fun f : Y -> flat X => compose (map_from_flat X) f).

(* There is a full subcategory of objects called *codiscrete* *)
Parameter is_codiscrete : Type -> Type.
Axiom is_codiscrete_is_prop : forall X, is_prop (is_codiscrete X).

(* Every object has a reflection into a codiscrete object *)
Axiom sharp : Type -> Type.
Axiom sharp_is_codiscrete : forall X, is_codiscrete (sharp X).
Axiom map_to_sharp : forall X, X -> sharp X.
Axiom sharp_is_reflection :
  forall X Y, is_codiscrete Y -> is_equiv (fun f : sharp X -> Y => compose f (map_to_sharp X)).

(* Finally the categories of discrete and codiscrete objects are equivalent via the adjonction
   [♭ ⊣ ♯] and when they are identified along this equivalence, the coreflector into discrete
   objects coincides with the reflector into codiscrete objects (both being Γ) *)
(* TODO *)