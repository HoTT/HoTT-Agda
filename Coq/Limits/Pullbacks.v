Add LoadPath "..".

Require Import Homotopy.

(* Note, I’m using [admit] at some points that will be definitional equalities with Coq 8.4 (and I
   tested with the latest dev version that these are indeed definitional equalities) *)

Section Pullback.

  (* We want to construct a pullback of this diagram:

              B
              |
              | g
              |
              v
     A -----> C
         f
  *)
  Variable A B C : Type.
  Variable f : A -> C.
  Variable g : B -> C.

  (* [map_to_diagram D] is the type of maps from [D] to the diagram. Concretely an element of this
     type is a map from [D] to [A], a map from [D] to [B], and a homotopy between the composites with
     [f] and [g]. *)
  Definition map_to_diagram (D : Type) :=
    {t : D -> A & {u : D -> B & forall x : D, f (t x) ~~> g (u x)}}.

  (* If you have a map from [D] to the diagram and a map from [E] to [D], you can compose them to
     get a map from [E] to the diagram *)
  Definition compose_map_to_diag (D E : Type) (p : map_to_diagram D) (v : E -> D) : map_to_diagram E.
  Proof.
    destruct p as [t [u p]].
    exists (compose t v).
    exists (compose u v).    
    exact (fun x : E => p (v x)).
  Defined.

  (* A homotopy pullback is a type [D] together with a map to the diagram [p] such that for all [E],
     the previous function is an equivalence between [E -> D] and [map_to_diagram E] *)
  Definition is_homotopy_pullback (D : Type) (p : map_to_diagram D) :=
    forall (E : Type), is_equiv (compose_map_to_diag D E p).

  (* Now we define what should be the homotopy pullback in HoTT. Here is the underlying type. *)
  Definition hopullback_type := {x : A & {y : B & f x ~~> g y}}.

  (* And here is the map to the diagram *)
  Definition hopullback_map : map_to_diagram (hopullback_type).
  Proof.
    exists pr1.
    exists (fun x : hopullback_type => pr1 (pr2 x)).
    exact (fun x => pr2 (pr2 x)).
  Defined.

  (* This is the map going backward, that we will use to prove that [compose_map_to_diag] is indeed
     an equivalence. *)
  Definition factor (E : Type) : map_to_diagram E -> (E -> hopullback_type).
  Proof.
    intros [t [u p]].
    exact (fun x : E => tpair (t x) (tpair (u x) (p x))).
  Defined.

  Theorem homotopy_pullbacks : is_homotopy_pullback hopullback_type hopullback_map.
  Proof.
    unfold is_homotopy_pullback.
    intro E.
    apply (hequiv_is_equiv _ (factor E)).
      intros [t [u p]].
      compute.
      admit. (* For Coq 8.3 *)
      (* apply idpath. (* For Coq 8.4 *) *)
    intro x.
    apply funext; intro t.
    compute.
    destruct (x t).
    destruct s.
    apply idpath.
  Defined.

  (* Pullbacks are unique up to equivalence (this takes some time to compile).
     I’m only proving that the underlying types of the pullbacks are equivalent here, but of course I
     should prove that the map to the diagram is unique too. *)
  Theorem unicity_pullback (D E : Type) (pD : map_to_diagram D) (pE : map_to_diagram E)
    (hoD : is_homotopy_pullback D pD) (hoE : is_homotopy_pullback E pE) : D ≃> E.
  Proof.
    set (eqDE := tpair _ (hoE D) : _ ≃> _).
    set (eqED := tpair _ (hoD E) : _ ≃> _).
    set (eqDD := tpair _ (hoD D) : _ ≃> _).
    set (eqEE := tpair _ (hoE E) : _ ≃> _).
    set (mapDE := eqDE⁻¹ pD).
    set (mapED := eqED⁻¹ pE).
    set (mapDD := eqDD⁻¹ pD).
    set (mapEE := eqEE⁻¹ pE).
    exists mapDE.
    apply (hequiv_is_equiv _ mapED).
      apply happly.
      path_via (compose mapDE mapED).
      fold (idmap E).
      apply equiv_injective with (w := eqEE).
      path_via (compose_map_to_diag D E (eqDE mapDE) mapED).
        compute.
        destruct pE.
        destruct s.
        destruct (hoE D pD).
        destruct x1.
        destruct (hoD E (tpair x (tpair x0 p))).
        destruct x2.
        apply idpath.
      path_via (eqED mapED).
        unfold eqED.
        apply (map (fun x => compose_map_to_diag D E x mapED)).
        unfold mapDE.
        apply inverse_is_section.
      path_via pE.
        unfold mapED.
        apply inverse_is_section.
      compute.
      destruct pE.
      destruct s.
      admit. (* Coq 8.3 *)
      (* apply idpath. (* Coq 8.4 *) *)
    apply happly.
    path_via (compose mapED mapDE).
    fold (idmap D).
    apply equiv_injective with (w := eqDD).
    path_via (compose_map_to_diag _ _ (eqED mapED) mapDE).
      compute.
      destruct pD.
      destruct s.
      destruct (hoD E pE).
      destruct x1.
      destruct (hoE D (tpair x (tpair x0 p))).
      destruct x2.
      apply idpath.
    path_via (eqDE mapDE).
      unfold eqDE.
      apply (map (fun x => compose_map_to_diag E D x mapDE)).
      apply inverse_is_section.
    path_via pD.
      apply inverse_is_section.
    compute.
    destruct pD.
    destruct s.
    admit. (* Coq 8.3 *)
    (* apply idpath. (* Coq 8.4 *) *)
  Defined.
End Pullback.
