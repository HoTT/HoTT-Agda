Add LoadPath "..".

Require Import Homotopy.

Section Pushout.
  
  (* We want to construct a pushout of this diagram:

         f
     C -----> B
     |
    g|
     |
     v
     A
      
  *)
  Variable A B C : Type.
  Variable f : C -> B.
  Variable g : C -> A.
  
  (* [map_from_diagram D] is the type of maps from the diagram to [D]. Concretely an element of this
     type is a map from [A] to [D], a map from [B] to [D], and a homotopy between the composites
     with [f] and [g]. *)
  Definition map_from_diagram (D : Type) :=
    {t : A -> D & {u : B -> D & forall x : C, t (g x) ~~> u (f x)}}.

  (* If you have a map from the diagram to [D] and a map from [D] to [E], you can compose them to
     get a map from the diagram to [E] *)
  Definition compose_map_from_diag (D E : Type) (p : map_from_diagram D) (v : D -> E) :
    map_from_diagram E.
  Proof.
    destruct p as [t [u p]].
    exists (compose v t).
    exists (compose v u).
    exact (fun x : C => map v (p x)).
  Defined.

  (* A homotopy pushout is a type [D] together with a map from the diagram [p] such that for all
     [E], the previous function is an equivalence between [D -> E] and [map_from_diagram E] *)
  Definition is_homotopy_pushout (D : Type) (p : map_from_diagram D) :=
    forall (E : Type), is_equiv (compose_map_from_diag D E p).

  (* Now we define what should be the homotopy pushout is HoTT. Here is the underlying type. *)
  (*
     HigherInductive hopushout_type :=
       | inl : A -> hopushout_type
       | inr : B -> hopushout_type
       | glue : forall x : C, inl (g x) ~~> inr (f x).
  *)
  (* Type *)
  Axiom hopushout_type : Type.

  (* Constructors *)
  Axiom inl : A -> hopushout_type.
  Axiom inr : B -> hopushout_type.
  Axiom glue : forall x : C, inl (g x) ~~> inr (f x).

  (* Dependent elimination rule *)
  Axiom hopushout_rect : forall P : hopushout_type -> Type,
    forall l : (forall a : A, P (inl a)),
    forall r : (forall b : B, P (inr b)),
    forall g' : (forall x : C, transport (glue x) (l (g x)) ~~> r (f x)),
      forall x : hopushout_type, P x.

  (* Dependent computation rules *)
  Axiom compute_inl : forall P l r g', forall (a : A), hopushout_rect P l r g' (inl a) ~~> l a.
  Axiom compute_inr : forall P l r g', forall (b : B), hopushout_rect P l r g' (inr b) ~~> r b.
  Axiom compute_glue : forall P l r g', forall (c : C),
    map_dep (hopushout_rect P l r g') (glue c) ~~>
      map (transport (glue c)) (compute_inl P l r g' (g c)) @
      g' c @
      !compute_inr P l r g' (f c).

  (* Non-dependent elimination rule *)
  Lemma hopushout_rect' : forall D : Type,
    forall l : A -> D,
    forall r : B -> D,
    forall g' : (forall x : C, l (g x) ~~> r (f x)),
      hopushout_type -> D.
  Proof.
   intros D l r g'.
   apply hopushout_rect with (P := fun _ => D) (l := l) (r := r).
   intro x.
   eapply concat.
     apply trans_trivial.
   apply g'.
  Defined.

  (* Non-dependent computation rules *)
  Lemma compute_inl' : forall D l r g', forall (a : A), hopushout_rect' D l r g' (inl a) ~~> l a.
  Proof.
    intros D l r g' a.
    apply compute_inl with (P := fun _ => D).
  Defined.

  Lemma compute_inr' : forall D l r g', forall (b : B), hopushout_rect' D l r g' (inr b) ~~> r b.
  Proof.
    intros D l r g' a.
    apply compute_inr with (P := fun _ => D).
  Defined.

  Lemma compute_glue' : forall D l r g', forall (c : C),
    map (hopushout_rect' D l r g') (glue c) ~~>
      compute_inl' D l r g' (g c) @
      g' c @
      !compute_inr' D l r g' (f c).
  Proof.
    intros D l r g' c.
    eapply concat.
      apply map_dep_trivial2.
    moveright_onleft.
    eapply concat.
      apply compute_glue with (P := fun _ => D).
    unwhisker.
    path_simplify.
  Defined.

  (* And here is the map from the diagram *)
  Definition hopushout_map : map_from_diagram (hopushout_type).
  Proof.
    exists inl.
    exists inr.
    exact glue.
  Defined.

  (* This is the map going backward, that we will use to prove that [compose_map_from_diag] is
     indeed an equivalence. *)
  Definition factor_pushout (E : Type) : map_from_diagram E -> (hopushout_type -> E).
  Proof.
    intros [t [u p]].
    exact (hopushout_rect' _ t u p).
  Defined.

  Theorem homotopy_pushouts : is_homotopy_pushout hopushout_type hopushout_map.
  Proof.
    unfold is_homotopy_pushout.
    intro E.
    apply (hequiv_is_equiv _ (factor_pushout E)).
      intros [t [u p]].
      unfold factor_pushout.
      unfold compose_map_from_diag.
      unfold hopushout_map.
      admit. (* In a perfect world, this would be a definitional equality (eta + HIT). I do not want
                to try to prove it here, it would be too complicated. *)
    intro x.
    apply funext; intro t.
    unfold factor_pushout.
    unfold compose_map_from_diag.
    unfold hopushout_map.
    
    (* Perfect world : *)
      (* induction t; simpl. *) 
    (*/ Perfect world *)
    
    (* Not-so-perfect world : *)
    Definition P_induction (E : Type) (x : hopushout_type -> E) (t : hopushout_type) :=
      hopushout_rect' E (compose x inl) (compose x inr) (fun x0 : C => map x (glue x0)) t ~~> x t.
    
    Lemma induction_inl : forall E x, forall a : A, P_induction E x (inl a).
    Proof.
      intros E x a.
      unfold P_induction.
      eapply concat.
        apply compute_inl'.
      auto.
    Defined.
    
    Lemma induction_inr : forall E x, forall b : B, P_induction E x (inr b).
    Proof.
      intros E x b.
      eapply concat.
        apply compute_inr'.
      auto.
    Defined.
    
    Lemma induction_transp : forall E x,
      forall u v : hopushout_type, forall p : u ~~> v, forall q : P_induction E x u,
      transport (P := P_induction E x) p q ~~> map _ (!p) @ q @ map x p.
    Proof.
      path_induction.
      cancel_units.
    Defined.
    
    Lemma induction_glue : forall E x, forall c : C,
     transport (P := P_induction E x) (glue c) (induction_inl E x (g c)) ~~> induction_inr E x (f c).
    Proof.
      intros E x c.
      eapply concat.
        apply induction_transp.
      do_opposite_map.
      moveright_onright.
      moveright_onright.
      eapply concat.
        set (p := compute_glue' E (x ○ inl) (x ○ inr) (fun x0 : C => map x (glue x0)) c).
        eexact (map opposite p).
      unfold induction_inr, induction_inl.
      cancel_units.
      undo_opposite_concat.
      unwhisker.
    Defined.
    
    exact (hopushout_rect (P_induction E x) (induction_inl E x) (induction_inr E x)
      (induction_glue E x) t).
    (*/ Not-so-perfect world *)
  Defined.
End Pushout.
