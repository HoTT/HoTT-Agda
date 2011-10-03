Add LoadPath "..".

Require Import Homotopy.

(* Very hacky rewrite tactic, this does not work very well but can be useful *)
Ltac rewr X :=
  lazymatch (type of X) with
     | @paths _ ?x ?y =>
         lazymatch goal with
           | |- @paths _ ?z _ =>
               lazymatch z with
                  | context ctx [x] =>
                      let new := context ctx [y] in
                        path_via new
               end
         end
  end.

(* The rest of this file is currently unused *)

(* It’s cleaner to create maps directly from paths rather than using [pr1 (path_to_equiv p)] when
   needed. There are cases where this is much easier to work with *)
Lemma path_to_map {U : Type} {V : Type} : U ~~> V -> (U -> V).
Proof.
  path_induction.
Defined.

Lemma path_to_map_concat {U V W : Type} : forall p : U ~~> V, forall q : V ~~> W, forall x : U,
   path_to_map q (path_to_map p x) ~~> path_to_map (p @ q) x.
Proof.
  path_induction.
Defined.

Ltac do_pathtomap_concat_in s :=
  match s with
    | context ctx [ path_to_map ?q (path_to_map ?p ?x) ] =>
        let mid := context ctx [ path_to_map (p @ q) x ] in path_using mid path_to_map_concat
  end.

Ltac do_pathtomap_concat :=
  repeat progress (
    match goal with
      |- ?s ~~> ?t => first [ do_pathtomap_concat_in s | do_pathtomap_concat_in t ]
    end
  ).

Ltac undo_pathtomap_concat_in s :=
  match s with
    | context ctx [ path_to_map (?p @ ?q) ?x ] =>
        let mid := context ctx [ path_to_map q (path_to_map p x) ] in path_using mid path_to_map_concat
  end.

Ltac undo_pathtomap_concat :=
  repeat progress (
    match goal with
      |- ?s ~~> ?t => first [ undo_pathtomap_concat_in s | undo_pathtomap_concat_in t ]
    end
  ).

Lemma path_to_map_map {A : Type} (P : A -> Type) (x y : A) (p : x ~~> y) :
  path_to_map (map P p) ~~> transport p.
Proof.
  path_induction.
Defined.

Lemma path_to_map_equiv_to_path {A B : Type} (f : A ≃> B) : path_to_map (equiv_to_path f) ~~> pr1 f.
Proof.
  generalize A B f.
  apply equiv_induction.
  intro t.
  simpl.
  path_via (path_to_map (idpath t)).
  admit. (* It’s easy, I’m missing something *)
Defined.
