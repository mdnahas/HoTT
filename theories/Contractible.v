(* -*- mode: coq; mode: visual-line -*- *)
(** Contractibility *)

Require Import Common Paths.

Local Open Scope path_scope.

(** Naming convention: we consistently abbreviate "contractible" as "contr".  A theorem about a space [X] being contractible (which will usually be an instance of the typeclass [Contr]) is called [contr_X]. *)

(** A space [A] is contractible if there is a point [x : A] and a (pointwise) homotopy connecting the identity on [A] to the constant map at [x].  Thus an element of [contr A] is a pair whose first component is a point [x] and the second component is a pointwise retraction of [A] to [x]. *)

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_} : simpl never.

(** Allow ourselves to implicitly generalize over types [A] and [B]. *)
Generalizable Variables A B.

(** If a space is contractible, then any two points in it are connected by a path in a canonical way. *)
Definition path_contr `{Contr A} (x y : A) 
  : x = y
:= 
  (contr x)^ @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr `{Contr A} {x y : A} (p q : x = y) 
  : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    { intros r. destruct r as [(*idpath*)]. exact (inverse (concat_Vp _)). }
  path_via (path_contr x y).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) := {
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
}.



(** Also, the total space of any based path space is contractible. *)
Lemma contr_basedpaths_proof {X : Type} (x : X) : 
  forall y : (exists y : X, x = y), (x; 1) = y.
Proof.
  intros y.
  destruct y as [(*sigT*) witness proof].
  destruct proof as [(*idpath*)].
  reflexivity.
Defined.

Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y} := {
  center := (x ; 1);
  contr := contr_basedpaths_proof x
}.

Lemma contr_basedpaths_proof' {X : Type} (x : X) : 
  forall y : (exists y : X, y = x), (x; 1) = y.
Proof.
  intros y.
  destruct y as [(*sigT*) witness proof].
  destruct proof as [(*idpath*)].
  reflexivity.
Defined.

Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x} := {
  center := (existT (fun y => y = x) x 1);
  contr := contr_basedpaths_proof' x
}.

