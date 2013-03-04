(* WARNING: Requires Yves Bertot's "local" extension to Coq! *)

Require Import Overture Contractible Equivalences Sigma Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.


(* 
Stolen from Dan Licata's Agda version:
https://github.com/dlicata335/hott-agda/blob/master/lib/spaces/Interval.agda
*)

Module Interval.

Local Inductive interval : Type := 
  | zero : interval
  | one : interval.

Axiom seg : paths zero one.

(*
+Definition interval_rec : forall (X : Set) (a b : X) (p : a ~~> b), interval -> X :=
+  fun X a b p i => i X a b p.
*)

Definition interval_rec {C : Type} (a b : C) (p : a = b) 
 (i : interval)
: C :=
  match i with
      | zero => a
      | one => b
  end.

Definition interval_elim {C : interval -> Type} 
  (a : C zero) (b : C one) (p : (transport C seg a) = b) 
  (x : interval) : C x :=
  match x return C x with 
      | zero => a
      | one  => b
  end.
(* Dan Licata's version is incomplete.
Axiom interval_induction_seg : forall {C : interval -> Type} 
  (a : C zero) (b : C one) (p : paths (transport B loop v) v)
  (x : interval), paths (apD (interval_induction v p) loop) p.
*)
End Interval.

Import Interval.

(* Licata's proof of function extensionality *)
Definition  ext_from_I (A B : Type) (f g : A -> B) 
  (alpha : forall x:A, f x = g x) 
: (f = g) :=
  let h := fun (i:interval) (x:A) => 
             interval_rec (f x) (g x) (alpha x) i
  in
    ap h seg.



(* Mike Shulman's definitions *)
Definition funext_dep_statement :=
  forall (X : Type) (P : X -> Type) (f g : forall x : X, P x),
    (forall x : X, f x = g x) -> f = g.


Definition interval_implies_funext_dep : funext_dep_statement.
Proof.
  intros X P f g H.
  set (mate := fun (i:interval) x => interval_rec _ _ (H x) i).
  exact (ap mate seg).
Defined.

(*
I tried to follow Mike S.'s proof, but it ended up like Dan's.
The symmetry came from "apply opposite" from the proof in
   git show 323452705:Coq/HIT/ImpredicativeInterval.v

My initial solution was:
  path_via (mate zero).
  symmetry.
  path_via (mate one).
  symmetry.
  exact (ap mate seg).
*)

(* This is the error I got when I tried Mike S.'s proof.

Definition eta {A B} (f : A -> B) :=
  fun x => f x.
Definition eta_statement :=
  forall (A B:Type) (f : A -> B), eta f = f.
Definition interval_implies_funext_dep_MikeS : eta_statement -> funext_dep_statement.
Proof.
  intros etastmt X P f g H.
  set (mate := fun (i:interval) x => interval_rec _ _ (H x) i).
  path_via (mate zero).
  path_via (eta f).

Toplevel input, characters 29-30:
Error:
In environment
etastmt : eta_statement
X : Type
P : X -> Type
f : forall x : X, P x
g : forall x : X, P x
H : forall x : X, f x = g x
mate := fun (i : interval) (x : X) => interval_rec (f x) (g x) (H x) i
     : interval -> forall x : X, P x
The term "f" has type "forall x : X, P x" while it is expected to have type
 "?68 -> ?69".
*)
 




