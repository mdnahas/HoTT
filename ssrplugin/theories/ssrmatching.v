(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Declare ML Module "ssreflect".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SsrMatchingSyntax.

(* Reserve the notation for rewrite patterns so that the user is not allowed  *)
(* to declare it at a different level.                                        *)
Reserved Notation "( a 'in' b )"        (at level 0).
Reserved Notation "( a 'as' b )"        (at level 0).
Reserved Notation "( a 'in' b 'in' c )" (at level 0).
Reserved Notation "( a 'as' b 'in' c )" (at level 0).

(* Notation to define shortcuts for the "X in t" part of a pattern.           *)
Notation "( X 'in' t )" := (_ : fun X => t) : ssrpatternscope.
Delimit Scope ssrpatternscope with pattern.

(* Some shortcuts for recurrent "X in t" parts.                               *)
Notation RHS := (X in identity _ X)%pattern.
Notation LHS := (X in identity X _)%pattern.

End SsrMatchingSyntax.

Export SsrMatchingSyntax.
