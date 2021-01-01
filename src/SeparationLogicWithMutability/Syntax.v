Require Import Coq.Strings.String.

Require Export SPAM.SeparationLogic.Syntax.

Inductive massert : Type :=
  | mut_s (A : sassert)
  | immut_s (A : sassert)
  | indif_s (A : sassert)
  | and_m (a : massert) (b : massert)
  | or_m (a : massert) (b : massert)
  | not_m (a : massert)
  | implies_m (a : massert) (b : massert)
  | sand_m (a : massert) (b : massert)
  | simplies_m (a : massert) (b : massert)
  | forall_m (x : lvar) (a : massert)
  | exists_m (x: lvar) (a : massert).

Notation "[ A ]mut" := (mut_s A) (at level 50).
Notation "[ A ]immut" := (immut_s A) (at level 50).
Notation "[ A ]indif" := (indif_s A) (at level 50).
Notation "A m/\ B" := (and_m A B) (at level 70).
Notation "A m\/ B" := (or_m A B) (at level 80).
Notation "m~ A" := (not_m A) (at level 65).
Notation "A m-> B" := (implies_m A B) (at level 85).
Notation "A m* B" := (sand_m A B) (at level 75).
Notation "A m-* B" := (simplies_m A B) (at level 90).
Notation "'mforall' X , B" := (forall_m X B) (at level 50).
Notation "'mexists' X , B" := (exists_m X B) (at level 50).
