Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import SPAM.Arithmetic.

Definition concrete := nat.

Definition lvar := string.

Definition pvar := string.

Inductive basevalue : Type :=
  | vlit (n : concrete)
  | vlvar (v : lvar)
  | vpvar (v : pvar).

Definition value_ : Type := arithmetic (X:=basevalue).

Inductive sassert : Type :=
  | top
  | eq_s (x : value_) (y : value_)
  | and_ (a : sassert) (b : sassert)
  | or_ (a : sassert) (b : sassert)
  | not_ (a : sassert)
  | implies_ (a : sassert) (b : sassert)
  | empty
  | singleton (x : value_) (v : value_)
  | sand (a : sassert) (b : sassert)
  | simplies (a : sassert) (b : sassert)
  | forall_ (x : lvar) (a : sassert)
  | exists_ (x: lvar) (a : sassert).

Definition multiton (x : value_) (vs : list value_) : sassert
  := List.fold_left (fun ass '(idx, v) => sand ass (singleton (x a+ aembed (vlit idx)) v))
      (List.combine (List.seq 0 (List.length vs)) vs) empty.

Notation "x s= y" := (eq_s x y) (at level 70).
Notation "x |-> y , .. , z" := (multiton x (y :: .. (z :: nil) ..)) (at level 60).
Notation "A s/\ B" := (and_ A B) (at level 79).
Notation "A s\/ B" := (or_ A B) (at level 84).
Notation "s~ A" := (not_ A) (at level 74).
Notation "A s-> B" := (implies_ A B) (at level 90).
Notation "A s* B" := (sand A B) (at level 79).
Notation "A s-* B" := (simplies A B) (at level 90).
Notation "'sforall' X , B" := (forall_ X B) (at level 50).
Notation "'sexists' X , B" := (exists_ X B) (at level 50).

