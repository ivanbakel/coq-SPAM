Inductive arithmetic { X : Type } : Type :=
  | aembed : X -> arithmetic
  | aplus : arithmetic -> arithmetic -> arithmetic
  | aminus : arithmetic -> arithmetic -> arithmetic
  | atimes : arithmetic -> arithmetic -> arithmetic.

Inductive interpret { X : Type } { eval : X -> nat -> Prop } : arithmetic (X:=X) -> nat -> Prop :=
  | interpEmbed (x : X) (n : nat)
  : eval x n
    -> interpret (aembed x) n
  | interpPlus (x y : arithmetic) (n1 n2 : nat)
  : interpret x n1
    -> interpret y n2
    -> interpret (aplus x y) (n1 + n2)
  | interpMinus (x y : arithmetic) (n1 n2 : nat)
  : interpret x n1
    -> interpret y n2
    -> interpret (aminus x y) (n1 - n2)
  | interpTimes (x y : arithmetic) (n1 n2 : nat)
  : interpret x n1
    -> interpret y n2
    -> interpret (atimes x y) (n1 * n2).

Notation "x a+ y" := (aplus x y) (at level 50).
Notation "x a- y" := (aminus x y) (at level 50).
Notation "x a* y" := (atimes x y) (at level 49).
