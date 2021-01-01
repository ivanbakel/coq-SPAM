Require        Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.
Require        Coq.Structures.Equalities.

Require Import SPAM.SeparationLogic.Syntax.

Module DecidableLvar.
Import Coq.Structures.Equalities.
Include (UsualDecidableTypeBoth with Definition t := Syntax.lvar).
End DecidableLvar.

Module DecidablePvar.
Import Coq.Structures.Equalities.
Include (UsualDecidableTypeBoth with Definition t := Syntax.pvar).
End DecidablePvar.

Module DecidableConcrete.
Import Coq.Structures.Equalities.
Include (UsualDecidableTypeBoth with Definition t := Syntax.concrete).
End DecidableConcrete.

Module LogicalMap := FMapWeakList.Make DecidableLvar.

Definition logicalEnv : Type := LogicalMap.t concrete.

Module ProgramMap := FMapWeakList.Make DecidablePvar.

Definition variableStore : Type := ProgramMap.t concrete.

Module HeapMap := FMapWeakList.Make DecidableConcrete.
Module HeapMapF := WFacts HeapMap.
Module HeapMapP := WProperties HeapMap.

Definition heap : Type := HeapMap.t concrete.

Inductive InterpsTo (e : logicalEnv) (s : variableStore) :  basevalue -> concrete -> Prop :=
  | iConcrete (c : concrete)
  : InterpsTo e s (vlit c) c
  | iProgram (p : pvar) (c : concrete)
  : ProgramMap.MapsTo p c s
    -> InterpsTo e s (vpvar p) c
  | iLogical (l : lvar) (c : concrete)
  : LogicalMap.MapsTo l c e
    -> InterpsTo e s (vlvar l) c.

Notation "[[ v ]]_{ e , s } = c" := (Arithmetic.interpret (eval:=InterpsTo e s) v c) (at level 70).

Definition InterpsList (e : logicalEnv) (s : variableStore) : list (value_ * concrete) -> Prop
  := Forall (fun '(v, c) => [[ v ]]_{ e, s } = c).

Definition addConsecutive (c : concrete) (vals : list concrete) (h : heap)
  := fold_left (fun h' '(idx, v) => HeapMap.add (c + idx) v h') (combine (List.seq 0 (length vals)) vals) h.

Fixpoint Satisfies (e : logicalEnv) (s : variableStore) (h : heap) (A : sassert) : Prop :=
  match A with
  | empty => HeapMap.Empty h
  | singleton x y =>
      exists (c c' : concrete),
        [[ x ]]_{e,s} = c
        /\ [[ y ]]_{e,s} = c'
        /\ h = HeapMap.add c c' (HeapMap.empty concrete)
  | top => True
  | x s= y =>
      forall (c c' : concrete),
        [[ x ]]_{e,s} = c
        /\ [[ y ]]_{e,s} = c'
        -> c = c'
  | A s/\ B => Satisfies e s h A /\ Satisfies e s h B
  | A s\/ B => Satisfies e s h A \/ Satisfies e s h B
  | s~ A => ~ Satisfies e s h A
  | A s-> B => Satisfies e s h A -> Satisfies e s h B
  | A s* B =>
      exists (h' h'' : heap),
        HeapMapP.Partition h h' h''
        /\ Satisfies e s h' A
        /\ Satisfies e s h'' B
  | A s-* B =>
      forall (h' : heap),
        HeapMapP.Disjoint h h'
          -> Satisfies e s h A
          -> Satisfies e s (HeapMapP.update h h') B
  | sforall x, A =>
      forall (c : concrete),
        Satisfies (LogicalMap.add x c e) s h A
  | sexists x, A =>
      exists (c : concrete),
        Satisfies (LogicalMap.add x c e) s h A
  end.

Notation "env |= A" := (let '(e, s, h) := env in Satisfies e s h A) (at level 99).

Definition Tautology (A : sassert) : Prop
  := forall e s h, (e, s, h) |= A.

Notation "_|= A" := (Tautology A) (at level 99).

Example top_taut : _|= top.
Proof.
  unfold Tautology.
  intros e s h.
  unfold Satisfies.
  easy.
  Qed.

Definition Empty (A : sassert) : Prop
  := forall e s h, (e, s, h) |= A -> HeapMap.Empty h.

Example empty_Empty : Empty empty.
Proof.
  unfold Empty.
  intros e s h.
  unfold Satisfies.
  easy.
  Qed.

Theorem equiv_definition_of_Empty (A : sassert)
  : Empty A <-> _|= A s-> empty.
Proof.
  split.
  { intros empty_A.
    unfold Tautology.
    intros e s h.
    simpl.
    apply empty_A.
  }
  { intros A_impl_empty.
    unfold Empty.
    unfold Tautology in A_impl_empty.
    simpl in A_impl_empty.
    apply A_impl_empty.
  }
  Qed.

Theorem empty_duplicable (A : sassert)
  : Empty A -> forall e s h, forall (B : sassert),
        (e, s, h) |= B s* A -> (e, s, h) |= B s* A s* A.
Proof.
  intros empty_A e s h B sat_B_sand_A.
  simpl.
  exists h.
  exists(HeapMap.empty concrete).
  split.
  { unfold HeapMapP.Partition.
    split.
    { admit. (* h is disjoint from the empty map *)
    }
    { intros k c.
      admit. (* no key appears in the empty map *)
    }
  }
  { split.
    { simpl in sat_B_sand_A.
      assumption.
    }
    { simpl in sat_B_sand_A.
      destruct sat_B_sand_A as [ h' [ h'' [ _ [ _ sat_A ] ] ] ].
      apply empty_A in sat_A as empty_h''.
      assert (forall h, HeapMap.Empty h -> h = HeapMap.empty concrete) as empty_impl_eq.
      { admit. (* The above *) }
      apply empty_impl_eq in empty_h''.
      rewrite <- empty_h''.
      exact sat_A.
    }
  }
  Admitted.
