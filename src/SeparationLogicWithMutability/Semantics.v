Require        Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.
Require        Coq.Structures.Equalities.

Require Import SPAM.SeparationLogicWithMutability.Syntax.
Require Import SPAM.SeparationLogic.Semantics.

Inductive mutability : Type :=
  | mutable
  | immutable.

Module DecidableMutability.
Import Coq.Structures.Equalities.
Include (UsualDecidableTypeBoth with Definition t := mutability).
End DecidableMutability.

Definition mutheap : Type := HeapMap.t (concrete * mutability).

Definition valHeap (mh : mutheap) : heap :=
  HeapMap.fold (fun k '(v, _) h => HeapMap.add k v h) mh (HeapMap.empty concrete).

(* TODO: theorems about the well-behavedness of the above def *)

Definition Mutable (mh : mutheap) : Prop :=
  forall iota v m, HeapMap.MapsTo iota (v, m) mh -> m = mutable.

Definition Immutable (mh : mutheap) : Prop :=
  forall iota v m, HeapMap.MapsTo iota (v, m) mh -> m = immutable.

Lemma partition_mutable_immutable (h : mutheap) :
  exists h' h'',
    HeapMapP.Partition h h' h''
    /\ Mutable h'
    /\ Immutable h''.
Proof.
  destruct (HeapMapP.partition (fun _ '(_, m) =>
    match m with
    | mutable => true
    | immutable => false
    end) h) as [ h' h'' ] eqn:e.
  exists h'.
  exists h''.
  split.
  { apply HeapMapP.partition_Partition in e as partition.
    assumption.
    admit. (* partition respects eq *)
  }
  split.
  { unfold Mutable.
    admit. (* All keys in the mutable filter are mutable *)
  }
  { unfold Immutable.
    admit. (* And the same for the immutable filter *)
  }
  Admitted.

Fixpoint MSatisfies (e : logicalEnv) (s : variableStore) (h : mutheap) (A : massert) : Prop :=
  match A with
  | mut_s A => Satisfies e s (valHeap h) A /\ Mutable h
  | immut_s A => Satisfies e s (valHeap h) A /\ Immutable h
  | indif_s A => Satisfies e s (valHeap h) A
  | A m/\ B => MSatisfies e s h A /\ MSatisfies e s h B
  | A m\/ B => MSatisfies e s h A \/ MSatisfies e s h B
  | m~ A => ~ MSatisfies e s h A
  | A m-> B => MSatisfies e s h A -> MSatisfies e s h B
  | A m* B =>
      exists (h' h'' : mutheap),
        HeapMapP.Partition h h' h''
        /\ MSatisfies e s h' A
        /\ MSatisfies e s h'' B
  | A m-* B =>
      forall (h' : mutheap),
        HeapMapP.Disjoint h h'
          -> MSatisfies e s h A
          -> MSatisfies e s (HeapMapP.update h h') B
  | mforall x, A =>
      forall (c : concrete),
        MSatisfies (LogicalMap.add x c e) s h A
  | mexists x, A =>
      exists (c : concrete),
        MSatisfies (LogicalMap.add x c e) s h A
  end.

Notation "( e , s , h ) m|= A" := (MSatisfies e s h A) (at level 94).

Example empty_both_mut_immut (e : logicalEnv) (s : variableStore) : (e, s, HeapMap.empty (concrete * mutability)) m|= [ top ]mut m/\ [ top ]immut.
Proof.
  simpl.
  split.
  { split.
    { easy.  }
    { unfold Mutable.
      admit. (* Trivial key property over the empty heap *)
    }
  }
  { split.
    { easy.  }
    { unfold Mutable.
      admit. (* Trivial key property over the empty heap *)
    }
  }
  Admitted.

Definition MTautology (A : massert) : Prop
  := forall e s h, (e, s, h) m|= A.

Notation "_m|= A" := (MTautology A) (at level 94).

Example mut_immut_taut: MTautology ([ top ]mut m* [ top ]immut).
Proof.
  unfold MTautology.
  intros e s h.
  simpl.
  destruct (partition_mutable_immutable h) as [ h' [ h'' [ partition [ h'mut h''immut ]]]].
  exists h'.
  exists h''.
  auto.
  Qed.

Example mut_land_equiv_mland_mut (e : logicalEnv) (s : variableStore) (h : mutheap)
  : forall A B : sassert,
      (e, s, h) m|= [ A s/\ B ]mut
      <-> (e, s, h) m|= [ A ]mut m/\ [ B ]mut.
Proof.
  intros A B.
  split.
  { simpl.
    intros [ [ satA satB ] mut_h ].
    auto.
  }
  { simpl.
    intros [ [ satA mut_h ] [ satB _ ] ].
    auto.
  }
Qed.

Example mut_lor_equiv_mlor_mut (e : logicalEnv) (s : variableStore) (h : mutheap)
  : forall A B : sassert,
      (e, s, h) m|= [ A s\/ B ]mut
      <-> (e, s, h) m|= [ A ]mut m\/ [ B ]mut.
Proof.
  intros A B.
  split.
  { simpl.
    intros [ [ satA | satB ] mut_h ]; auto.
  }
  { simpl.
    intros [ [ satA mut_h ] | [ satB mut_h ] ]; auto.
  }
Qed.

(* By comparison, much trickier! *)
Example mut_sand_equiv_mand_mut (e : logicalEnv) (s : variableStore) (h : mutheap)
  : forall A B : sassert,
      (e, s, h) m|= [ A s* B ]mut
      <-> (e, s, h) m|= [ A ]mut m* [ B ]mut.
Proof.
  intros A B.
  split.
  { simpl.
    intros [ [ h' [ h'' [ partition [ satA satB ]]]] mutable ].
    admit. (* Hard! *)
  }
  { simpl.
    intros [ h' [ h'' [ partition [ [ satA mut_h' ] [ satB mut_h'' ]]]]].
    split.
    { exists (valHeap h').
      exists (valHeap h'').
      split.
      { admit. (* Partition -> valHeap Partition *) }
      { auto.  }
    }
    { admit. (* Mutable Partition -> mutable heap *)
    }
  }
  Admitted.
