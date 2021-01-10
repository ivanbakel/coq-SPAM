Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetWeakList.

Require Import SPAM.Arithmetic.
Require Import SPAM.SeparationLogic.Syntax.
Require Import SPAM.SeparationLogic.Semantics.

Module ProgramSet := MSetWeakList.Make DecidablePvar.

Definition pvarSet := ProgramSet.t.

Inductive baseexpr : Type :=
  | elit (c : concrete)
  | evar (p : pvar).

Definition expr : Type := arithmetic (X:=baseexpr).

Fixpoint exprToValue (e : expr) : value_ :=
  match e with
  | aembed (elit c) => aembed (vlit c)
  | aembed (evar p) => aembed (vpvar p)
  | x a+ y => (exprToValue x) a+ (exprToValue y)
  | x a- y => (exprToValue x) a- (exprToValue y)
  | x a* y => (exprToValue x) a* (exprToValue y)
  end.

Inductive statement : Type :=
  | cons (v : pvar) (inits : list expr)
  | lookup (x : pvar) (e : expr)
  | mutate (e : expr) (v : expr)
  | dispose (e : expr).

Inductive program : Type :=
  | final (s : statement)
  | seq (s : statement) (p : program).

Inductive EvalsTo (s : variableStore) :  baseexpr -> concrete -> Prop :=
  | eConcrete (c : concrete)
  : EvalsTo s (elit c) c
  | eProgram (p : pvar) (c : concrete)
  : ProgramMap.MapsTo p c s
    -> EvalsTo s (evar p) c.

Notation "[[ v ]]_{ s } = c" := (Arithmetic.interpret (eval:=EvalsTo s) v c) (at level 70).

Lemma evals_implies_interps :
  forall (s : variableStore) (ex : expr) (c : concrete),
    [[ ex ]]_{ s } = c
    -> forall (e : logicalEnv), [[ exprToValue ex ]]_{ e, s } = c.
Proof.
  intros s ex c ex_evals_to_c.
  intros e.
  generalize dependent c.
  induction ex.
  { destruct x.
    { intros c0.
      intro elit_eval_c.
      enough (c0=c) as cs_eq.
      { rewrite cs_eq.
        simpl.
        apply interpEmbed.
        apply iConcrete.
      }

      inversion elit_eval_c.
      inversion H0.
      easy.
    }
    { intros c evar_eval_c.
      unfold exprToValue.
      apply interpEmbed.
      apply iProgram.

      inversion evar_eval_c.
      inversion H0.
      assumption.
    }
  }
  { intros c aplus_eval_c.
    unfold exprToValue.
    fold exprToValue.
    inversion aplus_eval_c.
    apply interpPlus.
    apply IHex1.
    assumption.
    apply IHex2.
    assumption.
  }
  { intros c aminus_eval_c.
    unfold exprToValue.
    fold exprToValue.
    inversion aminus_eval_c.
    apply interpMinus.
    apply IHex1.
    assumption.
    apply IHex2.
    assumption.
  }
  { intros c atimes_eval_c.
    unfold exprToValue.
    fold exprToValue.
    inversion atimes_eval_c.
    apply interpTimes.
    apply IHex1.
    assumption.
    apply IHex2.
    assumption.
  }
Qed.

Definition AllFree (c : concrete) (length : nat) (h : heap) : Prop
  := forall c' : concrete,
      c <= c' < c + length
      -> ~ HeapMap.In c' h.

Definition EvalList (s : variableStore) : list (expr * concrete) -> Prop
  := Forall (fun '(e, c) => [[ e ]]_{ s } = c).

Reserved Notation "< stat , ( s , h ) > ~> ( s' , h' )" (at level 90).

Inductive RunsTo (sv : variableStore) (h : heap) : statement -> variableStore -> heap -> Prop :=
  | consRunsTo (v : pvar) (inits : list expr) (c : concrete) (vals : list concrete)
  : length inits = length vals
    -> EvalList sv (combine inits vals)
    -> AllFree c (length inits) h
    -> <cons v inits, (sv, h)> ~> (ProgramMap.add v c sv, addConsecutive c vals h)
  | lookupRunsTo (x : pvar) (e : expr) (c c' : concrete)
  : [[ e ]]_{ sv } = c
    -> HeapMap.MapsTo c c' h
    -> <lookup x e, (sv, h)> ~> (ProgramMap.add x c' sv, h)
  | mutateRunsTo (e v : expr) (c c' : concrete)
  : [[ e ]]_{ sv } = c
    -> [[ v ]]_{ sv } = c'
    -> <mutate e v, (sv, h)> ~> (sv, HeapMap.add c c' h)
  | disposeRunsTo (e : expr) (c : concrete)
  : [[ e ]]_{ sv } = c
    -> <dispose e, (sv, h)> ~> (sv, HeapMap.remove c h)
  where "< stat , ( s , h ) > ~> ( s' , h' )" := (RunsTo s h stat s' h').

Definition statementModifies (stat : statement) : pvarSet :=
  match stat with
  | cons v _ => ProgramSet.singleton v
  | lookup x _ => ProgramSet.singleton x
  | mutate _ _ => ProgramSet.empty
  | dispose _ => ProgramSet.empty
  end.

Lemma not_in_statementModifies_implies_unmodified (s s' : variableStore) (stat : statement)
  : forall (h h' : heap),
      <stat, (s, h)> ~> (s', h')
      -> forall (v : pvar) (c : concrete),
          ~ ProgramSet.In v (statementModifies stat)
          -> (ProgramMap.MapsTo v c s
              <-> ProgramMap.MapsTo v c s').
Proof.
  intros h h' stat_runs.
  destruct stat as [ v _inits | x _e | _e _v | _e ]; inversion stat_runs.
  { intros v1 c1 v1_not_in_v.
    split.
    { intro v1_mapsto_c1.
      apply ProgramMapF.add_neq_mapsto_iff.
      simpl in v1_not_in_v.
      contradict v1_not_in_v.
      now apply ProgramSet.singleton_spec.
      assumption.
    }
    { intros v1_mapsto_c1.
      apply ProgramMapF.add_neq_mapsto_iff in v1_mapsto_c1.
      assumption.
      simpl in v1_not_in_v.
      contradict v1_not_in_v.
      now apply ProgramSet.singleton_spec.
    }
  }
  { intros v1 c1 v1_not_in_x.
    split.
    { intro v1_mapsto_c1.
      apply ProgramMapF.add_neq_mapsto_iff.
      simpl in v1_not_in_x.
      contradict v1_not_in_x.
      now apply ProgramSet.singleton_spec.
      assumption.
    }
    { intros v1_mapsto_c1.
      apply ProgramMapF.add_neq_mapsto_iff in v1_mapsto_c1.
      assumption.
      simpl in v1_not_in_x.
      contradict v1_not_in_x.
      now apply ProgramSet.singleton_spec.
    }
  }
  { easy. }
  { easy. }
  Qed.

Fixpoint modifies (prog : program) : pvarSet :=
  match prog with
  | final stat => statementModifies stat
  | seq stat rest => ProgramSet.union (statementModifies stat) (modifies rest)
  end.

Fixpoint pvarsOfValue (v : value_) : pvarSet :=
  match v with
  | aembed (vpvar v) => ProgramSet.singleton v
  | aembed _         => ProgramSet.empty
  | x a+ y => ProgramSet.union (pvarsOfValue x) (pvarsOfValue y)
  | x a- y => ProgramSet.union (pvarsOfValue x) (pvarsOfValue y)
  | x a* y => ProgramSet.union (pvarsOfValue x) (pvarsOfValue y)
  end.

Fixpoint pvarsOfAssert (A : sassert) : pvarSet :=
  match A with
  | top => ProgramSet.empty
  | x s= y => ProgramSet.union (pvarsOfValue x) (pvarsOfValue y)
  | x s/\ y => ProgramSet.union (pvarsOfAssert x) (pvarsOfAssert y)
  | x s\/ y => ProgramSet.union (pvarsOfAssert x) (pvarsOfAssert y)
  | s~ x  => pvarsOfAssert x
  | x s-> y => ProgramSet.union (pvarsOfAssert x) (pvarsOfAssert y)
  | empty => ProgramSet.empty
  | singleton x y => ProgramSet.union (pvarsOfValue x) (pvarsOfValue y)
  | x s* y => ProgramSet.union (pvarsOfAssert x) (pvarsOfAssert y)
  | x s-* y => ProgramSet.union (pvarsOfAssert x) (pvarsOfAssert y)
  | forall_ _ B => pvarsOfAssert B
  | exists_ _ B => pvarsOfAssert B
  end.

Reserved Notation "{ A }- s -{ B }" (at level 99).

Inductive Triple : sassert -> statement -> sassert -> Prop :=
  | localAllocate (v : pvar) (exprs : list expr)
  : { empty }- cons v exprs -{ multiton (aembed (vpvar v)) (List.map exprToValue exprs) }
  | localLookup (x : pvar) (e : expr) (v : expr)
  : { exprToValue e |-> exprToValue v }- lookup x e -{ (exprToValue e |-> exprToValue v) s/\ exprToValue e s= exprToValue v }
  | localMutate (e v v' : expr)
  : { exprToValue e |-> exprToValue v' }- mutate e v -{ exprToValue e |-> exprToValue v }
  | localDispose (e v : expr)
  : { exprToValue e |-> exprToValue v }- dispose e -{ empty }
  (* Consequence and frame are defined for statements because it's easier to
  * argue that they then allow for all specifications *)
  | consequence (A A' B B' : sassert) (stat : statement)
  : _|= A' s-> A
    -> _|= B s-> B'
    -> { A }- stat -{ B }
    -> { A' }- stat -{ B' }
  | frame (A B C : sassert) (stat : statement)
  : ProgramSet.Empty (ProgramSet.inter (statementModifies stat) (pvarsOfAssert C))
    -> { A }- stat -{ B }
    -> { A s* C }- stat -{ B s* C }
  where "{ A }- s -{ B }" := (Triple A s B).

Reserved Notation "< stat , ( s , h ) > ~>* ( s' , h' )" (at level 90).

Inductive ProgramRunsTo (sv : variableStore) (h : heap) : program -> variableStore -> heap -> Prop :=
  | finalRunsTo (stat : statement) (sv' : variableStore) (h' : heap)
  : <stat, (sv, h)> ~> (sv', h')
    -> <final stat, (sv, h)> ~>* (sv', h')
  | seqRunsTo (stat : statement) (prog : program) (sv' sv'' : variableStore) (h' h'' : heap)
  : <stat, (sv, h)> ~> (sv', h')
    -> <prog, (sv', h')> ~>* (sv'', h'')
    -> <seq stat prog, (sv, h)> ~>* (sv'', h'')
  where "< stat , ( s , h ) > ~>* ( s' , h' )" := (ProgramRunsTo s h stat s' h').

Corollary not_in_modifies_implies_unmodified (s s' : variableStore) (prog : program)
  : forall (h h' : heap),
      <prog, (s, h)> ~>* (s', h')
      -> forall (v : pvar) (c : concrete),
          ~ ProgramSet.In v (modifies prog)
          -> (ProgramMap.MapsTo v c s
                <-> ProgramMap.MapsTo v c s').
Proof.
  intros h h' prog_runs.
  elim prog_runs.
  { intros s1 h1 stat s1' h1' stat_runs.
    now apply not_in_statementModifies_implies_unmodified with (h:=h1) (h':=h1').
  }
  { intros s1 h1 stat prog' s1' s1'' h1' h1'' stat_runs prog'_runs IH.

    intros v c v_not_in_modifies.
    simpl in v_not_in_modifies.
    rewrite <- IH.
    apply not_in_statementModifies_implies_unmodified with (h:=h1) (h':=h1') (stat:=stat); try assumption.
    contradict v_not_in_modifies.
    apply ProgramSet.union_spec; left; assumption.
    contradict v_not_in_modifies.
    now apply ProgramSet.union_spec; right; assumption.
  }
  Qed.

Reserved Notation "{ A }* p *{ B }" (at level 99).

Inductive ProgramTriple : sassert -> program -> sassert -> Prop :=
  | finalTriple (A B : sassert) (stat : statement)
  : { A }- stat -{ B }
    -> { A }* final stat *{ B }
  | seqTriple (A B C : sassert) (stat : statement) (prog : program)
  : { A }- stat -{ B }
    -> { B }* prog *{ C }
    -> { A }* seq stat prog *{ C }
  where "{ A }* p *{ B }" := (ProgramTriple A p B).

Lemma relevant_pvars_decide_interps_to (e : logicalEnv) (expr : value_) (c' : concrete)
  : forall (s s' : variableStore),
      (forall (v : pvar) (c : concrete),
        ProgramSet.In v (pvarsOfValue expr)
        -> (ProgramMap.MapsTo v c s
            <-> ProgramMap.MapsTo v c s'))
      -> ([[ expr ]]_{ e, s } = c'
          <-> [[ expr ]]_{ e, s' } = c').
Proof.
  intros s s'.
  generalize c'.
  elim expr.
  { intros x c'1 pvars_agree.
    split.
    { intro x_interp_to_c'.
      destruct x; inversion x_interp_to_c'; apply interpEmbed; inversion H0.
      { apply iConcrete.  }
      { now apply iLogical. }
      { apply iProgram.
        apply pvars_agree; try assumption.
        now apply ProgramSet.singleton_spec.
      }
    }
    { intro x_interp_to_c'.
      destruct x; inversion x_interp_to_c'; apply interpEmbed; inversion H0.
      { apply iConcrete.  }
      { now apply iLogical. }
      { apply iProgram.
        apply pvars_agree; try assumption.
        now apply ProgramSet.singleton_spec.
      }
    }
  }
  { intros a a_pvars_agree b b_pvars_agree c'0 pvars_agree.
    split.
    { intro a_plus_b_interp_c'.
      inversion a_plus_b_interp_c'.
      apply interpPlus.
      apply a_pvars_agree; try assumption.
      intros v c v_in_a.
      apply pvars_agree.
      unfold pvarsOfValue.
      fold pvarsOfValue.
      apply ProgramSet.union_spec.
      now left.
      apply b_pvars_agree; try assumption.
      intros v c v_in_b.
      apply pvars_agree.
      unfold pvarsOfValue.
      fold pvarsOfValue.
      apply ProgramSet.union_spec.
      now right.
    }
    { intro a_plus_b_interp_c'.
      inversion a_plus_b_interp_c'.
      apply interpPlus.
      apply a_pvars_agree; try assumption.
      intros v c v_in_a.
      apply pvars_agree.
      unfold pvarsOfValue.
      fold pvarsOfValue.
      apply ProgramSet.union_spec.
      now left.
      apply b_pvars_agree; try assumption.
      intros v c v_in_b.
      apply pvars_agree.
      unfold pvarsOfValue.
      fold pvarsOfValue.
      apply ProgramSet.union_spec.
      now right.
    }
  }
  { admit. (* Minus case *) }
  { admit. (* Times case *) }
  Admitted.

Lemma relevant_pvars_decide_statement (e : logicalEnv) (h : heap) (A : sassert)
  : forall (s s' : variableStore),
      (forall (v : pvar) (c : concrete),
        ProgramSet.In v (pvarsOfAssert A)
        -> (ProgramMap.MapsTo v c s
            <-> ProgramMap.MapsTo v c s'))
      -> (((e, s, h) |= A)
          <-> ((e, s', h) |= A)).
Proof.
  eelim A.
  { easy. }
  { simpl.
    admit. (* TODO: needs helper lemma for EvalsTo *)
  }
  { simpl.
    intros L L_pvars_agree R R_pvars_agree s s' pvars_agree.
    split.
    { split.
      { apply L_pvars_agree with (s:=s).
        intros v c v_in_L.
        apply pvars_agree.
        apply ProgramSet.union_spec.
        now left.
        easy.
      }
      { apply R_pvars_agree with (s:=s).
        intros v c v_in_R.
        apply pvars_agree.
        apply ProgramSet.union_spec.
        now right.
        easy.
      }
    }
    { split.
      { apply L_pvars_agree with (s:=s').
        intros v c v_in_L.
        rewrite pvars_agree.
        easy.
        apply ProgramSet.union_spec.
        now left.
        easy.
      }
      { apply R_pvars_agree with (s:=s').
        intros v c v_in_R.
        rewrite pvars_agree.
        easy.
        apply ProgramSet.union_spec.
        now right.
        easy.
      }
    }
  }
  { simpl.
    intros L L_pvars_agree R R_pvars_agree s s' pvars_agree.
    split.
    { intros [ L_sat | R_sat ].
      { left.
        apply L_pvars_agree with (s:=s).
        intros v c v_in_L.
        apply pvars_agree.
        apply ProgramSet.union_spec.
        now left.
        easy.
      }
      { right.
        apply R_pvars_agree with (s:=s).
        intros v c v_in_R.
        apply pvars_agree.
        apply ProgramSet.union_spec.
        now right.
        easy.
      }
    }
    { intros [ L_sat | R_sat ].
      { left.
        apply L_pvars_agree with (s:=s').
        intros v c v_in_L.
        rewrite pvars_agree.
        easy.
        apply ProgramSet.union_spec.
        now left.
        easy.
      }
      { right.
        apply R_pvars_agree with (s:=s').
        intros v c v_in_R.
        rewrite pvars_agree.
        easy.
        apply ProgramSet.union_spec.
        now right.
        easy.
      }
    }
  }
  { simpl.
    intros nA nA_pvars_agree s s' pvars_agree.
    split.
    { intros not_A.
      contradict not_A.
      rewrite <- nA_pvars_agree with (s:=s'); try assumption.
      intros v c v_in_nA.
      now rewrite pvars_agree.
    }
    { intros not_A.
      contradict not_A.
      rewrite <- nA_pvars_agree with (s:=s); try assumption.
    }
  }
  { intros L L_pvars_agree R R_pvars_agree s s' pvars_agree.
    split.
    { intros L_impl_R_sat L_sat.
      apply R_pvars_agree with (s:=s).
      intros v c v_in_R.
      apply pvars_agree.
      apply ProgramSet.union_spec.
      now right.
      apply L_impl_R_sat.
      fold Satisfies.
      rewrite L_pvars_agree with (s':=s'); try assumption.
      intros v c v_in_L.
      apply pvars_agree.
      apply ProgramSet.union_spec.
      now left.
    }
    { intros L_impl_R_sat L_sat.
      apply R_pvars_agree with (s:=s').
      intros v c v_in_R.
      rewrite pvars_agree.
      easy.
      apply ProgramSet.union_spec.
      now right.
      apply L_impl_R_sat.
      fold Satisfies.
      rewrite L_pvars_agree with (s':=s); try assumption.
      intros v c v_in_L.
      rewrite pvars_agree.
      easy.
      apply ProgramSet.union_spec.
      now left.
    }
  }
  { intros; easy. }
  { intros x v s s' pvars_agree.
    split.
    { unfold Satisfies.
      intros [ c [ c' [ x_interps_c [ v_interps_c' h_singleton_c_c' ]]]].
      exists c.
      exists c'.
      split.
      { rewrite relevant_pvars_decide_interps_to with (s':=s).
        easy.
        intros v0 c0 v0_in_x.
        rewrite pvars_agree; try easy.
        apply ProgramSet.union_spec.
        now left.
      }
      split.
      { rewrite relevant_pvars_decide_interps_to with (s':=s).
        easy.
        intros v0 c0 v0_in_x.
        rewrite pvars_agree; try easy.
        apply ProgramSet.union_spec.
        now right.
      }
      { easy.
      }
    }
    { unfold Satisfies.
      intros [ c [ c' [ x_interps_c [ v_interps_c' h_singleton_c_c' ]]]].
      exists c.
      exists c'.
      split.
      { rewrite relevant_pvars_decide_interps_to with (s':=s').
        easy.
        intros v0 c0 v0_in_x.
        rewrite pvars_agree; try easy.
        apply ProgramSet.union_spec.
        now left.
      }
      split.
      { rewrite relevant_pvars_decide_interps_to with (s':=s').
        easy.
        intros v0 c0 v0_in_x.
        rewrite pvars_agree; try easy.
        apply ProgramSet.union_spec.
        now right.
      }
      { easy.
      }
    }
  }
  { admit. (* Separating conjunction *)
  }
  { admit. (* Separating implication *)
  }
  { admit. (* Forall *)
  }
  { admit. (* Exists *)
  }
  Admitted.

