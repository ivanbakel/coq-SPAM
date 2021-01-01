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
    -> <cons v inits, (sv, h)> ~> (sv, addConsecutive c vals h)
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
  : { exprToValue e |-> exprToValue v }- lookup x e -{ (exprToValue e |-> exprToValue v) s/\ eq_s (exprToValue e) (exprToValue v) }
  | localMutate (e v v' : expr)
  : { exprToValue e |-> exprToValue v' }- mutate e v -{ exprToValue e |-> exprToValue v }
  | localDispose (e v : expr)
  : { exprToValue e |-> exprToValue v }- dispose e -{ empty }
  where "{ A }- s -{ B }" := (Triple A s B).

Theorem triple_sound :
  forall
    (pre post : sassert)
    (stat : statement)
    (e : logicalEnv)
    (s s' : variableStore)
    (h h' : heap),
    { pre }- stat -{ post }
    -> (e, s, h) |= pre
    -> <stat, (s, h)> ~> (s', h')
    -> (e, s', h') |= post.
Proof.
  (* TODO: this proof requires many lemmas *)
  Admitted.

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

Reserved Notation "{ A }* p *{ B }" (at level 99).

Inductive ProgramTriple : sassert -> program -> sassert -> Prop :=
  | finalTriple (A B : sassert) (stat : statement)
  : { A }- stat -{ B }
    -> { A }* final stat *{ B }
  | seqTriple (A B C : sassert) (stat : statement) (prog : program)
  : { A }- stat -{ B }
    -> { B }* prog *{ C }
    -> { A }* seq stat prog *{ C }
  | consequence (A A' B B' : sassert) (prog : program)
  : _|= A' s-> A
    -> _|= B s-> B'
    -> { A }* prog *{ B }
    -> { A' }* prog *{ B' }
  | frame (A B C : sassert) (prog : program)
  : ProgramSet.Empty (ProgramSet.inter (modifies prog) (pvarsOfAssert C))
    -> { A }* prog *{ B }
    -> { A s* C }* prog *{ B s* C }
  where "{ A }* p *{ B }" := (ProgramTriple A p B).

Theorem program_triple_sound :
  forall
    (pre post : sassert)
    (prog : program)
    (e : logicalEnv)
    (s s' : variableStore)
    (h h' : heap),
    { pre }* prog *{ post }
    -> (e, s, h) |= pre
    -> <prog, (s, h)> ~>* (s', h')
    -> (e, s', h') |= post.
Proof.
  intros pre0 post0 prog0 e s0 s1 h0 h1 triple.
  generalize s0 h0 s1 h1.
  eelim triple.
  { intros pre post stat triple_ s h s' h' pre_sat final_runs.
    inversion final_runs as [ stat_ s'_ h'_ | ].
    now apply triple_sound with (pre:=pre) (stat:=stat) (s:=s) (h:=h).
  }
  { intros A B C stat prog triple_stat triple_prog IHtriple s h s' h' pre_sat seq_runs.
    inversion seq_runs as [ | stat_ prog_ s'' s'_ h'' h'_ ].
    apply IHtriple with (s0:=s'') (h0:=h''); try assumption.
    now apply triple_sound with (pre:= A) (stat:=stat) (s:=s) (h:=h).
  }
  { intros A A' B B' prog A'_impl_A B_impl_B' triple_ IHtriple s h s' h' A_sat prog_runs.
    apply B_impl_B'.
    apply IHtriple with (s0:=s) (h0:=h); try assumption.
    now apply A'_impl_A.
  }
  { (* TODO: probably the hardest part of this proof
       - showing that frame is sound! *)
    (* The basic sketch is:
        * Anything not in the modifies set is unchanged by execution
        * A statement which doesn't use the modifies set has the same truth value after execution
        * So the framed off statement still holds
    *)
    admit.
  }
  Admitted.
