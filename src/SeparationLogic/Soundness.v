Require Import SPAM.SeparationLogic.Syntax.
Require Import SPAM.SeparationLogic.Semantics.
Require Import SPAM.SeparationLogic.Program.

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
  intros pre post stat0 e s s' h0 h'0 triple.
  generalize h0 h'0.
  eelim triple.
  { admit.
  }
  { admit.
  }
  { admit.
  }
  { admit.
  }
  { intros A A' B B' stat A'_impl_A B_impl_B' triple_ IHtriple h h' A'_sat stat_runs.
    apply B_impl_B'.
    apply IHtriple with (h0:=h); try assumption.
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
  Qed.
