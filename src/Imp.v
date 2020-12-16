(*! Definition of a small imperative language !*)

From PresburgerAI Require Export TotalMap EqDec RelationalAbstractDomain Utils.
From Coq Require Export Strings.String ZArith List.

Open Scope list_scope.

(** Variables id **)
Notation Vid n := (Fin n).

(** Location ids **)
Definition Location := list nat.

(** Binary operation codes **)
Inductive BinOpCode := Add | Mul | Le.

(** A Program **)
Inductive Program {n: nat} :=
| PBinop (res: Vid n) (opc: BinOpCode) (op1 op2: Vid n)
| PSeq (p1 p2: Program)
| PIf (cond_var: Vid n) (p_true p_false: Program)
| PWhile (cond: Vid n) (p1: Program).

Arguments Program : clear implicits.

(** A state in the program **)
Notation State n := (TotalMap (Vid n) Z).

(** Execute a binary operation given both operands values **)
Definition execute_binop (opc: BinOpCode) (v1 v2: Z) :=
  match opc with
  | Add => (v1 + v2)%Z
  | Mul => (v1 * v2)%Z
  | Le => if (v1 <=? v2)%Z then 1%Z else 0%Z
  end.

(** Execute a binary operation on a state **)
Definition execute_binop_state {n: nat} (opc: BinOpCode) (op1 op2: Vid n) (s: State n) :=
  execute_binop opc (s op1) (s op2).

(** Notation for relational semantics **)
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, st constr, st' constr at next level).

(** Relational semantics of a program **)
Inductive semantics {n: nat} : Program n -> State n -> State n -> Prop :=
| EBinop res opc op1 op2 s :
  s =[ PBinop res opc op1 op2 ]=> (res !!-> execute_binop_state opc op1 op2 s; s)
| ESeq p1 p2 s s' s'' :
    s =[ p1 ]=> s' ->
    s' =[ p2 ]=> s'' ->
    s =[ PSeq p1 p2 ]=> s''
| EIfTrue var p_true p_false (s s': State n) :
    (s var) <> 0%Z ->
    s =[ p_true ]=> s' ->
    s =[ PIf var p_true p_false ]=> s'
| EIfFalse var p_true p_false (s s': State n) :
    (s var) = 0%Z ->
    s =[ p_false ]=> s' ->
    s =[ PIf var p_true p_false ]=> s'
| EWhileTrue var p (s s' s'': State n) :
    (s var) <> 0%Z ->
    s =[ p ]=> s' ->
    s' =[ PWhile var p ]=> s'' ->
    s =[ PWhile var p ]=> s''
| EWhileFalse var p (s: State n) :
    (s var) = 0%Z ->
    s =[ PWhile var p ]=> s
where "st =[ p ]=> st'" := (semantics p st st').

Section ImpLemmas.

  (** When we are out of the while loop, the condition is false **)
  Lemma while_out_cond n cond p s s' :
    s =[ @PWhile n cond p ]=> s' ->
    s' cond = 0%Z.
  Proof.
    intros.
    remember (PWhile _ _).
    induction H; try discriminate; inversion Heqp0; subst; auto.
  Qed.

  (** equivalence with the denotational semantics**)
  Lemma while_trans_closure n cond p s s' :
    s =[ @PWhile n cond p ]=> s' <->
    transitive_closure (fun (s: State n * State n) => ((fst s) cond <> 0%Z) /\ (fst s) =[ p ]=> (snd s)) (s, s') /\ s' cond = 0%Z.
  Proof.
    split; intros.
    - split; [ | eauto using while_out_cond ].
      remember (PWhile _ _).
      induction H; try discriminate; inversion Heqp0; subst; [ | constructor ].
      specialize (IHsemantics2 eq_refl).
      eapply tc_app; [ | eauto].
      auto.
    - destruct H.
      remember (s, s').
      generalize dependent s'.
      generalize dependent s.
      induction H; intros; inversion Heqp0; subst; [ constructor; auto | ].
      destruct H.
      simpl in *.
      eapply EWhileTrue; eauto.
  Qed.

End ImpLemmas.
