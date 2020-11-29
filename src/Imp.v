(*! Definition of a small imperative language !*)

From PresburgerAI Require Export TotalMap EqDec.
From Coq Require Export Strings.String ZArith List.

Open Scope list_scope.
Open Scope Z_scope.

(** Variables id **)
Definition Vid := string.

(** Location ids **)
Definition Location := list nat.

(** Binary operation codes **)
Inductive BinOpCode := Add | Mul | Le.

(** A Program **)
Inductive Program :=
| PBinop (res: Vid) (opc: BinOpCode) (op1 op2: Vid)
| PSeq (p1 p2: Program)
| PIf (cond_var: Vid) (p_true p_false: Program)
| PWhile (cond: Vid) (p1: Program).

(** A state in the program **)
Notation State := (TotalMap Vid Z).

(** Execute a binary operation given both operands values **)
Definition execute_binop (opc: BinOpCode) (v1 v2: Z) :=
  match opc with
  | Add => v1 + v2
  | Mul => v1 * v2
  | Le => if v1 <=? v2 then 1 else 0
  end.

(** Execute a binary operation on a state **)
Definition execute_binop_state (opc: BinOpCode) (op1 op2: Vid) (s: State) :=
  execute_binop opc (s op1) (s op2).

(** Notation for relational semantics **)
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, st constr, st' constr at next level).

(** Relational semantics of a program **)
Inductive semantics : Program -> State -> State -> Prop :=
| EBinop res opc op1 op2 s :
  s =[ PBinop res opc op1 op2 ]=> (res !!-> execute_binop_state opc op1 op2 s; s)
| ESeq p1 p2 s s' s'' :
    s =[ p1 ]=> s' ->
    s' =[ p2 ]=> s'' ->
    s =[ PSeq p1 p2 ]=> s''
| EIfTrue var p_true p_false (s s': State) :
    (s var) <> 0 ->
    s =[ p_true ]=> s' ->
    s =[ PIf var p_true p_false ]=> s'
| EIfFalse var p_true p_false (s s': State) :
    (s var) = 0 ->
    s =[ p_false ]=> s' ->
    s =[ PIf var p_true p_false ]=> s'
| EWhileTrue var p (s s' s'': State) :
    (s var) <> 0 ->
    s =[ p ]=> s' ->
    s' =[ PWhile var p ]=> s'' ->
    s =[ PWhile var p ]=> s''
| EWhileFalse var p (s: State) :
    (s var) = 0 ->
    s =[ PWhile var p ]=> s
where "st =[ p ]=> st'" := (semantics p st st').

