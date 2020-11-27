(*! Definition of a small imperative language !*)

From Coq Require Import Strings.String ZArith.

(** Variables id **)
Definition vid := string.

(** Location ids **)
Definition location := nat.

(** Binary operation codes **)
Inductive BinOpCode := Add | Mul | Le.

(** Single instruction **)
Inductive Instruction :=
| IBinop (res_val op1 op2: vid).

(** A program **)
Inductive Program :=
| PInst (inst: Instruction)
| PSeq (p1 p2: Program)
| PIf (cond_var: vid) (p_true p_false: Program)
| PLoop (min max: Z) (loop_var: vid) (p1: Program).
