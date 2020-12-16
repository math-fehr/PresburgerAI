(*! Useful definitions !*)
From Coq Require Import Lists.List ZArith NArith.
From PresburgerAI Require Import EqDec.

(** Nonnegative integers less than n **)
Definition Fin (n: nat) := { v : nat | v < n}.

(** List with fixed size **)
Definition Array (T: Type) (n: nat) := { l : list T | length l = n }.

(** Access the array at a given index **)
Definition array_get {T: Type} {n: nat} (a: Array T n) (i: Fin n) : T.
  destruct a.
  destruct i.
  subst.
  apply nth_error_Some in l.
  destruct (nth_error x x0).
  - apply t.
  - destruct l. reflexivity.
Defined.

Fixpoint set_nth {T: Type} (l: list T) (n: nat) (t: T) :=
  match l with
  | nil => nil
  | a::l' => match n with
           | 0 => t::l'
           | S n' => a::(set_nth l' n' t)
           end
  end.

Lemma set_nth_length :
  forall (n: nat) {T: Type} (l: list T) (t: T),
  length (set_nth l n t) = length l.
Proof.
  induction n; destruct l; intuition.
  simpl.
  rewrite IHn.
  intuition.
Qed.

Lemma nth_set_nth :
  forall (n: nat) {T: Type} (l: list T),
  n < length l ->
  forall t, nth_error (set_nth l n t) n = Some t.
Proof.
  induction n; intros; destruct l; simpl in *; intuition.
Qed.

(** Set the value on an index **)
Definition array_set {T: Type} {n: nat} (a: Array T n) (i: Fin n) (t: T) : Array T n.
  destruct a.
  destruct i.
  subst.
  eapply exist.
  apply (set_nth_length x0 x t).
Defined.
