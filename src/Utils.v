(*! Useful definitions !*)
From Coq Require Import Lists.List ZArith NArith.
From PresburgerAI Require Import EqDec.
Require Import Coq.Logic.ProofIrrelevance.

(** Nonnegative integers less than n **)
Definition Fin (n: nat) := { v : nat | v < n}.

(** List with fixed size **)
Definition Array (T: Type) (n: nat) := { l : list T | length l = n }.

Definition get_default {T: Type} {n: nat} (a: Array T n) (i: Fin n) : T.
  destruct i.
  destruct a.
  destruct n; intuition.
  destruct x0; intuition.
  simpl in e.
  inversion e.
Defined.

(** Access the array at a given index **)
Definition array_get {T: Type} {n: nat} (a: Array T n) (i: Fin n) :=
  nth (proj1_sig i) (proj1_sig a) (get_default a i).

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
  forall {T: Type} (l: list T) (n1 n2: nat),
    n1 < length l ->
    n2 < length l ->
    forall t, nth_error (set_nth l n1 t) n2 =
         if n1 == n2 then
           Some t
         else
           nth_error l n2.
Proof.
  induction l; [intros; simpl in *; intuition | ].
  simpl in *.
  destruct n1; [ destruct n2; auto | ].
  - destruct n2; intuition.
    simpl in *.
    apply lt_S_n in H.
    apply lt_S_n in H0.
    rewrite IHl; auto.
    destruct (n1 == n2).
    + cbv in e. subst.
      destruct (S n2 == S n2); intuition.
    + destruct (S n1 == S n2); intuition.
      inversion e.
      subst. intuition.
Qed.

(** Set the value on an index **)
Definition array_set {T: Type} {n: nat} (a: Array T n) (i: Fin n) (t: T) : Array T n.
  eapply exist.
  unfold Array in a.
  rewrite <-(proj2_sig a) at 1.
  apply (set_nth_length (proj1_sig i) (proj1_sig a) t).
Defined.


Lemma array_get_set_eq {T: Type} {n: nat} (a: Array T n) (i: Fin n) (t: T) :
  array_get (array_set a i t) i = t.
Proof.
  unfold array_get, array_set.
  simpl.
  apply nth_error_nth.
  destruct a, i.
  simpl in *; subst.
  rewrite nth_set_nth; intuition.
  pose proof (equiv_dec_refl x0) as [? ?].
  rewrite H; auto.
Qed.


Lemma array_get_set_ne {T: Type} {n: nat} (a: Array T n) (i1 i2: Fin n) (t: T) :
  i1 <> i2 ->
  array_get (array_set a i1 t) i2 = array_get a i2.
Proof.
  unfold array_get, array_set.
  simpl.
  intros.
  apply nth_error_nth.
  destruct a. simpl.
  destruct i1, i2. subst.
  simpl (proj1_sig _).
  rewrite nth_set_nth; intuition.
  destruct (equiv_dec x0 x1).
  - destruct e.
    exfalso.
    apply H.
    f_equal.
    apply proof_irrelevance.
  - auto using nth_error_nth'.
Qed.
