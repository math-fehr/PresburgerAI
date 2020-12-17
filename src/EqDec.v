Require Export EquivDec.
Require Import Strings.String.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Relations.Relation_Definitions.

Coercion is_left A B (u : {A} + {B}) := if u then true else false.

Lemma equiv_dec_refl : forall {T} (x: T) {R: T -> T -> Prop} {equiv: Equivalence R} {ED: EqDec T R},
    exists p, equiv_dec x x = left p.
Proof.
  intros.
  destruct (equiv_dec x x); eauto; intuition.
Qed.

Global Instance string_eqdec : EqDec string eq := string_dec.

Lemma proj1_sig_injective :
  forall T P (t1 t2: { v: T | P v }),
    proj1_sig t1 = proj1_sig t2 -> t1 = t2.
Proof.
  intros T P [v1 p1] [v2 p2] H.
  simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.
Qed.

Global Instance sig_eqdec : forall T P, EqDec T eq -> EqDec { v: T | P v} eq.
Proof.
  intros.
  unfold EqDec.
  intros.
  destruct (proj1_sig x == proj1_sig y).
  - left.
    apply proj1_sig_injective.
    auto.
  - right.
    intro.
    unfold "===" in H.
    subst.
    apply c.
    reflexivity.
Qed.
