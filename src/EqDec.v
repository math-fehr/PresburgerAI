Require Export EquivDec.
Require Import Strings.String.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Relations.Relation_Definitions.
Require Import ZArith NArith.

Ltac solve_eq_eqb_translations :=
  intros;
  unfold "<>b", "==b" in *;
  destruct (equiv_dec _ _); intuition; eauto.

Lemma equiv_decb_refl : forall {T} (x: T) {R: T -> T -> Prop} {equiv: Equivalence R} {ED: EqDec T R},
    (equiv_decb x x) = true.
Proof. solve_eq_eqb_translations. Qed.

Lemma eqb_to_eq : forall {T} (x y: T) {ED: EqDec T eq},
    (x ==b y) = true -> x = y.
Proof. solve_eq_eqb_translations. Qed.

Lemma not_eqb_to_ne : forall {T} (x y: T) {ED: EqDec T eq},
    (x ==b y) = false -> x <> y.
Proof. solve_eq_eqb_translations. Qed.

Lemma neb_to_ne : forall {T} (x y: T) {ED: EqDec T eq},
    (x <>b y) = true -> x <> y.
Proof. solve_eq_eqb_translations. Qed.

Lemma not_neb_to_eq : forall {T} (x y: T) {ED: EqDec T eq},
    (x <>b y) = false -> x = y.
Proof. solve_eq_eqb_translations. Qed.

Lemma comp_equiv_dec_to_ne : forall {T} (x y: T) {ED: EqDec T eq},
    (x =/= y) -> x <> y.
Proof. intuition. Qed.

Lemma ne_to_neb : forall {T} (x y: T) {ED: EqDec T eq},
    x <> y -> x <>b y = true.
Proof. solve_eq_eqb_translations. Qed.

Lemma ne_to_neb' : forall {T} (x y: T) {ED: EqDec T eq},
    x <> y -> y <>b x = true.
Proof. solve_eq_eqb_translations. Qed.

Lemma ne_to_not_eqb : forall {T} (x y: T) {ED: EqDec T eq},
    x <> y -> x ==b y = false.
Proof. solve_eq_eqb_translations. Qed.

Lemma ne_to_not_eqb' : forall {T} (x y: T) {ED: EqDec T eq},
    x <> y -> y ==b x = false.
Proof. solve_eq_eqb_translations. Qed.

Hint Rewrite @equiv_decb_refl : rweq.
Hint Rewrite @ne_to_neb @ne_to_not_eqb @ne_to_neb' @ne_to_not_eqb' using assumption : rweq.

Ltac simpl_eqb :=
  repeat
    match goal with
    | [ H: ?x =/= ?y |- _ ] => apply (@comp_equiv_dec_to_ne _ _ _ _) in H
    | [ H: ?x === ?y |- _ ] => unfold "===" in H; subst
    | [ H: (?x ==b ?y) = true |- _ ] => apply (@eqb_to_eq _ _ _ _) in H; subst
    | [ H: (?x ==b ?y) = false |- _ ] => apply (@not_eqb_to_ne _ _ _ _) in H
    | [ H: (?x <>b ?y) = true |- _ ] => apply (@neb_to_ne _ _ _ _) in H
    | [ H: (?x <>b ?y) = false |- _ ] => apply (@not_neb_to_eq _ _ _ _) in H; subst
    end;
  autorewrite with rweq.

Global Instance string_eqdec : EqDec string eq := string_dec.

Global Instance Z_eqdec : EqDec Z eq.
Proof.
  intro a. intro b.
  destruct (Z_dec a b).
  - right.
    destruct s.
    + apply Z.lt_neq.
      assumption.
    + apply Z.gt_lt in g.
      apply Z.lt_neq in g.
      intro.
      auto.
  - intuition.
Qed.

Global Instance nat_eqdec : EqDec nat eq := eq_nat_dec.

Global Instance Some_eqdec :
  forall T, EqDec T eq -> EqDec (option T) eq.
Proof.
  intros.
  intro x. intro y.
  unfold "===", complement.
  destruct x; destruct y.
  - destruct (t == t0).
    + unfold "===" in *.
      subst; auto.
    + right.
      intros.
      inversion H. subst.
      intuition.
  - right.
    inversion 1.
  - right.
    inversion 1.
  - left.
    reflexivity.
Qed.

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
