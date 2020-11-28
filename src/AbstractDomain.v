From Coq Require Export Ensembles.

(** An abstract domain **)
Class AbstractDomain (ConcreteType AbstractType: Type) :=
{
  bot : AbstractType;
  top : AbstractType;
  join : AbstractType -> AbstractType -> AbstractType;

  gamma : AbstractType -> Ensemble ConcreteType;
  in_dom c a := Ensembles.In _ (gamma a) c;
  le a1 a2 := forall x, in_dom x a1 -> in_dom x a2;

  gamma_top : forall x, in_dom x top;
  gamma_bot : forall x, ~ in_dom x bot;
  join_sound_l : forall a1 a2, le a1 (join a1 a2);
  join_sound_r : forall a1 a2, le a2 (join a1 a2);
}.

(** Some simple facts about abstract domains **)
Section AbstractDomainTheorems.

  Context {ConcreteType AbstractType: Type}
          {ad: AbstractDomain ConcreteType AbstractType}.

  Theorem le_refl :
    forall a, le a a.
  Proof.
    unfold le.
    auto.
  Qed.

  Theorem le_trans :
    forall a1 a2, le a1 a2 -> forall a3, le a2 a3 -> le a1 a3.
  Proof.
    intros.
    unfold le in *.
    auto.
  Qed.

  Theorem le_join_l :
    forall a1 a2, le a1 a2 -> forall a3, le a1 (join a2 a3).
  Proof.
    eauto using le_trans, join_sound_l.
  Qed.

  Theorem le_join_r :
    forall a1 a2, le a1 a2 -> forall a3, le a1 (join a3 a2).
  Proof.
    eauto using le_trans, join_sound_r.
  Qed.

  Theorem le_bot :
    forall a, le bot a.
  Proof.
    unfold le.
    intros.
    apply gamma_bot in H.
    inversion H.
  Qed.

End AbstractDomainTheorems.

