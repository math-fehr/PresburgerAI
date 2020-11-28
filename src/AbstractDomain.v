From Coq Require Export Ensembles.

(** An abstract domain **)
Class adom (ConcreteType AbstractType: Type) :=
{
  bot : AbstractType;
  top : AbstractType;
  join : AbstractType -> AbstractType -> AbstractType;

  gamma : AbstractType -> Ensemble ConcreteType;

  gamma_top : forall x, Ensembles.In ConcreteType (gamma top) x;
  gamma_bot : forall x, ~ Ensembles.In ConcreteType (gamma bot) x;
  join_sound_l : forall a1 a2, Included _ (gamma a1) (gamma (join a1 a2));
  join_sound_r : forall a1 a2, Included _ (gamma a2) (gamma (join a1 a2));
}.

(** Order relation on abstract states **)
Definition le {ConcreteType AbstractType: Type}
           {ad: adom ConcreteType AbstractType}
           (a1 a2: AbstractType)
  := Included _ (gamma a1) (gamma a2).

Section AbstractDomainTheorems.

  Context {ConcreteType AbstractType: Type}
          {ad: adom ConcreteType AbstractType}.

  Theorem le_refl :
    forall a, le a a.
  Proof.
    unfold le, Included.
    auto.
  Qed.

  Theorem le_trans :
    forall a1 a2, le a1 a2 -> forall a3, le a2 a3 -> le a1 a3.
  Proof.
    unfold le, Included.
    auto.
  Qed.

  Theorem le_join_l :
    forall a1 a2, le a1 a2 -> forall a3, le a1 (join a2 a3).
  Proof.
    unfold le, Included.
    intros.
    apply join_sound_l.
    auto.
  Qed.

  Theorem le_join_r :
    forall a1 a2, le a1 a2 -> forall a3, le a1 (join a3 a2).
  Proof.
    unfold le, Included.
    intros.
    apply join_sound_r.
    auto.
  Qed.

  Theorem le_bot :
    forall a, le bot a.
  Proof.
    unfold le, Included.
    intros.
    apply gamma_bot in H.
    inversion H.
  Qed.

End AbstractDomainTheorems.

