From PresburgerAI Require Export AbstractDomain.
Require Export Coq.Sets.Ensembles.

(** Smallest relation containing the identity and closed by application **)
Inductive transitive_closure {T: Type} (R: (T * T) -> Prop) : (T * T) -> Prop :=
| tc_id : forall x, transitive_closure R (x, x)
| tc_app : forall x y z, R (x, y) ->
                    transitive_closure R (y, z) ->
                    transitive_closure R (x, z).

Lemma le_transitive_closure {T: Type} (R1 R2: (T * T) -> Prop) :
  (forall x, R1 x -> R2 x) -> forall x, transitive_closure R1 x -> transitive_closure R2 x.
Proof.
  intros.
  induction H0; [ constructor | ].
  eauto using tc_app.
Qed.

Section RelationalAbstractDomainDefinition.

  Context {ConcreteState AbstractState: Type}
          {AD: AbstractDomain (ConcreteState * ConcreteState) AbstractState}.

  (** An abstract domain over relations of concrete states
      In opposition to the standard abstract domain, we can
      compute a transitive closure, and compose the relations **)
  Class RelationalAbstractDomain :=
    {
    id_relation : AbstractState;
    id_relation_spec : forall x, in_dom (x, x) id_relation;

    compose_relation : AbstractState -> AbstractState -> AbstractState;
    compose_relation_spec :
      forall x1 x0 x2 a1 a2,
        in_dom (x0, x1) a1 ->
        in_dom (x1, x2) a2 ->
        in_dom (x0, x2) (compose_relation a1 a2);

    compose_transitive : AbstractState -> AbstractState;
    compose_transitive_spec :
      forall c1 c2 a, transitive_closure (gamma a) (c1, c2) ->
                 in_dom (c1, c2) (compose_transitive a);
    }.

End RelationalAbstractDomainDefinition.

Arguments RelationalAbstractDomain {ConcreteState AbstractState} AD.
