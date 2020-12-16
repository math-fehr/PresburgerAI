From PresburgerAI Require Export Imp TransferFunction.

Section AbstractInterpreter.

  Context {AbstractState: Type}
          {n: nat}
          {adom: AbstractDomain (State n * State n) AbstractState}
          {adom_relational: RelationalAbstractDomain adom}
          {transfer_function: TransferFunction adom}.

  Fixpoint interpret (p: Program n) :=
    match p with
    | PBinop res opc op1 op2 =>
      transfer_binop res opc op1 op2
    | PSeq p1 p2 =>
      compose_relation (interpret p1) (interpret p2)
    | PIf cond p1 p2 =>
      let s1 := compose_relation (filter_true_value cond) (interpret p1) in
      let s2 := compose_relation (filter_false_value cond) (interpret p2) in
      join s1 s2
    | PWhile cond p =>
      (* multiple steps of the loop *)
      let in_loop_s := compose_transitive (compose_relation (filter_true_value cond) (interpret p)) in
      (* leaving the loop at any iteration *)
      let out_loop_s := compose_relation in_loop_s (filter_false_value cond) in
      out_loop_s
    end.

End AbstractInterpreter.

Section AbstractInterpreterSoundness.

  Context {AbstractState: Type}
          {n: nat}
          {adom: AbstractDomain (State n * State n) AbstractState}
          (adom_relational: RelationalAbstractDomain adom)
          {transfer_function: TransferFunction adom}.

  Lemma interpret_sound (p: Program n) :
    forall s s', s =[ p ]=> s' -> in_dom (s, s') (interpret p).
  Proof.
    induction p; simpl; intros.
    - auto using transfer_binop_sound.
    - inversion H; subst.
      eauto using compose_relation_spec.
    - inversion H; subst.
      + apply join_sound_l.
        eapply compose_relation_spec; eauto using filter_true_value_sound.
      + apply join_sound_r.
        eapply compose_relation_spec; eauto using filter_false_value_sound.
    - apply while_trans_closure in H as [? ?].
      eapply compose_relation_spec; [ | auto using filter_false_value_sound ].
      apply compose_transitive_spec.
      eapply le_transitive_closure; [ | apply H ].
      intros [x1 x2] [H1 H2].
      eapply compose_relation_spec; eauto using filter_true_value_sound.
  Qed.

End AbstractInterpreterSoundness.
