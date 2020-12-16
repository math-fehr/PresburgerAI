From PresburgerAI Require Export RelationalAbstractDomain Imp.

Section TransferFunctionDefinition.

  Context {AbstractState: Type}
          {n: nat}
          {adom: AbstractDomain (State n * State n) AbstractState}.

  (** Properties on abstract domain to be able to use the abstract interpreter
      for Imp **)
  Class TransferFunction :=
  {
    transfer_binop : Vid n -> BinOpCode -> Vid n -> Vid n -> AbstractState;
    transfer_binop_sound :
      forall res opc op1 op2 s s',
        s =[ PBinop res opc op1 op2 ]=> s' ->
        in_dom (s, s') (transfer_binop res opc op1 op2);

    filter_true_value : Vid n -> AbstractState;
    filter_true_value_sound :
      forall (var: Vid n) (s: State n),
        (s var) <> 0%Z ->
        in_dom (s, s) (filter_true_value var);

    filter_false_value : Vid n -> AbstractState;
    filter_false_value_sound :
      forall (var: Vid n) (s: State n),
        (s var) = 0%Z ->
        in_dom (s, s) (filter_false_value var)
  }.

End TransferFunctionDefinition.

Arguments TransferFunction {AbstractState} {n} adom.
