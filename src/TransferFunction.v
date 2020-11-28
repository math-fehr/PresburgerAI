From PresburgerAI Require Export RelationalAbstractDomain Imp.

Section TransferFunctionDefinition.

  Context {AbstractState: Type}
          {adom: AbstractDomain (State * State) AbstractState}.

  (** Properties on abstract domain to be able to use the abstract interpreter
      for Imp **)
  Class TransferFunction :=
  {
    transfer_binop : Vid -> BinOpCode -> Vid -> Vid -> AbstractState;
    transfer_binop_sound :
      forall res opc op1 op2 s s', s =[ PBinop res opc op1 op2 ]=> s' ->
      in_dom (s, s') (transfer_binop res opc op1 op2)
  }.

End TransferFunctionDefinition.

Arguments TransferFunction {AbstractState} adom.
