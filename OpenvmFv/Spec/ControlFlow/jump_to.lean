import OpenvmFv.Spec.ControlFlow.local

def jump_to_simplified (target : BitVec 32) : SailM ExecutionResult :=
  λ state =>
    (
      if (BitVec.ofBool target[0]) == 1#1 then EStateM.Result.error (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30") state
      else match state.regs.get? Register.misa with
        | .none => EStateM.Result.error (Sail.Error.Unreachable) state
        | .some (misa_val: BitVec 32) =>
          if (BitVec.ofBool target[1] == 1#1 && !misa_val[2])
          then EStateM.Result.ok (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr target), (ExceptionType.E_Fetch_Addr_Align ()))) state
          else EStateM.Result.ok (ExecutionResult.Retire_Success ()) (write_reg_state state Register.nextPC target)
    )

lemma jump_to_simplified_equiv:
  Local.jump_to = jump_to_simplified
:= by
  funext target state
  unfold Local.jump_to
  unfold jump_to_simplified
  simp [
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, Functor.map,
    bind, Sail.SailME.run, EStateM.bind, ExceptT.bind, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.run, Functor.map, ExceptT.bindCont,
  ]
  by_cases h_bit_0 : (BitVec.ofBool target[0]) = 1#1
  . simp [h_bit_0, EStateM.map]
  . simp [
      bit_eq_zero_of_not_eq_one _ h_bit_0,
      EStateM.bind,
      EStateM.map, ExceptT.bindCont
    ]
    cases h_misa: state.regs.get? Register.misa with
      | none =>
        simp [readReg_fail h_misa]
      | some misa_val =>
        simp [readReg_state h_misa]
        by_cases h_bit_1 : (BitVec.ofBool target[1] = 1#1) ∧ misa_val[2] = false
        . simp [h_bit_1]
        . simp [h_bit_1]
          unfold EStateM.map
          simp [
            writeReg_state_success,
            ExceptT.bindCont
          ]
