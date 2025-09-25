import OpenvmFv.Spec.run_hart_active

namespace Local
  def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (LeanRV32D.Functions.sign_extend (m := 32) (imm ++ (0x000 : (BitVec 12))))
  (LeanRV32D.Functions.wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (LeanRV32D.Functions.get_arch_pc ())) + off))))
  (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_UTYPE_equiv :
    execute_UTYPE = LeanRV32D.Functions.execute_UTYPE
  := rfl

  def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) == (← (LeanRV32D.Functions.rX_bits rs2))))
    | .BNE => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) != (← (LeanRV32D.Functions.rX_bits rs2))))
    | .BLT => (pure (LeanRV32D.Functions.zopz0zI_s (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2))))
    | .BGE => (pure (LeanRV32D.Functions.zopz0zKzJ_s (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2))))
    | .BLTU => (pure (LeanRV32D.Functions.zopz0zI_u (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2))))
    | .BGEU => (pure (LeanRV32D.Functions.zopz0zKzJ_u (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (LeanRV32D.Functions.jump_to ((← Sail.readReg Register.PC) + (LeanRV32D.Functions.sign_extend (m := 32) imm)))
  else (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_BTYPE_equiv :
    execute_BTYPE = LeanRV32D.Functions.execute_BTYPE
  := rfl

  def jump_to (target : (BitVec 32)) : SailM ExecutionResult := Sail.SailME.run do
    match (LeanRV32D.Functions.ext_control_check_pc target) with
    | .some e => Sail.SailME.throw ((ExecutionResult.Ext_ControlAddr_Check_Failure e) : ExecutionResult)
    | none => (pure ())
    Sail.assert ((Sail.BitVec.access target 0) == 0#1) "extensions/I/base_insts.sail:59.29-59.30"
    if (((← (LeanRV32D.Functions.bit_to_bool (Sail.BitVec.access target 1))) && (not (← (LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca)))) : Bool)
    then (pure (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr target), (ExceptionType.E_Fetch_Addr_Align ()))))
    else
      (do
        (LeanRV32D.Functions.set_next_pc target)
        (pure LeanRV32D.Functions.RETIRE_SUCCESS))

  lemma jump_to_equiv :
    jump_to = LeanRV32D.Functions.jump_to
  := rfl
end Local
