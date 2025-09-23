import OpenvmFv.Spec.run_hart_active

structure JalInput where
  -- operands
  imm : BitVec 21
  rd: Fin 32
  -- registers
  PC : BitVec 32
  misa : BitVec 32

structure JalOutput where
  -- registers
  nextPC : Option (BitVec 32)
  rd : Option (Finset.Icc 1 31 × BitVec 32)
  -- result
  success : Bool
  throws : Bool

def execute_JAL_pure (input : JalInput) : JalOutput :=
  if (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 1#1) then
    {
      nextPC := (.some (input.PC + 4))
      rd := .none
      success := false
      throws := true
      : JalOutput
    }
  else if (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]! == 1#1 && !input.misa[2]) then
    {
      nextPC := (.some (input.PC + 4))
      rd := .none
      success := false
      throws := false
      : JalOutput
    }
  else if h: input.rd = 0 then
    {
      nextPC := (.some (input.PC + BitVec.signExtend 32 input.imm))
      rd := .none
      success := true
      throws := false
      : JalOutput
    }
  else {
      nextPC := (.some (input.PC + BitVec.signExtend 32 input.imm))
      rd := (.some (⟨input.rd, by {
        apply Finset.mem_Icc.mpr
        omega
      }⟩, input.PC + 4))
      success := true
      throws := false
      : JalOutput
    }

lemma execute_JAL_pure_throws:
  (execute_JAL_pure input).throws =
  (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 1#1)
:= by
  unfold execute_JAL_pure
  grind

lemma execute_JAL_pure_success:
  (execute_JAL_pure input).success =
  (
    (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 0#1) &&
    (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]! == 0#1 || input.misa[2])
  )
:= by
  unfold execute_JAL_pure
  simp
  match h: (
    BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0],
    BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]
  ) with
    | (0, 0) => simp_all; grind
    | (0, 1) => simp_all; grind
    | (1, 0) => simp_all
    | (1, 1) => simp_all

lemma execute_JAL_pure_nextPC:
  (execute_JAL_pure input).nextPC =
  if
    (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 1#1) ||
    (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]! == 1#1 && !input.misa[2])
  then
    (.some (input.PC + 4))
  else
    (.some (input.PC + BitVec.signExtend 32 input.imm))
:= by
  unfold execute_JAL_pure
  aesop

lemma execute_JAL_pure_rd:
  (execute_JAL_pure input).rd =
  if h:
    (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 1#1) ||
    (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]! == 1#1 && !input.misa[2]) ||
    input.rd = 0
  then
    .none
  else
    (.some (⟨input.rd, by {
        simp at h
        apply Finset.mem_Icc.mpr
        omega
      }⟩, input.PC + 4))
:= by
  unfold execute_JAL_pure
  aesop

lemma execute_JAL_pure_equiv
  (jal_input : JalInput)
  (imm: BitVec 21)
  (rd: regidx)
  (h_input_imm: jal_input.imm = imm)
  (h_input_rd: jal_input.rd = regidx_to_fin rd)
  (h_input_pc: state.regs.get? Register.PC = .some jal_input.PC)
  (h_input_misa: state.regs.get? Register.misa = .some jal_input.misa)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute (instruction.JAL (imm, rd))
  ) state =
  let jal_output := execute_JAL_pure jal_input
  (do
    match jal_output.nextPC with
      | .some nextPC => Sail.writeReg Register.nextPC nextPC
      | .none => pure ()
    match jal_output.rd with
      | .some (reg, rd_val) => write_xreg reg rd_val
      | .none => pure ()
    if jal_output.throws then
      throw (Sail.Error.Assertion "riscv_insts_base.sail:57.38-57.39")
    else if !jal_output.success then
      pure (
        ExecutionResult.Memory_Exception (
          (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 32 jal_input.imm)),
          (ExceptionType.E_Fetch_Addr_Align ())
        )
      )
    else
      (pure (ExecutionResult.Retire_Success ()))) state
:= by
  -- unfold to functional structure
  unfold bind Monad.toBind EStateM.instMonad
  dsimp
  unfold EStateM.bind EStateM.pure
  dsimp


  simp [←h_input_imm]; clear h_input_imm

  simp [
    readReg_state h_input_pc,
    writeReg_state_success,
    LeanRV32D.Functions.execute,
    ←Local.execute_jal_equiv
  ]

  have (x : BitVec 32) : Sail.BitVec.addInt x 4 = x + 4 := rfl
  simp [this]

  unfold Local.execute_JAL

  unfold bind Monad.toBind EStateM.instMonad
  dsimp
  unfold EStateM.bind EStateM.pure
  dsimp

  rewrite [readReg_state (writeReg_read_same _)]
  dsimp
  rewrite [readReg_state (writeReg_read_diff h_input_pc (by trivial))]
  dsimp
  rewrite [
    Local.sign_extend_equiv,
    ←Local.jump_to_equiv
  ]

  by_cases h_is_valid: Local.jump_to_is_valid (jal_input.PC + BitVec.signExtend 32 jal_input.imm) jal_input.misa
  . rewrite [
      Local.jump_to_valid_equiv
        (writeReg_read_diff h_input_misa (by trivial))
        h_is_valid
    ]
    unfold Local.jump_to_valid

    unfold bind Monad.toBind EStateM.instMonad
    dsimp
    unfold EStateM.bind EStateM.pure
    dsimp

    simp [
      writeReg_state_success,
      LeanRV32D.Functions.RETIRE_SUCCESS,
      writeReg_write_same,
    ]

    have : rd = regidx.Regidx (BitVec.ofNat 5 jal_input.rd.val) := by
      rewrite [h_input_rd]
      unfold regidx_to_fin
      simp

    rcases rd with ⟨rd⟩
    unfold Local.jump_to_is_valid at h_is_valid
    have h_jal_nextPC :
      (
        (BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 jal_input.imm)[0]! == 1#1 ||
        BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 jal_input.imm)[1]! == 1#1 && !jal_input.misa[2]) = true
      ) = False := by
        simp at h_is_valid
        grind
    by_cases h_rd_zero : rd = 0
    . rewrite [h_rd_zero, wX_write_xreg_0_equiv]
      simp [execute_JAL_pure_throws]
      simp at h_is_valid
      simp [
        h_is_valid.1,
        execute_JAL_pure_success
      ]
      rewrite [ite_cond_eq_false]
      . rewrite [execute_JAL_pure_nextPC, ite_cond_eq_false]
        . simp
          rewrite [execute_JAL_pure_rd, dite_cond_eq_true]
          . simp
          . simp
            right
            rewrite [h_input_rd, h_rd_zero]
            rfl
        . convert h_jal_nextPC
      . grind
    . have h_regidx_non_zero := regidx_non_zero h_rd_zero
      rewrite [←h_input_rd] at h_regidx_non_zero
      apply Finset.mem_Icc.mp at h_regidx_non_zero
      have h_input_rd_low : 1 ≤ jal_input.rd.val := by omega
      have h_input_rd_high : jal_input.rd.val ≤ 31 := by omega
      rewrite [wX_write_xreg_equiv _ _ (regidx.Regidx rd) ⟨jal_input.rd.val, Finset.mem_Icc.mpr ⟨h_input_rd_low, h_input_rd_high⟩⟩]
      . simp [execute_JAL_pure_throws]
        simp at h_is_valid
        simp [
          h_is_valid.1,
          execute_JAL_pure_success
        ]
        rewrite [ite_cond_eq_false]
        . rewrite [execute_JAL_pure_nextPC, ite_cond_eq_false]
          . simp [execute_JAL_pure_rd]
            rewrite [dite_cond_eq_false]
            . simp
            . simp [h_is_valid.1]
              split_ands
              . cases h_is_valid.2
                . simp [*]
                . intro h; assumption
              . omega
          . simp [h_is_valid.1]
            cases h_is_valid.2
            . simp [*]
            . intro h; assumption
        . simp
          cases h_is_valid.2
          . simp [*]
          . intro h; assumption
      . simp [this]
  . unfold Local.jump_to_is_valid at h_is_valid
    simp only [
      Nat.ofNat_pos, getElem!_pos, Nat.one_lt_ofNat, Bool.and_eq_true, beq_iff_eq,
      Bool.or_eq_true, not_or, Bool.not_eq_true, not_and_or
    ] at h_is_valid
    by_cases h_throws: ¬BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 jal_input.imm)[0] = 0#1
    . rewrite [execute_JAL_pure_throws, ite_cond_eq_true]
      . simp [
          Local.jump_to, Sail.BitVec.access, Sail.assert, PreSail.assert, h_throws
        ]

        unfold bind Monad.toBind EStateM.instMonad
        dsimp
        unfold EStateM.bind EStateM.pure
        dsimp

        simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]
        rewrite [execute_JAL_pure_nextPC, ite_cond_eq_true]
        . simp
          rewrite [execute_JAL_pure_rd, dite_cond_eq_true]
          . simp
          . simp
            left; left
            exact bit_eq_one_of_not_eq_zero _ h_throws
        . simp
          left
          exact bit_eq_one_of_not_eq_zero _ h_throws
      . simp
        exact bit_eq_one_of_not_eq_zero _ h_throws
    . rewrite [execute_JAL_pure_throws, ite_cond_eq_false]
      . rewrite [execute_JAL_pure_success, ite_cond_eq_true]
        . simp at h_throws
          simp [
            Local.jump_to, Sail.BitVec.access,
            h_throws, Sail.assert, PreSail.assert,
            LeanRV32D.Functions.bit_to_bool, LeanRV32D.Functions.bool_bit_backwards
          ]

          simp [h_throws] at h_is_valid

          unfold bind Monad.toBind EStateM.instMonad
          dsimp
          unfold EStateM.bind EStateM.pure
          dsimp

          rewrite [bit_eq_one_of_not_eq_zero _ h_is_valid.1]
          simp
          have h_misa :
            (write_reg_state state Register.nextPC (jal_input.PC + 4#32)).regs.get? Register.misa =
            .some jal_input.misa :=
            writeReg_read_diff h_input_misa (by trivial)
          rewrite [Local.currentlyEnabled_Zca_of_misa_val h_misa]
          simp [h_is_valid.2]

          rewrite [execute_JAL_pure_nextPC, ite_cond_eq_true]
          . simp
            rewrite [execute_JAL_pure_rd, dite_cond_eq_true]
            . simp
            . simp
              left; right
              split_ands
              . exact bit_eq_one_of_not_eq_zero _ h_is_valid.1
              . exact h_is_valid.2
          . simp
            right
            split_ands
            . exact bit_eq_one_of_not_eq_zero _ h_is_valid.1
            . exact h_is_valid.2
        . simp_all
      . simp_all
