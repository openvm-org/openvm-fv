import Mathlib

import LeanRV32D

-- #eval LeanRV32D.Functions.run_hart_active

lemma readReg_state
  (h: state.regs.get? reg = .some reg_val)
:
  Sail.readReg reg state = EStateM.Result.ok reg_val state
:= by
  unfold Sail.readReg PreSail.readReg
  unfold bind Monad.toBind EStateM.instMonad EStateM.bind EStateM.pure
  dsimp
  obtain ⟨regs⟩ := state
  unfold MonadState.get instMonadStateOfMonadStateOf
  unfold getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get
  dsimp
  dsimp at h
  rewrite [h]
  dsimp

def write_reg_state
  (state: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  (register: Register)
  (value: RegisterType register)
: PreSail.SequentialState RegisterType Sail.trivialChoiceSource := {
    regs := state.regs.insert register value,
    choiceState := state.choiceState,
    mem := state.mem,
    tags := state.tags,
    cycleCount := state.cycleCount,
    sailOutput := state.sailOutput
  }

lemma writeReg_state_success:
  (Sail.writeReg register value state) =
  EStateM.Result.ok PUnit.unit (write_reg_state state register value)
:= by
  unfold Sail.writeReg PreSail.writeReg modify modifyGet instMonadStateOfMonadStateOf
  dsimp
  unfold modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet EStateM.instMonadStateOf EStateM.modifyGet
  dsimp
  rfl

lemma writeReg_read_same
  (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
:
  (write_reg_state state register value).regs.get? register = Option.some value
:= by
  unfold write_reg_state
  grind

lemma writeReg_write_same
  (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
:
  write_reg_state
    (write_reg_state state register value1)
    register
    value2
  =
  write_reg_state state register value2
:= by
  simp [
    write_reg_state,
  ]
  apply Std.ExtDHashMap.ext_get?
  intro reg
  by_cases h: reg = register
  . grind
  . grind

lemma writeReg_read_diff
  (h: state.regs.get? register1 = .some value1)
  (h_neq: register1 ≠ register2)
:
  (write_reg_state state register2 value2).regs.get? register1 = Option.some value1
:= by
  unfold write_reg_state
  grind

lemma sail_assert_eq_pure_of_cond_eq_true :
  c = true → Sail.assert c s =
  pure ()
:= by
  intro h
  rewrite [h]
  rfl

-- Local copies of the RiscV spec so Lean Interactive mode can work better with them
-- Proven equivalent to the original
namespace Local
  def set_next_pc (pc : (BitVec 32)) : SailM Unit := do
    Sail.writeReg Register.nextPC pc

  lemma set_next_pc_equiv :
    LeanRV32D.Functions.set_next_pc = set_next_pc
  := by
    unfold LeanRV32D.Functions.set_next_pc
    unfold set_next_pc
    unfold LeanRV32D.Functions.sail_branch_announce
    rfl

  lemma ext_control_check_pc_equiv:
    LeanRV32D.Functions.ext_control_check_pc =
    λ x => Ext_ControlAddr_Check.Ext_ControlAddr_OK (virtaddr.Virtaddr x)
  := rfl

  lemma bits_of_virtaddr_of_bits {bits: BitVec 32}:
    LeanRV32D.Functions.bits_of_virtaddr (virtaddr.Virtaddr bits) =
    bits
  := rfl

  lemma currentlyEnabled_Zca_of_misa_val
    {misa_val : BitVec 32}
    (h: state.regs.get? Register.misa = .some misa_val)
  :
    LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca state =
    EStateM.Result.ok misa_val[2] state
  := by
    simp [
      LeanRV32D.Functions.currentlyEnabled.eq_def,
      LeanRV32D.Functions.hartSupports.eq_def,
      LeanRV32D.Functions.xlen.eq_def,
      LeanRV32D.Functions.not.eq_def,
      LeanRV32D.Functions._get_Misa_C,
      Sail.BitVec.extractLsb.eq_def,
      BitVec.extractLsb,
      ←BitVec.getElem_eq_extractLsb'
    ]
    unfold Functor.map EStateM.instMonad
    dsimp
    unfold EStateM.map
    dsimp
    rewrite [readReg_state h]
    dsimp

  def jump_to_is_valid (target : BitVec 32) (misa_val : BitVec 32) :=
    (BitVec.ofBool target[0]! == 0#1) && (
      (BitVec.ofBool target[1]! == 0#1) || misa_val[2]
    )

  def jump_to (target : (BitVec 32)) : SailM ExecutionResult := do
    (do
      Sail.assert ((Sail.BitVec.access target 0) == 0#1) "riscv_insts_base.sail:57.38-57.39"
      if (((← (LeanRV32D.Functions.bit_to_bool (Sail.BitVec.access target 1))) && (not
            (← (LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca)))) : Bool)
      then (pure (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr target), (ExceptionType.E_Fetch_Addr_Align ()))))
      else
        (do
          (Sail.writeReg Register.nextPC target)
          (pure LeanRV32D.Functions.RETIRE_SUCCESS)))

  lemma jump_to_equiv :
    jump_to = LeanRV32D.Functions.jump_to
  := rfl

  def jump_to_valid (target : BitVec 32) : SailM ExecutionResult := do
    (Sail.writeReg Register.nextPC target)
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma jump_to_valid_equiv
    {misa_val : BitVec 32}
    (h: state.regs.get? Register.misa = .some misa_val)
    (h_valid : jump_to_is_valid target misa_val)
  :
    jump_to target state =
    jump_to_valid target state
  := by
    unfold jump_to
    unfold jump_to_is_valid at h_valid
    simp at h_valid
    obtain ⟨h_bit_0, h_bit_1⟩ := h_valid

    unfold bind Monad.toBind EStateM.instMonad
    dsimp
    unfold EStateM.bind EStateM.pure
    dsimp

    rewrite [sail_assert_eq_pure_of_cond_eq_true (by simp [Sail.BitVec.access, h_bit_0])]
    simp [Sail.BitVec.access]
    unfold pure EStateM.instMonad EStateM.pure
    dsimp

    simp [
      LeanRV32D.Functions.bit_to_bool,
      LeanRV32D.Functions.bool_bit_backwards
    ]

    match h': (BitVec.ofBool target[1]) with
      | 0#1 =>
        simp [pure, EStateM.pure]
        rewrite [currentlyEnabled_Zca_of_misa_val h]
        dsimp
        rfl
      | 1#1 =>
        simp [pure, EStateM.pure]
        rewrite [currentlyEnabled_Zca_of_misa_val h]
        simp_all
        rfl


  def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
    let link_address ← do (Sail.readReg Register.nextPC)
    match (← (LeanRV32D.Functions.jump_to ((← Sail.readReg Register.PC) + (LeanRV32D.Functions.sign_extend (m := 32) imm)))) with
    | .Retire_Success () =>
      (do
        (LeanRV32D.Functions.wX_bits rd link_address)
        (pure (ExecutionResult.Retire_Success ())))
    | failure => (pure failure)

  lemma execute_jal_equiv :
    execute_JAL = LeanRV32D.Functions.execute_JAL
  := rfl

  def execute_JAL_valid (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := sorry

  -- lemma execute_jal_valid_equiv :
  --   execute_JAL imm rd state =
  --   execute_JAL_valid imm rd state
  -- := by
  --   unfold execute_JAL

  --   unfold bind Monad.toBind EStateM.instMonad
  --   dsimp
  --   unfold EStateM.bind EStateM.pure
  --   dsimp



  -- def execute_JAL' (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do

  lemma get_next_pc_equiv :
    LeanRV32D.Functions.get_next_pc () = Sail.readReg Register.nextPC
  := rfl

  lemma sign_extend_equiv {bv: BitVec width1} :
    @LeanRV32D.Functions.sign_extend width1 width2 bv =
    BitVec.signExtend width2 bv
  := rfl

  -- lemma execute_jal'_equiv
  --   (h_next_pc: state.regs.get? Register.nextPC = .some next_pc_val)
  --   (h_pc: state.regs.get? Register.PC = .some pc_val)
  --   (h_valid_target : (pc_val + BitVec.signExtend 32 imm).getLsb 0 = false)
  -- :
  --   execute_JAL imm rd state = sorry
  --   -- (do
  --   --   match (← (LeanRV32D.Functions.jump_to (pc_val + BitVec.signExtend 32 imm))) with
  --   --   | .Retire_Success () =>
  --   --     (do
  --   --       (LeanRV32D.Functions.wX_bits rd next_pc_val)
  --   --       (pure (ExecutionResult.Retire_Success ())))
  --   --   | failure => (pure failure)) state
  -- := by
  --   unfold execute_JAL

  --   unfold bind Monad.toBind EStateM.instMonad
  --   dsimp
  --   unfold EStateM.bind EStateM.pure
  --   dsimp

  --   rewrite [get_next_pc_equiv]
  --   rewrite [readReg_state h_next_pc]; dsimp
  --   rewrite [readReg_state h_pc]; dsimp
  --   rewrite [sign_extend_equiv]
  --   unfold LeanRV32D.Functions.jump_to
  --   unfold LeanRV32D.Functions.ext_control_check_pc
  --   unfold Sail.assert
  --   unfold PreSail.assert
  --   unfold LeanRV32D.Functions.bits_of_virtaddr
  --   unfold Sail.BitVec.access
  --   unfold LeanRV32D.Functions.bit_to_bool
  --   unfold LeanRV32D.Functions.bool_bit_backwards

  --   unfold bind Monad.toBind EStateM.instMonad
  --   dsimp
  --   unfold EStateM.bind EStateM.pure
  --   dsimp

  --   unfold LeanRV32D.Functions.currentlyEnabled
  --   unfold LeanRV32D.Functions.currentlyEnabled
  --   unfold LeanRV32D.Functions.hartSupports
  --   unfold LeanRV32D.Functions.hartSupports
  --   unfold LeanRV32D.Functions.xlen
  --   unfold LeanRV32D.Functions.not
  --   simp

  --   have : (BitVec.ofBool (pc_val + BitVec.signExtend 32 imm)[0]! == 0#1) = true := by
  --     unfold BitVec.getLsb at h_valid_target
  --     simp_all [BitVec.getElem_eq_testBit_toNat]
  --   rewrite [this]; dsimp


  --   done

  noncomputable def execute (merge_var : instruction) : SailM ExecutionResult := do
    match merge_var with
    | .NTL g__4 => (pure (LeanRV32D.Functions.execute_NTL g__4))
    | .C_NTL g__5 => (pure (LeanRV32D.Functions.execute_C_NTL g__5))
    | .PAUSE arg0 => (pure (LeanRV32D.Functions.execute_PAUSE arg0))
    | .UTYPE (imm, rd, op) => (LeanRV32D.Functions.execute_UTYPE imm rd op)
    | .JAL (imm, rd) => (execute_JAL imm rd)
    | .BTYPE (imm, rs2, rs1, op) => (LeanRV32D.Functions.execute_BTYPE imm rs2 rs1 op)
    | .ITYPE (imm, rs1, rd, op) => (LeanRV32D.Functions.execute_ITYPE imm rs1 rd op)
    | .SHIFTIOP (shamt, rs1, rd, op) => (LeanRV32D.Functions.execute_SHIFTIOP shamt rs1 rd op)
    | .RTYPE (rs2, rs1, rd, op) => (LeanRV32D.Functions.execute_RTYPE rs2 rs1 rd op)
    | .LOAD (imm, rs1, rd, is_unsigned, width) => (LeanRV32D.Functions.execute_LOAD imm rs1 rd is_unsigned width)
    | .STORE (imm, rs2, rs1, width) => (LeanRV32D.Functions.execute_STORE imm rs2 rs1 width)
    | .ADDIW (imm, rs1, rd) => (LeanRV32D.Functions.execute_ADDIW imm rs1 rd)
    | .RTYPEW (rs2, rs1, rd, op) => (LeanRV32D.Functions.execute_RTYPEW rs2 rs1 rd op)
    | .SHIFTIWOP (shamt, rs1, rd, op) => (LeanRV32D.Functions.execute_SHIFTIWOP shamt rs1 rd op)
    | .FENCE (pred, succ) => (LeanRV32D.Functions.execute_FENCE pred succ)
    | .FENCE_TSO arg0 => (LeanRV32D.Functions.execute_FENCE_TSO arg0)
    | .ECALL arg0 => (LeanRV32D.Functions.execute_ECALL arg0)
    | .MRET arg0 => (LeanRV32D.Functions.execute_MRET arg0)
    | .SRET arg0 => (LeanRV32D.Functions.execute_SRET arg0)
    | .EBREAK arg0 => (LeanRV32D.Functions.execute_EBREAK arg0)
    | .WFI arg0 => (LeanRV32D.Functions.execute_WFI arg0)
    | .SFENCE_VMA (rs1, rs2) => (LeanRV32D.Functions.execute_SFENCE_VMA rs1 rs2)
    | .FENCE_RESERVED (fm, pred, succ, rs, rd) => (pure (LeanRV32D.Functions.execute_FENCE_RESERVED fm pred succ rs rd))
    | .FENCEI_RESERVED (imm, rs, rd) => (pure (LeanRV32D.Functions.execute_FENCEI_RESERVED imm rs rd))
    | .JALR (imm, rs1, rd) => (LeanRV32D.Functions.execute_JALR imm rs1 rd)
    | .AMO (op, aq, rl, rs2, rs1, width, rd) => (LeanRV32D.Functions.execute_AMO op aq rl rs2 rs1 width rd)
    | .LOADRES (aq, rl, rs1, width, rd) => (LeanRV32D.Functions.execute_LOADRES aq rl rs1 width rd)
    | .STORECON (aq, rl, rs2, rs1, width, rd) => (LeanRV32D.Functions.execute_STORECON aq rl rs2 rs1 width rd)
    | .MUL (rs2, rs1, rd, mul_op) => (LeanRV32D.Functions.execute_MUL rs2 rs1 rd mul_op)
    | .DIV (rs2, rs1, rd, is_unsigned) => (LeanRV32D.Functions.execute_DIV rs2 rs1 rd is_unsigned)
    | .REM (rs2, rs1, rd, is_unsigned) => (LeanRV32D.Functions.execute_REM rs2 rs1 rd is_unsigned)
    | .MULW (rs2, rs1, rd) => (LeanRV32D.Functions.execute_MULW rs2 rs1 rd)
    | .DIVW (rs2, rs1, rd, is_unsigned) => (LeanRV32D.Functions.execute_DIVW rs2 rs1 rd is_unsigned)
    | .REMW (rs2, rs1, rd, is_unsigned) => (LeanRV32D.Functions.execute_REMW rs2 rs1 rd is_unsigned)
    | .SLLIUW (shamt, rs1, rd) => (LeanRV32D.Functions.execute_SLLIUW shamt rs1 rd)
    | .ZBA_RTYPEUW (rs2, rs1, rd, shamt) => (LeanRV32D.Functions.execute_ZBA_RTYPEUW rs2 rs1 rd shamt)
    | .ZBA_RTYPE (rs2, rs1, rd, shamt) => (LeanRV32D.Functions.execute_ZBA_RTYPE rs2 rs1 rd shamt)
    | .RORIW (shamt, rs1, rd) => (LeanRV32D.Functions.execute_RORIW shamt rs1 rd)
    | .RORI (shamt, rs1, rd) => (LeanRV32D.Functions.execute_RORI shamt rs1 rd)
    | .ZBB_RTYPEW (rs2, rs1, rd, op) => (LeanRV32D.Functions.execute_ZBB_RTYPEW rs2 rs1 rd op)
    | .ZBB_RTYPE (rs2, rs1, rd, op) => (LeanRV32D.Functions.execute_ZBB_RTYPE rs2 rs1 rd op)
    | .ZBB_EXTOP (rs1, rd, op) => (LeanRV32D.Functions.execute_ZBB_EXTOP rs1 rd op)
    | .REV8 (rs1, rd) => (LeanRV32D.Functions.execute_REV8 rs1 rd)
    | .ORCB (rs1, rd) => (LeanRV32D.Functions.execute_ORCB rs1 rd)
    | .CPOP (rs1, rd) => (LeanRV32D.Functions.execute_CPOP rs1 rd)
    | .CPOPW (rs1, rd) => (LeanRV32D.Functions.execute_CPOPW rs1 rd)
    | .CLZ (rs1, rd) => (LeanRV32D.Functions.execute_CLZ rs1 rd)
    | .CLZW (rs1, rd) => (LeanRV32D.Functions.execute_CLZW rs1 rd)
    | .CTZ (rs1, rd) => (LeanRV32D.Functions.execute_CTZ rs1 rd)
    | .CTZW (rs1, rd) => (LeanRV32D.Functions.execute_CTZW rs1 rd)
    | .CLMUL (rs2, rs1, rd) => (LeanRV32D.Functions.execute_CLMUL rs2 rs1 rd)
    | .CLMULH (rs2, rs1, rd) => (LeanRV32D.Functions.execute_CLMULH rs2 rs1 rd)
    | .CLMULR (rs2, rs1, rd) => (LeanRV32D.Functions.execute_CLMULR rs2 rs1 rd)
    | .ZBS_IOP (shamt, rs1, rd, op) => (LeanRV32D.Functions.execute_ZBS_IOP shamt rs1 rd op)
    | .ZBS_RTYPE (rs2, rs1, rd, op) => (LeanRV32D.Functions.execute_ZBS_RTYPE rs2 rs1 rd op)
    | .C_NOP g__6 => (pure (LeanRV32D.Functions.execute_C_NOP g__6))
    | .C_ADDI4SPN (rdc, nzimm) => (LeanRV32D.Functions.execute_C_ADDI4SPN rdc nzimm)
    | .C_LW (uimm, rsc, rdc) => (LeanRV32D.Functions.execute_C_LW uimm rsc rdc)
    | .C_LD (uimm, rsc, rdc) => (LeanRV32D.Functions.execute_C_LD uimm rsc rdc)
    | .C_SW (uimm, rsc1, rsc2) => (LeanRV32D.Functions.execute_C_SW uimm rsc1 rsc2)
    | .C_SD (uimm, rsc1, rsc2) => (LeanRV32D.Functions.execute_C_SD uimm rsc1 rsc2)
    | .C_ADDI (imm, rsd) => (LeanRV32D.Functions.execute_C_ADDI imm rsd)
    | .C_JAL imm => (LeanRV32D.Functions.execute_C_JAL imm)
    | .C_ADDIW (imm, rsd) => (LeanRV32D.Functions.execute_C_ADDIW imm rsd)
    | .C_LI (imm, rd) => (LeanRV32D.Functions.execute_C_LI imm rd)
    | .C_ADDI16SP imm => (LeanRV32D.Functions.execute_C_ADDI16SP imm)
    | .C_LUI (imm, rd) => (LeanRV32D.Functions.execute_C_LUI imm rd)
    | .C_SRLI (shamt, rsd) => (LeanRV32D.Functions.execute_C_SRLI shamt rsd)
    | .C_SRAI (shamt, rsd) => (LeanRV32D.Functions.execute_C_SRAI shamt rsd)
    | .C_ANDI (imm, rsd) => (LeanRV32D.Functions.execute_C_ANDI imm rsd)
    | .C_SUB (rsd, rs2) => (LeanRV32D.Functions.execute_C_SUB rsd rs2)
    | .C_XOR (rsd, rs2) => (LeanRV32D.Functions.execute_C_XOR rsd rs2)
    | .C_OR (rsd, rs2) => (LeanRV32D.Functions.execute_C_OR rsd rs2)
    | .C_AND (rsd, rs2) => (LeanRV32D.Functions.execute_C_AND rsd rs2)
    | .C_SUBW (rsd, rs2) => (LeanRV32D.Functions.execute_C_SUBW rsd rs2)
    | .C_ADDW (rsd, rs2) => (LeanRV32D.Functions.execute_C_ADDW rsd rs2)
    | .C_J imm => (LeanRV32D.Functions.execute_C_J imm)
    | .C_BEQZ (imm, rs) => (LeanRV32D.Functions.execute_C_BEQZ imm rs)
    | .C_BNEZ (imm, rs) => (LeanRV32D.Functions.execute_C_BNEZ imm rs)
    | .C_SLLI (shamt, rsd) => (LeanRV32D.Functions.execute_C_SLLI shamt rsd)
    | .C_LWSP (uimm, rd) => (LeanRV32D.Functions.execute_C_LWSP uimm rd)
    | .C_LDSP (uimm, rd) => (LeanRV32D.Functions.execute_C_LDSP uimm rd)
    | .C_SWSP (uimm, rs2) => (LeanRV32D.Functions.execute_C_SWSP uimm rs2)
    | .C_SDSP (uimm, rs2) => (LeanRV32D.Functions.execute_C_SDSP uimm rs2)
    | .C_JR rs1 => (LeanRV32D.Functions.execute_C_JR rs1)
    | .C_JALR rs1 => (LeanRV32D.Functions.execute_C_JALR rs1)
    | .C_MV (rd, rs2) => (LeanRV32D.Functions.execute_C_MV rd rs2)
    | .C_EBREAK arg0 => (LeanRV32D.Functions.execute_C_EBREAK arg0)
    | .C_ADD (rsd, rs2) => (LeanRV32D.Functions.execute_C_ADD rsd rs2)
    | .C_LBU (uimm, rdc, rsc1) => (LeanRV32D.Functions.execute_C_LBU uimm rdc rsc1)
    | .C_LHU (uimm, rdc, rsc1) => (LeanRV32D.Functions.execute_C_LHU uimm rdc rsc1)
    | .C_LH (uimm, rdc, rsc1) => (LeanRV32D.Functions.execute_C_LH uimm rdc rsc1)
    | .C_SB (uimm, rsc1, rsc2) => (LeanRV32D.Functions.execute_C_SB uimm rsc1 rsc2)
    | .C_SH (uimm, rsc1, rsc2) => (LeanRV32D.Functions.execute_C_SH uimm rsc1 rsc2)
    | .C_ZEXT_B rsdc => (LeanRV32D.Functions.execute_C_ZEXT_B rsdc)
    | .C_SEXT_B rsdc => (LeanRV32D.Functions.execute_C_SEXT_B rsdc)
    | .C_ZEXT_H rsdc => (LeanRV32D.Functions.execute_C_ZEXT_H rsdc)
    | .C_SEXT_H rsdc => (LeanRV32D.Functions.execute_C_SEXT_H rsdc)
    | .C_ZEXT_W rsdc => (LeanRV32D.Functions.execute_C_ZEXT_W rsdc)
    | .C_NOT rsdc => (LeanRV32D.Functions.execute_C_NOT rsdc)
    | .C_MUL (rsdc, rsc2) => (LeanRV32D.Functions.execute_C_MUL rsdc rsc2)
    | .LOAD_FP (imm, rs1, rd, width) => (LeanRV32D.Functions.execute_LOAD_FP imm rs1 rd width)
    | .STORE_FP (imm, rs2, rs1, width) => (LeanRV32D.Functions.execute_STORE_FP imm rs2 rs1 width)
    | .F_MADD_TYPE_S (rs3, rs2, rs1, rm, rd, op) => (LeanRV32D.Functions.execute_F_MADD_TYPE_S rs3 rs2 rs1 rm rd op)
    | .F_BIN_RM_TYPE_S (rs2, rs1, rm, rd, op) => (LeanRV32D.Functions.execute_F_BIN_RM_TYPE_S rs2 rs1 rm rd op)
    | .F_UN_RM_FF_TYPE_S (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_FF_TYPE_S rs1 rm rd arg3)
    | .F_UN_RM_FX_TYPE_S (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_FX_TYPE_S rs1 rm rd arg3)
    | .F_UN_RM_XF_TYPE_S (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_XF_TYPE_S rs1 rm rd arg3)
    | .F_BIN_TYPE_F_S (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_F_BIN_TYPE_F_S rs2 rs1 rd arg3)
    | .F_BIN_TYPE_X_S (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_F_BIN_TYPE_X_S rs2 rs1 rd arg3)
    | .F_UN_TYPE_X_S (rs1, rd, arg2) => (LeanRV32D.Functions.execute_F_UN_TYPE_X_S rs1 rd arg2)
    | .F_UN_TYPE_F_S (rs1, rd, arg2) => (LeanRV32D.Functions.execute_F_UN_TYPE_F_S rs1 rd arg2)
    | .C_FLWSP (imm, rd) => (LeanRV32D.Functions.execute_C_FLWSP imm rd)
    | .C_FSWSP (uimm, rs2) => (LeanRV32D.Functions.execute_C_FSWSP uimm rs2)
    | .C_FLW (uimm, rsc, rdc) => (LeanRV32D.Functions.execute_C_FLW uimm rsc rdc)
    | .C_FSW (uimm, rsc1, rsc2) => (LeanRV32D.Functions.execute_C_FSW uimm rsc1 rsc2)
    | .F_MADD_TYPE_D (rs3, rs2, rs1, rm, rd, op) => (LeanRV32D.Functions.execute_F_MADD_TYPE_D rs3 rs2 rs1 rm rd op)
    | .F_BIN_RM_TYPE_D (rs2, rs1, rm, rd, op) => (LeanRV32D.Functions.execute_F_BIN_RM_TYPE_D rs2 rs1 rm rd op)
    | .F_UN_RM_FF_TYPE_D (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_FF_TYPE_D rs1 rm rd arg3)
    | .F_UN_RM_FX_TYPE_D (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_FX_TYPE_D rs1 rm rd arg3)
    | .F_UN_RM_XF_TYPE_D (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_XF_TYPE_D rs1 rm rd arg3)
    | .F_BIN_F_TYPE_D (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_F_BIN_F_TYPE_D rs2 rs1 rd arg3)
    | .F_BIN_X_TYPE_D (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_F_BIN_X_TYPE_D rs2 rs1 rd arg3)
    | .F_UN_X_TYPE_D (rs1, rd, arg2) => (LeanRV32D.Functions.execute_F_UN_X_TYPE_D rs1 rd arg2)
    | .F_UN_F_TYPE_D (rs1, rd, arg2) => (LeanRV32D.Functions.execute_F_UN_F_TYPE_D rs1 rd arg2)
    | .C_FLDSP (uimm, rd) => (LeanRV32D.Functions.execute_C_FLDSP uimm rd)
    | .C_FSDSP (uimm, rs2) => (LeanRV32D.Functions.execute_C_FSDSP uimm rs2)
    | .C_FLD (uimm, rsc, rdc) => (LeanRV32D.Functions.execute_C_FLD uimm rsc rdc)
    | .C_FSD (uimm, rsc1, rsc2) => (LeanRV32D.Functions.execute_C_FSD uimm rsc1 rsc2)
    | .F_BIN_RM_TYPE_H (rs2, rs1, rm, rd, op) => (LeanRV32D.Functions.execute_F_BIN_RM_TYPE_H rs2 rs1 rm rd op)
    | .F_MADD_TYPE_H (rs3, rs2, rs1, rm, rd, op) => (LeanRV32D.Functions.execute_F_MADD_TYPE_H rs3 rs2 rs1 rm rd op)
    | .F_BIN_F_TYPE_H (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_F_BIN_F_TYPE_H rs2 rs1 rd arg3)
    | .F_BIN_X_TYPE_H (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_F_BIN_X_TYPE_H rs2 rs1 rd arg3)
    | .F_UN_RM_FF_TYPE_H (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_FF_TYPE_H rs1 rm rd arg3)
    | .F_UN_RM_FX_TYPE_H (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_FX_TYPE_H rs1 rm rd arg3)
    | .F_UN_RM_XF_TYPE_H (rs1, rm, rd, arg3) => (LeanRV32D.Functions.execute_F_UN_RM_XF_TYPE_H rs1 rm rd arg3)
    | .F_UN_X_TYPE_H (rs1, rd, arg2) => (LeanRV32D.Functions.execute_F_UN_X_TYPE_H rs1 rd arg2)
    | .F_UN_F_TYPE_H (rs1, rd, arg2) => (LeanRV32D.Functions.execute_F_UN_F_TYPE_H rs1 rd arg2)
    | .FLI_H (constantidx, rd) => (LeanRV32D.Functions.execute_FLI_H constantidx rd)
    | .FLI_S (constantidx, rd) => (LeanRV32D.Functions.execute_FLI_S constantidx rd)
    | .FLI_D (constantidx, rd) => (LeanRV32D.Functions.execute_FLI_D constantidx rd)
    | .FMINM_H (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMINM_H rs2 rs1 rd)
    | .FMAXM_H (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMAXM_H rs2 rs1 rd)
    | .FMINM_S (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMINM_S rs2 rs1 rd)
    | .FMAXM_S (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMAXM_S rs2 rs1 rd)
    | .FMINM_D (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMINM_D rs2 rs1 rd)
    | .FMAXM_D (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMAXM_D rs2 rs1 rd)
    | .FROUND_H (rs1, rm, rd) => (LeanRV32D.Functions.execute_FROUND_H rs1 rm rd)
    | .FROUNDNX_H (rs1, rm, rd) => (LeanRV32D.Functions.execute_FROUNDNX_H rs1 rm rd)
    | .FROUND_S (rs1, rm, rd) => (LeanRV32D.Functions.execute_FROUND_S rs1 rm rd)
    | .FROUNDNX_S (rs1, rm, rd) => (LeanRV32D.Functions.execute_FROUNDNX_S rs1 rm rd)
    | .FROUND_D (rs1, rm, rd) => (LeanRV32D.Functions.execute_FROUND_D rs1 rm rd)
    | .FROUNDNX_D (rs1, rm, rd) => (LeanRV32D.Functions.execute_FROUNDNX_D rs1 rm rd)
    | .FMVH_X_D (rs1, rd) => (LeanRV32D.Functions.execute_FMVH_X_D rs1 rd)
    | .FMVP_D_X (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FMVP_D_X rs2 rs1 rd)
    | .FLEQ_H (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FLEQ_H rs2 rs1 rd)
    | .FLTQ_H (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FLTQ_H rs2 rs1 rd)
    | .FLEQ_S (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FLEQ_S rs2 rs1 rd)
    | .FLTQ_S (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FLTQ_S rs2 rs1 rd)
    | .FLEQ_D (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FLEQ_D rs2 rs1 rd)
    | .FLTQ_D (rs2, rs1, rd) => (LeanRV32D.Functions.execute_FLTQ_D rs2 rs1 rd)
    | .FCVTMOD_W_D (rs1, rd) => (LeanRV32D.Functions.execute_FCVTMOD_W_D rs1 rd)
    | .VSETVLI (ma, ta, sew, lmul, rs1, rd) => (LeanRV32D.Functions.execute_VSETVLI ma ta sew lmul rs1 rd)
    | .VSETVL (rs2, rs1, rd) => (LeanRV32D.Functions.execute_VSETVL rs2 rs1 rd)
    | .VSETIVLI (ma, ta, sew, lmul, uimm, rd) => (LeanRV32D.Functions.execute_VSETIVLI ma ta sew lmul uimm rd)
    | .VVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VVTYPE funct6 vm vs2 vs1 vd)
    | .NVSTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_NVSTYPE funct6 vm vs2 vs1 vd)
    | .NVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_NVTYPE funct6 vm vs2 vs1 vd)
    | .MASKTYPEV (vs2, vs1, vd) => (LeanRV32D.Functions.execute_MASKTYPEV vs2 vs1 vd)
    | .MOVETYPEV (vs1, vd) => (LeanRV32D.Functions.execute_MOVETYPEV vs1 vd)
    | .VXTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VXTYPE funct6 vm vs2 rs1 vd)
    | .NXSTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_NXSTYPE funct6 vm vs2 rs1 vd)
    | .NXTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_NXTYPE funct6 vm vs2 rs1 vd)
    | .VXSG (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VXSG funct6 vm vs2 rs1 vd)
    | .MASKTYPEX (vs2, rs1, vd) => (LeanRV32D.Functions.execute_MASKTYPEX vs2 rs1 vd)
    | .MOVETYPEX (rs1, vd) => (LeanRV32D.Functions.execute_MOVETYPEX rs1 vd)
    | .VITYPE (funct6, vm, vs2, simm, vd) => (LeanRV32D.Functions.execute_VITYPE funct6 vm vs2 simm vd)
    | .NISTYPE (funct6, vm, vs2, uimm, vd) => (LeanRV32D.Functions.execute_NISTYPE funct6 vm vs2 uimm vd)
    | .NITYPE (funct6, vm, vs2, uimm, vd) => (LeanRV32D.Functions.execute_NITYPE funct6 vm vs2 uimm vd)
    | .VISG (funct6, vm, vs2, simm, vd) => (LeanRV32D.Functions.execute_VISG funct6 vm vs2 simm vd)
    | .MASKTYPEI (vs2, simm, vd) => (LeanRV32D.Functions.execute_MASKTYPEI vs2 simm vd)
    | .MOVETYPEI (vd, simm) => (LeanRV32D.Functions.execute_MOVETYPEI vd simm)
    | .VMVRTYPE (vs2, nreg, vd) => (LeanRV32D.Functions.execute_VMVRTYPE vs2 nreg vd)
    | .MVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_MVVTYPE funct6 vm vs2 vs1 vd)
    | .MVVMATYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_MVVMATYPE funct6 vm vs2 vs1 vd)
    | .WVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_WVVTYPE funct6 vm vs2 vs1 vd)
    | .WVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_WVTYPE funct6 vm vs2 vs1 vd)
    | .WMVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_WMVVTYPE funct6 vm vs2 vs1 vd)
    | .VEXTTYPE (funct6, vm, vs2, vd) => (LeanRV32D.Functions.execute_VEXTTYPE funct6 vm vs2 vd)
    | .VMVXS (vs2, rd) => (LeanRV32D.Functions.execute_VMVXS vs2 rd)
    | .MVVCOMPRESS (vs2, vs1, vd) => (LeanRV32D.Functions.execute_MVVCOMPRESS vs2 vs1 vd)
    | .MVXTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_MVXTYPE funct6 vm vs2 rs1 vd)
    | .MVXMATYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_MVXMATYPE funct6 vm vs2 rs1 vd)
    | .WVXTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_WVXTYPE funct6 vm vs2 rs1 vd)
    | .WXTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_WXTYPE funct6 vm vs2 rs1 vd)
    | .WMVXTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_WMVXTYPE funct6 vm vs2 rs1 vd)
    | .VMVSX (rs1, vd) => (LeanRV32D.Functions.execute_VMVSX rs1 vd)
    | .FVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_FVVTYPE funct6 vm vs2 vs1 vd)
    | .FVVMATYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_FVVMATYPE funct6 vm vs2 vs1 vd)
    | .FWVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_FWVVTYPE funct6 vm vs2 vs1 vd)
    | .FWVVMATYPE (funct6, vm, vs1, vs2, vd) => (LeanRV32D.Functions.execute_FWVVMATYPE funct6 vm vs1 vs2 vd)
    | .FWVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_FWVTYPE funct6 vm vs2 vs1 vd)
    | .VFUNARY0 (vm, vs2, vfunary0, vd) => (LeanRV32D.Functions.execute_VFUNARY0 vm vs2 vfunary0 vd)
    | .VFWUNARY0 (vm, vs2, vfwunary0, vd) => (LeanRV32D.Functions.execute_VFWUNARY0 vm vs2 vfwunary0 vd)
    | .VFNUNARY0 (vm, vs2, vfnunary0, vd) => (LeanRV32D.Functions.execute_VFNUNARY0 vm vs2 vfnunary0 vd)
    | .VFUNARY1 (vm, vs2, vfunary1, vd) => (LeanRV32D.Functions.execute_VFUNARY1 vm vs2 vfunary1 vd)
    | .VFMVFS (vs2, rd) => (LeanRV32D.Functions.execute_VFMVFS vs2 rd)
    | .FVFTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_FVFTYPE funct6 vm vs2 rs1 vd)
    | .FVFMATYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_FVFMATYPE funct6 vm vs2 rs1 vd)
    | .FWVFTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_FWVFTYPE funct6 vm vs2 rs1 vd)
    | .FWVFMATYPE (funct6, vm, rs1, vs2, vd) => (LeanRV32D.Functions.execute_FWVFMATYPE funct6 vm rs1 vs2 vd)
    | .FWFTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_FWFTYPE funct6 vm vs2 rs1 vd)
    | .VFMERGE (vs2, rs1, vd) => (LeanRV32D.Functions.execute_VFMERGE vs2 rs1 vd)
    | .VFMV (rs1, vd) => (LeanRV32D.Functions.execute_VFMV rs1 vd)
    | .VFMVSF (rs1, vd) => (LeanRV32D.Functions.execute_VFMVSF rs1 vd)
    | .VLSEGTYPE (nf, vm, rs1, width, vd) => (LeanRV32D.Functions.execute_VLSEGTYPE nf vm rs1 width vd)
    | .VLSEGFFTYPE (nf, vm, rs1, width, vd) => (LeanRV32D.Functions.execute_VLSEGFFTYPE nf vm rs1 width vd)
    | .VSSEGTYPE (nf, vm, rs1, width, vs3) => (LeanRV32D.Functions.execute_VSSEGTYPE nf vm rs1 width vs3)
    | .VLSSEGTYPE (nf, vm, rs2, rs1, width, vd) => (LeanRV32D.Functions.execute_VLSSEGTYPE nf vm rs2 rs1 width vd)
    | .VSSSEGTYPE (nf, vm, rs2, rs1, width, vs3) => (LeanRV32D.Functions.execute_VSSSEGTYPE nf vm rs2 rs1 width vs3)
    | .VLUXSEGTYPE (nf, vm, vs2, rs1, width, vd) => (LeanRV32D.Functions.execute_VLUXSEGTYPE nf vm vs2 rs1 width vd)
    | .VLOXSEGTYPE (nf, vm, vs2, rs1, width, vd) => (LeanRV32D.Functions.execute_VLOXSEGTYPE nf vm vs2 rs1 width vd)
    | .VSUXSEGTYPE (nf, vm, vs2, rs1, width, vs3) => (LeanRV32D.Functions.execute_VSUXSEGTYPE nf vm vs2 rs1 width vs3)
    | .VSOXSEGTYPE (nf, vm, vs2, rs1, width, vs3) => (LeanRV32D.Functions.execute_VSOXSEGTYPE nf vm vs2 rs1 width vs3)
    | .VLRETYPE (nf, rs1, width, vd) => (LeanRV32D.Functions.execute_VLRETYPE nf rs1 width vd)
    | .VSRETYPE (nf, rs1, vs3) => (LeanRV32D.Functions.execute_VSRETYPE nf rs1 vs3)
    | .VMTYPE (rs1, vd_or_vs3, op) => (LeanRV32D.Functions.execute_VMTYPE rs1 vd_or_vs3 op)
    | .MMTYPE (funct6, vs2, vs1, vd) => (LeanRV32D.Functions.execute_MMTYPE funct6 vs2 vs1 vd)
    | .VCPOP_M (vm, vs2, rd) => (LeanRV32D.Functions.execute_VCPOP_M vm vs2 rd)
    | .VFIRST_M (vm, vs2, rd) => (LeanRV32D.Functions.execute_VFIRST_M vm vs2 rd)
    | .VMSBF_M (vm, vs2, vd) => (LeanRV32D.Functions.execute_VMSBF_M vm vs2 vd)
    | .VMSIF_M (vm, vs2, vd) => (LeanRV32D.Functions.execute_VMSIF_M vm vs2 vd)
    | .VMSOF_M (vm, vs2, vd) => (LeanRV32D.Functions.execute_VMSOF_M vm vs2 vd)
    | .VIOTA_M (vm, vs2, vd) => (LeanRV32D.Functions.execute_VIOTA_M vm vs2 vd)
    | .VID_V (vm, vd) => (LeanRV32D.Functions.execute_VID_V vm vd)
    | .VVMTYPE (funct6, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VVMTYPE funct6 vs2 vs1 vd)
    | .VVMCTYPE (funct6, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VVMCTYPE funct6 vs2 vs1 vd)
    | .VVMSTYPE (funct6, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VVMSTYPE funct6 vs2 vs1 vd)
    | .VVCMPTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VVCMPTYPE funct6 vm vs2 vs1 vd)
    | .VXMTYPE (funct6, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VXMTYPE funct6 vs2 rs1 vd)
    | .VXMCTYPE (funct6, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VXMCTYPE funct6 vs2 rs1 vd)
    | .VXMSTYPE (funct6, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VXMSTYPE funct6 vs2 rs1 vd)
    | .VXCMPTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VXCMPTYPE funct6 vm vs2 rs1 vd)
    | .VIMTYPE (funct6, vs2, simm, vd) => (LeanRV32D.Functions.execute_VIMTYPE funct6 vs2 simm vd)
    | .VIMCTYPE (funct6, vs2, simm, vd) => (LeanRV32D.Functions.execute_VIMCTYPE funct6 vs2 simm vd)
    | .VIMSTYPE (funct6, vs2, simm, vd) => (LeanRV32D.Functions.execute_VIMSTYPE funct6 vs2 simm vd)
    | .VICMPTYPE (funct6, vm, vs2, simm, vd) => (LeanRV32D.Functions.execute_VICMPTYPE funct6 vm vs2 simm vd)
    | .FVVMTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_FVVMTYPE funct6 vm vs2 vs1 vd)
    | .FVFMTYPE (funct6, vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_FVFMTYPE funct6 vm vs2 rs1 vd)
    | .RIVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_RIVVTYPE funct6 vm vs2 vs1 vd)
    | .RMVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_RMVVTYPE funct6 vm vs2 vs1 vd)
    | .RFVVTYPE (funct6, vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_RFVVTYPE funct6 vm vs2 vs1 vd)
    | .SHA256SIG0 (rs1, rd) => (LeanRV32D.Functions.execute_SHA256SIG0 rs1 rd)
    | .SHA256SIG1 (rs1, rd) => (LeanRV32D.Functions.execute_SHA256SIG1 rs1 rd)
    | .SHA256SUM0 (rs1, rd) => (LeanRV32D.Functions.execute_SHA256SUM0 rs1 rd)
    | .SHA256SUM1 (rs1, rd) => (LeanRV32D.Functions.execute_SHA256SUM1 rs1 rd)
    | .AES32ESMI (bs, rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES32ESMI bs rs2 rs1 rd)
    | .AES32ESI (bs, rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES32ESI bs rs2 rs1 rd)
    | .AES32DSMI (bs, rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES32DSMI bs rs2 rs1 rd)
    | .AES32DSI (bs, rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES32DSI bs rs2 rs1 rd)
    | .SHA512SIG0H (rs2, rs1, rd) => (LeanRV32D.Functions.execute_SHA512SIG0H rs2 rs1 rd)
    | .SHA512SIG0L (rs2, rs1, rd) => (LeanRV32D.Functions.execute_SHA512SIG0L rs2 rs1 rd)
    | .SHA512SIG1H (rs2, rs1, rd) => (LeanRV32D.Functions.execute_SHA512SIG1H rs2 rs1 rd)
    | .SHA512SIG1L (rs2, rs1, rd) => (LeanRV32D.Functions.execute_SHA512SIG1L rs2 rs1 rd)
    | .SHA512SUM0R (rs2, rs1, rd) => (LeanRV32D.Functions.execute_SHA512SUM0R rs2 rs1 rd)
    | .SHA512SUM1R (rs2, rs1, rd) => (LeanRV32D.Functions.execute_SHA512SUM1R rs2 rs1 rd)
    | .AES64KS1I (rnum, rs1, rd) => (LeanRV32D.Functions.execute_AES64KS1I rnum rs1 rd)
    | .AES64KS2 (rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES64KS2 rs2 rs1 rd)
    | .AES64IM (rs1, rd) => (LeanRV32D.Functions.execute_AES64IM rs1 rd)
    | .AES64ESM (rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES64ESM rs2 rs1 rd)
    | .AES64ES (rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES64ES rs2 rs1 rd)
    | .AES64DSM (rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES64DSM rs2 rs1 rd)
    | .AES64DS (rs2, rs1, rd) => (LeanRV32D.Functions.execute_AES64DS rs2 rs1 rd)
    | .SHA512SIG0 (rs1, rd) => (LeanRV32D.Functions.execute_SHA512SIG0 rs1 rd)
    | .SHA512SIG1 (rs1, rd) => (LeanRV32D.Functions.execute_SHA512SIG1 rs1 rd)
    | .SHA512SUM0 (rs1, rd) => (LeanRV32D.Functions.execute_SHA512SUM0 rs1 rd)
    | .SHA512SUM1 (rs1, rd) => (LeanRV32D.Functions.execute_SHA512SUM1 rs1 rd)
    | .SM3P0 (rs1, rd) => (LeanRV32D.Functions.execute_SM3P0 rs1 rd)
    | .SM3P1 (rs1, rd) => (LeanRV32D.Functions.execute_SM3P1 rs1 rd)
    | .SM4ED (bs, rs2, rs1, rd) => (LeanRV32D.Functions.execute_SM4ED bs rs2 rs1 rd)
    | .SM4KS (bs, rs2, rs1, rd) => (LeanRV32D.Functions.execute_SM4KS bs rs2 rs1 rd)
    | .ZBKB_RTYPE (rs2, rs1, rd, op) => (LeanRV32D.Functions.execute_ZBKB_RTYPE rs2 rs1 rd op)
    | .ZBKB_PACKW (rs2, rs1, rd) => (LeanRV32D.Functions.execute_ZBKB_PACKW rs2 rs1 rd)
    | .ZIP (rs1, rd) => (LeanRV32D.Functions.execute_ZIP rs1 rd)
    | .UNZIP (rs1, rd) => (LeanRV32D.Functions.execute_UNZIP rs1 rd)
    | .BREV8 (rs1, rd) => (LeanRV32D.Functions.execute_BREV8 rs1 rd)
    | .XPERM8 (rs2, rs1, rd) => (LeanRV32D.Functions.execute_XPERM8 rs2 rs1 rd)
    | .XPERM4 (rs2, rs1, rd) => (LeanRV32D.Functions.execute_XPERM4 rs2 rs1 rd)
    | .VANDN_VV (vm, vs1, vs2, vd) => (LeanRV32D.Functions.execute_VANDN_VV vm vs1 vs2 vd)
    | .VANDN_VX (vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VANDN_VX vm vs2 rs1 vd)
    | .VBREV_V (vm, vs2, vd) => (LeanRV32D.Functions.execute_VBREV_V vm vs2 vd)
    | .VBREV8_V (vm, vs2, vd) => (LeanRV32D.Functions.execute_VBREV8_V vm vs2 vd)
    | .VREV8_V (vm, vs2, vd) => (LeanRV32D.Functions.execute_VREV8_V vm vs2 vd)
    | .VCLZ_V (vm, vs2, vd) => (LeanRV32D.Functions.execute_VCLZ_V vm vs2 vd)
    | .VCTZ_V (vm, vs2, vd) => (LeanRV32D.Functions.execute_VCTZ_V vm vs2 vd)
    | .VCPOP_V (vm, vs2, vd) => (LeanRV32D.Functions.execute_VCPOP_V vm vs2 vd)
    | .VROL_VV (vm, vs1, vs2, vd) => (LeanRV32D.Functions.execute_VROL_VV vm vs1 vs2 vd)
    | .VROL_VX (vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VROL_VX vm vs2 rs1 vd)
    | .VROR_VV (vm, vs1, vs2, vd) => (LeanRV32D.Functions.execute_VROR_VV vm vs1 vs2 vd)
    | .VROR_VX (vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VROR_VX vm vs2 rs1 vd)
    | .VROR_VI (vm, vs2, uimm, vd) => (LeanRV32D.Functions.execute_VROR_VI vm vs2 uimm vd)
    | .VWSLL_VV (vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VWSLL_VV vm vs2 vs1 vd)
    | .VWSLL_VX (vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VWSLL_VX vm vs2 rs1 vd)
    | .VWSLL_VI (vm, vs2, uimm, vd) => (LeanRV32D.Functions.execute_VWSLL_VI vm vs2 uimm vd)
    | .VCLMUL_VV (vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VCLMUL_VV vm vs2 vs1 vd)
    | .VCLMUL_VX (vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VCLMUL_VX vm vs2 rs1 vd)
    | .VCLMULH_VV (vm, vs2, vs1, vd) => (LeanRV32D.Functions.execute_VCLMULH_VV vm vs2 vs1 vd)
    | .VCLMULH_VX (vm, vs2, rs1, vd) => (LeanRV32D.Functions.execute_VCLMULH_VX vm vs2 rs1 vd)
    | .VGHSH_VV (vs2, vs1, vd) => (LeanRV32D.Functions.execute_VGHSH_VV vs2 vs1 vd)
    | .VGMUL_VV (vs2, vd) => (LeanRV32D.Functions.execute_VGMUL_VV vs2 vd)
    | .VAESDF (funct6, vs2, vd) => (LeanRV32D.Functions.execute_VAESDF funct6 vs2 vd)
    | .VAESDM (funct6, vs2, vd) => (LeanRV32D.Functions.execute_VAESDM funct6 vs2 vd)
    | .VAESEF (funct6, vs2, vd) => (LeanRV32D.Functions.execute_VAESEF funct6 vs2 vd)
    | .VAESEM (funct6, vs2, vd) => (LeanRV32D.Functions.execute_VAESEM funct6 vs2 vd)
    | .VAESKF1_VI (vs2, rnd, vd) => (LeanRV32D.Functions.execute_VAESKF1_VI vs2 rnd vd)
    | .VAESKF2_VI (vs2, rnd, vd) => (LeanRV32D.Functions.execute_VAESKF2_VI vs2 rnd vd)
    | .VAESZ_VS (vs2, vd) => (LeanRV32D.Functions.execute_VAESZ_VS vs2 vd)
    | .VSM4K_VI (vs2, uimm, vd) => (LeanRV32D.Functions.execute_VSM4K_VI vs2 uimm vd)
    | .ZVKSM4RTYPE (funct6, vs2, vd) => (LeanRV32D.Functions.execute_ZVKSM4RTYPE funct6 vs2 vd)
    | .VSHA2MS_VV (vs2, vs1, vd) => (LeanRV32D.Functions.execute_VSHA2MS_VV vs2 vs1 vd)
    | .ZVKSHA2TYPE (funct6, vs2, vs1, vd) => (LeanRV32D.Functions.execute_ZVKSHA2TYPE funct6 vs2 vs1 vd)
    | .VSM3ME_VV (vs2, vs1, vd) => (LeanRV32D.Functions.execute_VSM3ME_VV vs2 vs1 vd)
    | .VSM3C_VI (vs2, uimm, vd) => (LeanRV32D.Functions.execute_VSM3C_VI vs2 uimm vd)
    | .CSRReg (csr, rs1, rd, op) => (LeanRV32D.Functions.execute_CSRReg csr rs1 rd op)
    | .CSRImm (csr, imm, rd, op) => (LeanRV32D.Functions.execute_CSRImm csr imm rd op)
    | .SINVAL_VMA (rs1, rs2) => (LeanRV32D.Functions.execute_SINVAL_VMA rs1 rs2)
    | .SFENCE_W_INVAL arg0 => (LeanRV32D.Functions.execute_SFENCE_W_INVAL arg0)
    | .SFENCE_INVAL_IR arg0 => (LeanRV32D.Functions.execute_SFENCE_INVAL_IR arg0)
    | .WRS arg0 => (pure (LeanRV32D.Functions.execute_WRS arg0))
    | .ZICOND_RTYPE (rs2, rs1, rd, arg3) => (LeanRV32D.Functions.execute_ZICOND_RTYPE rs2 rs1 rd arg3)
    | .ZICBOM (arg0, rs1) => (LeanRV32D.Functions.execute_ZICBOM arg0 rs1)
    | .ZICBOZ rs1 => (LeanRV32D.Functions.execute_ZICBOZ rs1)
    | .FENCEI arg0 => (pure (LeanRV32D.Functions.execute_FENCEI arg0))
    | .ZIMOP_MOP_R (mop, rs1, rd) => (LeanRV32D.Functions.execute_ZIMOP_MOP_R mop rs1 rd)
    | .ZIMOP_MOP_RR (mop, rs2, rs1, rd) => (LeanRV32D.Functions.execute_ZIMOP_MOP_RR mop rs2 rs1 rd)
    | .ZCMOP mop => (pure (LeanRV32D.Functions.execute_ZCMOP mop))
    | .ILLEGAL s => (pure (LeanRV32D.Functions.execute_ILLEGAL s))
    | .C_ILLEGAL s => (pure (LeanRV32D.Functions.execute_C_ILLEGAL s))

  lemma execute_equiv :
    execute = LeanRV32D.Functions.execute
  := rfl

  /-- Type quantifiers: step_no : Nat, 0 ≤ step_no -/
  noncomputable def run_hart_active (step_no : Nat) : SailM Step := do
    match (← (LeanRV32D.Functions.dispatchInterrupt (← Sail.readReg Register.cur_privilege))) with
    | .some (intr, priv) => (pure (Step.Step_Pending_Interrupt (intr, priv)))
    | none =>
      (do
        match (LeanRV32D.Functions.ext_fetch_hook (← (LeanRV32D.Functions.fetch ()))) with
        | .F_Ext_Error e => (pure (Step.Step_Ext_Fetch_Failure e))
        | .F_Error (e, addr) => (pure (Step.Step_Fetch_Failure ((virtaddr.Virtaddr addr), e)))
        | .F_RVC h =>
          (do
            let _ : Unit := (LeanRV32D.Functions.sail_instr_announce h)
            let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) h)
            let instruction ← do (LeanRV32D.Functions.ext_decode_compressed h)
            if ((LeanRV32D.Functions.get_config_print_instr ()) : Bool)
            then
              (pure (LeanRV32D.Functions.print_log_instr
                  (HAppend.hAppend "["
                    (HAppend.hAppend (Int.repr step_no)
                      (HAppend.hAppend "] ["
                        (HAppend.hAppend (LeanRV32D.Functions.privLevel_to_str (← Sail.readReg Register.cur_privilege))
                          (HAppend.hAppend "]: "
                            (HAppend.hAppend (Sail.BitVec.toFormatted (← Sail.readReg Register.PC))
                              (HAppend.hAppend " ("
                                (HAppend.hAppend (Sail.BitVec.toFormatted h)
                                  (HAppend.hAppend ") " (← (LeanRV32D.Functions.print_insn instruction)))))))))))
                  (LeanRV32D.Functions.zero_extend (m := 64) (← Sail.readReg Register.PC))))
            else (pure ())
            if ((← (LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca)) : Bool)
            then
              (do
                Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 2)
                let r ← do (LeanRV32D.Functions.execute instruction)
                (pure (Step.Step_Execute (r, instbits))))
            else (pure (Step.Step_Execute ((ExecutionResult.Illegal_Instruction ()), instbits))))
        | .F_Base w =>
          (do
            let _ : Unit := (LeanRV32D.Functions.sail_instr_announce w)
            let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) w)
            let instruction ← do (LeanRV32D.Functions.ext_decode w)
            if ((LeanRV32D.Functions.get_config_print_instr ()) : Bool)
            then
              (pure (LeanRV32D.Functions.print_log_instr
                  (HAppend.hAppend "["
                    (HAppend.hAppend (Int.repr step_no)
                      (HAppend.hAppend "] ["
                        (HAppend.hAppend (LeanRV32D.Functions.privLevel_to_str (← Sail.readReg Register.cur_privilege))
                          (HAppend.hAppend "]: "
                            (HAppend.hAppend (Sail.BitVec.toFormatted (← Sail.readReg Register.PC))
                              (HAppend.hAppend " ("
                                (HAppend.hAppend (Sail.BitVec.toFormatted w)
                                  (HAppend.hAppend ") " (← (LeanRV32D.Functions.print_insn instruction)))))))))))
                  (LeanRV32D.Functions.zero_extend (m := 64) (← Sail.readReg Register.PC))))
            else (pure ())
            Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
            let r ← do (LeanRV32D.Functions.execute instruction)
            (pure (Step.Step_Execute (r, instbits)))))

  lemma run_hart_active_equiv :
    run_hart_active = LeanRV32D.Functions.run_hart_active
  := rfl
end Local

-- noncomputable def run_hart_active_1 (step_no : Nat) : SailM Step := do
--   match (← (LeanRV32D.Functions.dispatchInterrupt (← Sail.readReg Register.cur_privilege))) with
--   | .some (intr, priv) => (pure (Step.Step_Pending_Interrupt (intr, priv)))
--   | none =>
--     (do
--       match (LeanRV32D.Functions.ext_fetch_hook (← (LeanRV32D.Functions.fetch ()))) with
--       | .F_Ext_Error e => (pure (Step.Step_Ext_Fetch_Failure e))
--       | .F_Error (e, addr) => (pure (Step.Step_Fetch_Failure ((virtaddr.Virtaddr addr), e)))
--       | .F_RVC h =>
--         (do
--           let _ : Unit := (LeanRV32D.Functions.sail_instr_announce h)
--           let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) h)
--           let instruction ← do (LeanRV32D.Functions.ext_decode_compressed h)
--           bif (LeanRV32D.Functions.get_config_print_instr ())
--           then
--             (pure (Sail.print_endline
--                 (HAppend.hAppend "["
--                   (HAppend.hAppend (Int.repr step_no)
--                     (HAppend.hAppend "] ["
--                       (HAppend.hAppend (LeanRV32D.Functions.privLevel_to_str (← Sail.readReg Register.cur_privilege))
--                         (HAppend.hAppend "]: "
--                           (HAppend.hAppend (Sail.BitVec.toFormatted (← Sail.readReg Register.PC))
--                             (HAppend.hAppend " ("
--                               (HAppend.hAppend (Sail.BitVec.toFormatted h)
--                                 (HAppend.hAppend ") " (← (LeanRV32D.Functions.print_insn instruction)))))))))))))
--           else (pure ())
--           bif (← (LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca))
--           then
--             (do
--               Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 2)
--               let r ← do (LeanRV32D.Functions.execute instruction)
--               (pure (Step.Step_Execute (r, instbits))))
--           else (pure (Step.Step_Execute ((ExecutionResult.Illegal_Instruction ()), instbits))))
--       | .F_Base w =>
--         (do
--           let _ : Unit := (LeanRV32D.Functions.sail_instr_announce w)
--           let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) w)
--           let instruction ← do (LeanRV32D.Functions.ext_decode w)
--           bif (LeanRV32D.Functions.get_config_print_instr ())
--           then
--             (pure (Sail.print_endline
--                 (HAppend.hAppend "["
--                   (HAppend.hAppend (Int.repr step_no)
--                     (HAppend.hAppend "] ["
--                       (HAppend.hAppend (LeanRV32D.Functions.privLevel_to_str (← Sail.readReg Register.cur_privilege))
--                         (HAppend.hAppend "]: "
--                           (HAppend.hAppend (Sail.BitVec.toFormatted (← Sail.readReg Register.PC))
--                             (HAppend.hAppend " ("
--                               (HAppend.hAppend (Sail.BitVec.toFormatted w)
--                                 (HAppend.hAppend ") " (← (LeanRV32D.Functions.print_insn instruction)))))))))))))
--           else (pure ())
--           Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
--           let r ← do (LeanRV32D.Functions.execute instruction)
--           (pure (Step.Step_Execute (r, instbits)))))

-- lemma run_hart_active_1_equiv :
--   run_hart_active_1 =
--   LeanRV32D.Functions.run_hart_active
-- := by
--   unfold LeanRV32D.Functions.run_hart_active
--   funext
--   unfold run_hart_active_1
--   congr

-- -- noncomputable def run_hart_active_2 (step_no : Nat) : SailM Step := do
-- --   match (← (LeanRV32D.Functions.dispatchInterrupt (← Sail.readReg Register.cur_privilege))) with
-- --   | .some (intr, priv) => (pure (Step.Step_Pending_Interrupt (intr, priv)))
-- --   | none =>
-- --     (do
-- --       match (LeanRV32D.Functions.ext_fetch_hook (← (LeanRV32D.Functions.fetch ()))) with
-- --       | .F_Ext_Error e => (pure (Step.Step_Ext_Fetch_Failure e))
-- --       | .F_Error (e, addr) => (pure (Step.Step_Fetch_Failure ((virtaddr.Virtaddr addr), e)))
-- --       | .F_RVC h =>
-- --         (do
-- --           let _ : Unit := (LeanRV32D.Functions.sail_instr_announce h)
-- --           let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) h)
-- --           let instruction ← do (LeanRV32D.Functions.ext_decode_compressed h)
-- --           bif (← (LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca))
-- --           then
-- --             (do
-- --               Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 2)
-- --               let r ← do (LeanRV32D.Functions.execute instruction)
-- --               (pure (Step.Step_Execute (r, instbits))))
-- --           else (pure (Step.Step_Execute ((ExecutionResult.Illegal_Instruction ()), instbits))))
-- --       | .F_Base w =>
-- --         (do
-- --           let _ : Unit := (LeanRV32D.Functions.sail_instr_announce w)
-- --           let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) w)
-- --           let instruction ← do (LeanRV32D.Functions.ext_decode w)
-- --           Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
-- --           let r ← do (LeanRV32D.Functions.execute instruction)
-- --           (pure (Step.Step_Execute (r, instbits)))))

-- -- lemma run_hart_active_2_equiv :
-- --   run_hart_active_1 state =
-- --   run_hart_active_2 state
-- -- := by
-- --   unfold run_hart_active_1 run_hart_active_2

-- --   unfold bind Monad.toBind EStateM.instMonad
-- --   dsimp
-- --   unfold EStateM.bind EStateM.pure
-- --   dsimp

-- --   unfold LeanRV32D.Functions.get_config_print_instr
-- --   simp

-- --   funext state1; congr
-- --   funext state2; congr
-- --   funext state3; congr
-- --   funext data state4
-- --   cases data <;> dsimp
-- --   congr
-- --   funext data1 state5; congr





-- noncomputable def run_hart_active_2 (step_no : Nat) : SailM Step := do
--   match (← (LeanRV32D.Functions.dispatchInterrupt (← Sail.readReg Register.cur_privilege))) with
--   | .some (intr, priv) => (pure (Step.Step_Pending_Interrupt (intr, priv)))
--   | none =>
--     (do
--       match (← (LeanRV32D.Functions.fetch ())) with
--       | .F_Ext_Error e => (pure (Step.Step_Ext_Fetch_Failure e))
--       | .F_Error (e, addr) => (pure (Step.Step_Fetch_Failure ((virtaddr.Virtaddr addr), e)))
--       | .F_RVC h =>
--         (do
--           let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) h)
--           let instruction ← do (LeanRV32D.Functions.ext_decode_compressed h)
--           bif (← (LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca))
--           then
--             (do
--               Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 2)
--               let r ← do (LeanRV32D.Functions.execute instruction)
--               (pure (Step.Step_Execute (r, instbits))))
--           else (pure (Step.Step_Execute ((ExecutionResult.Illegal_Instruction ()), instbits))))
--       | .F_Base w =>
--         (do
--           let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) w)
--           let instruction ← do (LeanRV32D.Functions.ext_decode w)
--           Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
--           let r ← do (LeanRV32D.Functions.execute instruction)
--           (pure (Step.Step_Execute (r, instbits)))))

-- -- def is_pending_machine_interrupt
-- --   (RegisterType: Register → Type)
-- --   (cur_privilege_val: Privilege)
-- --   (mstatus_val: BitVec 64)
-- --   (mip_val: RegisterType Register.mip)
-- --   (mie_val: RegisterType Register.mie)
-- --   (mideleg_val: RegisterType Register.mideleg)
-- --   [Complement (RegisterType Register.mideleg)]
-- --   [HAnd (RegisterType Register.mie) (RegisterType Register.mideleg) (RegisterType Register.mie)]
-- --   [HAnd (RegisterType Register.mip) (RegisterType Register.mie) (RegisterType Register.mip)]
-- --   [BEq (RegisterType Register.mip)]

-- -- : Bool :=
-- --   (cur_privilege_val == Privilege.Machine && BitVec.extractLsb 3 3 mstatus_val == 1#1 ||
-- --               (cur_privilege_val == Privilege.Supervisor || cur_privilege_val == Privilege.User)) &&
-- --             mip_val &&& (mie_val &&& ~~~mideleg_val) != 0#32

lemma dispatchInterrupt_none
  (cur_privilege_val: Privilege)
  (mideleg_val: RegisterType Register.mideleg)
  (mie_val: RegisterType Register.mie)
  (mip_val: RegisterType Register.mip)
  (misa_val: RegisterType Register.misa)
  (mstatus_val: RegisterType Register.mstatus)
  (h_mideleg: state.regs.get? Register.mideleg = .some mideleg_val)
  (h_mie: state.regs.get? Register.mie = .some mie_val)
  (h_mip: state.regs.get? Register.mip = .some mip_val)
  (h_misa: state.regs.get? Register.misa = .some misa_val)
  (h_mstatus: state.regs.get? Register.mstatus = .some mstatus_val)
  (h_assert: BitVec.extractLsb 18 18 misa_val = 1#1 ∨ mideleg_val = 0#32)
  (h_machine_interrupt: ((
    cur_privilege_val == Privilege.Machine && BitVec.extractLsb 3 3 mstatus_val == 1#1 ||
    (cur_privilege_val == Privilege.Supervisor || cur_privilege_val == Privilege.User)
  ) && mip_val &&& (mie_val &&& ~~~mideleg_val) != 0#32) = false)
  (h_supervisor_interrupt: ((
    cur_privilege_val == Privilege.Supervisor && BitVec.extractLsb 1 1 mstatus_val == 1#1 ||
    cur_privilege_val == Privilege.User
  ) && mip_val &&& (mie_val &&& mideleg_val) != 0#32) = false)
:
  LeanRV32D.Functions.dispatchInterrupt cur_privilege_val state = EStateM.Result.ok none state
:= by
  simp only [
    LeanRV32D.Functions.dispatchInterrupt,
    LeanRV32D.Functions.getPendingSet,
    LeanRV32D.Functions.currentlyEnabled,
    LeanRV32D.Functions.hartSupports,
    LeanRV32D.Functions._get_Misa_S,
    LeanRV32D.Functions.zeros,
    LeanRV32D.Functions._get_Mstatus_MIE,
    LeanRV32D.Functions._get_Mstatus_SIE,
    Sail.assert,
    PreSail.assert,
    Sail.BitVec.extractLsb
  ]

  unfold bind Monad.toBind EStateM.instMonad
  dsimp
  unfold EStateM.bind EStateM.pure
  dsimp

  simp [readReg_state, *]

lemma instructionFetch_neq_false:
  (@AccessType.InstructionFetch Unit () != AccessType.InstructionFetch ()) = false
:= rfl

-- lemma ext_fetch_check_ok:
--   LeanRV32D.Functions.ext_fetch_check_pc pc_val pc_val = Ext_FetchAddr_Check.Ext_FetchAddr_OK ⟨pc_val⟩
-- := rfl

-- lemma currentlyEnabled_Ext_Zca
--   (h_misa: state.regs.get? Register.misa = .some misa_val)
-- :
--   LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca state =
--   EStateM.Result.ok (Sail.BitVec.extractLsb misa_val 2 2 == 1#1) state
-- := by
--   simp [
--     LeanRV32D.Functions.currentlyEnabled.eq_def,
--     LeanRV32D.Functions.hartSupports.eq_def,
--     Functor.map, EStateM.map,
--     LeanRV32D.Functions.not,
--     readReg_state, *
--   ]
--   have (a b: ℕ): (a == b || a != b) = true := by grind only
--   have (a b: ℕ): (!a == b && !a != b) = false := by grind only
--   simp [LeanRV32D.Functions._get_Misa_C, *]

-- lemma unwrap_bits_of_virtaddr:
--   LeanRV32D.Functions.bits_of_virtaddr (virtaddr.Virtaddr pc_val) =
--   pc_val
-- := rfl

lemma effectivePrivilege_instructionFetch
:
  LeanRV32D.Functions.effectivePrivilege (AccessType.InstructionFetch ()) mstatus_val cur_privilege_val state =
  EStateM.Result.ok cur_privilege_val state
:= by
  unfold LeanRV32D.Functions.effectivePrivilege
  simp [
    instructionFetch_neq_false,
    pure, EStateM.pure
  ]

lemma architecture_backwards_mstatus_SXL
:
  LeanRV32D.Functions.architecture_backwards (LeanRV32D.Functions.get_mstatus_SXL mstatus_val) state =
  EStateM.Result.ok Architecture.RV32 state
:= by
  simp [
    LeanRV32D.Functions.architecture_backwards,
    LeanRV32D.Functions.get_mstatus_SXL,
    LeanRV32D.Functions.architecture_forwards,
    pure, EStateM.pure
  ]

-- -- example (b: BitVec 1) :
-- --   0#3 ++ b = 0#4
-- -- := by
-- --   match b with
-- --     | 0#1 => rfl
-- --     | 1#1 => rfl

lemma extract_all_satp
  (satp_val: RegisterType Register.satp)
:
  Sail.BitVec.extractLsb satp_val 31 0 = satp_val
:= by
  simp [
    Sail.BitVec.extractLsb,
    BitVec.extractLsb
  ]

lemma translationMode
  (h_mstatus: state.regs.get? Register.mstatus = .some mstatus_val)
  (h_satp: state.regs.get? Register.satp = .some satp_val)
:
  LeanRV32D.Functions.translationMode cur_privilege_val state =
  EStateM.Result.ok (
    bif (cur_privilege_val == Privilege.Machine || Sail.BitVec.extractLsb satp_val 31 31 == 0#1)
    then SATPMode.Bare
    else SATPMode.Sv32
  ) state
:= by
  unfold LeanRV32D.Functions.translationMode

  unfold bind Monad.toBind EStateM.instMonad
  dsimp
  unfold EStateM.bind EStateM.pure
  dsimp

  by_cases h: cur_privilege_val == Privilege.Machine
  . simp_all
  . simp_all [
      readReg_state, architecture_backwards_mstatus_SXL,
      LeanRV32D.Functions.satpMode_of_bits,
      LeanRV32D.Functions._get_Satp32_Mode,
      LeanRV32D.Functions.Mk_Satp32,
      extract_all_satp
    ]
    match (Sail.BitVec.extractLsb satp_val 31 31) with
      | 0#1 => simp
      | 1#1 => simp

lemma satp_mode_bare_eq: (SATPMode.Bare == SATPMode.Bare) = true := rfl
lemma satp_mode_sv32_neq_bare: (SATPMode.Sv32 == SATPMode.Bare) = false := rfl

lemma extract_all_pc (pc_val: xlenbits):
  BitVec.extractLsb 31 0 pc_val = pc_val
:= by
  simp [BitVec.extractLsb]

lemma sign_extend_extract_all_pc(pc_val: xlenbits):
  LeanRV32D.Functions.sign_extend (Sail.BitVec.extractLsb pc_val 31 0) = pc_val
:= by
  simp [
    Sail.BitVec.extractLsb,
    BitVec.extractLsb,
    LeanRV32D.Functions.sign_extend,
    Sail.BitVec.signExtend
  ]

-- lemma translateAddr_instructionFetch
--   (h_cur_privilege: state.regs.get? Register.cur_privilege = .some cur_privilege_val)
--   (h_mstatus: state.regs.get? Register.mstatus = .some mstatus_val)
--   (h_satp: state.regs.get? Register.satp = .some satp_val)
--   (h_tlb: state.regs.get? Register.tlb = .some tlb_val)
-- :
--   LeanRV32D.Functions.translateAddr (virtaddr.Virtaddr pc_val) (AccessType.InstructionFetch ()) state =
--   bif (cur_privilege_val == Privilege.Machine || Sail.BitVec.extractLsb satp_val 31 31 == 0#1)
--   then EStateM.Result.ok (Sail.Ok (⟨BitVec.setWidth 34 pc_val⟩, ())) state
--   else EStateM.Result.ok (Sail.Ok (ppclo, snd)) s
-- := by
--   unfold LeanRV32D.Functions.translateAddr

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   simp [readReg_state, *]
--   simp [effectivePrivilege_instructionFetch]
--   simp [translationMode, *]
--   simp [unwrap_bits_of_virtaddr]

--   by_cases h_case: cur_privilege_val == Privilege.Machine || Sail.BitVec.extractLsb satp_val 31 31 == 0#1
--   . simp [satp_mode_bare_eq, *]
--     simp [LeanRV32D.Functions.zero_extend, Sail.BitVec.zeroExtend]
--   . simp [satp_mode_sv32_neq_bare, *]
--     simp [LeanRV32D.Functions.satp_mode_width_forwards, pure, EStateM.pure]
--     simp [
--       LeanRV32D.Functions.get_satp,
--       Sail.assert,
--       PreSail.assert,
--       -- Functor.map, EStateM.map,
--       readReg_state, pure, EStateM.pure, bind, EStateM.bind,
--       *
--     ]
--     simp [
--       sign_extend_extract_all_pc,
--       readReg_state, *
--     ]
--     have (a b: ℕ) : (bif decide (32 = 32) then a else b) = a := by grind only
--     rewrite [this 32 64]
--     simp [
--       Sail.BitVec.extractLsb,
--       LeanRV32D.Functions.satp_to_ppn, LeanRV32D.Functions.Mk_Satp32,
--       LeanRV32D.Functions._get_Satp32_PPN,
--       LeanRV32D.Functions.pagesize_bits,
--       LeanRV32D.Functions._get_Mstatus_MXR,
--       LeanRV32D.Functions._get_Mstatus_SUM,
--       LeanRV32D.Functions.init_ext_ptw,
--       LeanRV32D.Functions.satp_to_asid,
--       LeanRV32D.Functions._get_Satp32_Asid,
--       LeanRV32D.Functions.zero_extend,
--       Sail.BitVec.zeroExtend
--     ]
--     simp [LeanRV32D.Functions.translate, LeanRV32D.Functions.lookup_TLB]

--     unfold bind Monad.toBind EStateM.instMonad
--     dsimp
--     unfold EStateM.bind EStateM.pure
--     dsimp

--     simp [readReg_state, *]

--     simp? [
--       LeanRV32D.Functions.tlb_hash,
--       LeanRV32D.Functions.match_TLB_Entry,
--       Sail.BitVec.extractLsb,
--       extract_all_pc,
--       -BitVec.extractLsb_toNat
--     ]

--     have : BitVec.extractLsb 5 0 (BitVec.extractLsb 31 12 pc_val) = BitVec.extractLsb 17 12 pc_val := by bv_decide
--     simp [
--       this,
--       LeanRV32D.Functions.sign_extend,
--       LeanRV32D.Functions.translate_TLB_hit,
--       LeanRV32D.Functions.check_PTE_permission,
--       -BitVec.extractLsb_toNat
--     ]

--     cases h_tlb_entry: tlb_val[(BitVec.extractLsb 17 12 pc_val).toNat]! with
--       | none =>
--         simp [LeanRV32D.Functions.translate_TLB_miss]

--         unfold bind Monad.toBind EStateM.instMonad
--         dsimp
--         unfold EStateM.bind EStateM.pure
--         dsimp

--         unfold LeanRV32D.Functions.pt_walk

--         simp
--         unfold bind Monad.toBind EStateM.instMonad
--         dsimp
--         unfold EStateM.bind EStateM.pure
--         dsimp

--         done
--       | some entry =>
--         done



--   done

-- lemma fetch_F_Base
--   (h_misa: state.regs.get? Register.misa = .some misa_val)
--   (h_pc: state.regs.get? Register.PC = .some pc_val)
--   (h_fetch_error: (
--     Sail.BitVec.access pc_val 0 != 0#1 ||
--     (Sail.BitVec.access pc_val 1 != 0#1 &&
--     !Sail.BitVec.extractLsb misa_val 2 2 == 1#1)
--   ) = false)
-- :
--   LeanRV32D.Functions.fetch () state = EStateM.Result.ok (FetchResult.F_Base w) s
-- := by
--   unfold LeanRV32D.Functions.fetch LeanRV32D.Functions.get_config_rvfi
--   dsimp

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   simp [readReg_state, *]
--   simp [ext_fetch_check_ok]
--   simp [
--     currentlyEnabled_Ext_Zca,
--     readReg_state,
--     unwrap_bits_of_virtaddr,
--     LeanRV32D.Functions.not,
--     *
--   ]

--   done


-- lemma run_hart_active_2_equiv
--   (h_cur_privilege: state.regs.get? Register.cur_privilege = .some cur_privilege_val)
--   (h_mideleg: state.regs.get? Register.mideleg = .some mideleg_val)
--   (h_mie: state.regs.get? Register.mie = .some mie_val)
--   (h_mip: state.regs.get? Register.mip = .some mip_val)
--   (h_misa: state.regs.get? Register.misa = .some misa_val)
--   (h_mstatus: state.regs.get? Register.mstatus = .some mstatus_val)
--   (h_pc: state.regs.get? Register.PC = .some pc_val)
--   (h_assert: BitVec.extractLsb 18 18 misa_val = 1#1 ∨ mideleg_val = 0#32)
--   (h_machine_interrupt: ((
--     cur_privilege_val == Privilege.Machine && BitVec.extractLsb 3 3 mstatus_val == 1#1 ||
--     (cur_privilege_val == Privilege.Supervisor || cur_privilege_val == Privilege.User)
--   ) && mip_val &&& (mie_val &&& ~~~mideleg_val) != 0#32) = false)
--   (h_supervisor_interrupt: ((
--     cur_privilege_val == Privilege.Supervisor && BitVec.extractLsb 1 1 mstatus_val == 1#1 ||
--     cur_privilege_val == Privilege.User
--   ) && mip_val &&& (mie_val &&& mideleg_val) != 0#32) = false)
--   (h_fetch_error: (
--     Sail.BitVec.access pc_val 0 != 0#1 ||
--     (Sail.BitVec.access pc_val 1 != 0#1 &&
--     !Sail.BitVec.extractLsb misa_val 2 2 == 1#1)
--   ) = false)
-- :
--   run_hart_active_1 step_no state =
--   run_hart_active_2 step_no state
-- := by
--   unfold run_hart_active_1 run_hart_active_2
--   unfold LeanRV32D.Functions.ext_fetch_hook
--   unfold LeanRV32D.Functions.sail_instr_announce
--   unfold LeanRV32D.Functions.get_config_print_instr
--   simp

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   simp [readReg_state, dispatchInterrupt_none, *]

--   unfold LeanRV32D.Functions.fetch LeanRV32D.Functions.get_config_rvfi

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   simp [readReg_state, *]

--   unfold LeanRV32D.Functions.ext_fetch_check_pc
--   dsimp
--   simp [
--     LeanRV32D.Functions.currentlyEnabled,
--     Functor.map, EStateM.map,
--     readReg_state, *
--   ]
--   unfold LeanRV32D.Functions.bits_of_virtaddr
--   simp [
--     LeanRV32D.Functions.hartSupports,
--     LeanRV32D.Functions.xlen,
--     LeanRV32D.Functions._get_Misa_C,
--     LeanRV32D.Functions.not, *
--   ]
--   unfold LeanRV32D.Functions.translateAddr

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   simp [readReg_state, *]
--   unfold LeanRV32D.Functions.effectivePrivilege
--   simp [instructionFetch_neq_false]
--   unfold pure EStateM.instMonad EStateM.pure
--   dsimp

--   unfold LeanRV32D.Functions.translationMode




--   sorry
--   -- done

def write_xreg (reg : Finset.Icc 1 31) (val : BitVec 32) : SailM Unit :=
  match reg.1 with
    | 1 => Sail.writeReg Register.x1 val
    | 2 => Sail.writeReg Register.x2 val
    | 3 => Sail.writeReg Register.x3 val
    | 4 => Sail.writeReg Register.x4 val
    | 5 => Sail.writeReg Register.x5 val
    | 6 => Sail.writeReg Register.x6 val
    | 7 => Sail.writeReg Register.x7 val
    | 8 => Sail.writeReg Register.x8 val
    | 9 => Sail.writeReg Register.x9 val
    | 10 => Sail.writeReg Register.x10 val
    | 11 => Sail.writeReg Register.x11 val
    | 12 => Sail.writeReg Register.x12 val
    | 13 => Sail.writeReg Register.x13 val
    | 14 => Sail.writeReg Register.x14 val
    | 15 => Sail.writeReg Register.x15 val
    | 16 => Sail.writeReg Register.x16 val
    | 17 => Sail.writeReg Register.x17 val
    | 18 => Sail.writeReg Register.x18 val
    | 19 => Sail.writeReg Register.x19 val
    | 20 => Sail.writeReg Register.x20 val
    | 21 => Sail.writeReg Register.x21 val
    | 22 => Sail.writeReg Register.x22 val
    | 23 => Sail.writeReg Register.x23 val
    | 24 => Sail.writeReg Register.x24 val
    | 25 => Sail.writeReg Register.x25 val
    | 26 => Sail.writeReg Register.x26 val
    | 27 => Sail.writeReg Register.x27 val
    | 28 => Sail.writeReg Register.x28 val
    | 29 => Sail.writeReg Register.x29 val
    | 30 => Sail.writeReg Register.x30 val
    | _ => Sail.writeReg Register.x31 val

lemma sail_get_slice_int_in_range
  (rd: ℕ)
  (h_rd: rd ≤ 31)
:
  Sail.get_slice_int 5 (↑rd) 0 =
  BitVec.ofNat 5 rd
:= by
  unfold Sail.get_slice_int
  simp [BitVec.extractLsb']
  rw [Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 0
lemma wX_write_xreg_equiv
  (data)
  (state)
  (rd_idx : regidx)
  (rd : Finset.Icc 1 31)
  (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
:
  LeanRV32D.Functions.wX_bits rd_idx data state =
  write_xreg rd data state
:= by
  unfold LeanRV32D.Functions.wX_bits
  simp [h_rd]
  obtain ⟨rd, h_rd_range⟩ := rd
  obtain ⟨h_rd_low, h_rd_high⟩ := Finset.mem_Icc.mp h_rd_range
  rewrite [Nat.mod_eq_of_lt (by {simp; omega})]
  unfold LeanRV32D.Functions.wX
  dsimp
  simp [LeanRV32D.Functions.regval_into_reg]
  simp [
    LeanRV32D.Functions.xreg_write_callback,
    LeanRV32D.Functions.to_bits,
    sail_get_slice_int_in_range rd h_rd_high,
    LeanRV32D.Functions.xreg_full_write_callback,
    Functor.map,
    LeanRV32D.Functions.reg_name_forwards,
    LeanRV32D.Functions.encdec_reg_forwards,
    LeanRV32D.Functions.zero_extend,
    Sail.BitVec.zeroExtend,
    LeanRV32D.Functions.get_config_use_abi_names,
    LeanRV32D.Functions.not,
    LeanRV32D.Functions.encdec_reg_forwards_matches,
    LeanRV32D.Functions.reg_arch_name_raw_forwards
  ]
  unfold EStateM.map pure EStateM.instMonad EStateM.pure
  dsimp
  unfold EStateM.bind
  unfold write_xreg
  simp [Sail.writeReg, PreSail.writeReg]
  unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet EStateM.instMonadStateOf EStateM.modifyGet
  dsimp

  by_cases rd = 0 ; simp_all
  by_cases rd = 1 ; simp_all
  by_cases rd = 2 ; simp_all
  by_cases rd = 3 ; simp_all
  by_cases rd = 4 ; simp_all
  by_cases rd = 5 ; simp_all
  by_cases rd = 6 ; simp_all
  by_cases rd = 7 ; simp_all
  by_cases rd = 8 ; simp_all
  by_cases rd = 9 ; simp_all
  by_cases rd = 10 ; simp_all
  by_cases rd = 11 ; simp_all
  by_cases rd = 12 ; simp_all
  by_cases rd = 13 ; simp_all
  by_cases rd = 14 ; simp_all
  by_cases rd = 15 ; simp_all
  by_cases rd = 16 ; simp_all
  by_cases rd = 17 ; simp_all
  by_cases rd = 18 ; simp_all
  by_cases rd = 19 ; simp_all
  by_cases rd = 20 ; simp_all
  by_cases rd = 21 ; simp_all
  by_cases rd = 22 ; simp_all
  by_cases rd = 23 ; simp_all
  by_cases rd = 24 ; simp_all
  by_cases rd = 25 ; simp_all
  by_cases rd = 26 ; simp_all
  by_cases rd = 27 ; simp_all
  by_cases rd = 28 ; simp_all
  by_cases rd = 29 ; simp_all
  by_cases rd = 30 ; simp_all
  by_cases rd = 31 ; simp_all
  omega

lemma wX_write_xreg_0_equiv :
  LeanRV32D.Functions.wX_bits (regidx.Regidx 0) data state =
  EStateM.Result.ok () state
:= by
  simp [
    LeanRV32D.Functions.wX_bits,
    LeanRV32D.Functions.wX,
    pure, bind, EStateM.bind, EStateM.pure
  ]

def fin_to_x_reg (r : Fin 32) : Option Register :=
  match r with
    | 0 => .none
    | 1 => Register.x1
    | 2 => Register.x2
    | 3 => Register.x3
    | 4 => Register.x4
    | 5 => Register.x5
    | 6 => Register.x6
    | 7 => Register.x7
    | 8 => Register.x8
    | 9 => Register.x9
    | 10 => Register.x10
    | 11 => Register.x11
    | 12 => Register.x12
    | 13 => Register.x13
    | 14 => Register.x14
    | 15 => Register.x15
    | 16 => Register.x16
    | 17 => Register.x17
    | 18 => Register.x18
    | 19 => Register.x19
    | 20 => Register.x20
    | 21 => Register.x21
    | 22 => Register.x22
    | 23 => Register.x23
    | 24 => Register.x24
    | 25 => Register.x25
    | 26 => Register.x26
    | 27 => Register.x27
    | 28 => Register.x28
    | 29 => Register.x29
    | 30 => Register.x30
    | _ => Register.x31

def regidx_to_fin (r: regidx): Fin 32 :=
  match r with
    | regidx.Regidx r => ⟨
        r.toNat,
        by {
          have : (if false = true then 4 else 5) ≤ 5 := by decide
          convert BitVec.toNat_lt_twoPow_of_le this
        }
      ⟩

lemma regidx_non_zero (h_non_zero: ¬rd = 0):
  regidx_to_fin (regidx.Regidx rd) ∈ Finset.Icc 1 31
:= by
  by_cases rd = 0; simp_all
  by_cases h: rd = 1; rewrite [h]; decide
  by_cases h: rd = 2; rewrite [h]; decide
  by_cases h: rd = 3; rewrite [h]; decide
  by_cases h: rd = 4; rewrite [h]; decide
  by_cases h: rd = 5; rewrite [h]; decide
  by_cases h: rd = 6; rewrite [h]; decide
  by_cases h: rd = 7; rewrite [h]; decide
  by_cases h: rd = 8; rewrite [h]; decide
  by_cases h: rd = 9; rewrite [h]; decide
  by_cases h: rd = 10; rewrite [h]; decide
  by_cases h: rd = 11; rewrite [h]; decide
  by_cases h: rd = 12; rewrite [h]; decide
  by_cases h: rd = 13; rewrite [h]; decide
  by_cases h: rd = 14; rewrite [h]; decide
  by_cases h: rd = 15; rewrite [h]; decide
  by_cases h: rd = 16; rewrite [h]; decide
  by_cases h: rd = 17; rewrite [h]; decide
  by_cases h: rd = 18; rewrite [h]; decide
  by_cases h: rd = 19; rewrite [h]; decide
  by_cases h: rd = 20; rewrite [h]; decide
  by_cases h: rd = 21; rewrite [h]; decide
  by_cases h: rd = 22; rewrite [h]; decide
  by_cases h: rd = 23; rewrite [h]; decide
  by_cases h: rd = 24; rewrite [h]; decide
  by_cases h: rd = 25; rewrite [h]; decide
  by_cases h: rd = 26; rewrite [h]; decide
  by_cases h: rd = 27; rewrite [h]; decide
  by_cases h: rd = 28; rewrite [h]; decide
  by_cases h: rd = 29; rewrite [h]; decide
  by_cases h: rd = 30; rewrite [h]; decide
  by_cases h: rd = 31; rewrite [h]; decide
  exfalso
  have : rd < 32 := by grind
  grind

lemma bit_eq_one_of_not_eq_zero (bit: BitVec 1) (h : ¬bit = 0) : bit = 1 := by grind
lemma bit_eq_zero_of_not_eq_one (bit: BitVec 1) (h : ¬bit = 1) : bit = 0 := by grind
