import LeanRV32D
import Mathlib

/-
  No need to simplify the following:

  bind
  LeanRV32D.Functions.translationMode
  LeanRV32D.Functions.set_next_pc

-/

attribute [simp]
  instBEqSATPMode.beq

  get
  getThe
  instMonadStateOfMonadStateOf
  liftM
  modify
  modifyGet
  monadLift
  MonadLift.monadLift
  pure

  Functor.map

  ExceptT.bind
  ExceptT.bindCont
  ExceptT.instMonad
  ExceptT.lift
  ExceptT.map
  ExceptT.mk
  ExceptT.pure
  ExceptT.run

  EStateM.bind
  EStateM.get
  EStateM.map
  EStateM.modifyGet
  EStateM.instMonad
  EStateM.instMonadStateOf
  EStateM.pure

  ExceptT.instMonad ExceptT.pure ExceptT.mk

  Int.le
  Int.neg
  Int.negOfNat
  Int.sub

  untilFuelM
  untilFuelM.go

  Sail.BitVec.access
  Sail.BitVec.addInt
  Sail.BitVec.extractLsb
  Sail.BitVec.signExtend
  Sail.BitVec.toNatInt
  Sail.BitVec.updateSubrange
  Sail.BitVec.updateSubrange'
  Sail.BitVec.zeroExtend
  Sail.get_slice_int
  zero_extend

  LeanRV32D.Functions._get_Misa_C
  LeanRV32D.Functions._get_Mstatus_MPRV
  LeanRV32D.Functions.bits_of_physaddr
  LeanRV32D.Functions.bits_of_virtaddr
  LeanRV32D.Functions.check_misaligned
  LeanRV32D.Functions.checked_mem_read
  LeanRV32D.Functions.checked_mem_write
  LeanRV32D.Functions.currentlyEnabled
  LeanRV32D.Functions.Data
  LeanRV32D.Functions.effectivePrivilege
  LeanRV32D.Functions.encdec_reg_forwards
  LeanRV32D.Functions.encdec_reg_forwards_matches
  LeanRV32D.Functions.ext_control_check_pc
  LeanRV32D.Functions.ext_data_get_addr
  LeanRV32D.Functions.extend_value
  LeanRV32D.Functions.get_config_rvfi
  LeanRV32D.Functions.get_config_use_abi_names
  LeanRV32D.Functions.get_next_pc
  LeanRV32D.Functions.hartSupports
  LeanRV32D.Functions.matching_pma
  LeanRV32D.Functions.matching_pma_bits_range
  LeanRV32D.Functions.mem_read
  LeanRV32D.Functions.mem_read_priv
  LeanRV32D.Functions.mem_read_priv_meta
  LeanRV32D.Functions.mem_write_ea
  LeanRV32D.Functions.mem_write_value
  LeanRV32D.Functions.mem_write_value_meta
  LeanRV32D.Functions.mem_write_value_priv_meta
  LeanRV32D.Functions.MemoryOpResult_drop_meta
  LeanRV32D.Functions.misaligned_order
  LeanRV32D.Functions.not
  LeanRV32D.Functions.phys_access_check
  LeanRV32D.Functions.plat_enable_misaligned_access
  LeanRV32D.Functions.pmaCheck
  LeanRV32D.Functions.pmpCheck
  LeanRV32D.Functions.range_subset
  LeanRV32D.Functions.read_kind_of_flags
  LeanRV32D.Functions.read_ram
  LeanRV32D.Functions.reg_arch_name_raw_forwards
  LeanRV32D.Functions.reg_name_forwards
  LeanRV32D.Functions.regval_from_reg
  LeanRV32D.Functions.regval_into_reg
  LeanRV32D.Functions.RETIRE_SUCCESS
  LeanRV32D.Functions.sail_branch_announce
  LeanRV32D.Functions.sign_extend
  LeanRV32D.Functions.sign_extend
  LeanRV32D.Functions.split_misaligned
  LeanRV32D.Functions.sys_misaligned_order_decreasing
  LeanRV32D.Functions.sys_pmp_count
  LeanRV32D.Functions.to_bits
  LeanRV32D.Functions.to_bits_checked
  LeanRV32D.Functions.translateAddr
  LeanRV32D.Functions.within_clint
  LeanRV32D.Functions.within_htif_readable
  LeanRV32D.Functions.within_htif_writable
  LeanRV32D.Functions.within_mmio_readable
  LeanRV32D.Functions.within_mmio_writable
  LeanRV32D.Functions.write_kind_of_flags
  LeanRV32D.Functions.write_ram
  LeanRV32D.Functions.xlen
  LeanRV32D.Functions.xlen_bytes
  LeanRV32D.Functions.xreg_full_write_callback
  LeanRV32D.Functions.xreg_write_callback
  LeanRV32D.Functions.zero_reg
  LeanRV32D.Functions.zeros
  LeanRV32D.Functions.zeros
  LeanRV32D.Functions.zopz0zI_s
  LeanRV32D.Functions.zopz0zI_u
  LeanRV32D.Functions.zopz0zIzJ_u
  LeanRV32D.Functions.zopz0zKzJ_s
  LeanRV32D.Functions.zopz0zKzJ_u

  PreSail.ConcurrencyInterfaceV1.sail_mem_read
  PreSail.ConcurrencyInterfaceV1.sail_mem_write
  PreSail.PreSailME.run
  PreSail.readByte
  PreSail.readBytes
  PreSail.writeByte
  PreSail.writeBytes

  Sail.ConcurrencyInterfaceV1.sail_mem_read
  Sail.ConcurrencyInterfaceV1.sail_mem_write
  Sail.SailME.run

section SimplerMonadicReasoning

  /-- Simpler monadic pure ok -/
  @[simp high]
  lemma pure_ok_equiv :
    @pure (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception) EStateM.instMonad.toPure T val =
    λ s => EStateM.Result.ok val s
  := by
    rfl

  /-- Simpler monadic pure exception -/
  @[simp high]
  lemma pure_except_equiv :
    @pure (SailME ExecutionResult) ExceptT.instMonad.toPure T val state =
    EStateM.Result.ok (Except.ok val) state
  := by
    rfl

  /-- Simpler monadic throw -/
  @[simp high]
  lemma throw_equiv :
    @throw
      (Sail.Error exception)
      (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception)
      (instMonadExceptOfMonadExceptOf
        (Sail.Error exception)
        (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception))
      T
      error =
    λ s_1 => EStateM.Result.error error s_1
  := by
    unfold throw instMonadExceptOfMonadExceptOf
    unfold throwThe MonadExceptOf.throw
    unfold EStateM.instMonadExceptOfOfBacktrackable EStateM.throw
    dsimp

  /-- Simpler bind equiv -/
  @[simp high]
  lemma bind_equiv :
    (@bind
      SailM
      EStateM.instMonad.toBind
      T1
      T2
      f1
      f2
    ) = λ s =>
      match f1 s with
      | EStateM.Result.ok a s => f2 a s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    unfold bind EStateM.instMonad EStateM.bind Monad.toBind
    simp
    funext state
    set state' := f1 state
    cases state' <;> simp

  @[simp high]
  lemma EStateM_bind_equiv :
    @EStateM.bind
      (Sail.Error exception)
      (PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (Except ExecutionResult Unit)
      (Except ExecutionResult ExecutionResult)
      f1
      f2
      state =
    (match f1 state with
    | EStateM.Result.ok a s => f2 a s
    | EStateM.Result.error e s => EStateM.Result.error e s)
  := by
    simp [EStateM.bind]
    set state' := f1 state
    cases state' <;> simp

end SimplerMonadicReasoning

section RegisterManipulation

  /-- Converting a register to a Fin 32 -/
  def regidx_to_fin (r : regidx): Fin 32 :=
    match r with
      | regidx.Regidx r => ⟨
          r.toNat,
          by {
            have : (if false = true then 4 else 5) ≤ 5 := by decide
            convert BitVec.toNat_lt_twoPow_of_le this
          }
        ⟩

  def reg_of_fin (r : Fin 32) : Register :=
    match r.1 with
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

  lemma register_type_equiv (r : Fin 32) :
    RegisterType (reg_of_fin r) = BitVec 32
  := by
    fin_cases r <;>
    simp [reg_of_fin, RegisterType]

  /-- Register read in terms of Fin 32 -/
  def read_xreg (reg : Fin 32) : SailM (BitVec 32) :=
    match reg.1 with
      | 0 => pure (0#32)
      | _ =>
        let result := Sail.readReg (reg_of_fin reg)
        cast (by rw [register_type_equiv]) result

  set_option maxHeartbeats 0 in
  /-- Equivalence of register reading when in Fin 32 -/
  lemma rX_read_xreg_equiv
    (state)
    (rd_idx : regidx)
    (rd : Fin 32)
    (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
  :
    LeanRV32D.Functions.rX_bits rd_idx state =
    read_xreg rd state
  := by
    unfold LeanRV32D.Functions.rX_bits
    simp [h_rd]
    unfold LeanRV32D.Functions.rX read_xreg
    fin_cases rd
    . simp
    all_goals
      simp [PreSail.readReg, reg_of_fin]
      aesop

  lemma regidx_non_zero (h_non_zero: ¬rd = 0):
    regidx_to_fin (regidx.Regidx rd) ∈ Finset.Icc 1 31
  := by
    obtain ⟨ rd', eq_rd' ⟩ : exists rd' : BitVec 5, rd' = rd := by simp
    subst rd
    by_cases rd' = 0; simp_all
    by_cases h: rd' = 1; rewrite [h]; decide
    by_cases h: rd' = 2; rewrite [h]; decide
    by_cases h: rd' = 3; rewrite [h]; decide
    by_cases h: rd' = 4; rewrite [h]; decide
    by_cases h: rd' = 5; rewrite [h]; decide
    by_cases h: rd' = 6; rewrite [h]; decide
    by_cases h: rd' = 7; rewrite [h]; decide
    by_cases h: rd' = 8; rewrite [h]; decide
    by_cases h: rd' = 9; rewrite [h]; decide
    by_cases h: rd' = 10; rewrite [h]; decide
    by_cases h: rd' = 11; rewrite [h]; decide
    by_cases h: rd' = 12; rewrite [h]; decide
    by_cases h: rd' = 13; rewrite [h]; decide
    by_cases h: rd' = 14; rewrite [h]; decide
    by_cases h: rd' = 15; rewrite [h]; decide
    by_cases h: rd' = 16; rewrite [h]; decide
    by_cases h: rd' = 17; rewrite [h]; decide
    by_cases h: rd' = 18; rewrite [h]; decide
    by_cases h: rd' = 19; rewrite [h]; decide
    by_cases h: rd' = 20; rewrite [h]; decide
    by_cases h: rd' = 21; rewrite [h]; decide
    by_cases h: rd' = 22; rewrite [h]; decide
    by_cases h: rd' = 23; rewrite [h]; decide
    by_cases h: rd' = 24; rewrite [h]; decide
    by_cases h: rd' = 25; rewrite [h]; decide
    by_cases h: rd' = 26; rewrite [h]; decide
    by_cases h: rd' = 27; rewrite [h]; decide
    by_cases h: rd' = 28; rewrite [h]; decide
    by_cases h: rd' = 29; rewrite [h]; decide
    by_cases h: rd' = 30; rewrite [h]; decide
    by_cases h: rd' = 31; rewrite [h]; decide
    exfalso
    have : rd' < 32 := by bv_decide
    grind

  /-- Successful read -/
  @[simp]
  lemma readReg_succ
    (h: state.regs.get? reg = .some reg_val)
  :
    Sail.readReg reg state = EStateM.Result.ok reg_val state
  := by
    unfold Sail.readReg PreSail.readReg
    aesop

  /-- Unsuccessful read -/
  @[simp]
  lemma readReg_fail
    (h: state.regs.get? reg = .none)
  :
    Sail.readReg reg state = EStateM.Result.error Sail.Error.Unreachable state
  := by
    unfold Sail.readReg PreSail.readReg
    aesop

  def write_xreg (reg : Finset.Icc 1 31) (val : BitVec 32) : SailM Unit :=
    match reg.1 with
      | _ =>
        let result := Sail.writeReg (reg_of_fin ⟨ reg, by grind ⟩ )
        (result (cast (by rw [register_type_equiv]) val))

  lemma wX_write_xreg_zero_equiv :
    LeanRV32D.Functions.wX_bits (regidx.Regidx 0) data state =
    EStateM.Result.ok () state
  := by
    simp [
      LeanRV32D.Functions.wX_bits,
      LeanRV32D.Functions.wX,
    ]

  set_option maxHeartbeats 0
  lemma wX_write_xreg_non_zero_equiv
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
    rewrite [Int.emod_eq_of_lt (by grind) (by grind)]
    unfold LeanRV32D.Functions.wX
    simp [write_xreg]
    by_cases rd = 0 ; aesop
    by_cases rd = 1 ; aesop
    by_cases rd = 2 ; aesop
    by_cases rd = 3 ; aesop
    by_cases rd = 4 ; aesop
    by_cases rd = 5 ; aesop
    by_cases rd = 6 ; aesop
    by_cases rd = 7 ; aesop
    by_cases rd = 8 ; aesop
    by_cases rd = 9 ; aesop
    by_cases rd = 10 ; aesop
    by_cases rd = 11 ; aesop
    by_cases rd = 12 ; aesop
    by_cases rd = 13 ; aesop
    by_cases rd = 14 ; aesop
    by_cases rd = 15 ; aesop
    by_cases rd = 16 ; aesop
    by_cases rd = 17 ; aesop
    by_cases rd = 18 ; aesop
    by_cases rd = 19 ; aesop
    by_cases rd = 20 ; aesop
    by_cases rd = 21 ; aesop
    by_cases rd = 22 ; aesop
    by_cases rd = 23 ; aesop
    by_cases rd = 24 ; aesop
    by_cases rd = 25 ; aesop
    by_cases rd = 26 ; aesop
    by_cases rd = 27 ; aesop
    by_cases rd = 28 ; aesop
    by_cases rd = 29 ; aesop
    by_cases rd = 30 ; aesop
    by_cases rd = 31 ; aesop
    omega

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
    simp [
      PreSail.writeReg,
      write_reg_state,
    ]

  @[simp]
  lemma writeReg_read_same
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :
    (write_reg_state state register value).regs.get? register = Option.some value
  := by
    unfold write_reg_state
    grind

  @[simp]
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

  set_option maxHeartbeats 0
  lemma read_xreg_write_other_reg_state
    (r1 : Fin 32)
    (h: read_xreg r1 state = EStateM.Result.ok read_val state)
    (h_neq: reg_of_fin r1 ≠ register)
  :
    read_xreg r1 (write_reg_state state register write_val) =
    EStateM.Result.ok
      read_val
      (write_reg_state state register write_val)
  := by
    have h_reg : (¬ r1 = 0) → state.regs.get? (reg_of_fin r1) = .some (cast (by rw [register_type_equiv]) read_val)
    := by
      clear h_neq; intro h_neq
      simp [read_xreg, PreSail.readReg] at *
      simp [h_neq] at h
      by_cases h_r1 : state.regs.get? (reg_of_fin r1) = .none
      . fin_cases r1 <;> simp_all
      . obtain ⟨ val, eq_val ⟩ : ∃ val, state.regs.get? (reg_of_fin r1) = .some val
        := by
          obtain ⟨ x, eq_x ⟩ : ∃ x, state.regs.get? (reg_of_fin r1) = x := by simp
          rw [eq_x] at h_r1 ⊢
          clear *- h_r1
          rw [← Option.isSome_iff_exists]
          rw [← Option.not_isSome_iff_eq_none] at h_r1
          tauto
        fin_cases r1 <;> simp_all
    by_cases rz : r1 = 0
    . simp [rz, read_xreg] at h ⊢
      assumption
    . specialize h_reg rz
      have :=
        @writeReg_read_diff
          (reg_of_fin r1)
          register
          state
          write_val
          _
          h_reg
          h_neq
      simp [rz, read_xreg, PreSail.readReg]
      fin_cases r1 <;> simp_all

  set_option maxHeartbeats 0 in
  lemma rX_bits_write_other_reg_state
    (h_r_val : LeanRV32D.Functions.rX_bits (regidx.Regidx r) state = EStateM.Result.ok r_val state)
    (h_neq : (reg_of_fin r.toFin) ≠ reg)
  :
    LeanRV32D.Functions.rX_bits (regidx.Regidx r) (write_reg_state state reg val) =
    EStateM.Result.ok r_val (write_reg_state state reg val)
  := by
    trans read_xreg r.toFin (write_reg_state state reg val)
    . clear *-
      simp [read_xreg, LeanRV32D.Functions.rX_bits, LeanRV32D.Functions.rX]
      rcases r with ⟨r, ub_r⟩
      simp at *; simp at ub_r
      interval_cases r <;> simp [reg_of_fin] <;> grind
    . have := @read_xreg_write_other_reg_state state r_val reg val r.toFin
      have h_read_xreg : read_xreg r.toFin state = EStateM.Result.ok r_val state
      := by
        simp [read_xreg]
        simp [LeanRV32D.Functions.rX_bits, LeanRV32D.Functions.rX] at h_r_val
        rw [← h_r_val]; clear *-
        simp [reg_of_fin]
        rcases r with ⟨r, ub_r⟩
        simp at *; simp at ub_r
        interval_cases r <;> simp <;> grind
      tauto

  lemma reg_of_fin_neq_nextPC :
    (reg_of_fin r) ≠ Register.nextPC
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_mstatus :
    (reg_of_fin r) ≠ Register.mstatus
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_cur_privilege :
    (reg_of_fin r) ≠ Register.cur_privilege
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_htif_tohost_base :
    (reg_of_fin r) ≠ Register.htif_tohost_base
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_pma_regions :
    (reg_of_fin r) ≠ Register.pma_regions
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma readReg_of_write_other_reg_state
    (h_reg : Sail.readReg reg state = EStateM.Result.ok val state)
    (h_neq : reg ≠ reg')
  :
    Sail.readReg reg (write_reg_state state reg' val') =
    EStateM.Result.ok val (write_reg_state state reg' val')
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_reg
    have :
      (state.regs.insert reg' val').get? reg = state.regs.get? reg
    := by grind
    simp [this]
    rcases h: state.regs.get? reg
    . simp [h] at h_reg
    . simp [h] at ⊢ h_reg
      exact h_reg

end RegisterManipulation

section SimplerFunctions

  @[simp high]
  lemma bit_to_bool :
    LeanRV32D.Functions.bit_to_bool =
    λ b => b == 1#1
  := by
    unfold
      LeanRV32D.Functions.bit_to_bool
      LeanRV32D.Functions.bool_bit_backwards
    grind

  @[simp]
  lemma bool_bits_forwards_to_if {b : Bool} :
    LeanRV32D.Functions.bool_bits_forwards b = if b then 1#1 else 0#1
  := by aesop

  @[simp high]
  lemma currentlyEnabled_Zca_of_misa_val
    {misa_val : BitVec 32}
    (h: state.regs.get? Register.misa = .some misa_val)
  :
    LeanRV32D.Functions.currentlyEnabled extension.Ext_Zca state =
    EStateM.Result.ok false state
  := by
    simp [LeanRV32D.Functions.currentlyEnabled]
    aesop

    @[simp high]
    lemma sail_assert_equiv :
      Sail.assert =
      λ check msg state =>
        if check
        then EStateM.Result.ok () state
        else EStateM.Result.error (Sail.Error.Assertion msg) state
    := by
      unfold Sail.assert PreSail.assert
      simp
      funext check message state
      cases check <;> simp

  @[simp]
  lemma translationMode_in_machine
  :
    LeanRV32D.Functions.translationMode Privilege.Machine state =
    EStateM.Result.ok ( SATPMode.Bare ) state
  := by
    aesop

  @[simp high]
  lemma set_next_pc_equiv :
    LeanRV32D.Functions.set_next_pc pc =
    Sail.writeReg Register.nextPC pc
  := rfl

end SimplerFunctions

section Memory

  -- OpenVM address space size
  notation "OpenVM_address_space_size" => 2 ^ 29

  lemma run_vmem_read_of_width_4
    (offset : BitVec 32)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + offset.toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + offset.toNat + 3]? = some data₃)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 4 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + offset.toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    let width := 4
    let data := data₃ ++ data₂ ++ data₁ ++ data₀
    (LeanRV32D.Functions.vmem_read
      rs
      offset
      width (MemoryAccessType.Load ())
      false false false
    ).run s = .ok (.Ok data) s
  := by
  subst privilege

  unfold
    LeanRV32D.Functions.vmem_read

  -- From vmem_read to vmem_read_addr
  simp [
    EStateM.run,
    EStateM.map,
    h_reg_val,
  ]
  -- Entering vmem_read_addr
  simp [
    LeanRV32D.Functions.vmem_read_addr,
    ExceptT.run,
    assumption_alignment
  ]
  unfold_projs
  simp [
    h_mstatus,
    h_cur_privilege,
    assumption_MPRV_not_set,
  ]
  obtain ⟨ is_readable, is_writable, is_misaligned_fault ⟩ := assumption_pma_attributes
  simp [assumption_pma_regions]
  rw [if_pos
      (by
        simp [assumption_pma_base]
        repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)]
        repeat rw [Int.emod_eq_of_lt (b := 4294967296) (by omega) (by omega)]
        simp [
          LeanRV32D.Functions.is_aligned_vaddr,
          Int.tmod_eq_emod
        ] at assumption_alignment
        omega)
    ]
  simp [is_misaligned_fault]
  rw [if_neg
     (by
        simp [LeanRV32D.Functions.is_aligned_vaddr] at assumption_alignment
        simp [LeanRV32D.Functions.is_aligned_paddr]
        rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
        omega)]
  simp [is_readable, h_htif_tohost_base]
  rw [if_neg
      (by
        simp; intro h_le
        iterate 2 rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_le
        simp [Int.nonneg_def] at h_le
        grind)]
  repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
  repeat rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
  simp [*]

  lemma run_vmem_read_of_width_2
    (offset : BitVec 32)
    (data₀ data₁ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + offset.toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    let width := 2
    let data := data₁ ++ data₀
    (LeanRV32D.Functions.vmem_read
      rs
      offset
      width (MemoryAccessType.Load ())
      false false false
    ).run s = .ok (.Ok data) s
  := by
  subst privilege

  unfold
    LeanRV32D.Functions.vmem_read

  -- From vmem_read to vmem_read_addr
  simp [
    EStateM.run,
    EStateM.map,
    h_reg_val,
  ]
  -- Entering vmem_read_addr
  simp [
    LeanRV32D.Functions.vmem_read_addr,
    ExceptT.run,
    assumption_alignment
  ]
  unfold_projs
  simp [
    h_mstatus,
    h_cur_privilege,
    assumption_MPRV_not_set,
  ]
  obtain ⟨ is_readable, is_writable, is_misaligned_fault ⟩ := assumption_pma_attributes
  simp [assumption_pma_regions]
  rw [if_pos
      (by
        simp [assumption_pma_base]
        repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)]
        repeat rw [Int.emod_eq_of_lt (b := 4294967296) (by omega) (by omega)]
        simp [
          LeanRV32D.Functions.is_aligned_vaddr,
          Int.tmod_eq_emod
        ] at assumption_alignment
        omega)
    ]
  simp [is_misaligned_fault]
  rw [if_neg
     (by
        simp [LeanRV32D.Functions.is_aligned_vaddr] at assumption_alignment
        simp [LeanRV32D.Functions.is_aligned_paddr]
        rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
        omega)]
  simp [is_readable, h_htif_tohost_base]
  rw [if_neg
      (by
        simp; intro h_le
        iterate 2 rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_le
        simp [Int.nonneg_def] at h_le
        grind)]
  repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
  repeat rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
  simp [*]

  lemma run_vmem_read_of_width_1
    (offset : BitVec 32)
    (data₀ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + offset.toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    let width := 1
    let data := data₀
    (LeanRV32D.Functions.vmem_read
      rs
      offset
      width (MemoryAccessType.Load ())
      false false false
    ).run s = .ok (.Ok data) s
  := by
  subst privilege

  unfold
    LeanRV32D.Functions.vmem_read

  -- From vmem_read to vmem_read_addr
  simp [
    EStateM.run,
    EStateM.map,
    h_reg_val,
  ]
  -- Entering vmem_read_addr
  simp [
    LeanRV32D.Functions.vmem_read_addr,
    ExceptT.run,
    assumption_alignment
  ]
  unfold_projs
  simp [
    h_mstatus,
    h_cur_privilege,
    assumption_MPRV_not_set,
  ]
  obtain ⟨ is_readable, is_writable, is_misaligned_fault ⟩ := assumption_pma_attributes
  simp [assumption_pma_regions]
  rw [if_pos
      (by
        simp [assumption_pma_base]
        repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)]
        repeat rw [Int.emod_eq_of_lt (b := 4294967296) (by omega) (by omega)]
        simp [
          LeanRV32D.Functions.is_aligned_vaddr,
          Int.tmod_eq_emod
        ] at assumption_alignment
        omega)
    ]
  simp [is_misaligned_fault]
  rw [if_neg
     (by
        simp [LeanRV32D.Functions.is_aligned_vaddr] at assumption_alignment
        simp [LeanRV32D.Functions.is_aligned_paddr])]
  simp [is_readable, h_htif_tohost_base]
  rw [if_neg
      (by
        simp; intro h_le
        iterate 2 rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_le
        simp [Int.nonneg_def] at h_le
        grind)]
  repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
  repeat rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
  simp [*]

  lemma execute_LOADW
    (s)
    (rd : regidx)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 3]? = some data₃)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 4 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_LOAD imm rs1 rd true 4 s =
    match LeanRV32D.Functions.wX_bits rd (data₃ ++ data₂ ++ data₁ ++ data₀) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_4
      (BitVec.signExtend 32 imm)
      data₀ data₁ data₂ data₃
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      hmem₀ hmem₁ hmem₂ hmem₃
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_fit
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [LeanRV32D.Functions.execute_LOAD, this]
    aesop

  lemma execute_LOADH
    (s)
    (rd : regidx)
    (data₀ data₁ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_LOAD imm rs1 rd false 2 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.signExtend 32 (data₁ ++ data₀)) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_2
      (BitVec.signExtend 32 imm)
      data₀ data₁
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      hmem₀ hmem₁
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_fit
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [LeanRV32D.Functions.execute_LOAD, this]
    aesop

  lemma execute_LOADHU
    (s)
    (rd : regidx)
    (data₀ data₁ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_LOAD imm rs1 rd true 2 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.setWidth 32 (data₁ ++ data₀)) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_2
      (BitVec.signExtend 32 imm)
      data₀ data₁
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      hmem₀ hmem₁
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_fit
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [LeanRV32D.Functions.execute_LOAD, this]
    aesop

  lemma execute_LOADB
    (s)
    (rd : regidx)
    (data₀ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_LOAD imm rs1 rd false 1 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.signExtend 32 data₀) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_1
      (BitVec.signExtend 32 imm)
      data₀
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      hmem₀
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_fit
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [LeanRV32D.Functions.execute_LOAD, this]
    aesop

  lemma execute_LOADBU
    (s)
    (rd : regidx)
    (data₀ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_LOAD imm rs1 rd true 1 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.setWidth 32 data₀) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_1
      (BitVec.signExtend 32 imm)
      data₀
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      hmem₀
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_fit
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [LeanRV32D.Functions.execute_LOAD, this]
    aesop

  lemma execute_STOREW
    (s)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 4 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : rs1_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_STORE imm rs2 rs1 4 s =
    EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
      regs := s.regs,
      choiceState := s.choiceState,
      tags := s.tags,
      cycleCount := s.cycleCount,
      sailOutput := s.sailOutput
      mem :=
        ((((s.mem.insert (rs1_val + BitVec.signExtend 32 imm).toNat (BitVec.extractLsb 7 0 rs2_val)
        ).insert ((rs1_val + BitVec.signExtend 32 imm).toNat + 1) (BitVec.extractLsb 15 8 rs2_val))
        ).insert ((rs1_val + BitVec.signExtend 32 imm).toNat + 2) (BitVec.extractLsb 23 16 rs2_val)
        ).insert ((rs1_val + BitVec.signExtend 32 imm).toNat + 3) (BitVec.extractLsb 31 24 rs2_val)
    }
  := by
    subst privilege

    simp [
      LeanRV32D.Functions.execute_STORE,
      h_rs2_val,
      LeanRV32D.Functions.vmem_write,
      h_rs1_val
    ]
    simp [
      ExceptT.run,
      LeanRV32D.Functions.vmem_write_addr,
      assumption_alignment,
      liftM, monadLift, MonadLift.monadLift
    ]
    iterate 2 (unfold_projs; simp)
    simp [
      h_mstatus,
      h_cur_privilege,
      assumption_MPRV_not_set,
      assumption_pma_regions,
      assumption_pma_base
    ]
    rw [if_pos
        (by
          repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)]
          repeat rw [Int.emod_eq_of_lt (b := 4294967296) (by omega) (by omega)]
          simp [
            LeanRV32D.Functions.is_aligned_vaddr,
            Int.tmod_eq_emod
          ] at assumption_alignment
          omega)]
    obtain ⟨ is_readable, is_writable, is_misaligned_fault ⟩ := assumption_pma_attributes
    simp [is_misaligned_fault]
    rw [if_neg
        (by
            simp [LeanRV32D.Functions.is_aligned_vaddr] at assumption_alignment
            simp [LeanRV32D.Functions.is_aligned_paddr]
            rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
            omega)]
    simp [is_writable, h_htif_tohost_base]
    rw [if_neg
        (by
          simp; intro h_le
          iterate 2 rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_le
          simp [Int.nonneg_def] at h_le
          grind)]
    unfold_projs
    simp [
      BitVec.extractLsb,
      BitVec.extractLsb'
    ]
    have back_to_usual_mod : forall (a b : ℕ), a.mod b = a % b := by tauto
    repeat rw [back_to_usual_mod]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]

lemma execute_STOREH
    (s)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : rs1_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_STORE imm rs2 rs1 2 s =
    EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
      regs := s.regs,
      choiceState := s.choiceState,
      tags := s.tags,
      cycleCount := s.cycleCount,
      sailOutput := s.sailOutput
      mem :=
        ((s.mem.insert (rs1_val + BitVec.signExtend 32 imm).toNat (BitVec.extractLsb 7 0 rs2_val)
        ).insert ((rs1_val + BitVec.signExtend 32 imm).toNat + 1) (BitVec.extractLsb 15 8 rs2_val))
    }
  := by
    subst privilege

    simp [
      LeanRV32D.Functions.execute_STORE,
      h_rs2_val,
      LeanRV32D.Functions.vmem_write,
      h_rs1_val
    ]
    simp [
      ExceptT.run,
      LeanRV32D.Functions.vmem_write_addr,
      assumption_alignment,
      liftM, monadLift, MonadLift.monadLift
    ]
    iterate 2 (unfold_projs; simp)
    simp [
      h_mstatus,
      h_cur_privilege,
      assumption_MPRV_not_set,
      assumption_pma_regions,
      assumption_pma_base
    ]
    rw [if_pos
        (by
          repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)]
          repeat rw [Int.emod_eq_of_lt (b := 4294967296) (by omega) (by omega)]
          simp [
            LeanRV32D.Functions.is_aligned_vaddr,
            Int.tmod_eq_emod
          ] at assumption_alignment
          omega)]
    obtain ⟨ is_readable, is_writable, is_misaligned_fault ⟩ := assumption_pma_attributes
    simp [is_misaligned_fault]
    rw [if_neg
        (by
            simp [LeanRV32D.Functions.is_aligned_vaddr] at assumption_alignment
            simp [LeanRV32D.Functions.is_aligned_paddr]
            rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
            omega)]
    simp [is_writable, h_htif_tohost_base]
    rw [if_neg
        (by
          simp; intro h_le
          iterate 2 rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_le
          simp [Int.nonneg_def] at h_le
          grind)]
    unfold_projs
    simp [
      BitVec.extractLsb,
      BitVec.extractLsb'
    ]
    have back_to_usual_mod : forall (a b : ℕ), a.mod b = a % b := by tauto
    repeat rw [back_to_usual_mod]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
    repeat rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
    congr 1
    . congr 1; simp [← BitVec.toNat_inj]
    . simp [← BitVec.toNat_inj]
      omega

lemma execute_STOREB
    (s)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    -- Assumptions
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- and not smaller than the OpenVM address space size
    (assumption_pma_size : OpenVM_address_space_size ≤ pmaRegion.size.toNat)
    -- and the pointer is in the OpenVM address space
    (assumption_pma_fit : rs1_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_address_space_size)    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    LeanRV32D.Functions.execute_STORE imm rs2 rs1 1 s =
    EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
      regs := s.regs,
      choiceState := s.choiceState,
      tags := s.tags,
      cycleCount := s.cycleCount,
      sailOutput := s.sailOutput
      mem :=
        s.mem.insert (rs1_val + BitVec.signExtend 32 imm).toNat (BitVec.extractLsb 7 0 rs2_val)
    }
  := by
    subst privilege

    simp [
      LeanRV32D.Functions.execute_STORE,
      h_rs2_val,
      LeanRV32D.Functions.vmem_write,
      h_rs1_val
    ]
    simp [
      ExceptT.run,
      LeanRV32D.Functions.vmem_write_addr,
      assumption_alignment,
      liftM, monadLift, MonadLift.monadLift
    ]
    iterate 2 (unfold_projs; simp)
    simp [
      h_mstatus,
      h_cur_privilege,
      assumption_MPRV_not_set,
      assumption_pma_regions,
      assumption_pma_base
    ]
    rw [if_pos
        (by
          repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)]
          repeat rw [Int.emod_eq_of_lt (b := 4294967296) (by omega) (by omega)]
          simp [
            LeanRV32D.Functions.is_aligned_vaddr,
            Int.tmod_eq_emod
          ] at assumption_alignment
          omega)]
    obtain ⟨ is_readable, is_writable, is_misaligned_fault ⟩ := assumption_pma_attributes
    simp [is_misaligned_fault]
    rw [if_neg
        (by
            simp [LeanRV32D.Functions.is_aligned_vaddr] at assumption_alignment
            simp [LeanRV32D.Functions.is_aligned_paddr])]
    simp [is_writable, h_htif_tohost_base]
    rw [if_neg
        (by
          simp; intro h_le
          iterate 2 rw [Int.emod_eq_of_lt (by omega) (by omega)] at h_le
          simp [Int.nonneg_def] at h_le
          grind)]
    unfold_projs
    simp [
      BitVec.extractLsb,
      BitVec.extractLsb'
    ]
    have back_to_usual_mod : forall (a b : ℕ), a.mod b = a % b := by tauto
    repeat rw [back_to_usual_mod]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
    repeat rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
    congr 1
    simp [← BitVec.toNat_inj]

  def general_memory_assumptions
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Host-target interface disabled
    Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok .none state ∧
    -- Current privilege is Machine
    Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state ∧
    -- MPRV bit is not set
    (∃ mstatus, Sail.readReg Register.mstatus state = EStateM.Result.ok mstatus state ∧ BitVec.extractLsb 17 17 mstatus = 0#1) ∧
    -- Single PMA region
    (∃ pmaRegion,
      Sail.readReg Register.pma_regions state = EStateM.Result.ok [ pmaRegion ] state ∧
      -- Starting from zero
      pmaRegion.base = 0 ∧
      -- and at least as large as the OpenVM address space
      OpenVM_address_space_size ≤ pmaRegion.size.toNat ∧
      -- and all addresses are readable, writable, and misaligned accesses throw
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)

end Memory

section ControlFlow

  @[simp]
  lemma jump_to_equiv:
    LeanRV32D.Functions.jump_to target state =
      if (BitVec.ofBool target[0]) == 1#1 then EStateM.Result.error (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30") state
        else match state.regs.get? Register.misa with
          | .none => EStateM.Result.error (Sail.Error.Unreachable) state
          | .some _ =>
            if (BitVec.ofBool target[1] == 1#1)
            then EStateM.Result.ok (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr target), (ExceptionType.E_Fetch_Addr_Align ()))) state
            else EStateM.Result.ok (ExecutionResult.Retire_Success ()) (write_reg_state state Register.nextPC target)

  := by
    simp [
      LeanRV32D.Functions.jump_to,
      LeanRV32D.Functions.currentlyEnabled
    ]
    by_cases h_bit_0 : BitVec.ofBool target[0] = 0#1 <;> simp [h_bit_0]
    . cases h_misa: state.regs.get? Register.misa with
      | none =>
        simp [readReg_fail h_misa]
      | some misa_val =>
        simp [readReg_succ h_misa]
        by_cases h_bit_1 : BitVec.ofBool target[1] = 1#1 <;> simp [h_bit_1]
        simp [writeReg_state_success]
    . grind

end ControlFlow
