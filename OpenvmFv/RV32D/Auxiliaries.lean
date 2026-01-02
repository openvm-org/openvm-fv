import LeanRV32D
import Mathlib

namespace ExtDHashMap

  lemma insert_eq_self [BEq K] [LawfulBEq K] [Hashable K]
    (m : Std.ExtDHashMap K V)
    (h : m.get? k = .some v)
  :
    m.insert k v = m
  := by
    grind

  lemma insert_comm [BEq K] [LawfulBEq K] [Hashable K]
    (m : Std.ExtDHashMap K V)
    (h_neq : ¬ K₁ = K₂)
  :
    (m.insert K₁ V₁).insert K₂ V₂ = (m.insert K₂ V₂).insert K₁ V₁
  := by
    grind


end ExtDHashMap

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
  Int.tmod_eq_emod

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
  LeanRV32D.Functions.allowed_misaligned
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
  LeanRV32D.Functions.is_aligned_vaddr
  LeanRV32D.Functions.is_aligned_paddr
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

  @[simp]
  lemma register_type_reg_of_fin_equiv (r : Fin 32) :
    RegisterType (reg_of_fin r) = BitVec 32
  := by
    fin_cases r <;>
    simp [reg_of_fin, RegisterType]

  @[simp]
  lemma register_type_pc_equiv :
    RegisterType Register.PC = BitVec 32
  := by
    simp [RegisterType]

  /-- Register read in terms of Fin 32 -/
  def read_xreg (reg : Fin 32) : SailM (BitVec 32) :=
    match reg.1 with
      | 0 => pure (0#32)
      | _ => (register_type_reg_of_fin_equiv reg) ▸ (Sail.readReg (reg_of_fin reg))

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
        (result (cast (by rw [register_type_reg_of_fin_equiv]) val))

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
    have h_reg : (¬ r1 = 0) → state.regs.get? (reg_of_fin r1) = .some (cast (by rw [register_type_reg_of_fin_equiv]) read_val)
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

  lemma insert_reg_eq_self
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {r : Fin 32}
    (h_r_not_zero : ¬ r.val = 0)
    (h_read_xreg : (read_xreg r state = EStateM.Result.ok val state))
  :
    state.regs.insert (reg_of_fin r) ((register_type_reg_of_fin_equiv r) ▸ val) = state.regs
  := by
    rw [ExtDHashMap.insert_eq_self]
    suffices h_some : ((register_type_reg_of_fin_equiv r) ▸ (state.regs.get? (reg_of_fin r))) = .some val
    . generalize_proofs pfl pft at h_some
      rw [← eq_rec_inj (h := pft)]
      grind
    . simp [read_xreg, Sail.readReg, PreSail.readReg] at h_read_xreg
      cases h : state.regs.get? (reg_of_fin r) <;>
        fin_cases r <;> simp_all

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

  @[simp]
  lemma bare_is_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl

  lemma arithmetic_helper
    (h_ub : a + b < OpenVM_address_space_size)
  :
    (a + b) % 4294967296 = (a + b) ∧
    (a + b) % 17179869184 = (a + b) ∧
    (a + b) % 18446744073709551616 = (a + b)
  := by
    omega

  def general_memory_assumptions
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
  : Prop :=
    -- Assumption A2: no host-target interface
    Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok .none state ∧
    -- Assumption A3: machine privilege
    Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state ∧
    -- Assumption A3: MPRV bit of the mstatus register not set
    (Sail.readReg Register.mstatus state = EStateM.Result.ok mstatus state ∧ BitVec.extractLsb 17 17 mstatus = 0#1) ∧
    -- A4.1 : Single PMA region
    Sail.readReg Register.pma_regions state = EStateM.Result.ok [ pmaRegion ] state ∧
    -- A4.2 : with base 0 and at least 2^29 bytes in size
    pmaRegion.base = 0 ∧
    OpenVM_address_space_size ≤ pmaRegion.size.toNat ∧
    -- A4.3 : with all addresses readable and writable, and misaligned accesses treated as errors
    pmaRegion.attributes.readable ∧
    pmaRegion.attributes.writable ∧
    pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault

  lemma gma_invariant_under_pc_increment
    (assumptions : general_memory_assumptions s mstatus pmaRegion)
  :
    general_memory_assumptions (write_reg_state s Register.nextPC val) mstatus pmaRegion
  := by
    obtain ⟨ h_htif, h_priv, h_mprv , h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned ⟩ := assumptions
    simp [general_memory_assumptions]
    split_ands
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_htif (by trivial)]
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_priv (by trivial)]
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_mprv.1 (by trivial)]
    . exact h_mprv.2
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_pma_regions (by trivial)]
    all_goals assumption

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

section Spec

  @[simp]
  noncomputable def execute_instruction
    (instr : instruction)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :=
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute instr
    ) state

end Spec
