import OpenvmFv.Spec.LoadStore.local2
import OpenvmFv.Spec.rX_bits

namespace PureSpec

  structure ShInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 32
    r2_val : BitVec 32
    PC : BitVec 32
    plat_ram_size : BitVec 34

  structure ShOutput where
    -- registers
    nextPC : BitVec 32
    -- memory
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREH_sh_pure (input : ShInput) : ShOutput := {
    nextPC := input.PC + 4#32
    data0 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    data1 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat + 1,
      BitVec.extractLsb 15 8 input.r2_val
    )
    : ShOutput
  }

  -- just used to allow the same tactics to handle the case for each non-zero register
  private def bitvec_to_reg (bv: BitVec 5) : Register :=
    match bv with
      | 0#5 => Register.x1 -- purely used for totality, does not come up
      | 1#5 => Register.x1
      | 2#5 => Register.x2
      | 3#5 => Register.x3
      | 4#5 => Register.x4
      | 5#5 => Register.x5
      | 6#5 => Register.x6
      | 7#5 => Register.x7
      | 8#5 => Register.x8
      | 9#5 => Register.x9
      | 10#5 => Register.x10
      | 11#5 => Register.x11
      | 12#5 => Register.x12
      | 13#5 => Register.x13
      | 14#5 => Register.x14
      | 15#5 => Register.x15
      | 16#5 => Register.x16
      | 17#5 => Register.x17
      | 18#5 => Register.x18
      | 19#5 => Register.x19
      | 20#5 => Register.x20
      | 21#5 => Register.x21
      | 22#5 => Register.x22
      | 23#5 => Register.x23
      | 24#5 => Register.x24
      | 25#5 => Register.x25
      | 26#5 => Register.x26
      | 27#5 => Register.x27
      | 28#5 => Register.x28
      | 29#5 => Register.x29
      | 30#5 => Register.x30
      | 31#5 => Register.x31
      | _ => Register.x1

  def sh_state_assumptions
    (i : ShInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    Sail.readReg Register.plat_ram_size state = EStateM.Result.ok i.plat_ram_size state ∧
    -- General memory assumptions
    Local.Assumptions.general_memory_assumptions state ∧
    -- Address is correctly aligned
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 2 = true ∧
    -- Operation does not overflow
    (i.r1_val + BitVec.signExtend 32 i.imm).toNat + 2 < i.plat_ram_size

  set_option maxHeartbeats 0 in
  lemma r1_of_write_state
    {r1 : BitVec 5}
    {r1_val : BitVec 32}
    (pc : BitVec 32)
    (h_r1_val : LeanRV32D.Functions.rX_bits (regidx.Regidx r1) state = EStateM.Result.ok r1_val state)
  :
    LeanRV32D.Functions.rX_bits (regidx.Regidx r1) (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok r1_val (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    by_cases h_r1: r1 = 0
    . simp [
        h_r1, LeanRV32D.Functions.rX_bits, LeanRV32D.Functions.rX
      ] at ⊢ h_r1_val
      exact h_r1_val
    by_cases h_r1 : r1 = 1 <;> [
      skip ; by_cases h_r1 : r1 = 2 <;> [
      skip ; by_cases h_r1 : r1 = 3 <;> [
      skip ; by_cases h_r1 : r1 = 4 <;> [
      skip ; by_cases h_r1 : r1 = 5 <;> [
      skip ; by_cases h_r1 : r1 = 6 <;> [
      skip ; by_cases h_r1 : r1 = 7 <;> [
      skip ; by_cases h_r1 : r1 = 8 <;> [
      skip ; by_cases h_r1 : r1 = 9 <;> [
      skip ; by_cases h_r1 : r1 = 10 <;> [
      skip ; by_cases h_r1 : r1 = 11 <;> [
      skip ; by_cases h_r1 : r1 = 12 <;> [
      skip ; by_cases h_r1 : r1 = 13 <;> [
      skip ; by_cases h_r1 : r1 = 14 <;> [
      skip ; by_cases h_r1 : r1 = 15 <;> [
      skip ; by_cases h_r1 : r1 = 16 <;> [
      skip ; by_cases h_r1 : r1 = 17 <;> [
      skip ; by_cases h_r1 : r1 = 18 <;> [
      skip ; by_cases h_r1 : r1 = 19 <;> [
      skip ; by_cases h_r1 : r1 = 20 <;> [
      skip ; by_cases h_r1 : r1 = 21 <;> [
      skip ; by_cases h_r1 : r1 = 22 <;> [
      skip ; by_cases h_r1 : r1 = 23 <;> [
      skip ; by_cases h_r1 : r1 = 24 <;> [
      skip ; by_cases h_r1 : r1 = 25 <;> [
      skip ; by_cases h_r1 : r1 = 26 <;> [
      skip ; by_cases h_r1 : r1 = 27 <;> [
      skip ; by_cases h_r1 : r1 = 28 <;> [
      skip ; by_cases h_r1 : r1 = 29 <;> [
      skip ; by_cases h_r1 : r1 = 30 <;> [
      skip ; by_cases h_r1 : r1 = 31 <;> [
        skip; (exfalso; grind)
      ]
    ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
    all_goals {
      simp [
        h_r1, LeanRV32D.Functions.rX_bits, LeanRV32D.Functions.rX,
        Sail.readReg, PreSail.readReg, write_reg_state,
        LeanRV32D.Functions.regval_from_reg
      ] at ⊢ h_r1_val
      unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_r1_val
      dsimp at ⊢ h_r1_val
      have :
        (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? (bitvec_to_reg r1) =
        state.regs.get? (bitvec_to_reg r1)
      := by rewrite [h_r1]; simp [bitvec_to_reg]; grind
      rewrite [h_r1] at this
      simp [bitvec_to_reg] at this
      simp [this]
      have : ∃ x_val, state.regs.get? (bitvec_to_reg r1) = .some x_val := by
        by_cases h_contr : ∃ x_val, state.regs.get? (bitvec_to_reg r1) = .some x_val
        . assumption
        . rewrite [h_r1] at h_contr
          simp [bitvec_to_reg] at h_contr
          apply Option.eq_none_iff_forall_ne_some.mpr at h_contr
          simp [h_contr] at h_r1_val
      rewrite [h_r1] at this
      simp [bitvec_to_reg] at this
      obtain ⟨x, h_x⟩ := this
      simp [h_x] at ⊢ h_r1_val
      exact h_r1_val
    }

  lemma mstatus_of_write_state
    {mstatus : BitVec 64}
    (pc : BitVec 32)
    (h_mstatus : Sail.readReg Register.mstatus state = EStateM.Result.ok mstatus state)
  :
    Sail.readReg Register.mstatus (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok mstatus (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_mstatus
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_mstatus
    dsimp at ⊢ h_mstatus
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.mstatus =
      state.regs.get? Register.mstatus
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.mstatus
    . simp [h] at h_mstatus
    . simp [h] at ⊢ h_mstatus
      exact h_mstatus

  lemma cur_privilege_of_write_state
    {cur_privilege : Privilege}
    (pc : BitVec 32)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok cur_privilege state)
  :
    Sail.readReg Register.cur_privilege (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok cur_privilege (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_cur_privilege
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_cur_privilege
    dsimp at ⊢ h_cur_privilege
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.cur_privilege =
      state.regs.get? Register.cur_privilege
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.cur_privilege
    . simp [h] at h_cur_privilege
    . simp [h] at ⊢ h_cur_privilege
      exact h_cur_privilege

  lemma clint_base_of_write_state
    {clint_base : BitVec 34}
    (pc : BitVec 32)
    (h_clint_base : Sail.readReg Register.plat_clint_base state = EStateM.Result.ok clint_base state)
  :
    Sail.readReg Register.plat_clint_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok clint_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_clint_base
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_clint_base
    dsimp at ⊢ h_clint_base
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.plat_clint_base =
      state.regs.get? Register.plat_clint_base
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.plat_clint_base
    . simp [h] at h_clint_base
    . simp [h] at ⊢ h_clint_base
      exact h_clint_base

  lemma clint_size_of_write_state
    {clint_size : BitVec 34}
    (pc : BitVec 32)
    (h_clint_size : Sail.readReg Register.plat_clint_size state = EStateM.Result.ok clint_size state)
  :
    Sail.readReg Register.plat_clint_size (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok clint_size (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_clint_size
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_clint_size
    dsimp at ⊢ h_clint_size
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.plat_clint_size =
      state.regs.get? Register.plat_clint_size
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.plat_clint_size
    . simp [h] at h_clint_size
    . simp [h] at ⊢ h_clint_size
      exact h_clint_size

  lemma ram_base_of_write_state
    {ram_base : BitVec 34}
    (pc : BitVec 32)
    (h_ram_base : Sail.readReg Register.plat_ram_base state = EStateM.Result.ok ram_base state)
  :
    Sail.readReg Register.plat_ram_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok ram_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_ram_base
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_ram_base
    dsimp at ⊢ h_ram_base
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.plat_ram_base =
      state.regs.get? Register.plat_ram_base
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.plat_ram_base
    . simp [h] at h_ram_base
    . simp [h] at ⊢ h_ram_base
      exact h_ram_base

  lemma ram_size_of_write_state
    {ram_size : BitVec 34}
    (pc : BitVec 32)
    (h_ram_size : Sail.readReg Register.plat_ram_size state = EStateM.Result.ok ram_size state)
  :
    Sail.readReg Register.plat_ram_size (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok ram_size (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_ram_size
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_ram_size
    dsimp at ⊢ h_ram_size
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.plat_ram_size =
      state.regs.get? Register.plat_ram_size
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.plat_ram_size
    . simp [h] at h_ram_size
    . simp [h] at ⊢ h_ram_size
      exact h_ram_size

  lemma rom_base_of_write_state
    {rom_base : BitVec 34}
    (pc : BitVec 32)
    (h_rom_base : Sail.readReg Register.plat_rom_base state = EStateM.Result.ok rom_base state)
  :
    Sail.readReg Register.plat_rom_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok rom_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_rom_base
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_rom_base
    dsimp at ⊢ h_rom_base
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.plat_rom_base =
      state.regs.get? Register.plat_rom_base
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.plat_rom_base
    . simp [h] at h_rom_base
    . simp [h] at ⊢ h_rom_base
      exact h_rom_base

  lemma rom_size_of_write_state
    {rom_size : BitVec 34}
    (pc : BitVec 32)
    (h_rom_size : Sail.readReg Register.plat_rom_size state = EStateM.Result.ok rom_size state)
  :
    Sail.readReg Register.plat_rom_size (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok rom_size (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_rom_size
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_rom_size
    dsimp at ⊢ h_rom_size
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.plat_rom_size =
      state.regs.get? Register.plat_rom_size
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.plat_rom_size
    . simp [h] at h_rom_size
    . simp [h] at ⊢ h_rom_size
      exact h_rom_size

  lemma htif_tohost_base_of_write_state
    {htif_tohost_base : Option (BitVec 34)}
    (pc : BitVec 32)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok htif_tohost_base state)
  :
    Sail.readReg Register.htif_tohost_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok htif_tohost_base (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_htif_tohost_base
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_htif_tohost_base
    dsimp at ⊢ h_htif_tohost_base
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.htif_tohost_base =
      state.regs.get? Register.htif_tohost_base
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.htif_tohost_base
    . simp [h] at h_htif_tohost_base
    . simp [h] at ⊢ h_htif_tohost_base
      exact h_htif_tohost_base

  def modify_memory_2
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_output: ShOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((s.mem.insert sh_output.data0.1 sh_output.data0.2
      ).insert sh_output.data1.1 sh_output.data1.2)
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  set_option maxHeartbeats 0 in
  lemma execute_STOREH_sh_pure_equiv
    (sh_input : ShInput)
    (h_assumptions : sh_state_assumptions sh_input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.STORE (
          sh_input.imm,
          regidx.Regidx sh_input.r2,
          regidx.Regidx sh_input.r1,
          2
        ))
    ) state =
    let sh_output := execute_STOREH_sh_pure sh_input
    (do
      Sail.writeReg Register.nextPC sh_output.nextPC
      set (modify_memory_2 (← get) sh_output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    obtain ⟨
      h_pc,
      h_r1_val,
      h_r2_val,
      h_plat_ram_size,
      ⟨
        h_cur_privilege,
        ⟨ mstatus, ⟨ h_mstatus, h_plat_mstatus_val⟩ ⟩,
        h_plat_clint_base_val,
        h_plat_clint_size_val,
        h_plat_rom_base_val,
        h_plat_rom_size_val,
        h_plat_ram_base_val,
        h_plat_htif_tohost_base_val
      ⟩,
      h_aligned,
      h_does_fit
    ⟩ := h_assumptions

    simp [
      readReg_state h_pc,
      writeReg_state_success,
    ]

    replace h_r1_val := r1_of_write_state sh_input.PC h_r1_val
    replace h_r2_val := r1_of_write_state sh_input.PC h_r2_val
    replace h_mstatus := mstatus_of_write_state sh_input.PC h_mstatus
    replace h_cur_privilege := cur_privilege_of_write_state sh_input.PC h_cur_privilege
    replace h_clint_base := clint_base_of_write_state sh_input.PC h_plat_clint_base_val
    replace h_clint_size := clint_size_of_write_state sh_input.PC h_plat_clint_size_val
    replace h_plat_ram_base := ram_base_of_write_state sh_input.PC h_plat_ram_base_val
    replace h_plat_ram_size := ram_size_of_write_state sh_input.PC h_plat_ram_size
    replace h_plat_rom_base := rom_base_of_write_state sh_input.PC h_plat_rom_base_val
    replace h_plat_rom_size := rom_size_of_write_state sh_input.PC h_plat_rom_size_val
    replace h_htif_tohost_base := htif_tohost_base_of_write_state sh_input.PC h_plat_htif_tohost_base_val

    have h_execute_store := Local.execute_STOREH_simplified
      (write_reg_state state Register.nextPC (Sail.BitVec.addInt sh_input.PC 4))
      h_aligned
      h_r1_val
      h_r2_val
      h_mstatus
      h_cur_privilege
      h_clint_base
      h_clint_size
      h_plat_ram_base
      h_plat_rom_base
      h_plat_ram_size
      h_plat_rom_size
      h_htif_tohost_base
      h_plat_mstatus_val
      h_does_fit

    rewrite [
      Local.execute_store_instruction
    ]
    simp only [Int.toNat]
    rewrite [
      h_execute_store
    ]

    unfold write_reg_state
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get
    simp [EStateM.instMonadStateOf, EStateM.get, EStateM.set, modify_memory_2, execute_STOREH_sh_pure, Sail.BitVec.addInt]

end PureSpec
