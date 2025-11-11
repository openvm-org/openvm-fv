import OpenvmFv.Spec.Load.local2
import OpenvmFv.Spec.rX_bits

namespace PureSpec

  structure LwInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    -- registers
    r1_val : BitVec 32
    PC : BitVec 32
    mstatus : BitVec 64
    cur_privilege : Privilege
    plat_clint_base : BitVec 34
    plat_clint_size : BitVec 34
    plat_ram_base : BitVec 34
    plat_ram_size : BitVec 34
    plat_rom_base : BitVec 34
    plat_rom_size : BitVec 34
    htif_tohost_base : Option (BitVec 34)
    -- memory
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8

  structure LwOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  def execute_LOAD_lw_pure (input : LwInput) : LwOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          by
            apply Finset.mem_Icc.mpr;
            done
        ⟩,
        input.data3 ++ input.data2 ++ input.data1 ++ input.data0
      )
    : LwOutput
  }

  def bitvec_to_reg (bv: BitVec 5) : Register :=
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

  def lw_state_assumptions
    (i : LwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 4 = true ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    Sail.readReg Register.mstatus state = EStateM.Result.ok i.mstatus state ∧
    Sail.readReg Register.cur_privilege state = EStateM.Result.ok i.cur_privilege state ∧
    Sail.readReg Register.plat_clint_base state = EStateM.Result.ok i.plat_clint_base state ∧
    Sail.readReg Register.plat_clint_size state = EStateM.Result.ok i.plat_clint_size state ∧
    Sail.readReg Register.plat_ram_base state = EStateM.Result.ok i.plat_ram_base state ∧
    Sail.readReg Register.plat_rom_base state = EStateM.Result.ok i.plat_rom_base state ∧
    Sail.readReg Register.plat_ram_size state = EStateM.Result.ok i.plat_ram_size state ∧
    Sail.readReg Register.plat_rom_size state = EStateM.Result.ok i.plat_rom_size state ∧
    Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok i.htif_tohost_base state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat]? = .some i.data0 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 3]? = .some i.data3 ∧
    state.regs.get? Register.PC = .some i.PC ∧
    i.cur_privilege = Privilege.Machine ∧
    i.plat_clint_base = 0 ∧
    i.plat_clint_size = 0 ∧
    i.plat_ram_base = 0 ∧
    i.plat_ram_size = (BitVec.ofNat 34 (2^32 - 1)) ∧
    i.plat_rom_base = 0 ∧
    i.htif_tohost_base = .none ∧
    BitVec.extractLsb 17 17 i.mstatus = 0#1 ∧
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 4 < 2^32

  set_option maxHeartbeats 0 in
  lemma execute_LOAD_lw_pure_equiv
    (lw_input : LwInput)
    (h_assumptions : lw_state_assumptions lw_input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.LOAD (
          lw_input.imm,
          regidx.Regidx lw_input.r1,
          regidx.Regidx lw_input.rd,
          true,
          4
        ))
    ) state =
    let lw_output := execute_LOAD_lw_pure lw_input
    (do
      Sail.writeReg Register.nextPC lw_output.nextPC
      match lw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    obtain ⟨
      h_aligned,
      h_r1_val,
      h_mstatus,
      h_cur_privilege,
      h_clint_base,
      h_clint_size,
      h_plat_ram_base,
      h_plat_rom_base,
      h_plat_ram_size,
      h_plat_rom_size,
      h_htif_tohost_base,
      h_mem_0,
      h_mem_1,
      h_mem_2,
      h_mem_3,
      h_pc,
      h_cur_privilege_val,
      h_plat_clint_base_val,
      h_plat_clint_size_val,
      h_plat_ram_base_val,
      h_plat_ram_size_val,
      h_plat_rom_base_val,
      h_htif_tohost_base_val,
      h_mstatus_val,
      h_does_fit
    ⟩ := h_assumptions

    rewrite [h_cur_privilege_val] at h_cur_privilege
    rewrite [h_plat_clint_base_val] at h_clint_base
    rewrite [h_plat_clint_size_val] at h_clint_size
    rewrite [h_plat_ram_base_val] at h_plat_ram_base
    rewrite [h_plat_ram_size_val] at h_plat_ram_size
    rewrite [h_plat_rom_base_val] at h_plat_rom_base
    rewrite [h_htif_tohost_base_val] at h_htif_tohost_base


    simp [
      readReg_state h_pc,
      writeReg_state_success,
    ]

    rewrite [
      Local.execute_load_instruction,
      ←Local.execute_LOAD_equiv
    ]
    simp

    set state' := (write_reg_state state Register.nextPC (Sail.BitVec.addInt lw_input.PC 4)) with h_state'

    replace h_r1_val : LeanRV32D.Functions.rX_bits (regidx.Regidx lw_input.r1) state' = EStateM.Result.ok lw_input.r1_val state' := by
      clear *- h_r1_val h_state'
      rewrite [h_state']
      by_cases h_r1: lw_input.r1 = 0
      . simp [
         h_r1, LeanRV32D.Functions.rX_bits, LeanRV32D.Functions.rX
        ] at ⊢ h_r1_val
        exact h_r1_val
      by_cases h_r1 : lw_input.r1 = 1 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 2 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 3 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 4 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 5 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 6 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 7 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 8 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 9 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 10 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 11 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 12 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 13 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 14 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 15 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 16 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 17 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 18 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 19 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 20 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 21 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 22 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 23 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 24 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 25 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 26 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 27 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 28 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 29 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 30 <;> [
        skip ; by_cases h_r1 : lw_input.r1 = 31 <;> [
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
          (state.regs.insert Register.nextPC (Sail.BitVec.addInt lw_input.PC 4)).get? (bitvec_to_reg lw_input.r1) =
          state.regs.get? (bitvec_to_reg lw_input.r1)
        := by rewrite [h_r1]; simp [bitvec_to_reg]; grind
        rewrite [h_r1] at this
        simp [bitvec_to_reg] at this
        simp [this]
        have : ∃ x_val, state.regs.get? (bitvec_to_reg lw_input.r1) = .some x_val := by
          by_cases h_contr : ∃ x_val, state.regs.get? (bitvec_to_reg lw_input.r1) = .some x_val
          . assumption
          . rewrite [h_r1] at h_contr
            simp [bitvec_to_reg] at h_contr
            apply Option.eq_none_iff_forall_ne_some.mpr at h_contr
            simp [h_contr] at h_r1_val
            done
        rewrite [h_r1] at this
        simp [bitvec_to_reg] at this
        obtain ⟨x, h_x⟩ := this
        simp [h_x] at ⊢ h_r1_val
        exact h_r1_val
      }

    replace h_mstatus :
      Sail.readReg Register.mstatus state' =
      EStateM.Result.ok lw_input.mstatus state'
    := by
      rewrite [h_state']
      clear *-h_mstatus
      simp [
        Sail.readReg, PreSail.readReg, write_reg_state
      ] at ⊢ h_mstatus
      unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_mstatus
      dsimp at ⊢ h_mstatus
      have :
        (state.regs.insert Register.nextPC (Sail.BitVec.addInt lw_input.PC 4)).get? Register.mstatus =
        state.regs.get? Register.mstatus
      := by grind
      simp [this, h_mstatus]
      done




    have h_execute_load := Local.execute_LOAD_simplified
      state'
      (regidx.Regidx lw_input.rd)
      lw_input.data0
      lw_input.data1
      lw_input.data2
      lw_input.data3
      h_aligned
      h_r1_val
      -- h_mstatus
      -- h_cur_privilege
      -- h_clint_base
      -- h_clint_size
      -- h_plat_ram_base
      -- h_plat_rom_base
      -- h_plat_ram_size
      -- h_plat_rom_size
      -- h_htif_tohost_base
      -- h_mstatus_val
      -- h_does_fit
      -- h_mem_0
      -- h_mem_1
      -- h_mem_2
      -- h_mem_3

    rewrite [
      Local.execute_LOAD_equiv,
      h_execute_load
    ]



    unfold bind Monad.toBind EStateM.instMonad
    dsimp
    unfold EStateM.bind
    dsimp

    simp [
      readReg_state h_input_pc,
      writeReg_state_success,
      ←Local.execute_equiv,
      Local.execute.eq_def
    ]

    have (x : BitVec 32) : Sail.BitVec.addInt x 4 = x + 4 := rfl
    simp [this]

    have := Local.execute_LOAD_simplified
      lw_input.data0
      lw_input.data1
      lw_input.data2
      lw_input.data3


    simp [
      Local.execute_LOAD_simplified
    ]

    simp [
      ←Local.execute_RTYPE_equiv,
      Local.execute_RTYPE.eq_def,
      bind, EStateM.instMonad, EStateM.bind
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_reg_state_nextPC _ h_input_r1]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_reg_state_nextPC _ h_input_r2]
    simp [EStateM.pure]

    simp [execute_RTYPE_add_pure]

    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_0_equiv]
      simp
      rewrite [dite_cond_eq_true]
      . simp
      . simp [h_input_rd, h_zero, regidx_to_fin]
    . have h_inc := regidx_non_zero h_zero
      apply Finset.mem_Icc.mp at h_inc
      obtain ⟨h_low, h_high⟩ := h_inc
      rewrite [
        wX_write_xreg_equiv _ _
          (regidx.Regidx rd)
          ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
          (by simp [regidx_to_fin])
      ]
      simp [regidx_to_fin]
      rewrite [dite_cond_eq_false]
      . simp [h_input_rd, regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
