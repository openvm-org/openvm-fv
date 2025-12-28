import OpenvmFv.Spec.run_hart_active
import OpenvmFv.Spec.LoadStore.local

namespace Local

  set_option maxHeartbeats 1_000_000_000

  attribute [local simp]
    instBEqSATPMode.beq

    getThe
    instMonadStateOfMonadStateOf
    pure

    BitVec.extend

    Int.le
    Int.neg
    Int.negOfNat
    Int.sub

    Functor.map

    untilFuelM
    untilFuelM.go

    Sail.BitVec.addInt
    Sail.BitVec.extractLsb
    Sail.BitVec.signExtend
    Sail.BitVec.updateSubrange
    Sail.BitVec.updateSubrange'
    Sail.BitVec.zeroExtend
    zero_extend
    Sail.get_slice_int

    Sail.SailME.run
    PreSail.PreSailME.run
    Sail.ConcurrencyInterfaceV1.sail_mem_read
    PreSail.ConcurrencyInterfaceV1.sail_mem_read
    Sail.ConcurrencyInterfaceV1.sail_mem_write
    PreSail.ConcurrencyInterfaceV1.sail_mem_write
    PreSail.readBytes
    PreSail.readByte
    PreSail.writeBytes
    PreSail.writeByte

    ExceptT.bind
    ExceptT.bindCont
    ExceptT.lift
    ExceptT.map
    ExceptT.mk
    ExceptT.pure

    EStateM.bind
    EStateM.get
    EStateM.map
    EStateM.instMonadStateOf
    EStateM.pure

    LeanRV32D.Functions.ext_data_get_addr
    LeanRV32D.Functions.check_misaligned
    LeanRV32D.Functions.plat_enable_misaligned_access
    LeanRV32D.Functions.split_misaligned
    LeanRV32D.Functions.translateAddr
    LeanRV32D.Functions.effectivePrivilege
    LeanRV32D.Functions._get_Mstatus_MPRV
    LeanRV32D.Functions.mem_read
    LeanRV32D.Functions.mem_read_priv
    LeanRV32D.Functions.mem_read_priv_meta
    LeanRV32D.Functions.checked_mem_read
    LeanRV32D.Functions.phys_access_check
    LeanRV32D.Functions.bits_of_virtaddr
    LeanRV32D.Functions.pmpCheck
    LeanRV32D.Functions.sys_pmp_count
    LeanRV32D.Functions.pmaCheck
    LeanRV32D.Functions.matching_pma
    LeanRV32D.Functions.matching_pma_bits_range
    LeanRV32D.Functions.range_subset
    LeanRV32D.Functions.zopz0zIzJ_u
    LeanRV32D.Functions.bits_of_physaddr
    LeanRV32D.Functions.to_bits
    LeanRV32D.Functions.not
    LeanRV32D.Functions.to_bits_checked
    LeanRV32D.Functions.within_mmio_readable
    LeanRV32D.Functions.get_config_rvfi
    LeanRV32D.Functions.within_clint
    LeanRV32D.Functions.within_htif_readable
    LeanRV32D.Functions.within_htif_writable
    LeanRV32D.Functions.read_kind_of_flags
    LeanRV32D.Functions.read_ram
    LeanRV32D.Functions.MemoryOpResult_drop_meta
    LeanRV32D.Functions.misaligned_order
    LeanRV32D.Functions.sys_misaligned_order_decreasing
    LeanRV32D.Functions.zeros
    LeanRV32D.Functions.xlen_bytes
    LeanRV32D.Functions.sign_extend
    LeanRV32D.Functions.extend_value
    LeanRV32D.Functions.Data
    LeanRV32D.Functions.mem_write_ea
    LeanRV32D.Functions.write_kind_of_flags
    LeanRV32D.Functions.mem_write_value
    LeanRV32D.Functions.mem_write_value_meta
    LeanRV32D.Functions.mem_write_value_priv_meta
    LeanRV32D.Functions.checked_mem_write
    LeanRV32D.Functions.within_mmio_writable
    LeanRV32D.Functions.write_ram

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
    (assumption_mem_ptr : reg_val.toNat + offset.toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 4 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
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
  unfold
    LeanRV32D.Functions.vmem_read

  -- From vmem_read to vmem_read_addr
  simp [
    EStateM.run,
    EStateM.map,
    h_reg_val
  ]
  -- Entering vmem_read_addr
  simp [
    LeanRV32D.Functions.vmem_read_addr,
    ExceptT.run,
    liftM, monadLift, MonadLift.monadLift,
    assumption_alignment
  ]
  unfold_projs
  simp [
    bind,
    h_mstatus,
    h_cur_privilege,
    assumption_MPRV_not_set,
    (Local.translation_mode assumption_privilege)
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
    (assumption_mem_ptr : reg_val.toNat + offset.toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
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
  unfold
    LeanRV32D.Functions.vmem_read

  -- From vmem_read to vmem_read_addr
  simp [
    EStateM.run,
    EStateM.map,
    h_reg_val
  ]
  -- Entering vmem_read_addr
  simp [
    LeanRV32D.Functions.vmem_read_addr,
    ExceptT.run,
    liftM, monadLift, MonadLift.monadLift,
    assumption_alignment
  ]
  unfold_projs
  simp [
    bind,
    h_mstatus,
    h_cur_privilege,
    assumption_MPRV_not_set,
    (Local.translation_mode assumption_privilege)
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
    (assumption_mem_ptr : reg_val.toNat + offset.toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
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
  unfold
    LeanRV32D.Functions.vmem_read

  -- From vmem_read to vmem_read_addr
  simp [
    EStateM.run,
    EStateM.map,
    h_reg_val
  ]
  -- Entering vmem_read_addr
  simp [
    LeanRV32D.Functions.vmem_read_addr,
    ExceptT.run,
    liftM, monadLift, MonadLift.monadLift,
    assumption_alignment
  ]
  unfold_projs
  simp [
    bind,
    h_mstatus,
    h_cur_privilege,
    assumption_MPRV_not_set,
    (Local.translation_mode assumption_privilege)
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
  rw [if_neg (by simp [LeanRV32D.Functions.is_aligned_paddr])]
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

  lemma execute_LOAD_simplified
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
    (assumption_mem_ptr : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 4 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    execute_LOAD imm rs1 rd true 4 s =
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
      assumption_mem_ptr
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [execute_LOAD, this]
    aesop

  lemma execute_LOADHU_simplified
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
    (assumption_mem_ptr : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    execute_LOAD imm rs1 rd true 2 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend (data₁ ++ data₀) 32 false) s with
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
      assumption_mem_ptr
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [execute_LOAD, this]
    aesop

  lemma execute_LOADH_simplified
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
    (assumption_mem_ptr : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    execute_LOAD imm rs1 rd false 2 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend (data₁ ++ data₀) 32 true) s with
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
      assumption_mem_ptr
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [execute_LOAD, this]
    aesop

  lemma execute_LOADBU_simplified
    (s)
    (rd : regidx)
    (data₀ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    -- Assumptions
    (assumption_mem_ptr : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    execute_LOAD imm rs1 rd true 1 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend data₀ 32 false) s with
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
      assumption_mem_ptr
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [execute_LOAD, this]
    aesop

  lemma execute_LOADB_simplified
    (s)
    (rd : regidx)
    (data₀ : BitVec 8)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    -- Assumptions
    (assumption_mem_ptr : reg_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
    -- All addresses are readable, writable, and misaligned accesses throw
    (assumption_pma_attributes :
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
  :
    execute_LOAD imm rs1 rd false 1 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend data₀ 32 true) s with
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
      assumption_mem_ptr
      assumption_alignment
      assumption_privilege
      assumption_MPRV_not_set
      assumption_pma_regions
      assumption_pma_base
      assumption_pma_size
      assumption_pma_attributes
    simp [EStateM.run] at this
    simp [execute_LOAD, this]
    aesop

  lemma execute_load_instruction:
    LeanRV32D.Functions.execute (instruction.LOAD (imm, rs1, rd, is_unsigned, width)) =
    LeanRV32D.Functions.execute_LOAD imm rs1 rd is_unsigned width
  := rfl

  lemma execute_STOREW_simplified
    (s)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    -- Assumptions
    (assumption_mem_ptr : rs1_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 4 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
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
      (Local.translation_mode assumption_privilege),
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
      modify,
      EStateM.modifyGet,
      BitVec.extractLsb,
      BitVec.extractLsb'
    ]
    have back_to_usual_mod : forall (a b : ℕ), a.mod b = a % b := by tauto
    repeat rw [back_to_usual_mod]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]

lemma execute_STOREH_simplified
    (s)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    -- Assumptions
    (assumption_mem_ptr : rs1_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 2 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
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
      (Local.translation_mode assumption_privilege),
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
      modify,
      EStateM.modifyGet,
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

lemma execute_STOREB_simplified
    (s)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus : Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege : Sail.readReg Register.cur_privilege s = EStateM.Result.ok privilege s)
    (h_htif_tohost_base : Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    -- Assumptions
    (assumption_mem_ptr : rs1_val.toNat + (BitVec.signExtend 32 imm).toNat < OpenVM_memory_address_space_size)
    (assumption_alignment : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 1 = true)
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 mstatus = 0)
    -- PMA assumptions
    -- Single region
    (assumption_pma_regions : Sail.readReg Register.pma_regions s = EStateM.Result.ok [ pmaRegion ] s)
    -- Starting from zero
    (assumption_pma_base : pmaRegion.base = 0)
    -- At least as large as the address space in size
    (assumption_pma_size : OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat)
    -- All addresses are readable, writable, and misaligned accesses throw
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
      (Local.translation_mode assumption_privilege),
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
      modify,
      EStateM.modifyGet,
      BitVec.extractLsb,
      BitVec.extractLsb'
    ]
    have back_to_usual_mod : forall (a b : ℕ), a.mod b = a % b := by tauto
    repeat rw [back_to_usual_mod]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
    repeat rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
    congr 1
    simp [← BitVec.toNat_inj]

  lemma execute_store_instruction:
    LeanRV32D.Functions.execute (instruction.STORE (imm, rs2, rs1, width)) =
    LeanRV32D.Functions.execute_STORE imm rs2 rs1 width
  := rfl

end Local

namespace Local.Assumptions

  def general_memory_assumptions
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok .none state ∧
    Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state ∧
    (∃ mstatus, Sail.readReg Register.mstatus state = EStateM.Result.ok mstatus state ∧ BitVec.extractLsb 17 17 mstatus = 0#1) ∧
    (∃ pmaRegion,
      Sail.readReg Register.pma_regions state = EStateM.Result.ok [ pmaRegion ] state ∧
      pmaRegion.base = 0 ∧
      OpenVM_memory_address_space_size ≤ pmaRegion.size.toNat ∧
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)

end Local.Assumptions

namespace Local.RegisterInvariants

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

  lemma pma_regions_of_write_state
    {pma_regions : List PMA_Region}
    (pc : BitVec 32)
    (h_pma_regions : Sail.readReg Register.pma_regions state = EStateM.Result.ok pma_regions state)
  :
    Sail.readReg Register.pma_regions (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok pma_regions (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_pma_regions
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_pma_regions
    dsimp at ⊢ h_pma_regions
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.pma_regions =
      state.regs.get? Register.pma_regions
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.pma_regions
    . simp [h] at h_pma_regions
    . simp [h] at ⊢ h_pma_regions
      exact h_pma_regions

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

end Local.RegisterInvariants
