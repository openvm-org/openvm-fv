import OpenvmFv.Spec.run_hart_active
import OpenvmFv.Spec.LoadStore.local


namespace Local

  lemma run_vmem_read_of_width_4'
    (offset : BitVec 32)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 4 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + offset).toNat + 4 < ram_size)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + offset).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + offset).toNat + 3]? = some data₃) :
    let width := 4
    let data := data₃ ++ data₂ ++ data₁ ++ data₀
    (LeanRV32D.Functions.vmem_read
      rs
      offset
      width (AccessType.Read ())
      false false false
    ).run s = .ok (.Ok data) s
  := by
  rewrite [←vmem_read_equiv, vmem_read'_equiv]
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296]? = some data₀ := by
    clear *- hmem₀ h_does_fit
    convert hmem₀
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 1]? = some data₁ := by
    clear *- hmem₁ h_does_fit
    convert hmem₁
  have hmem₂' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 2]? = some data₂ := by
    clear *- hmem₂ h_does_fit
    convert hmem₂
  have hmem₃' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 3]? = some data₃ := by
    clear *- hmem₃ h_does_fit
    convert hmem₃

  simp [
    Nat.reduceMul, vmem_read',
    Sail.SailME.run,
    LeanRV32D.Functions.ext_data_get_addr,
    bind_pure_comp,
    Bool.false_eq_true, ↓reduceIte,
    LeanRV32D.Functions.plat_enable_misaligned_access,
    LeanRV32D.Functions.split_misaligned,
    LeanRV32D.Functions.allowed_misaligned,
    LeanRV32D.Functions.check_misaligned,
    CharP.cast_eq_zero, gt_iff_lt, Nat.ofNat_pos,
    Int.toNat_lt', Nat.cast_ofNat, decide_eq_true_eq,
    LeanRV32D.Functions.bits_of_virtaddr,
    Bool.if_false_left,
    Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_lt,
    Sail.assert, PreSail.assert,
    beq_iff_eq,
    LeanRV32D.Functions.misaligned_order,
    LeanRV32D.Functions.sys_misaligned_order_decreasing,
    Int.toNat_zero, Int.pred_toNat,
    Int.toNat_natCast_add_one, Prod.mk.eta,
    pure_bind, bind_assoc,
    EStateM.run, Functor.map,
    ExceptT.map, ExceptT.mk, ExceptT.run,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift
  ]

  unfold_projs
  simp [
    ExceptT.bind, ExceptT.mk, EStateM.map, h_reg_val,
    ExceptT.bindCont, ExceptT.pure,
    h_aligned,
    untilFuelM,
    untilFuelM.go
  ]
  have h_pmp_check := pmp_check_machine_read reg_val offset 4 s
  simp [EStateM.run] at h_pmp_check
  simp [
    LeanRV32D.Functions.translateAddr,
    h_mstatus,
    h_cur_privilege,
    bind, ExceptT.bind, EStateM.bind, ExceptT.mk,
    LeanRV32D.Functions.translationMode,
    LeanRV32D.Functions.effectivePrivilege,
    hfetch,
    LeanRV32D.Functions._get_Mstatus_MPRV,
    Sail.BitVec.extractLsb,
    h_mprv_disabled,
    hmachine, hsatp_bare,
    LeanRV32D.Functions.mem_read,
    LeanRV32D.Functions.mem_read_priv,
    LeanRV32D.Functions.mem_read_priv_meta,
    LeanRV32D.Functions.checked_mem_read,
    LeanRV32D.Functions.phys_access_check,
    LeanRV32D.Functions.sys_pmp_count,
    h_pmp_check,
    LeanRV32D.Functions.bits_of_virtaddr
  ]

  simp [
    LeanRV32D.Functions.within_mmio_readable,
    LeanRV32D.Functions.get_config_rvfi,
    LeanRV32D.Functions.within_clint,
    h_clint_base,
    h_clint_size,
    LeanRV32D.Functions.within_htif_readable,
    LeanRV32D.Functions.within_htif_writable,
    h_htif_tohost_base,
    LeanRV32D.Functions.zero_extend,
    Sail.BitVec.zeroExtend,
    Sail.BitVec.addInt,
  ]

  rewrite [ite_cond_eq_false _ _ (by simp; omega)]
  simp [
    EStateM.bind,
    LeanRV32D.Functions.within_phys_mem,
  ]

  simp only [
    h_plat_ram_base,
    h_plat_rom_base,
    h_plat_ram_size,
    h_plat_rom_size,
    Nat.reducePow,
    BitVec.toNat_ofNat,
    CharP.cast_eq_zero,
    Nat.reduceMod,
    zero_add,
    BitVec.ofNat_eq_ofNat,
    decide_true,
    ↓dreduceIte,
  ]
  rewrite [ite_cond_eq_true]; swap
  . simp
    clear *-h_does_fit
    simp at h_does_fit
    rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
    simp [← BitVec.ult_iff_lt, BitVec.ult_iff_toNat_lt] at h_does_fit
    omega

  simp [
    LeanRV32D.Functions.phys_mem_read,
    LeanRV32D.Functions.read_kind_of_flags,
    LeanRV32D.Functions.read_ram,
    Sail.sail_mem_read, PreSail.sail_mem_read,
    PreSail.readBytes,
    PreSail.readByte
  ]
  unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf
  dsimp [EStateM.get]

  have h_mod (n: ℕ) : n % 4294967296 % 17179869184 = n % 4294967296 := by omega
  rewrite [h_mod]

  simp [
    hmem₀',
    hmem₁',
    hmem₂',
    hmem₃'
  ]
  simp [
    LeanRV32D.Functions.MemoryOpResult_drop_meta,
    ExceptT.bindCont,
    Functor.map, ExceptT.map, ExceptT.mk,
    Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange',
    LeanRV32D.Functions.zeros,
    Int.sub
  ]

  lemma run_vmem_read_of_width_2'
    (offset : BitVec 32)
    (data₀ data₁ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 2 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + offset).toNat + 2 < ram_size)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + offset).toNat + 1]? = some data₁) :
    let width := 2
    let data := data₁ ++ data₀
    (LeanRV32D.Functions.vmem_read
      rs
      offset
      width (AccessType.Read ())
      false false false
    ).run s = .ok (.Ok data) s
  := by
  rewrite [←vmem_read_equiv, vmem_read'_equiv]
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296]? = some data₀ := by
    clear *- hmem₀ h_does_fit
    convert hmem₀
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 1]? = some data₁ := by
    clear *- hmem₁ h_does_fit
    convert hmem₁

  simp [
    Nat.reduceMul, vmem_read',
    Sail.SailME.run,
    LeanRV32D.Functions.ext_data_get_addr,
    bind_pure_comp,
    Bool.false_eq_true, ↓reduceIte,
    LeanRV32D.Functions.plat_enable_misaligned_access,
    LeanRV32D.Functions.split_misaligned,
    LeanRV32D.Functions.allowed_misaligned,
    LeanRV32D.Functions.check_misaligned,
    CharP.cast_eq_zero, gt_iff_lt, Nat.ofNat_pos,
    Int.toNat_lt', Nat.cast_ofNat, decide_eq_true_eq,
    LeanRV32D.Functions.bits_of_virtaddr,
    Bool.if_false_left,
    Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_lt,
    Sail.assert, PreSail.assert,
    beq_iff_eq,
    LeanRV32D.Functions.misaligned_order,
    LeanRV32D.Functions.sys_misaligned_order_decreasing,
    Int.toNat_zero, Int.pred_toNat,
    Int.toNat_natCast_add_one, Prod.mk.eta,
    pure_bind, bind_assoc,
    EStateM.run, Functor.map,
    ExceptT.map, ExceptT.mk, ExceptT.run,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift
  ]

  unfold_projs
  simp [
    ExceptT.bind, ExceptT.mk, EStateM.map, h_reg_val,
    ExceptT.bindCont, ExceptT.pure,
    h_aligned,
    untilFuelM,
    untilFuelM.go
  ]
  have h_pmp_check := pmp_check_machine_read reg_val offset 2 s
  simp [EStateM.run] at h_pmp_check
  simp [
    LeanRV32D.Functions.translateAddr,
    h_mstatus,
    h_cur_privilege,
    bind, ExceptT.bind, EStateM.bind, ExceptT.mk,
    LeanRV32D.Functions.translationMode,
    LeanRV32D.Functions.effectivePrivilege,
    hfetch,
    LeanRV32D.Functions._get_Mstatus_MPRV,
    Sail.BitVec.extractLsb,
    h_mprv_disabled,
    hmachine, hsatp_bare,
    LeanRV32D.Functions.mem_read,
    LeanRV32D.Functions.mem_read_priv,
    LeanRV32D.Functions.mem_read_priv_meta,
    LeanRV32D.Functions.checked_mem_read,
    LeanRV32D.Functions.phys_access_check,
    LeanRV32D.Functions.sys_pmp_count,
    h_pmp_check,
    LeanRV32D.Functions.bits_of_virtaddr
  ]

  simp [
    LeanRV32D.Functions.within_mmio_readable,
    LeanRV32D.Functions.get_config_rvfi,
    LeanRV32D.Functions.within_clint,
    h_clint_base,
    h_clint_size,
    LeanRV32D.Functions.within_htif_readable,
    LeanRV32D.Functions.within_htif_writable,
    h_htif_tohost_base,
    LeanRV32D.Functions.zero_extend,
    Sail.BitVec.zeroExtend,
    Sail.BitVec.addInt,
  ]

  rewrite [ite_cond_eq_false _ _ (by simp; omega)]
  simp [
    EStateM.bind,
    LeanRV32D.Functions.within_phys_mem,
  ]

  simp only [
    h_plat_ram_base,
    h_plat_rom_base,
    h_plat_ram_size,
    h_plat_rom_size,
    Nat.reducePow,
    BitVec.toNat_ofNat,
    CharP.cast_eq_zero,
    Nat.reduceMod,
    zero_add,
    BitVec.ofNat_eq_ofNat,
    decide_true,
    ↓dreduceIte,
  ]
  rewrite [ite_cond_eq_true]; swap
  . simp
    clear *-h_does_fit
    simp at h_does_fit
    rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
    simp [← BitVec.ult_iff_lt, BitVec.ult_iff_toNat_lt] at h_does_fit
    omega

  simp [
    LeanRV32D.Functions.phys_mem_read,
    LeanRV32D.Functions.read_kind_of_flags,
    LeanRV32D.Functions.read_ram,
    Sail.sail_mem_read, PreSail.sail_mem_read,
    PreSail.readBytes,
    PreSail.readByte
  ]
  unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf
  dsimp [EStateM.get]

  have h_mod (n: ℕ) : n % 4294967296 % 17179869184 = n % 4294967296 := by omega
  rewrite [h_mod]

  simp [
    hmem₀',
    hmem₁',
  ]
  simp [
    LeanRV32D.Functions.MemoryOpResult_drop_meta,
    ExceptT.bindCont,
    Functor.map, ExceptT.map, ExceptT.mk,
    Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange',
    LeanRV32D.Functions.zeros,
    Int.sub
  ]

  lemma run_vmem_read_of_width_1'
    (offset : BitVec 32)
    (data₀ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + offset)) 1 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + offset).toNat + 1 < ram_size)
    (hmem₀ : s.mem[(reg_val + offset).toNat]? = some data₀) :
    let width := 1
    let data := data₀
    (LeanRV32D.Functions.vmem_read
      rs
      offset
      width (AccessType.Read ())
      false false false
    ).run s = .ok (.Ok data) s
  := by
  rewrite [←vmem_read_equiv, vmem_read'_equiv]
  have hfetch : (AccessType.Read () != AccessType.InstructionFetch ()) = true := rfl
  have hsatp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl
  have hmachine : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hmem₀' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296]? = some data₀ := by
    clear *- hmem₀ h_does_fit
    convert hmem₀

  simp [
    Nat.reduceMul, vmem_read',
    Sail.SailME.run,
    LeanRV32D.Functions.ext_data_get_addr,
    bind_pure_comp,
    Bool.false_eq_true, ↓reduceIte,
    LeanRV32D.Functions.plat_enable_misaligned_access,
    LeanRV32D.Functions.split_misaligned,
    LeanRV32D.Functions.allowed_misaligned,
    LeanRV32D.Functions.check_misaligned,
    CharP.cast_eq_zero, gt_iff_lt,
    decide_eq_true_eq,
    LeanRV32D.Functions.bits_of_virtaddr,
    Bool.if_false_left,
    Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not,
    Sail.assert, PreSail.assert,
    beq_iff_eq,
    LeanRV32D.Functions.misaligned_order,
    LeanRV32D.Functions.sys_misaligned_order_decreasing,
    Int.toNat_zero, Int.pred_toNat,
    Int.toNat_natCast_add_one, Prod.mk.eta,
    pure_bind, bind_assoc,
    EStateM.run, Functor.map,
    ExceptT.map, ExceptT.mk, ExceptT.run,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift
  ]

  unfold_projs
  simp [
    ExceptT.bind, ExceptT.mk, EStateM.map, h_reg_val,
    ExceptT.bindCont, ExceptT.pure,
    h_aligned,
    untilFuelM,
    untilFuelM.go
  ]
  have h_pmp_check := pmp_check_machine_read reg_val offset 1 s
  simp [EStateM.run] at h_pmp_check
  simp [
    LeanRV32D.Functions.translateAddr,
    h_mstatus,
    h_cur_privilege,
    bind, ExceptT.bind, EStateM.bind, ExceptT.mk,
    LeanRV32D.Functions.translationMode,
    LeanRV32D.Functions.effectivePrivilege,
    hfetch,
    LeanRV32D.Functions._get_Mstatus_MPRV,
    Sail.BitVec.extractLsb,
    h_mprv_disabled,
    hmachine, hsatp_bare,
    LeanRV32D.Functions.mem_read,
    LeanRV32D.Functions.mem_read_priv,
    LeanRV32D.Functions.mem_read_priv_meta,
    LeanRV32D.Functions.checked_mem_read,
    LeanRV32D.Functions.phys_access_check,
    LeanRV32D.Functions.sys_pmp_count,
    h_pmp_check,
    LeanRV32D.Functions.bits_of_virtaddr
  ]

  simp [
    LeanRV32D.Functions.within_mmio_readable,
    LeanRV32D.Functions.get_config_rvfi,
    LeanRV32D.Functions.within_clint,
    h_clint_base,
    h_clint_size,
    LeanRV32D.Functions.within_htif_readable,
    LeanRV32D.Functions.within_htif_writable,
    h_htif_tohost_base,
    LeanRV32D.Functions.zero_extend,
    Sail.BitVec.zeroExtend,
    Sail.BitVec.addInt,
  ]

  rewrite [ite_cond_eq_false _ _ (by simp; omega)]
  simp [
    EStateM.bind,
    LeanRV32D.Functions.within_phys_mem,
  ]

  simp only [
    h_plat_ram_base,
    h_plat_rom_base,
    h_plat_ram_size,
    h_plat_rom_size,
    Nat.reducePow,
    BitVec.toNat_ofNat,
    CharP.cast_eq_zero,
    Nat.reduceMod,
    zero_add,
    BitVec.ofNat_eq_ofNat,
    decide_true,
    ↓dreduceIte,
  ]
  rewrite [ite_cond_eq_true]; swap
  . simp
    clear *-h_does_fit
    simp at h_does_fit
    rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
    simp [← BitVec.ult_iff_lt, BitVec.ult_iff_toNat_lt] at h_does_fit
    omega

  simp [
    LeanRV32D.Functions.phys_mem_read,
    LeanRV32D.Functions.read_kind_of_flags,
    LeanRV32D.Functions.read_ram,
    Sail.sail_mem_read, PreSail.sail_mem_read,
    PreSail.readBytes,
    PreSail.readByte
  ]
  unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf
  dsimp [EStateM.get]

  have h_mod (n: ℕ) : n % 4294967296 % 17179869184 = n % 4294967296 := by omega
  rewrite [h_mod]

  simp [
    hmem₀',
  ]
  simp [
    LeanRV32D.Functions.MemoryOpResult_drop_meta,
    ExceptT.bindCont,
    Functor.map, ExceptT.map, ExceptT.mk,
    Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange',
    LeanRV32D.Functions.zeros,
    Int.sub
  ]

  lemma execute_LOAD_simplified
    (s)
    (rd : regidx)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 4 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + BitVec.signExtend 32 imm).toNat + 4 < ram_size)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat + 3]? = some data₃)
  :
    execute_LOAD imm rs1 rd true 4 s =
    match LeanRV32D.Functions.wX_bits rd (data₃ ++ data₂ ++ data₁ ++ data₀) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_4'
      (BitVec.signExtend 32 imm)
      data₀ data₁ data₂ data₃
      h_aligned
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_clint_base
      h_clint_size
      h_plat_ram_base
      h_plat_rom_base
      h_plat_ram_size
      h_plat_rom_size
      h_htif_tohost_base
      h_mprv_disabled
      h_does_fit
      hmem₀ hmem₁ hmem₂ hmem₃
    simp [EStateM.run] at this
    simp [
      execute_LOAD,
      LeanRV32D.Functions.xlen_bytes,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      LeanRV32D.Functions.Data,
      this,
      LeanRV32D.Functions.extend_value, LeanRV32D.Functions.zero_extend, Sail.BitVec.zeroExtend
    ]
    aesop

  lemma execute_LOADHU_simplified
    (s)
    (rd : regidx)
    (data₀ data₁ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 2 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + BitVec.signExtend 32 imm).toNat + 2 < ram_size)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
  :
    execute_LOAD imm rs1 rd true 2 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend (data₁ ++ data₀) 32 false) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_2'
      (BitVec.signExtend 32 imm)
      data₀ data₁
      h_aligned
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_clint_base
      h_clint_size
      h_plat_ram_base
      h_plat_rom_base
      h_plat_ram_size
      h_plat_rom_size
      h_htif_tohost_base
      h_mprv_disabled
      h_does_fit
      hmem₀ hmem₁
    simp [EStateM.run] at this
    simp [
      execute_LOAD,
      LeanRV32D.Functions.xlen_bytes,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      BitVec.extend,
      LeanRV32D.Functions.Data,
      this,
      LeanRV32D.Functions.extend_value, LeanRV32D.Functions.zero_extend, Sail.BitVec.zeroExtend
    ]
    aesop

  lemma execute_LOADH_simplified
    (s)
    (rd : regidx)
    (data₀ data₁ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 2 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + BitVec.signExtend 32 imm).toNat + 2 < ram_size)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
  :
    execute_LOAD imm rs1 rd false 2 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend (data₁ ++ data₀) 32 true) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_2'
      (BitVec.signExtend 32 imm)
      data₀ data₁
      h_aligned
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_clint_base
      h_clint_size
      h_plat_ram_base
      h_plat_rom_base
      h_plat_ram_size
      h_plat_rom_size
      h_htif_tohost_base
      h_mprv_disabled
      h_does_fit
      hmem₀ hmem₁
    simp [EStateM.run] at this
    simp [
      execute_LOAD,
      LeanRV32D.Functions.xlen_bytes,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      BitVec.extend,
      LeanRV32D.Functions.Data,
      this,
      LeanRV32D.Functions.extend_value,
    ]
    aesop

  lemma execute_LOADBU_simplified
    (s)
    (rd : regidx)
    (data₀ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 1 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + BitVec.signExtend 32 imm).toNat + 1 < ram_size)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat]? = some data₀)
  :
    execute_LOAD imm rs1 rd true 1 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend data₀ 32 false) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_1'
      (BitVec.signExtend 32 imm)
      data₀
      h_aligned
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_clint_base
      h_clint_size
      h_plat_ram_base
      h_plat_rom_base
      h_plat_ram_size
      h_plat_rom_size
      h_htif_tohost_base
      h_mprv_disabled
      h_does_fit
      hmem₀
    simp [EStateM.run] at this
    simp [
      execute_LOAD,
      LeanRV32D.Functions.xlen_bytes,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      BitVec.extend,
      LeanRV32D.Functions.Data,
      this,
      LeanRV32D.Functions.extend_value, LeanRV32D.Functions.zero_extend, Sail.BitVec.zeroExtend
    ]
    aesop

  lemma execute_LOADB_simplified
    (s)
    (rd : regidx)
    (data₀ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 1 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (reg_val + BitVec.signExtend 32 imm).toNat + 1 < ram_size)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 32 imm).toNat]? = some data₀)
  :
    execute_LOAD imm rs1 rd false 1 s =
    match LeanRV32D.Functions.wX_bits rd (BitVec.extend data₀ 32 true) s with
      | EStateM.Result.ok _ s => EStateM.Result.ok (ExecutionResult.Retire_Success ()) s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    have := run_vmem_read_of_width_1'
      (BitVec.signExtend 32 imm)
      data₀
      h_aligned
      h_reg_val
      h_mstatus
      h_cur_privilege
      h_clint_base
      h_clint_size
      h_plat_ram_base
      h_plat_rom_base
      h_plat_ram_size
      h_plat_rom_size
      h_htif_tohost_base
      h_mprv_disabled
      h_does_fit
      hmem₀
    simp [EStateM.run] at this
    simp [
      execute_LOAD,
      LeanRV32D.Functions.xlen_bytes,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      BitVec.extend,
      LeanRV32D.Functions.Data,
      this,
      LeanRV32D.Functions.extend_value,
    ]
    aesop

  lemma execute_load_instruction:
    LeanRV32D.Functions.execute (instruction.LOAD (imm, rs1, rd, is_unsigned, width)) =
    LeanRV32D.Functions.execute_LOAD imm rs1 rd is_unsigned width
  := rfl

  lemma execute_STORE_simplified
    (s)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 4 = true)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (rs1_val + BitVec.signExtend 32 imm).toNat + 4 < ram_size)
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
      LeanRV32D.Functions.xlen_bytes,
      h_rs2_val,
      LeanRV32D.Functions.Data,
      LeanRV32D.Functions.vmem_write,
      LeanRV32D.Functions.ext_data_get_addr
    ]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift Functor.map ExceptT.mk EStateM.instMonad EStateM.map
    dsimp
    simp [Sail.SailME.run, ExceptT.run]
    unfold bind ExceptT.instMonad ExceptT.bind EStateM.bind ExceptT.mk ExceptT.bindCont ExceptT.pure EStateM.pure ExceptT.mk
    dsimp
    simp [
      h_rs1_val,
      LeanRV32D.Functions.check_misaligned,
      LeanRV32D.Functions.plat_enable_misaligned_access,
      ←Local.vmem_write_addr'_equiv,
      Local.vmem_write_addr',
      LeanRV32D.Functions.split_misaligned,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      h_aligned
    ]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift ExceptT.mk Functor.map EStateM.instMonad EStateM.map ExceptT.instMonad ExceptT.bind EStateM.bind ExceptT.bindCont ExceptT.map ExceptT.mk bind
    dsimp [Sail.SailME.run, ExceptT.run, untilFuelM, untilFuelM.go]
    unfold bind EStateM.instMonad EStateM.bind
    dsimp

    have h_fetch : (AccessType.Write () != AccessType.InstructionFetch ()) = true := rfl
    have h_machine : (Privilege.Machine == Privilege.Machine) = true := rfl
    have h_satp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl

    have h_pmp_check := pmp_check_machine_write rs1_val (BitVec.signExtend 32 imm) 4 s
    simp [EStateM.run] at h_pmp_check

    simp [
      LeanRV32D.Functions.translateAddr,
      h_mstatus,
      h_cur_privilege,
      LeanRV32D.Functions.effectivePrivilege,
      h_fetch,
      LeanRV32D.Functions._get_Mstatus_MPRV,
      Sail.BitVec.extractLsb,
      h_mprv_disabled,
      LeanRV32D.Functions.translationMode,
      h_machine,
      h_satp_bare,
      LeanRV32D.Functions.mem_write_ea,
      LeanRV32D.Functions.write_kind_of_flags,
      LeanRV32D.Functions.mem_write_value,
      LeanRV32D.Functions.mem_write_value_meta,
      LeanRV32D.Functions.mem_write_value_priv_meta,
      LeanRV32D.Functions.checked_mem_write,
      LeanRV32D.Functions.default_write_acc,
      LeanRV32D.Functions.Data,
      LeanRV32D.Functions.phys_access_check,
      LeanRV32D.Functions.sys_pmp_count,
      LeanRV32D.Functions.bits_of_virtaddr,
      h_pmp_check,
      LeanRV32D.Functions.within_mmio_writable,
      LeanRV32D.Functions.get_config_rvfi,
      LeanRV32D.Functions.within_clint,
      h_clint_base,
      h_clint_size,
      LeanRV32D.Functions.within_htif_writable,
      h_htif_tohost_base
    ]

    rewrite [ite_cond_eq_false _ _ (by simp; omega)]
    have bitvec_zero_extend_to_nat (a: BitVec 32): (BitVec.zeroExtend 34 a).toNat = a.toNat := by
      clear *-a
      simp
      omega
    simp only [
      LeanRV32D.Functions.within_phys_mem,
      LeanRV32D.Functions.zero_extend,
      Sail.BitVec.zeroExtend,
      Sail.BitVec.addInt,
      h_plat_ram_base,
      h_plat_rom_base,
      h_plat_ram_size,
      h_plat_rom_size,
      decide_true,
      ↓dreduceIte,
      pure_equiv,
      bind_equiv,
      decide_eq_true_eq,
      Bool.and_eq_true,
      BitVec.ofInt_ofNat,
      BitVec.add_zero,
      bitvec_zero_extend_to_nat
    ]

    simp at h_does_fit
    simp only [
      BitVec.ofNat_eq_ofNat,
      decide_true,
      ↓dreduceIte,
      Nat.reducePow,
      BitVec.toNat_add,
      Int.natCast_emod,
      Nat.cast_add,
      Nat.cast_ofNat,
      CharP.cast_eq_zero,
      zero_add,
      BitVec.truncate_eq_setWidth
    ]
    rewrite [BitVec.toNat_ofNat]
    have : 2^34 = 17179869184 := rfl
    rewrite [this]; clear this
    simp only [Nat.reduceMod]
    rewrite [ite_cond_eq_true]; swap
    . simp
      clear *-h_does_fit
      simp [← BitVec.ult_iff_lt, BitVec.ult_iff_toNat_lt] at h_does_fit
      rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)] at h_does_fit
      omega

    simp [
      LeanRV32D.Functions.phys_mem_write,
      LeanRV32D.Functions.write_ram,
      Sail.sail_mem_write,
      PreSail.sail_mem_write,
      LeanRV32D.Functions.misaligned_order,
      LeanRV32D.Functions.sys_misaligned_order_decreasing
    ]

    rewrite [Nat.mod_eq_of_lt (by omega)]

    simp [
      PreSail.writeBytes,
      PreSail.writeByte
    ]

    unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet EStateM.instMonadStateOf EStateM.modifyGet ExceptT.pure ExceptT.mk EStateM.pure
    dsimp

    have (bv : BitVec 32) : BitVec.extractLsb 31 0 bv = bv := by simp [BitVec.extractLsb]
    simp [this]
    rfl

  lemma execute_STOREH_simplified
    (s)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 2 = true)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (rs1_val + BitVec.signExtend 32 imm).toNat + 2 < ram_size)
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
      LeanRV32D.Functions.xlen_bytes,
      h_rs2_val,
      LeanRV32D.Functions.Data,
      LeanRV32D.Functions.vmem_write,
      LeanRV32D.Functions.ext_data_get_addr
    ]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift Functor.map ExceptT.mk EStateM.instMonad EStateM.map
    dsimp
    simp [Sail.SailME.run, ExceptT.run]
    unfold bind ExceptT.instMonad ExceptT.bind EStateM.bind ExceptT.mk ExceptT.bindCont ExceptT.pure EStateM.pure ExceptT.mk
    dsimp
    simp [
      h_rs1_val,
      LeanRV32D.Functions.check_misaligned,
      LeanRV32D.Functions.plat_enable_misaligned_access,
      ←Local.vmem_write_addr'_equiv,
      Local.vmem_write_addr',
      LeanRV32D.Functions.split_misaligned,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      h_aligned
    ]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift ExceptT.mk Functor.map EStateM.instMonad EStateM.map ExceptT.instMonad ExceptT.bind EStateM.bind ExceptT.bindCont ExceptT.map ExceptT.mk bind
    dsimp [Sail.SailME.run, ExceptT.run, untilFuelM, untilFuelM.go]
    unfold bind EStateM.instMonad EStateM.bind
    dsimp

    have h_fetch : (AccessType.Write () != AccessType.InstructionFetch ()) = true := rfl
    have h_machine : (Privilege.Machine == Privilege.Machine) = true := rfl
    have h_satp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl

    have h_pmp_check := pmp_check_machine_write rs1_val (BitVec.signExtend 32 imm) 2 s
    simp [EStateM.run] at h_pmp_check

    simp [
      LeanRV32D.Functions.translateAddr,
      h_mstatus,
      h_cur_privilege,
      LeanRV32D.Functions.effectivePrivilege,
      h_fetch,
      LeanRV32D.Functions._get_Mstatus_MPRV,
      Sail.BitVec.extractLsb,
      h_mprv_disabled,
      LeanRV32D.Functions.translationMode,
      h_machine,
      h_satp_bare,
      LeanRV32D.Functions.mem_write_ea,
      LeanRV32D.Functions.write_kind_of_flags,
      LeanRV32D.Functions.mem_write_value,
      LeanRV32D.Functions.mem_write_value_meta,
      LeanRV32D.Functions.mem_write_value_priv_meta,
      LeanRV32D.Functions.checked_mem_write,
      LeanRV32D.Functions.default_write_acc,
      LeanRV32D.Functions.Data,
      LeanRV32D.Functions.phys_access_check,
      LeanRV32D.Functions.sys_pmp_count,
      LeanRV32D.Functions.bits_of_virtaddr,
      h_pmp_check,
      LeanRV32D.Functions.within_mmio_writable,
      LeanRV32D.Functions.get_config_rvfi,
      LeanRV32D.Functions.within_clint,
      h_clint_base,
      h_clint_size,
      LeanRV32D.Functions.within_htif_writable,
      h_htif_tohost_base
    ]

    rewrite [ite_cond_eq_false _ _ (by simp; omega)]
    have bitvec_zero_extend_to_nat (a: BitVec 32): (BitVec.zeroExtend 34 a).toNat = a.toNat := by
      clear *-a
      simp
      omega
    simp only [
      LeanRV32D.Functions.within_phys_mem,
      LeanRV32D.Functions.zero_extend,
      Sail.BitVec.zeroExtend,
      Sail.BitVec.addInt,
      h_plat_ram_base,
      h_plat_rom_base,
      h_plat_ram_size,
      h_plat_rom_size,
      decide_true,
      ↓dreduceIte,
      pure_equiv,
      bind_equiv,
      decide_eq_true_eq,
      Bool.and_eq_true,
      BitVec.ofInt_ofNat,
      BitVec.add_zero,
      bitvec_zero_extend_to_nat
    ]

    simp at h_does_fit
    simp only [
      BitVec.ofNat_eq_ofNat,
      decide_true,
      ↓dreduceIte,
      Nat.reducePow,
      BitVec.toNat_add,
      Int.natCast_emod,
      Nat.cast_add,
      Nat.cast_ofNat,
      CharP.cast_eq_zero,
      zero_add,
      BitVec.truncate_eq_setWidth
    ]
    rewrite [BitVec.toNat_ofNat]
    have : 2^34 = 17179869184 := rfl
    rewrite [this]; clear this
    simp only [Nat.reduceMod]
    rewrite [ite_cond_eq_true]; swap
    . simp
      clear *-h_does_fit
      simp [← BitVec.ult_iff_lt, BitVec.ult_iff_toNat_lt] at h_does_fit
      rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)] at h_does_fit
      omega

    simp [
      LeanRV32D.Functions.phys_mem_write,
      LeanRV32D.Functions.write_ram,
      Sail.sail_mem_write,
      PreSail.sail_mem_write,
      LeanRV32D.Functions.misaligned_order,
      LeanRV32D.Functions.sys_misaligned_order_decreasing
    ]

    rewrite [Nat.mod_eq_of_lt (by omega)]

    simp [
      PreSail.writeBytes,
      PreSail.writeByte
    ]

    unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet EStateM.instMonadStateOf EStateM.modifyGet ExceptT.pure ExceptT.mk EStateM.pure
    simp
    congr! <;> bv_decide

  lemma execute_STOREB_simplified
    (s)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (rs1_val + (BitVec.signExtend 32 imm))) 1 = true)
    (h_rs1_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok rs1_val s)
    (h_rs2_val : LeanRV32D.Functions.rX_bits rs2 s = EStateM.Result.ok rs2_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok ram_size s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : (rs1_val + BitVec.signExtend 32 imm).toNat + 1 < ram_size)
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
      LeanRV32D.Functions.xlen_bytes,
      h_rs2_val,
      LeanRV32D.Functions.Data,
      LeanRV32D.Functions.vmem_write,
      LeanRV32D.Functions.ext_data_get_addr
    ]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift Functor.map ExceptT.mk EStateM.instMonad EStateM.map
    dsimp
    simp [Sail.SailME.run, ExceptT.run]
    unfold bind ExceptT.instMonad ExceptT.bind EStateM.bind ExceptT.mk ExceptT.bindCont ExceptT.pure EStateM.pure ExceptT.mk
    dsimp
    simp [
      h_rs1_val,
      LeanRV32D.Functions.check_misaligned,
      LeanRV32D.Functions.plat_enable_misaligned_access,
      ←Local.vmem_write_addr'_equiv,
      Local.vmem_write_addr',
      LeanRV32D.Functions.split_misaligned,
      LeanRV32D.Functions.sign_extend,
      Sail.BitVec.signExtend,
      h_aligned
    ]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift ExceptT.mk Functor.map EStateM.instMonad EStateM.map ExceptT.instMonad ExceptT.bind EStateM.bind ExceptT.bindCont ExceptT.map ExceptT.mk bind
    dsimp [Sail.SailME.run, ExceptT.run, untilFuelM, untilFuelM.go]
    unfold bind EStateM.instMonad EStateM.bind
    dsimp

    have h_fetch : (AccessType.Write () != AccessType.InstructionFetch ()) = true := rfl
    have h_machine : (Privilege.Machine == Privilege.Machine) = true := rfl
    have h_satp_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl

    have h_pmp_check := pmp_check_machine_write rs1_val (BitVec.signExtend 32 imm) 1 s
    simp [EStateM.run] at h_pmp_check

    simp [
      LeanRV32D.Functions.translateAddr,
      h_mstatus,
      h_cur_privilege,
      LeanRV32D.Functions.effectivePrivilege,
      h_fetch,
      LeanRV32D.Functions._get_Mstatus_MPRV,
      Sail.BitVec.extractLsb,
      h_mprv_disabled,
      LeanRV32D.Functions.translationMode,
      h_machine,
      h_satp_bare,
      LeanRV32D.Functions.mem_write_ea,
      LeanRV32D.Functions.write_kind_of_flags,
      LeanRV32D.Functions.mem_write_value,
      LeanRV32D.Functions.mem_write_value_meta,
      LeanRV32D.Functions.mem_write_value_priv_meta,
      LeanRV32D.Functions.checked_mem_write,
      LeanRV32D.Functions.default_write_acc,
      LeanRV32D.Functions.Data,
      LeanRV32D.Functions.phys_access_check,
      LeanRV32D.Functions.sys_pmp_count,
      LeanRV32D.Functions.bits_of_virtaddr,
      h_pmp_check,
      LeanRV32D.Functions.within_mmio_writable,
      LeanRV32D.Functions.get_config_rvfi,
      LeanRV32D.Functions.within_clint,
      h_clint_base,
      h_clint_size,
      LeanRV32D.Functions.within_htif_writable,
      h_htif_tohost_base
    ]

    rewrite [ite_cond_eq_false _ _ (by simp)]
    have bitvec_zero_extend_to_nat (a: BitVec 32): (BitVec.zeroExtend 34 a).toNat = a.toNat := by
      clear *-a
      simp
      omega
    simp only [
      LeanRV32D.Functions.within_phys_mem,
      LeanRV32D.Functions.zero_extend,
      Sail.BitVec.zeroExtend,
      Sail.BitVec.addInt,
      h_plat_ram_base,
      h_plat_rom_base,
      h_plat_ram_size,
      h_plat_rom_size,
      decide_true,
      ↓dreduceIte,
      pure_equiv,
      bind_equiv,
      decide_eq_true_eq,
      Bool.and_eq_true,
      BitVec.ofInt_ofNat,
      BitVec.add_zero,
      bitvec_zero_extend_to_nat
    ]

    simp at h_does_fit
    simp only [
      BitVec.ofNat_eq_ofNat,
      decide_true,
      ↓dreduceIte,
      Nat.reducePow,
      BitVec.toNat_add,
      Int.natCast_emod,
      Nat.cast_add,
      Nat.cast_ofNat,
      CharP.cast_eq_zero,
      zero_add,
      BitVec.truncate_eq_setWidth
    ]
    rewrite [BitVec.toNat_ofNat]
    have : 2^34 = 17179869184 := rfl
    rewrite [this]; clear this
    simp only [Nat.reduceMod]
    rewrite [ite_cond_eq_true]; swap
    . simp
      clear *-h_does_fit
      simp [← BitVec.ult_iff_lt, BitVec.ult_iff_toNat_lt] at h_does_fit
      rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)] at h_does_fit
      omega

    simp [
      LeanRV32D.Functions.phys_mem_write,
      LeanRV32D.Functions.write_ram,
      Sail.sail_mem_write,
      PreSail.sail_mem_write,
      LeanRV32D.Functions.misaligned_order,
      LeanRV32D.Functions.sys_misaligned_order_decreasing
    ]

    rewrite [Nat.mod_eq_of_lt (by omega)]

    simp [
      PreSail.writeBytes,
      PreSail.writeByte
    ]

    unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet EStateM.instMonadStateOf EStateM.modifyGet ExceptT.pure ExceptT.mk EStateM.pure
    simp
    congr 1; bv_decide

  lemma execute_store_instruction:
    LeanRV32D.Functions.execute (instruction.STORE (imm, rs2, rs1, width)) =
    LeanRV32D.Functions.execute_STORE imm rs2 rs1 width
  := rfl

end Local
