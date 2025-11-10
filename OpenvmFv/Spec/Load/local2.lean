import OpenvmFv.Spec.run_hart_active
import OpenvmFv.Spec.Load.local


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
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok (BitVec.ofNat 34 (2^32 - 1)) s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : reg_val.toNat + offset.toNat + 4 < 2^32)
    (hmem₀ : s.mem[reg_val.toNat + offset.toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + offset.toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + offset.toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + offset.toNat + 3]? = some data₃) :
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
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₁' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 1]? = some data₁ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₂' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 2]? = some data₂ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega
  have hmem₃' : s.mem[(reg_val.toNat + offset.toNat) % 4294967296 + 3]? = some data₃ := by
    rwa [Nat.mod_eq_of_lt]; clear *- h_does_fit; omega

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
    Nat.add_one_sub_one,
    BitVec.toNat_ofNat,
    CharP.cast_eq_zero,
    Nat.reduceMod,
    Nat.cast_ofNat,
    zero_add,
    BitVec.ofNat_eq_ofNat,
    decide_true,
    ↓dreduceIte,
  ]
  rewrite [ite_cond_eq_true _ _ (by simp; omega)]

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

  example
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (h_aligned : LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (reg_val + (BitVec.signExtend 32 imm))) 4 = true)
    (h_reg_val : LeanRV32D.Functions.rX_bits rs1 s = EStateM.Result.ok reg_val s)
    (h_mstatus: Sail.readReg Register.mstatus s = EStateM.Result.ok mstatus s)
    (h_cur_privilege: Sail.readReg Register.cur_privilege s = EStateM.Result.ok Privilege.Machine s)
    (h_clint_base: Sail.readReg Register.plat_clint_base s = EStateM.Result.ok 0 s)
    (h_clint_size: Sail.readReg Register.plat_clint_size s = EStateM.Result.ok 0 s)
    (h_plat_ram_base: Sail.readReg Register.plat_ram_base s = EStateM.Result.ok 0 s)
    (h_plat_rom_base: Sail.readReg Register.plat_rom_base s = EStateM.Result.ok 0 s)
    (h_plat_ram_size: Sail.readReg Register.plat_ram_size s = EStateM.Result.ok (BitVec.ofNat 34 (2^32 - 1)) s)
    (h_plat_rom_size: Sail.readReg Register.plat_rom_size s = EStateM.Result.ok rom_size s)
    (h_htif_tohost_base: Sail.readReg Register.htif_tohost_base s = EStateM.Result.ok .none s)
    (h_mprv_disabled : BitVec.extractLsb 17 17 mstatus = 0#1)
    (h_does_fit : reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 4 < 2^32)
    (hmem₀ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[reg_val.toNat + (BitVec.signExtend 32 imm).toNat + 3]? = some data₃)
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

end Local






















#print LeanRV32D.Functions.ext_data_get_addr
#print LeanRV32D.Functions.vmem_read

noncomputable def vmem_read (rs : regidx) (offset : (BitVec 32)) (width : Nat) (acc : (AccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Result (BitVec (8 * width)) ExecutionResult) := SailME.run do
  let vaddr ← (( do
    match (← (ext_data_get_addr rs offset acc width)) with
    | .Ext_DataAddr_OK vaddr => (pure vaddr)
    | .Ext_DataAddr_Error e =>
      SailME.throw ((Err (Ext_DataAddr_Check_Failure e)) : (Result (BitVec (8 * width)) ExecutionResult))
    ) : SailME (Result (BitVec (8 * width)) ExecutionResult) virtaddr )
  if (res : Bool)
  then
    (do
      if ((not (is_aligned_vaddr vaddr width)) : Bool)
      then
        SailME.throw ((Err (Memory_Exception (vaddr, (E_Load_Addr_Align ())))) : (Result (BitVec (8 * width)) ExecutionResult))
      else (pure ()))
  else
    (do
      if ((check_misaligned vaddr width) : Bool)
      then
        SailME.throw ((Err (Memory_Exception (vaddr, (E_Load_Addr_Align ())))) : (Result (BitVec (8 * width)) ExecutionResult))
      else (pure ()))
  let (n, bytes) ← do (split_misaligned vaddr width)
  let data := (zeros (n := ((8 *i n) *i bytes)))
  let (first, last, step) := (misaligned_order n)
  let i : Nat := first
  let finished : Bool := false
  let vaddr := (bits_of_virtaddr vaddr)
  let (data, finished, i) ← (( do
    let mut loop_vars := (data, finished, i)
    repeat
      let (data, finished, i) := loop_vars
      loop_vars ← do
        let offset := i
        let vaddr := (BitVec.addInt vaddr (offset *i bytes))
        let data ← (( do
          match (← (translateAddr (Virtaddr vaddr) acc)) with
          | .Err (e, _) =>
            SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result (BitVec (8 * width)) ExecutionResult))
          | .Ok (paddr, _) =>
            (do
              match (← (mem_read acc paddr bytes aq rl res)) with
              | .Err e =>
                SailME.throw ((Err (Memory_Exception ((Virtaddr vaddr), e))) : (Result (BitVec (8 * width)) ExecutionResult))
              | .Ok v =>
                (do
                  if (res : Bool)
                  then (load_reservation (bits_of_physaddr paddr))
                  else (pure ())
                  (pure (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i bytes) -i 1)
                      ((8 *i offset) *i bytes) v)))) ) : SailME
          (Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * n * bytes)) )
        let (finished, i) : (Bool × Nat) :=
          if ((offset == last) : Bool)
          then
            (let finished : Bool := true
            (finished, i))
          else
            (let i : Nat := (offset +i step)
            (finished, i))
        (pure (data, finished, i))
    until (λ (data, finished, i) => finished) loop_vars
    (pure loop_vars) ) : SailME (Result (BitVec (8 * width)) ExecutionResult)
    ((BitVec (8 * n * bytes)) × Bool × Nat) )
  (pure (Ok data))

noncomputable def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width: ℕ) : SailM ExecutionResult := do
    let offset : xlenbits := (LeanRV32D.Functions.sign_extend (m := 32) imm)
    Sail.assert (width ≤b LeanRV32D.Functions.xlen_bytes) "extensions/I/base_insts.sail:287.28-287.29"
    match (← (LeanRV32D.Functions.vmem_read rs1 offset width (AccessType.Read LeanRV32D.Functions.Data) false false false)) with
      | .Ok data =>
        (do
          (LeanRV32D.Functions.wX_bits rd (LeanRV32D.Functions.extend_value is_unsigned data))
          (pure LeanRV32D.Functions.RETIRE_SUCCESS))
      | .Err e => (pure e)

lemma execute_LOAD_equiv:
  execute_LOAD =
  LeanRV32D.Functions.execute_LOAD
:= by
  sorry
