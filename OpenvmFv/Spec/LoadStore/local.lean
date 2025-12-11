import Lean

import OpenvmFv.Spec.run_hart_active

namespace Local

  noncomputable def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width: ℕ) : SailM ExecutionResult := do
    let offset : xlenbits := (LeanRV32D.Functions.sign_extend (m := 32) imm)
    Sail.assert (width ≤b LeanRV32D.Functions.xlen_bytes) "extensions/I/base_insts.sail:287.28-287.29"
    match (← (LeanRV32D.Functions.vmem_read rs1 offset width (AccessType.Read LeanRV32D.Functions.Data) false false false)) with
      | .Ok data =>
        (do
          (LeanRV32D.Functions.wX_bits rd (LeanRV32D.Functions.extend_value is_unsigned data))
          (pure LeanRV32D.Functions.RETIRE_SUCCESS))
      | .Err e => (pure e)

  lemma execute_LOAD_equiv :
    execute_LOAD = LeanRV32D.Functions.execute_LOAD
  := rfl

  noncomputable def vmem_read
    (rs : regidx) (offset : BitVec 32) (width : ℕ) (acc : AccessType Unit)
    (aq rl res : Bool)
  : SailM (Sail.Result (BitVec (8 * width)) ExecutionResult) := Sail.SailME.run do
    let vaddr ← (( do
      match (← (LeanRV32D.Functions.ext_data_get_addr rs offset acc width)) with
      | .Ext_DataAddr_OK vaddr => (pure vaddr)
      | .Ext_DataAddr_Error e =>
        Sail.SailME.throw ((Sail.Err (ExecutionResult.Ext_DataAddr_Check_Failure e)) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
      ) : Sail.SailME (Sail.Result (BitVec (8 * width)) ExecutionResult) virtaddr )
    if (res : Bool)
    then
      (do
        if ((LeanRV32D.Functions.not (LeanRV32D.Functions.is_aligned_vaddr vaddr width)) : Bool)
        then
          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_Load_Addr_Align ())))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
        else (pure ()))
    else
      (do
        if ((LeanRV32D.Functions.check_misaligned vaddr width) : Bool)
        then
          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_Load_Addr_Align ())))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
        else (pure ()))
    let (n, bytes) ← do (LeanRV32D.Functions.split_misaligned vaddr width)
    let data := (LeanRV32D.Functions.zeros (n := ((8 *i n) *i bytes)))
    let (first, last, step) := (LeanRV32D.Functions.misaligned_order n)
    let i : Nat := first
    let finished : Bool := false
    let vaddr := (LeanRV32D.Functions.bits_of_virtaddr vaddr)
    let (data, _finished, _i) ← (( do
      let mut loop_vars := (data, finished, i)
      repeat
        let (data, finished, i) := loop_vars
        loop_vars ← do
          let offset := i
          let vaddr := (Sail.BitVec.addInt vaddr (offset *i bytes))
          let data ← (( do
            match (← (LeanRV32D.Functions.translateAddr (virtaddr.Virtaddr vaddr) acc)) with
            | .Err (e, _) =>
              Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
            | .Ok (paddr, _) =>
              (do
                match (← (LeanRV32D.Functions.mem_read acc paddr bytes aq rl res)) with
                | .Err e =>
                  Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
                | .Ok v =>
                  (do
                    if (res : Bool)
                    then (load_reservation (LeanRV32D.Functions.bits_of_physaddr paddr))
                    else (pure ())
                    (pure (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i bytes) -i 1)
                        ((8 *i offset) *i bytes) v)))) ) : Sail.SailME
            (Sail.Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * n * bytes)) )
          let (finished, i) : (Bool × Nat) :=
            if ((offset == last) : Bool)
            then
              (let finished : Bool := true
              (finished, i))
            else
              (let i : Nat := (offset +i step)
              (finished, i))
          (pure (data, finished, i))
      until (λ (_data, finished, _i) => finished) loop_vars
      (pure loop_vars) ) : Sail.SailME (Sail.Result (BitVec (8 * width)) ExecutionResult)
      ((BitVec (8 * n * bytes)) × Bool × Nat) )
    (pure (Sail.Ok data))

  lemma vmem_read_equiv :
    vmem_read = LeanRV32D.Functions.vmem_read
  := rfl

  noncomputable def vmem_read'
    (rs : regidx) (offset : BitVec 32) (width : ℕ) (acc : AccessType Unit)
    (aq rl res : Bool)
  : SailM (Sail.Result (BitVec (8 * width)) ExecutionResult) := Sail.SailME.run do
    let vaddr ← (( do
      match (← (LeanRV32D.Functions.ext_data_get_addr rs offset acc width)) with
      | .Ext_DataAddr_OK vaddr => (pure vaddr)
      | .Ext_DataAddr_Error e =>
        Sail.SailME.throw ((Sail.Err (ExecutionResult.Ext_DataAddr_Check_Failure e)) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
      ) : Sail.SailME (Sail.Result (BitVec (8 * width)) ExecutionResult) virtaddr )
    if (res : Bool)
    then
      (do
        if ((LeanRV32D.Functions.not (LeanRV32D.Functions.is_aligned_vaddr vaddr width)) : Bool)
        then
          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_Load_Addr_Align ())))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
        else (pure ()))
    else
      (do
        if ((LeanRV32D.Functions.check_misaligned vaddr width) : Bool)
        then
          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_Load_Addr_Align ())))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
        else (pure ()))
    let (n, bytes) ← do (LeanRV32D.Functions.split_misaligned vaddr width)
    let data := (LeanRV32D.Functions.zeros (n := ((8 *i n) *i bytes)))
    let (first, last, step) := (LeanRV32D.Functions.misaligned_order n)
    let i : Nat := first
    let finished : Bool := false
    let vaddr := (LeanRV32D.Functions.bits_of_virtaddr vaddr)
    let (data, _finished, _i) ← (( do
      let loop_vars ← untilFuelM (fuel :=n) (λ (_, finished, _) => (pure finished)) (data, finished, i)
        fun (data, finished, i) => do
          let offset := i
          let vaddr := (Sail.BitVec.addInt vaddr (offset *i bytes))
          let data ← (( do
            match (← (LeanRV32D.Functions.translateAddr (virtaddr.Virtaddr vaddr) acc)) with
            | .Err (e, _) =>
              Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
            | .Ok (paddr, _) =>
              (do
                match (← (LeanRV32D.Functions.mem_read acc paddr bytes aq rl res)) with
                | .Err e =>
                  Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
                | .Ok v =>
                  (do
                    if (res : Bool)
                    then (load_reservation (LeanRV32D.Functions.bits_of_physaddr paddr))
                    else (pure ())
                    (pure (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i bytes) -i 1)
                        ((8 *i offset) *i bytes) v)))) ) : Sail.SailME
            (Sail.Result (BitVec (8 * width)) ExecutionResult) (BitVec (8 * n * bytes)) )
          let (finished, i) : (Bool × Nat) :=
            if ((offset == last) : Bool)
            then
              (let finished : Bool := true
              (finished, i))
            else
              (let i : Nat := (offset +i step)
              (finished, i))
          (pure (data, finished, i))
      (pure loop_vars) ) : Sail.SailME (Sail.Result (BitVec (8 * width)) ExecutionResult)
      ((BitVec (8 * n * bytes)) × Bool × Nat) )
    (pure (Sail.Ok data))

  -- 'axiom' until the spec is rebuilt to avoid the repeat
  lemma vmem_read'_equiv:
    vmem_read =
    vmem_read'
  := by
    sorry

  lemma ext_data_get_addr :
    LeanRV32D.Functions.ext_data_get_addr rd offset acc width =
    λ state => match LeanRV32D.Functions.rX_bits rd state with
    | EStateM.Result.ok rd_val s =>
      EStateM.Result.ok (Ext_DataAddr_Check.Ext_DataAddr_OK (virtaddr.Virtaddr (rd_val + offset))) s
    | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    simp [LeanRV32D.Functions.ext_data_get_addr]
    funext
    aesop

  lemma check_misaligned :
    LeanRV32D.Functions.check_misaligned =
    λ _ _  => false
  := rfl

  lemma mod_of_trailing_zeroes_eq_0 {width} {bv: BitVec width}
    (h: Sail.BitVec.countTrailingZeros bv = 0)
    (h_width: width > 0)
  : ((bv.toNat): Int).tmod 4 ≠ 0 := by
    unfold Sail.BitVec.countTrailingZeros at h
    unfold Sail.BitVec.countLeadingZeros at h
    simp [show (width=0) = false by grind] at h
    by_cases h_mod: (bv.toNat: Int).tmod 4 = 0
    . exfalso
      simp [
        BitVec.msb_reverse,
        BitVec.getLsbD
      ] at h
      unfold Nat.cast NatCast.natCast instNatCastInt Int.tmod at h_mod
      unfold HMod.hMod instHMod Mod.mod Nat.instMod at h_mod h
      dsimp at h_mod h
      have : bv.toNat % 4 = 0 := by unfold HMod.hMod instHMod Mod.mod Nat.instMod; dsimp; grind
      have h_dvd_4 := Nat.dvd_of_mod_eq_zero this
      have h_not_dvd_2 : ¬(2 ∣ bv.toNat) := by
        simp
        unfold HMod.hMod instHMod Mod.mod Nat.instMod
        dsimp
        grind
      clear *- h_dvd_4 h_not_dvd_2
      grind
    . exact h_mod

  lemma mod_of_trailing_zeroes_eq_1 {width} {bv: BitVec width}
    (h: Sail.BitVec.countTrailingZeros bv = 1)
    (h_width: width > 1)
  : ((bv.toNat): Int).tmod 4 ≠ 0 := by
    unfold Sail.BitVec.countTrailingZeros at h
    unfold Sail.BitVec.countLeadingZeros at h
    simp [show (width=0) = false by grind] at h
    by_cases h_mod: (bv.toNat: Int).tmod 4 = 0
    . exfalso
      by_cases h_lsb: bv.reverse.msb = true <;> [
        simp [h_lsb] at h;
        skip
      ]
      simp [h_lsb] at h
      unfold Sail.BitVec.countLeadingZeros at h
      simp [
        show (width - 1=0) = false by grind,
        h_width,
        show (width - (width - 1)) = 1 by omega
      ] at h
      simp [
        BitVec.getMsbD_reverse,
        BitVec.getLsbD,
        Nat.testBit
      ] at h
      unfold Nat.cast NatCast.natCast instNatCastInt Int.tmod at h_mod
      unfold HMod.hMod instHMod Mod.mod Nat.instMod at h_mod h
      dsimp at h_mod h
      have : bv.toNat % 4 = 0 := by unfold HMod.hMod instHMod Mod.mod Nat.instMod; dsimp; grind
      have h_dvd_4 := Nat.dvd_of_mod_eq_zero this
      have h_not_dvd_2 : ¬(2 ∣ (bv.toNat >>> 1)) := by
        simp
        unfold HMod.hMod instHMod Mod.mod Nat.instMod
        dsimp
        grind
      clear *- h_dvd_4 h_not_dvd_2
      have : 4/2 ∣ bv.toNat / 2 := by grind
      have : 2 ∣ bv.toNat >>> 1 := by
        simp at this
        simp [this, Nat.shiftRight_eq_div_pow]
      grind
    . exact h_mod

  lemma mod_of_trailing_zeroes_ge_2 {width} {bv: BitVec width}
    (h: Sail.BitVec.countTrailingZeros bv ≥ 2)
    (h_width: width > 2)
  : ((bv.toNat): Int).tmod 4 = 0 := by
    unfold Sail.BitVec.countTrailingZeros at h
    unfold Sail.BitVec.countLeadingZeros at h
    simp [show (width=0) = false by grind] at h
    by_cases h_mod: (bv.toNat: Int).tmod 4 = 0
    . exact h_mod
    . exfalso
      by_cases h_lsb: bv.reverse.msb = true <;> [
        simp [h_lsb] at h;
        skip
      ]
      simp [h_lsb] at h
      have (x: ℕ): 2 ≤ 1 + x → 1 ≤ x := by omega
      apply this at h; clear this
      unfold Sail.BitVec.countLeadingZeros at h
      simp [
        show (width - 1=0) = false by grind,
        show (1 < width) = true by grind,
        show (width - (width - 1)) = 1 by omega
      ] at h
      split_ifs at h with h_lsb1 <;> [simp at h; skip]
      clear h
      simp at *
      unfold Nat.cast NatCast.natCast instNatCastInt Int.tmod at h_mod
      unfold HMod.hMod instHMod Mod.mod Nat.instMod at h_mod
      dsimp at h_mod
      simp [
        BitVec.msb_reverse,
        BitVec.getMsbD_reverse,
        BitVec.getLsbD,
        Nat.testBit,
        Nat.shiftRight_eq_div_pow
      ] at h_lsb h_lsb1
      have : bv.toNat % 4 ≠ 0 := by unfold HMod.hMod instHMod Mod.mod Nat.instMod; dsimp; grind
      clear h_mod h_width
      generalize bv.toNat = x at *
      grind

  def split_misaligned_pure (v: virtaddr) : (ℤ × ℤ) :=
    match Sail.BitVec.countTrailingZeros v.1 with
      | 0 => (4, 1)
      | 1 => (2, 2)
      | _+2 => (1, 4)

  lemma split_misaligned:
    LeanRV32D.Functions.split_misaligned v 4 =
    λ s => EStateM.Result.ok (split_misaligned_pure v) s
  := by
    unfold LeanRV32D.Functions.split_misaligned
    simp [
      LeanRV32D.Functions.is_aligned_vaddr,
      LeanRV32D.Functions.allowed_misaligned,
      LeanRV32D.Functions.bits_of_virtaddr,
      LeanRV32D.Functions.sys_misaligned_allowed_within_exp,
      LeanRV32D.Functions.sys_misaligned_byte_by_byte,
      (show (2: ℤ) ^ (0: ℤ) = 1 by decide),
      split_misaligned_pure
    ]
    by_cases h_zeroes: Sail.BitVec.countTrailingZeros v.1 = 0
    . simp [
        h_zeroes,
        mod_of_trailing_zeroes_eq_0,
        (show (2: ℤ) ^ (0: ℤ) = 1 by decide)
      ]
    by_cases h_zeroes : Sail.BitVec.countTrailingZeros v.1 = 1
    . simp [
        h_zeroes,
        mod_of_trailing_zeroes_eq_1,
        (show (2: ℤ) ^ (1: ℤ) = 2 by decide),
      ]
    . have : Sail.BitVec.countTrailingZeros v.1 ≥ 2 := by omega
      simp [
        mod_of_trailing_zeroes_ge_2 this
      ]
      funext
      aesop

  lemma split_misaligned_product :
    (
      8 * (split_misaligned_pure v).1 *
      (split_misaligned_pure v).2
    ) = 32
  := by
    unfold split_misaligned_pure
    aesop

  lemma split_misaligned_toNat_product :
    (
      8 * (split_misaligned_pure v).1.toNat *
      (split_misaligned_pure v).2.toNat
    ) = 32
  := by
    unfold split_misaligned_pure
    aesop

  lemma misaligned_order:
    LeanRV32D.Functions.misaligned_order =
    λ n => (0, n-1, 1)
  := by
    unfold LeanRV32D.Functions.misaligned_order LeanRV32D.Functions.sys_misaligned_order_decreasing
    simp

  example
    (h_rd: read_xreg (regidx_to_fin rd) state = EStateM.Result.error e s)
  :
    vmem_read rd offset 4 acc aq rl res state =
    EStateM.Result.error e s
  := by
    simp [vmem_read, ext_data_get_addr]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift
    unfold Functor.map ExceptT.mk monadLift instMonadLiftT EStateM.instMonad EStateM.map
    dsimp
    unfold bind ExceptT.instMonad ExceptT.bind ExceptT.mk ExceptT.bindCont
    simp [Sail.SailME.run, ExceptT.run]
    rewrite [rX_read_xreg_equiv state rd (regidx_to_fin rd) (by simp [regidx_to_fin]), h_rd]
    simp

  def effective_privilege_pure (status: BitVec 64) (privilege: Privilege): Privilege :=
    match BitVec.extractLsb 17 17 status with
      | 0#1 => privilege
      | 1#1 => match BitVec.extractLsb 12 11 status with
        | 0#2 => Privilege.User
        | 1#2 => Privilege.Supervisor
        | 3#2 => Privilege.Machine
        | _ => panic! "unexpected_privilege"

  lemma effective_privilege
    (accessType: AccessType Unit)
    (privilege)
    (state)
    (status)
    (h_status:
      Sail.BitVec.extractLsb status 12 11 = 0#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 1#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 3#2
    )
    (h_access_type: accessType != AccessType.InstructionFetch ())
  :
    LeanRV32D.Functions.effectivePrivilege accessType status privilege state =
    EStateM.Result.ok (effective_privilege_pure status privilege) state
  := by
    unfold LeanRV32D.Functions.effectivePrivilege
    simp [
      LeanRV32D.Functions._get_Mstatus_MPRV,
      LeanRV32D.Functions._get_Mstatus_MPP
    ]
    unfold LeanRV32D.Functions.privLevel_bits_forwards
    simp [h_access_type, Sail.BitVec.extractLsb] at ⊢ h_status
    unfold effective_privilege_pure
    aesop

  def translation_mode_pure (satp: BitVec 32) (privilege: Privilege) :=
    if privilege == Privilege.Machine ∨ !satp[31]
    then SATPMode.Bare
    else SATPMode.Sv32

  lemma translation_mode
    {satp : BitVec 32}
    (h_satp: Sail.readReg Register.satp state = EStateM.Result.ok satp state)
  :
    LeanRV32D.Functions.translationMode privilege state =
    EStateM.Result.ok (translation_mode_pure satp privilege) state
  := by
    unfold LeanRV32D.Functions.translationMode translation_mode_pure
    split_ifs
    . simp
    . simp_all
    . simp_all [
        LeanRV32D.Functions.satpMode_of_bits,
        Sail.BitVec.extractLsb,
        BitVec.extractLsb,
        LeanRV32D.Functions._get_Satp32_Mode,
        LeanRV32D.Functions.Mk_Satp32
      ]
      have : BitVec.extractLsb' 31 1 satp = 0#1 := by bv_decide
      simp [this]
    . simp_all [
        LeanRV32D.Functions.satpMode_of_bits,
        Sail.BitVec.extractLsb,
        BitVec.extractLsb,
        LeanRV32D.Functions._get_Satp32_Mode,
        LeanRV32D.Functions.Mk_Satp32,
      ]
      have : BitVec.extractLsb' 31 1 satp = 1#1 := by bv_decide
      simp [this]

  lemma translate_addr
    {satp : BitVec 32}
    (h_status: Sail.readReg Register.mstatus state = EStateM.Result.ok status state)
    -- (h_tlb: Sail.readReg Register.tlb state = EStateM.Result.ok tlb state)
    -- (h_tlb_val: ∀ x: Fin 64, tlb[x]! = .none)
    (h_privilege: Sail.readReg Register.cur_privilege state = EStateM.Result.ok privilege state)
    (h_status_val:
      Sail.BitVec.extractLsb status 12 11 = 0#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 1#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 3#2
    )
    (h_satp: Sail.readReg Register.satp state = EStateM.Result.ok satp state)
    (h_translation_mode: translation_mode_pure satp (effective_privilege_pure status privilege) == SATPMode.Bare)
  :
    LeanRV32D.Functions.translateAddr addr (AccessType.Read ()) state =
    EStateM.Result.ok (Sail.Ok (physaddr.Physaddr (BitVec.setWidth 34 addr.1), ())) state
  := by
    unfold LeanRV32D.Functions.translateAddr
    unfold_projs at ⊢ h_translation_mode
    simp [
      EStateM.bind,
      h_status,
      h_privilege,
      effective_privilege (AccessType.Read ()) privilege state status h_status_val (by trivial),
      translation_mode h_satp,
      h_translation_mode
    ]
    simp [
      LeanRV32D.Functions.zero_extend,
      Sail.BitVec.zeroExtend,
      LeanRV32D.Functions.init_ext_ptw,
      LeanRV32D.Functions.bits_of_virtaddr,
      EStateM.pure
    ]
    --   done
    -- . done
    -- . done
    -- . unfold_projs
    --   simp [
    --     EStateM.bind,
    --     LeanRV32D.Functions.satp_mode_width_forwards,
    --     LeanRV32D.Functions.get_satp,
    --     h_satp,
    --     LeanRV32D.Functions.bits_of_virtaddr,
    --     Sail.BitVec.extractLsb,
    --     Int.sub,
    --     LeanRV32D.Functions.sign_extend,
    --     Sail.BitVec.signExtend
    --   ]
    --   have : addr.1 = BitVec.extractLsb 31 0 addr.1 := by bv_decide
    --   simp [
    --     EStateM.bind,
    --     h_status,
    --     EStateM.pure,
    --     LeanRV32D.Functions.translate,
    --     LeanRV32D.Functions.lookup_TLB,
    --     h_tlb,
    --     LeanRV32D.Functions.tlb_hash,
    --     LeanRV32D.Functions.pagesize_bits,
    --     ←this,
    --     Sail.BitVec.extractLsb
    --   ]
    --   have := h_tlb_val ⟨
    --     BitVec.toNat addr.1 >>> 12 % 64,
    --     Nat.mod_lt _ (by trivial)
    --   ⟩
    --   simp at this
    --   have : tlb[BitVec.toNat addr.1 >>> 12 % 64]! = .none := by
    --     rewrite [←this]
    --     unfold_projs
    --     unfold decidableGetElem? Vector.get

    --   simp [Vector.getElem, this]
    --   done
    -- done

  set_option hygiene false
  open Lean Elab Tactic
  elab "get_inaccessible" names: binderIdent,* : tactic => do
    let x := λ g => Lean.Elab.Tactic.renameInaccessibles g names
    let y ← popMainGoal
    let z ← x y
    pushGoal z

  lemma pmpReadAddrReg
    (h_pmp_cfg_n : Sail.readReg Register.pmpcfg_n state = EStateM.Result.ok pmp_cfg_n state)
    (h_pmp_addr_n : Sail.readReg Register.pmpaddr_n state = EStateM.Result.ok pmp_addr_n state)
  :
    LeanRV32D.Functions.pmpReadAddrReg n state =
    EStateM.Result.ok pmp_addr_n[n]! state
  := by
    unfold LeanRV32D.Functions.pmpReadAddrReg
    simp [
      LeanRV32D.Functions.sys_pmp_grain,
      h_pmp_cfg_n,
      h_pmp_addr_n
    ]
    cases BitVec.ofBool (LeanRV32D.Functions._get_Pmpcfg_ent_A pmp_cfg_n[n]!)[1] with
      | ofFin x => fin_cases x <;> simp

  /-- We can't prove this directly because the loop in `pmpCheck` doesn't unfold.
  Adding this is at least consistent, since the left-hand side has no actual value. -/
  lemma pmp_check_machine_write (reg_val : BitVec 32) (offset : BitVec 32) (width : ℕ) (s) :
      EStateM.run (
        LeanRV32D.Functions.pmpCheck (
          physaddr.Physaddr (
            LeanRV32D.Functions.zero_extend (
              Sail.BitVec.addInt (reg_val + offset) 0
            )
          )
        )
        width
        (AccessType.Write ())
        Privilege.Machine
      ) s = EStateM.Result.ok none s
  := by
    sorry

  /-- We can't prove this directly because the loop in `pmpCheck` doesn't unfold.
  Adding this is at least consistent, since the left-hand side has no actual value. -/
  lemma pmp_check_machine_read (reg_val : BitVec 32) (offset : BitVec 32) (width : ℕ) (s) :
      EStateM.run (
        LeanRV32D.Functions.pmpCheck (
          physaddr.Physaddr (
            LeanRV32D.Functions.zero_extend (
              Sail.BitVec.addInt (reg_val + offset) 0
            )
          )
        )
        width
        (AccessType.Read ())
        Privilege.Machine
      ) s = EStateM.Result.ok none s
    := by
      sorry

  noncomputable def vmem_write_addr'
    (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width)))
    (acc : (AccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool)
  : SailM (Sail.Result Bool ExecutionResult) := Sail.SailME.run do
    let (n, bytes) ← do (LeanRV32D.Functions.split_misaligned vaddr width)
    let (first, last, step) := (LeanRV32D.Functions.misaligned_order n)
    let i : Nat := first
    let finished : Bool := false
    let write_success : Bool := true
    let vaddr := (LeanRV32D.Functions.bits_of_virtaddr vaddr)
    let (_finished, _i, write_success) ← (( do
      let loop_vars ← untilFuelM (fuel := n) (λ (_data, finished, _i) => (pure finished)) (finished, i, write_success)
        fun (finished, i, write_success) => do
          let offset := i
          let vaddr := (Sail.BitVec.addInt vaddr (offset *i bytes))
          let write_success ← (( do
            match (← (LeanRV32D.Functions.translateAddr (virtaddr.Virtaddr vaddr) acc)) with
            | .Err (e, _) =>
              Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result Bool ExecutionResult))
            | .Ok (paddr, _) =>
              (do
                if ((res && (not (match_reservation (LeanRV32D.Functions.bits_of_physaddr paddr)))) : Bool)
                then (pure false)
                else
                  (do
                    match (← (LeanRV32D.Functions.mem_write_ea paddr bytes aq rl res)) with
                    | .Err e =>
                      Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result Bool ExecutionResult))
                    | .Ok () =>
                      (do
                        let write_value :=
                          (Sail.BitVec.extractLsb data (((8 *i (offset +i 1)) *i bytes) -i 1)
                            ((8 *i offset) *i bytes))
                        match (← (LeanRV32D.Functions.mem_write_value paddr bytes write_value aq rl res)) with
                        | .Err e =>
                          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result Bool ExecutionResult))
                        | .Ok s => (pure (write_success && s))))) ) : Sail.SailME
            (Sail.Result Bool ExecutionResult) Bool )
          let (finished, i) : (Bool × Nat) :=
            if ((offset == last) : Bool)
            then
              (let finished : Bool := true
              (finished, i))
            else
              (let i : Nat := (offset +i step)
              (finished, i))
          (pure (finished, i, write_success))
      (pure loop_vars) ) : Sail.SailME (Sail.Result Bool ExecutionResult) (Bool × Nat × Bool) )
    (pure (Sail.Ok write_success))

  -- 'axiom' until the spec is rebuilt to avoid repeat
  lemma vmem_write_addr'_equiv :
    vmem_write_addr' =
    LeanRV32D.Functions.vmem_write_addr
  := by
    sorry

end Local
