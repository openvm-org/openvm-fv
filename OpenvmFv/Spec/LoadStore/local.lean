import Lean

import OpenvmFv.Spec.run_hart_active

namespace Local

  open LeanRV32D.Functions in
  noncomputable def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width: ℕ) : SailM ExecutionResult := do
    let offset : xlenbits := (sign_extend (m := 32) imm)
    Sail.assert (width ≤b LeanRV32D.Functions.xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29"
    match (← (vmem_read rs1 offset width (MemoryAccessType.Load Data) false false false)) with
    | .Ok data =>
      (do
        (wX_bits rd (extend_value is_unsigned data))
        (pure RETIRE_SUCCESS))
    | .Err e => (pure e)

  lemma execute_LOAD_equiv :
    execute_LOAD = LeanRV32D.Functions.execute_LOAD
  := rfl

  open LeanRV32D.Functions in
  noncomputable def vmem_read_addr (vaddr : virtaddr) (_offset : (BitVec 32)) (width : Nat) (acc : (MemoryAccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Sail.Result (BitVec (8 * width)) ExecutionResult) := Sail.SailME.run do
    if (res : Bool)
    then
      (do
        if ((LeanRV32D.Functions.not (is_aligned_vaddr vaddr width)) : Bool)
        then
          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_Load_Addr_Align ())))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
        else (pure ()))
    else
      (do
        if ((check_misaligned vaddr width) : Bool)
        then
          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_Load_Addr_Align ())))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
        else (pure ()))
    let (n, bytes) ← do (split_misaligned vaddr width)
    let data := (zeros (n := ((8 *i n) *i bytes)))
    let (first, last, step) := (misaligned_order n)
    let i : Nat := first
    let finished : Bool := false
    let vaddr := (bits_of_virtaddr vaddr)
    let (data, _finished, _i) ← (( do
      let loop_vars ← untilFuelM (fuel :=n) (fun (_data, finished, _i) => (pure finished)) (data, finished, i)
        fun (data, finished, i) => do
          Sail.assert true "loop dummy assert"
          let offset := i
          let vaddr := (Sail.BitVec.addInt vaddr (offset *i bytes))
          let data ← (( do
            match (← (translateAddr (virtaddr.Virtaddr vaddr) acc)) with
            | .Err (e, _) =>
              Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
            | .Ok (paddr, _) =>
              (do
                match (← (mem_read acc paddr bytes aq rl res)) with
                | .Err e =>
                  Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
                | .Ok v =>
                  (do
                    if (res : Bool)
                    then (load_reservation (bits_of_physaddr paddr) width)
                    else (pure ())
                    (pure (Sail.BitVec.updateSubrange data (((8 *i (offset +i 1)) *i bytes) -i 1)
                        ((8 *i offset) *i bytes) v)))) ) : SailME
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
      (pure loop_vars) ) : SailME (Sail.Result (BitVec (8 * width)) ExecutionResult)
      ((BitVec (8 * n * bytes)) × Bool × Nat) )
    (pure (Sail.Ok data))

  lemma vmem_read_addr_equiv :
    vmem_read_addr = LeanRV32D.Functions.vmem_read_addr
  := rfl

  open LeanRV32D.Functions in
  noncomputable def vmem_read
    (rs : regidx) (offset : BitVec 32) (width : ℕ) (acc : MemoryAccessType Unit)
    (aq rl res : Bool)
  : SailM (Sail.Result (BitVec (8 * width)) ExecutionResult) := Sail.SailME.run do
    let vaddr ← (( do
      match (← (LeanRV32D.Functions.ext_data_get_addr rs offset acc width)) with
      | .Ext_DataAddr_OK vaddr => (pure vaddr)
      | .Ext_DataAddr_Error e =>
        Sail.SailME.throw ((Sail.Err (ExecutionResult.Ext_DataAddr_Check_Failure e)) : (Sail.Result (BitVec (8 * width)) ExecutionResult))
      )  )
    (vmem_read_addr vaddr offset width acc aq rl res)

  lemma vmem_read_equiv :
    vmem_read = LeanRV32D.Functions.vmem_read
  := rfl

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
    simp [BitVec.clz_eq_reverse_ctz] at h
    have neqz : ¬ (bv = 0#width)
    := by
      have := @BitVec.ctz_lt_iff_ne_zero width bv
      simp [← BitVec.toNat_inj, BitVec.lt_def] at this
      grind
    . have bit := BitVec.getLsbD_true_ctz_of_ne_zero neqz
      rw [h] at bit
      rw [BitVec.getLsbD_eq_getElem (by omega)] at bit
      simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq] at bit
      simp [Int.tmod_eq_emod, -EuclideanDomain.mod_eq_zero]
      omega

  lemma mod_of_trailing_zeroes_eq_1 {width} {bv: BitVec width}
    (h: Sail.BitVec.countTrailingZeros bv = 1)
    (h_width: width > 1)
  : ((bv.toNat): Int).tmod 4 ≠ 0 := by
    unfold Sail.BitVec.countTrailingZeros at h
    unfold Sail.BitVec.countLeadingZeros at h
    simp [BitVec.clz_eq_reverse_ctz] at h
    have neqz : ¬ (bv = 0#width)
    := by
      have := @BitVec.ctz_lt_iff_ne_zero width bv
      simp [← BitVec.toNat_inj, BitVec.lt_def] at this
      grind
    . have bit := BitVec.getLsbD_true_ctz_of_ne_zero neqz
      rw [h] at bit
      rw [BitVec.getLsbD_eq_getElem (by omega)] at bit
      simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq] at bit
      simp [Int.tmod_eq_emod, -EuclideanDomain.mod_eq_zero]
      omega

  lemma mod_of_trailing_zeroes_ge_2 {width} {bv: BitVec width}
    (h: Sail.BitVec.countTrailingZeros bv ≥ 2)
    (h_width: width > 2)
  : ((bv.toNat): Int).tmod 4 = 0 := by
    unfold Sail.BitVec.countTrailingZeros at h
    unfold Sail.BitVec.countLeadingZeros at h
    simp [BitVec.clz_eq_reverse_ctz] at h
    have bit0 := @BitVec.getLsbD_false_of_lt_ctz width 0 bv (by omega)
    have bit1 := @BitVec.getLsbD_false_of_lt_ctz width 1 bv (by omega)
    rw [BitVec.getLsbD_eq_getElem (by omega)] at bit0 bit1
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq] at bit0 bit1
    simp [Int.tmod_eq_emod, -EuclideanDomain.mod_eq_zero]
    omega

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
      simp [mod_of_trailing_zeroes_ge_2 this]
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
    simp [vmem_read, vmem_read_addr, ext_data_get_addr]
    unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift
    unfold Functor.map ExceptT.mk monadLift instMonadLiftT EStateM.instMonad EStateM.map
    dsimp
    unfold bind ExceptT.instMonad ExceptT.bind ExceptT.mk ExceptT.bindCont
    simp [Sail.SailME.run, PreSail.PreSailME.run, ExceptT.run]
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
    (accessType: MemoryAccessType Unit)
    (privilege)
    (state)
    (status)
    (h_status:
      Sail.BitVec.extractLsb status 12 11 = 0#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 1#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 3#2
    )
    (h_access_type: accessType != MemoryAccessType.InstructionFetch ())
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

  lemma translation_mode
    (h_priv : (privilege : Privilege) = Privilege.Machine)
  :
    LeanRV32D.Functions.translationMode privilege state =
    EStateM.Result.ok (SATPMode.Bare) state
  := by
    unfold LeanRV32D.Functions.translationMode
    split_ifs with h_if
    . simp
    . exfalso
      simp_all
      tauto

  open LeanRV32D.Functions in
  lemma translate_addr
    (h_status: Sail.readReg Register.mstatus state = EStateM.Result.ok status state)
    (h_machine_privilege: Sail.readReg Register.cur_privilege state = EStateM.Result.ok privilege state)
    (h_status_val:
      Sail.BitVec.extractLsb status 12 11 = 0#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 1#2 ∨
      Sail.BitVec.extractLsb status 12 11 = 3#2
    )
    (assumption_privilege : privilege = Privilege.Machine)
    (assumption_MPRV_not_set : BitVec.extractLsb 17 17 status = 0#1)
  :
    translateAddr addr (MemoryAccessType.Load ()) state =
    EStateM.Result.ok (Sail.Ok (physaddr.Physaddr (BitVec.setWidth 34 addr.1), ())) state
  := by
    unfold translateAddr
    unfold_projs
    simp [
      EStateM.bind,
      h_status,
      h_machine_privilege,
      assumption_privilege,
      effective_privilege (MemoryAccessType.Load ()) Privilege.Machine state status h_status_val (by trivial),
      effective_privilege_pure,
      assumption_MPRV_not_set,
      translation_mode,
      instBEqSATPMode.beq,
    ]
    rw [zero_extend]
    simp [
      Sail.BitVec.zeroExtend,
      LeanRV32D.Functions.init_ext_ptw,
      LeanRV32D.Functions.bits_of_virtaddr,
      EStateM.pure
    ]

  set_option hygiene false
  open Lean Elab Tactic
  elab "get_inaccessible" names: binderIdent,* : tactic => do
    let x := λ g => Lean.Elab.Tactic.renameInaccessibles g names
    let y ← popMainGoal
    let z ← x y
    pushGoal z

  open LeanRV32D.Functions in
  noncomputable def vmem_write_addr (vaddr : virtaddr) (width : Nat) (data : (BitVec (8 * width))) (acc : (MemoryAccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Sail.Result Bool ExecutionResult) := Sail.SailME.run do
    if ((LeanRV32D.Functions.check_misaligned vaddr width) : Bool)
    then (pure (Sail.Err (ExecutionResult.Memory_Exception (vaddr, (ExceptionType.E_SAMO_Addr_Align ())))))
    else
      (do
        let (n, bytes) ← do (LeanRV32D.Functions.split_misaligned vaddr width)
        let (first, last, step) := (LeanRV32D.Functions.misaligned_order n)
        let i : Nat := first
        let finished : Bool := false
        let write_success : Bool := true
        let vaddr := (bits_of_virtaddr vaddr)
        let (_finished, _i, write_success) ← (( do
          let loop_vars ← untilFuelM (fuel :=n) (fun (finished, _i, _write_success) => (pure finished)) (finished, i, write_success)
            fun (finished, i, write_success) => do
              Sail.assert true "loop dummy assert"
              let offset := i
              let vaddr := (Sail.BitVec.addInt vaddr (offset *i bytes))
              let write_success ← (( do
                match (← (translateAddr (virtaddr.Virtaddr vaddr) acc)) with
                | .Err (e, _) =>
                  Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result Bool ExecutionResult))
                | .Ok (paddr, _) =>
                  (do
                    if ((res && (LeanRV32D.Functions.not (match_reservation (bits_of_physaddr paddr)))) : Bool)
                    then (pure false)
                    else
                      (do
                        match (← (mem_write_ea paddr bytes aq rl res)) with
                        | .Err e =>
                          Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result Bool ExecutionResult))
                        | .Ok () =>
                          (do
                            let write_value :=
                              (Sail.BitVec.extractLsb data (((8 *i (offset +i 1)) *i bytes) -i 1)
                                ((8 *i offset) *i bytes))
                            match (← (mem_write_value paddr bytes write_value aq rl res)) with
                            | .Err e =>
                              Sail.SailME.throw ((Sail.Err (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr vaddr), e))) : (Sail.Result Bool ExecutionResult))
                            | .Ok s => (pure (write_success && s))))) ) : SailME
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
          (pure loop_vars) ) : SailME (Sail.Result Bool ExecutionResult) (Bool × Nat × Bool) )
        (pure (Sail.Ok write_success)))

  lemma vmem_write_adder_equiv :
    vmem_write_addr = LeanRV32D.Functions.vmem_write_addr
  := rfl

  open LeanRV32D.Functions in
  noncomputable def vmem_write (rs_addr : regidx) (offset : (BitVec 32)) (width : Nat) (data : (BitVec (8 * width))) (acc : (MemoryAccessType Unit)) (aq : Bool) (rl : Bool) (res : Bool) : SailM (Sail.Result Bool ExecutionResult) := Sail.SailME.run do
    let vaddr ← (( do
      match (← (LeanRV32D.Functions.ext_data_get_addr rs_addr offset acc width)) with
      | .Ext_DataAddr_OK vaddr => (pure vaddr)
      | .Ext_DataAddr_Error e =>
        Sail.SailME.throw ((Sail.Err (ExecutionResult.Ext_DataAddr_Check_Failure e)) : (Sail.Result Bool ExecutionResult)) ) : SailME
      (Sail.Result Bool ExecutionResult) virtaddr )
    (vmem_write_addr vaddr width data acc aq rl res)

  lemma vmem_write_equiv :
    vmem_write = LeanRV32D.Functions.vmem_write
  := rfl

end Local
