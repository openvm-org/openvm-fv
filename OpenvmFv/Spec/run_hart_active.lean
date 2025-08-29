-- import Mathlib

-- import LeanRV32D

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
--   funext
--   rfl

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

-- lemma readReg_state
--   (h: state.regs.get? reg = .some reg_val)
-- :
--   Sail.readReg reg state = EStateM.Result.ok reg_val state
-- := by
--   unfold Sail.readReg PreSail.readReg
--   unfold bind Monad.toBind EStateM.instMonad EStateM.bind EStateM.pure
--   dsimp
--   obtain ⟨regs⟩ := state
--   unfold MonadState.get instMonadStateOfMonadStateOf
--   unfold getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get
--   dsimp
--   dsimp at h
--   rewrite [h]
--   dsimp

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

-- lemma dispatchInterrupt_none
--   (cur_privilege_val: Privilege)
--   (mideleg_val: RegisterType Register.mideleg)
--   (mie_val: RegisterType Register.mie)
--   (mip_val: RegisterType Register.mip)
--   (misa_val: RegisterType Register.misa)
--   (mstatus_val: RegisterType Register.mstatus)
--   (h_mideleg: state.regs.get? Register.mideleg = .some mideleg_val)
--   (h_mie: state.regs.get? Register.mie = .some mie_val)
--   (h_mip: state.regs.get? Register.mip = .some mip_val)
--   (h_misa: state.regs.get? Register.misa = .some misa_val)
--   (h_mstatus: state.regs.get? Register.mstatus = .some mstatus_val)
--   (h_assert: BitVec.extractLsb 18 18 misa_val = 1#1 ∨ mideleg_val = 0#32)
--   (h_machine_interrupt: ((
--     cur_privilege_val == Privilege.Machine && BitVec.extractLsb 3 3 mstatus_val == 1#1 ||
--     (cur_privilege_val == Privilege.Supervisor || cur_privilege_val == Privilege.User)
--   ) && mip_val &&& (mie_val &&& ~~~mideleg_val) != 0#32) = false)
--   (h_supervisor_interrupt: ((
--     cur_privilege_val == Privilege.Supervisor && BitVec.extractLsb 1 1 mstatus_val == 1#1 ||
--     cur_privilege_val == Privilege.User
--   ) && mip_val &&& (mie_val &&& mideleg_val) != 0#32) = false)
-- :
--   LeanRV32D.Functions.dispatchInterrupt cur_privilege_val state = EStateM.Result.ok none state
-- := by
--   simp only [
--     LeanRV32D.Functions.dispatchInterrupt,
--     LeanRV32D.Functions.getPendingSet,
--     LeanRV32D.Functions.currentlyEnabled,
--     LeanRV32D.Functions.hartSupports,
--     LeanRV32D.Functions._get_Misa_S,
--     LeanRV32D.Functions.zeros,
--     LeanRV32D.Functions._get_Mstatus_MIE,
--     LeanRV32D.Functions._get_Mstatus_SIE,
--     Sail.assert,
--     PreSail.assert,
--     Sail.BitVec.extractLsb
--   ]

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   simp [readReg_state, *]

-- lemma instructionFetch_neq_false:
--   (@AccessType.InstructionFetch Unit () != AccessType.InstructionFetch ()) = false
-- := rfl

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

-- lemma effectivePrivilege_instructionFetch
-- :
--   LeanRV32D.Functions.effectivePrivilege (AccessType.InstructionFetch ()) mstatus_val cur_privilege_val state =
--   EStateM.Result.ok cur_privilege_val state
-- := by
--   unfold LeanRV32D.Functions.effectivePrivilege
--   simp [
--     instructionFetch_neq_false,
--     pure, EStateM.pure
--   ]

-- lemma architecture_backwards_mstatus_SXL
-- :
--   LeanRV32D.Functions.architecture_backwards (LeanRV32D.Functions.get_mstatus_SXL mstatus_val) state =
--   EStateM.Result.ok Architecture.RV32 state
-- := by
--   simp [
--     LeanRV32D.Functions.architecture_backwards,
--     LeanRV32D.Functions.get_mstatus_SXL,
--     LeanRV32D.Functions.architecture_forwards,
--     pure, EStateM.pure
--   ]

-- -- example (b: BitVec 1) :
-- --   0#3 ++ b = 0#4
-- -- := by
-- --   match b with
-- --     | 0#1 => rfl
-- --     | 1#1 => rfl

-- lemma extract_all_satp
--   (satp_val: RegisterType Register.satp)
-- :
--   Sail.BitVec.extractLsb satp_val 31 0 = satp_val
-- := by
--   simp [
--     Sail.BitVec.extractLsb,
--     BitVec.extractLsb
--   ]

-- lemma translationMode
--   (h_mstatus: state.regs.get? Register.mstatus = .some mstatus_val)
--   (h_satp: state.regs.get? Register.satp = .some satp_val)
-- :
--   LeanRV32D.Functions.translationMode cur_privilege_val state =
--   EStateM.Result.ok (
--     bif (cur_privilege_val == Privilege.Machine || Sail.BitVec.extractLsb satp_val 31 31 == 0#1)
--     then SATPMode.Bare
--     else SATPMode.Sv32
--   ) state
-- := by
--   unfold LeanRV32D.Functions.translationMode

--   unfold bind Monad.toBind EStateM.instMonad
--   dsimp
--   unfold EStateM.bind EStateM.pure
--   dsimp

--   by_cases h: cur_privilege_val == Privilege.Machine
--   . simp_all
--   . simp_all [
--       readReg_state, architecture_backwards_mstatus_SXL,
--       LeanRV32D.Functions.satpMode_of_bits,
--       LeanRV32D.Functions._get_Satp32_Mode,
--       LeanRV32D.Functions.Mk_Satp32,
--       extract_all_satp
--     ]
--     match (Sail.BitVec.extractLsb satp_val 31 31) with
--       | 0#1 => simp
--       | 1#1 => simp

-- lemma satp_mode_bare_eq: (SATPMode.Bare == SATPMode.Bare) = true := rfl
-- lemma satp_mode_sv32_neq_bare: (SATPMode.Sv32 == SATPMode.Bare) = false := rfl

-- lemma extract_all_pc (pc_val: xlenbits):
--   BitVec.extractLsb 31 0 pc_val = pc_val
-- := by
--   simp [BitVec.extractLsb]

-- lemma sign_extend_extract_all_pc(pc_val: xlenbits):
--   LeanRV32D.Functions.sign_extend (Sail.BitVec.extractLsb pc_val 31 0) = pc_val
-- := by
--   simp [
--     Sail.BitVec.extractLsb,
--     BitVec.extractLsb,
--     LeanRV32D.Functions.sign_extend,
--     Sail.BitVec.signExtend
--   ]

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
