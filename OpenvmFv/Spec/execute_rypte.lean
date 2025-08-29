import Mathlib

import LeanRV32D

#print LeanRV32D.Functions.execute_RTYPE
#print LeanRV32D.Functions.run_hart_active
#print LeanRV32D.Functions.rX_bits
#print LeanRV32D.Functions.rX

-- #print LeanRV32D.Functions.run_hart_active

-- noncomputable def run_hart_active' (step_no : ℕ) (w: word) : SailM Step := do
--     let instbits : instbits := (LeanRV32D.Functions.zero_extend (m := 32) w)
--     let instruction ← do (LeanRV32D.Functions.ext_decode w)
--     Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
--     let r ← do (LeanRV32D.Functions.execute instruction)
--     (pure (Step.Step_Execute (r, instbits)))

-- lemma run_hart_equiv
--     (step_no: ℕ)
--     (state1 state2 state3 state4: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
--     (h_priv: Sail.readReg Register.cur_privilege state1 = EStateM.Result.ok priv state2)
--     (h_dispatch: LeanRV32D.Functions.dispatchInterrupt priv state2 = EStateM.Result.ok .none state3)
--     (h_fetch: LeanRV32D.Functions.fetch () state3 = EStateM.Result.ok fetch_result state4)
--     (h_fetch_hook: LeanRV32D.Functions.ext_fetch_hook fetch_result = FetchResult.F_Base w)
--     (h_decode: LeanRV32D.Functions.ext_decode w state4 = EStateM.Result.ok inst state6)
--     (h_priv': Sail.readReg Register.cur_privilege state6 = EStateM.Result.ok priv state7)
--     (h_pc : Sail.readReg Register.PC state7 = Sail.readReg Register.PC state6)
-- :
--     LeanRV32D.Functions.run_hart_active step_no state1 =
--     run_hart_active' step_no w state4
-- := by
--     unfold LeanRV32D.Functions.run_hart_active
--     unfold run_hart_active'

--     unfold bind Monad.toBind EStateM.instMonad
--     dsimp
--     unfold EStateM.bind
--     dsimp

--     simp [h_priv]

--     unfold LeanRV32D.Functions.dispatchInterrupt
--     unfold LeanRV32D.Functions.getPendingSet
--     unfold LeanRV32D.Functions.currentlyEnabled
--     unfold LeanRV32D.Functions.currentlyEnabled
--     unfold LeanRV32D.Functions.hartSupports
--     unfold LeanRV32D.Functions._get_Misa_S

--     unfold bind Monad.toBind EStateM.instMonad
--     dsimp
--     unfold EStateM.bind EStateM.pure
--     dsimp



--     unfold LeanRV32D.Functions.fetch LeanRV32D.Functions.get_config_rvfi
--     dsimp
--     unfold bind Monad.toBind EStateM.instMonad
--     dsimp
--     unfold EStateM.bind
--     done
--         h_fetch,
--         h_fetch_hook,
--         h_decode,
--         h_priv',
--         h_pc
--     ]
