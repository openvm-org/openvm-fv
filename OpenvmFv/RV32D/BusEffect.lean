import OpenvmFv.RV32D.Auxiliaries
import OpenvmFv.Fundamentals.Interaction

/-- `bus_effect` captures the effect of execution and memory bus contents
    on the RISC-V state, returning:
    - the hypotheses obtained from the reads; and
    - the state after the writes.

    Assumes that:
    - the execution bus holds two entries, a read and a write; and
    - the memory bus entries are in chronological order

    - the multiplicities of each entry are in { -1, 0, 1 }; and
    - the address space is either 1 (registers) or 2 (memory) -/
def bus_effect
  (execution_bus : List (Interaction.ExecutionBusEntry FBB))
  (memory_bus : List (Interaction.MemoryBusEntry FBB))
  (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
:
  Prop × (EStateM.Result (Sail.Error exception) (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult)
:=
  -- Execution bus assumption
  if execution_bus.length = 2 ∧ execution_bus[0]!.multiplicity = -1 ∧ execution_bus[1]!.multiplicity = 1
  then
    -- from the first entry on the execution bus, we learn the current program counter
    let initial_result : Prop × (EStateM.Result (Sail.Error exception) (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult) :=
      ⟨ Sail.readReg Register.PC state = EStateM.Result.ok (register_type_pc_equiv ▸ (BitVec.ofNat 32 (execution_bus[0]!.pc).val)) state, EStateM.Result.ok (ExecutionResult.Retire_Success ()) state ⟩
    let post_memory : Prop × (EStateM.Result (Sail.Error exception) (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult) :=
      List.foldl
        (fun ⟨ cond, result ⟩ entry =>
          match result with
          -- Previously got an error: impossible under assumptions
          | .error _ _ => ⟨ cond, result ⟩
          | .ok _ state =>
            -- Read
            if (entry.multiplicity = (-1 : FBB)) then
              -- Register read adds the assumption that the value of the read
              -- register is equal to the 32-bit interpretation of the
              -- appropriate memory bus entry values
              (if (entry.as = 1) then
                let val := U32.toBV #v[entry.x0, entry.x1, entry.x2, entry.x3]
                let reg_idx := Transpiler.wrap_to_regidx entry.ptr
                ⟨ cond ∧ read_xreg reg_idx state = EStateM.Result.ok val state, result ⟩
              -- Memory read adds the assumption that the four values in memory
              -- starting from the given pointer are equal to the appropriate
              -- memory bus entry values
              else if (entry.as = 2) then
                ⟨
                  state.mem[entry.ptr.toNat]? = .some entry.x0 ∧
                  state.mem[entry.ptr.toNat + 1]? = .some entry.x1 ∧
                  state.mem[entry.ptr.toNat + 2]? = .some entry.x2 ∧
                  state.mem[entry.ptr.toNat + 3]? = .some entry.x3
                , result ⟩
              -- Neither a register nor a memory read: impossible under assumptions
              else ⟨ cond, EStateM.Result.error Sail.Error.Unreachable state ⟩)
          -- Write
          else if (entry.multiplicity = (1 : FBB)) then
            (match entry.as with
            -- Register write writes the four values from the memory bus entry
            -- to the given register as a 32-bit value
            | 1 =>
              if h : Transpiler.wrap_to_regidx entry.ptr = 0 then
                ⟨ cond, result ⟩
              else
                let val := U32.toBV #v[entry.x0, entry.x1, entry.x2, entry.x3]
                let reg_idx := ⟨ (Transpiler.wrap_to_regidx entry.ptr).val, by simp; omega ⟩
                ⟨ cond, EStateM.Result.map
                        (fun x ↦ ExecutionResult.Retire_Success ())
                          (write_xreg reg_idx val state) ⟩
            -- Memory write writes the four values from the memory bus entry
            -- to memory starting from the given pointer
            | 2 =>
              ⟨
                cond
              , EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
                  state with mem :=
                    ((((state.mem.insert entry.ptr.toNat entry.x0
                    ).insert (entry.ptr.toNat + 1) entry.x1
                    ).insert (entry.ptr.toNat + 2) entry.x2
                    ).insert (entry.ptr.toNat + 3) entry.x3)
                }⟩
            -- Address space not 1 or 2 : impossible under assumptions
            | _ => ⟨ cond, EStateM.Result.error Sail.Error.Unreachable state ⟩)
          -- Multiplicity zero: no effect
          else if (entry.multiplicity = (0 : FBB)) then ⟨ cond, result ⟩
          -- Neither a register nor a memory read nor a no-effect: impossible under assumptions
          else ⟨ cond, EStateM.Result.error Sail.Error.Unreachable state ⟩
        )
        ⟨ Sail.readReg Register.PC state = EStateM.Result.ok (register_type_pc_equiv ▸ (BitVec.ofNat 32 (execution_bus[0]!.pc).val)) state, EStateM.Result.ok (ExecutionResult.Retire_Success ()) state ⟩
        memory_bus
    match post_memory.2 with
    -- the second entry on the execution bus sets the next program counter
    | .ok _ state => ⟨ post_memory.1,
                       EStateM.Result.map
                        (fun x ↦ ExecutionResult.Retire_Success ())
                        (Sail.writeReg
                           Register.nextPC
                           (register_type_pc_equiv ▸ (BitVec.ofNat 32 (execution_bus[1]!.pc).val))
                           state) ⟩
    -- Memory pass returned an error: impossible under assumptions
    | _ => post_memory
  else
    -- Malformed execution bus: impossible under assumptions
    ⟨ True, EStateM.Result.error Sail.Error.Unreachable state ⟩
