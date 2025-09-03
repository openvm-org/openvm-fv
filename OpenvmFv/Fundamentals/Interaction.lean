import OpenvmFv.Fundamentals.BabyBear

import LeanZKCircuit.Interactions

namespace Interaction

section ExecutionBus

-- TODO: Are there any constraints to be placed on the parameters?

/-- Constrained ExecutionBus entry -/
def executionBus_entry
  (mul pc : FBB) (timestamp : Fin 1073741824)
: (FBB × List FBB) :=
  (mul, [ pc, ⟨timestamp.val, by omega⟩ ])

/-- Useful equalities and entailments resulting from ExecutionBus balancing -/
lemma executionBus_balances_facts
  (h_balance : Interaction.balances
                (mul, [pc, timestamp])
                (executionBus_entry mul' pc' timestamp'))
:
  mul + mul' = 0 ∧
    (¬ mul = 0 → pc = pc' ∧
                 timestamp.val = timestamp'.val ∧
                 timestamp.val < 1073741824)
:= by
  simp_all [balances, executionBus_entry]

end ExecutionBus

section MemoryBus

/-- Constrained MemoryBus read entry -/
def memoryBus_read_entry
  (mul as ptr x1 x2 x3 x4 timestamp : FBB)
: (FBB × List FBB) :=
  (mul, [ as, ptr, x1, x2, x3, x4, timestamp])

/-- Constrained MemoryBus write entry -/
def memoryBus_write_entry
  (mul as ptr : FBB) (val : U32) (timestamp : Fin 1073741824)
: (FBB × List FBB) :=
  (mul, [ as, ptr, val[0], val[1], val[2], val[3], ⟨timestamp.val, by omega⟩ ])

/-- Useful equalities and entailments resulting from MemoryBus read balancing -/
lemma memoryBus_read_balances_facts
  (h_balance : Interaction.balances
                (mul, [ as, ptr, x0, x1, x2, x3, timestamp ])
                (memoryBus_read_entry mul' as' ptr' x0' x1' x2' x3' timestamp'))
:
  mul + mul' = 0 ∧
    (¬ mul = 0 → as = as' ∧
                 ptr = ptr' ∧
                 x0 = x0' ∧
                 x1 = x1' ∧
                 x2 = x2' ∧
                 x3 = x3' ∧
                 timestamp = timestamp')
:= by
  simp_all [balances, memoryBus_read_entry]

/-- Useful equalities and entailments resulting from MemoryBus read balancing -/
lemma memoryBus_write_balances_facts
  (h_balance : Interaction.balances
                (mul, [ as, ptr, x0, x1, x2, x3, timestamp ])
                (memoryBus_write_entry mul' as' ptr' x' timestamp'))
:
  mul + mul' = 0 ∧
    (¬ mul = 0 → as = as' ∧
                 ptr = ptr' ∧
                 x0 = x'[0] ∧
                 x1 = x'[1] ∧
                 x2 = x'[2] ∧
                 x3 = x'[3] ∧
                 timestamp.val = timestamp'.val ∧
                 timestamp.val < 1073741824 ∧
                 x0.val < 256 ∧
                 x1.val < 256 ∧
                 x2.val < 256 ∧
                 x3.val < 256)
:= by
  simp_all [balances, memoryBus_write_entry]
  omega

end MemoryBus

section RangeBus

/-- Constrained RangeBus entry -/
def rangeBus_entry
  (mul : FBB) (deg : Fin 30) (val : Fin (2 ^ deg.val))
: (FBB × List FBB) :=
  (mul, [ ⟨ val.val, by trans 2 ^ deg.val <;> [ omega; skip ];
                        apply lt_of_le_of_lt (b := 2 ^ 30) <;>
                        [ apply pow_le_pow; simp ] <;> simp ⟩,
          ⟨ deg.val, by omega ⟩ ])

/-- Useful equalities and entailments resulting from RangeBus balancing -/
lemma rangeBus_balances_facts
  (h_balance : Interaction.balances
                (mul, [val, deg])
                (rangeBus_entry mul' deg' val'))
:
  mul + mul' = 0 ∧
    (¬ mul = 0 → deg.val = deg'.val ∧
                 val.val = val'.val ∧
                 deg.val < 30 ∧ val.val < 2 ^ deg'.val)
:= by
  simp_all [balances, rangeBus_entry]

end RangeBus

section ReadInstructionBus

-- TODO: What do the three unknown parameters do?
-- TODO: Are there any constraints to be placed on the parameters?

/-- Constrained ReadInstructionBus entry -/
def readInstructionBus_entry
  (mul pc opcode rd rs1 rs2 unknown0 rs2_as unknown1 unknown2 : FBB)
: (FBB × List FBB) :=
  (mul, [ pc, opcode, rd, rs1, rs2, unknown0, rs2_as, unknown1, unknown2 ])

/-- Useful equalities and entailments resulting from ReadInstructionBus balancing -/
lemma readInstructionBus_balances_facts
  (h_balance : Interaction.balances
                (mul, [pc, opcode, rd, rs1, rs2, unknown0, rs2_as, unknown1, unknown2])
                (readInstructionBus_entry mul' pc' opcode' rd' rs1' rs2' unknown0' rs2_as' unknown1' unknown2'))
:
  mul + mul' = 0 ∧
    (¬ mul = 0 → pc = pc' ∧
                 opcode = opcode' ∧
                 rd = rd' ∧
                 rs1 = rs1' ∧
                 rs2 = rs2' ∧
                 unknown0 = unknown0' ∧
                 rs2_as = rs2_as' ∧
                 unknown1 = unknown1' ∧
                 unknown2 = unknown2')
:= by
  simp_all [balances, readInstructionBus_entry]

end ReadInstructionBus

section BitwiseBus

/-- Constrained BitwiseBus entry -/
def bitwiseBus_entry
  (mul : FBB) (a b : Fin 256) (is_lookup : Fin 2)
: (FBB × List FBB) :=
  (mul, [ ⟨ a.val, by omega ⟩,
          ⟨ b.val, by omega ⟩,
          ⟨ a ^^^ b, by have := @Nat.xor_lt_two_pow a b 8 (by omega); omega ⟩ ,
          ⟨ is_lookup.val, by omega ⟩ ])

/-- Useful equalities and entailments resulting from BitwiseBus balancing -/
lemma bitwiseBus_balances_facts
  (h_balance : Interaction.balances
                (mul, [a, b, c, is_lookup])
                (bitwiseBus_entry mul' a' b' is_lookup'))
:
  mul + mul' = 0 ∧
    (¬ mul = 0 → a.val = a'.val ∧
                 b.val = b'.val ∧
                 c.val = a.val ^^^ b.val ∧
                 is_lookup.val = is_lookup'.val ∧
                 a.val < 256 ∧
                 b.val < 256 ∧
                 c.val < 256 ∧
                 (is_lookup = 0 ∨ is_lookup = 1))
:= by
  simp_all [balances, bitwiseBus_entry]
  have := @Nat.xor_lt_two_pow a b 8 (by simp_all);
  simp_all
  omega

end BitwiseBus

end Interaction
