import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Execution

import LeanZKCircuit.Interactions

axiom constraints_MemoryBus
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu_BB ExtF) :
  ∀ x ∈ c.buses MemoryBus,
    x.1 = 1 →
      x.2[2]!.val < 256 ∧
      x.2[3]!.val < 256 ∧
      x.2[4]!.val < 256 ∧
      x.2[5]!.val < 256

theorem spec
  [Field F] [Field ExtF]
  [BEq (List F)] [Inhabited F]
  (c : Valid_VmAirWrapper_alu F ExtF)
  (h_last_row : c.last_row = 0)
  (h_constraints : all_constraints c 0)
  (h_is_add : c.core.opcode_add_flag = 1)
  (h_bitwise:
    Interaction.balanced_by (c.buses BitwiseBus) bitwise_bus →
      ∀ x ∈ bitwise_bus, x.1 ≠ 0 →
        ∀ e ∈ x.2, field_to_nat e < 256
  )
  (h_memory:
    Interaction.balanced_by (c.buses MemoryBus) memory_bus →
      ∀ x ∈ memory_bus, x.1 = 1 →
        field_to_nat x.2[2]! < 256 ∧
        field_to_nat x.2[3]! < 256 ∧
        field_to_nat x.2[4]! < 256 ∧
        field_to_nat x.2[5]! < 256
  )
:
  U32.toBV #v[
    BitVec.ofNat 8 (field_to_nat (c.core.a_0 0 0)),
    BitVec.ofNat 8 (field_to_nat (c.core.a_1 0 0)),
    BitVec.ofNat 8 (field_to_nat (c.core.a_2 0 0)),
    BitVec.ofNat 8 (field_to_nat (c.core.a_3 0 0)),
  ] =
  execute_RTYPE_pure_U32
    #v[
      BitVec.ofNat 8 (field_to_nat (c.core.b_0 0 0)),
      BitVec.ofNat 8 (field_to_nat (c.core.b_1 0 0)),
      BitVec.ofNat 8 (field_to_nat (c.core.b_2 0 0)),
      BitVec.ofNat 8 (field_to_nat (c.core.b_3 0 0)),
    ]
    #v[
      BitVec.ofNat 8 (field_to_nat (c.core.c_0 0 0)),
      BitVec.ofNat 8 (field_to_nat (c.core.c_1 0 0)),
      BitVec.ofNat 8 (field_to_nat (c.core.c_2 0 0)),
      BitVec.ofNat 8 (field_to_nat (c.core.c_3 0 0)),
    ]
    .ADD
  ∧ in_range (c.core.a_0 0 0)
  ∧ in_range (c.core.a_1 0 0)
  ∧ in_range (c.core.a_2 0 0)
  ∧ in_range (c.core.a_3 0 0)
:= by
  unfold all_constraints at h_constraints
  obtain ⟨c0, c1, c2, c3, c4, c5, c_interactions⟩ := h_constraints
  replace c0 := VmAirWrapper_alu.constraints.constraint_0' c 0 c0
  replace c1 := VmAirWrapper_alu.constraints.constraint_1' c 0 c1
  replace c2 := VmAirWrapper_alu.constraints.constraint_2' c 0 c2
  replace c3 := VmAirWrapper_alu.constraints.constraint_3' c 0 c3
  replace c4 := VmAirWrapper_alu.constraints.constraint_4' c 0 c4
  replace c5 := VmAirWrapper_alu.constraints.constraint_5' c 0 c5
  replace c_interactions := VmAirWrapper_alu.constraints.constrain_interactions' c c_interactions
  -- simp_all

  -- unfold BitwiseBus ExecutionBus MemoryBus RangeCheckerBus ReadInstructionBus at h_bitwise
  -- simp at h_bitwise

  -- have : c.core.is_valid 0 0 = 1 := by sorry
  -- simp [this] at h_bitwise
  -- unfold Valid_BaseAluCoreAir.x_0 at h_bitwise

  done
