import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace VmAirWrapper_alu.constraints

def constraint_list
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List Prop :=
  [
    VmAirWrapper_alu.extraction.constraint_0 c row,
    VmAirWrapper_alu.extraction.constraint_1 c row,
    VmAirWrapper_alu.extraction.constraint_2 c row,
    VmAirWrapper_alu.extraction.constraint_3 c row,
    VmAirWrapper_alu.extraction.constraint_4 c row,
    VmAirWrapper_alu.extraction.constraint_5 c row,
    VmAirWrapper_alu.extraction.constraint_6 c row,
    VmAirWrapper_alu.extraction.constraint_7 c row,
    VmAirWrapper_alu.extraction.constraint_8 c row,
    VmAirWrapper_alu.extraction.constraint_9 c row,
    VmAirWrapper_alu.extraction.constraint_10 c row,
    VmAirWrapper_alu.extraction.constraint_11 c row,
    VmAirWrapper_alu.extraction.constraint_12 c row,
    VmAirWrapper_alu.extraction.constraint_13 c row,
    VmAirWrapper_alu.extraction.constraint_14 c row,
    VmAirWrapper_alu.extraction.constraint_15 c row,
    VmAirWrapper_alu.extraction.constraint_16 c row,
    VmAirWrapper_alu.extraction.constraint_17 c row,
    VmAirWrapper_alu.extraction.constraint_18 c row,
    VmAirWrapper_alu.extraction.constraint_19 c row,
    VmAirWrapper_alu.extraction.constraint_20 c row,
    VmAirWrapper_alu.extraction.constraint_21 c row,
    VmAirWrapper_alu.extraction.constrain_interactions c
  ]

@[simp]
def allHold
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (_ : row ≤ c.last_row)
: Prop :=
  List.Forall (fun x => x) (constraint_list c row)

lemma allHold_constraints
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (valid_row : row ≤ c.last_row)
:
  allHold c row valid_row ↔
    (c.core.opcode_add_flag row 0 = 0 ∨ c.core.opcode_add_flag row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ c.core.opcode_sub_flag row 0 = 1) ∧
    (c.core.opcode_xor_flag row 0 = 0 ∨ c.core.opcode_xor_flag row 0 = 1) ∧
    (c.core.opcode_or_flag row 0 = 0 ∨ c.core.opcode_or_flag row 0 = 1) ∧
    (c.core.opcode_and_flag row 0 = 0 ∨ c.core.opcode_and_flag row 0 = 1) ∧
    (c.core.is_valid row 0 = 0 ∨ c.core.is_valid row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_0 row 0 + c.core.c_0 row 0 = c.core.a_0 row 0) ∨ c.core.carry_add_0 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_0 row 0 + c.core.c_0 row 0 = c.core.b_0 row 0) ∨ c.core.carry_sub_0 row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 + c.core.carry_add_0 row 0 = 0) ∨ c.core.carry_add_1 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 + c.core.carry_sub_0 row 0 = 0) ∨ c.core.carry_sub_1 row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_2 row 0 + c.core.c_2 row 0 - c.core.a_2 row 0 + c.core.carry_add_1 row 0 = 0) ∨ c.core.carry_add_2 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_2 row 0 + c.core.c_2 row 0 - c.core.b_2 row 0 + c.core.carry_sub_1 row 0 = 0) ∨ c.core.carry_sub_2 row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_3 row 0 + c.core.c_3 row 0 - c.core.a_3 row 0 + c.core.carry_add_2 row 0 = 0) ∨ c.core.carry_add_3 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_3 row 0 + c.core.c_3 row 0 - c.core.b_3 row 0 + c.core.carry_sub_2 row 0 = 0) ∨ c.core.carry_sub_3 row 0 = 1) ∧
    (c.adapter.rs2_as row 0 = 0 ∨ c.adapter.rs2_as row 0 = 1) ∧
    (c.adapter.rs2_as row 0 = 1 ∨ c.adapter.rs2 row 0 = c.rs2_imm row 0) ∧
    (c.adapter.rs2_as row 0 = 1 ∨ c.rs2_sign row 0 = c.rs2_limbs row 0 3) ∧
    (c.adapter.rs2_as row 0 = 1 ∨ c.core.c_2 row 0 = 0 ∨ c.core.c_2 row 0 = 255) ∧
    (c.core.is_valid row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 - c.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 = c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) ∧
    (c.adapter.rs2_as row 0 = 0 ∨ c.core.is_valid row 0 = 1) ∧
    (c.adapter.rs2_as row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 + 1 - c.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 = c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) ∧
    (c.core.is_valid row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 + 2 - c.adapter.writes_aux.base.prev_timestamp row 0 - 1 = c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) ∧
    VmAirWrapper_alu.extraction.constrain_interactions c
:= by
  simp [constraint_list]
  simp [openvm_encapsulation]

lemma single_op
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (valid_row : row ≤ c.last_row)
  (cstrs : allHold c row valid_row)
:
  let is_add := c.core.opcode_add_flag row 0
  let is_sub := c.core.opcode_sub_flag row 0
  let is_xor := c.core.opcode_xor_flag row 0
  let is_or := c.core.opcode_or_flag row 0
  let is_and := c.core.opcode_and_flag row 0
  (is_add = 1 → is_sub = 0 ∧ is_xor = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
  (is_sub = 1 → is_add = 0 ∧ is_xor = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
  (is_xor = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
  (is_or = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_xor = 0 ∧ is_and = 0) ∧
  (is_and = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_xor = 0 ∧ is_or = 0)
:= by
  rw [allHold_constraints c row valid_row] at cstrs
  obtain ⟨ h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
  rw [Valid_BaseAluCoreAir.is_valid] at h5
  clear rest
  grind (splits := 23)

lemma op_from_opcode
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (valid_row : row ≤ c.last_row)
  (cstrs : allHold c row valid_row)
  (is_valid : c.core.is_valid row 0 = 1)
:
  let is_add := c.core.opcode_add_flag row 0
  let is_sub := c.core.opcode_sub_flag row 0
  let is_xor := c.core.opcode_xor_flag row 0
  let is_or := c.core.opcode_or_flag row 0
  let is_and := c.core.opcode_and_flag row 0
  ((c.core.ctx row 0).instruction.opcode = 512 → is_add = 1) ∧
  ((c.core.ctx row 0).instruction.opcode = 513 → is_sub = 1) ∧
  ((c.core.ctx row 0).instruction.opcode = 514 → is_xor = 1) ∧
  ((c.core.ctx row 0).instruction.opcode = 515 → is_or = 1) ∧
  ((c.core.ctx row 0).instruction.opcode = 516 → is_and = 1)
:= by
  rw [allHold_constraints c row valid_row] at cstrs
  obtain ⟨ h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
  rw [Valid_BaseAluCoreAir.is_valid] at h5
  rw [← BaseAluCoreAir.is_valid_def] at is_valid
  rw [← BaseAluCoreAir.ctx.instruction.opcode_def]
  clear rest
  grind

lemma opcode_bounds
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (valid_row : row ≤ c.last_row)
  (cstrs : allHold c row valid_row)
  (is_valid : c.core.is_valid row 0 = 1)
:
  (c.core.ctx row 0).instruction.opcode = 512 ∨
  (c.core.ctx row 0).instruction.opcode = 513 ∨
  (c.core.ctx row 0).instruction.opcode = 514 ∨
  (c.core.ctx row 0).instruction.opcode = 515 ∨
  (c.core.ctx row 0).instruction.opcode = 516
:= by
  have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op c row valid_row cstrs
  rw [← BaseAluCoreAir.ctx.instruction.opcode_def]
  rw [← BaseAluCoreAir.is_valid_def] at is_valid
  rw [allHold_constraints c row valid_row] at cstrs
  obtain ⟨ h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
  clear rest
  grind

end VmAirWrapper_alu.constraints

namespace VmAirWrapper_alu.buses

lemma buses_eq [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (h : VmAirWrapper_alu.extraction.constrain_interactions c)
: c.buses = fun index ↦
  if index = ExecutionBus then
    List.flatMap
      (fun row ↦
        [(-c.core.is_valid row 0, [c.adapter.from_state.pc row 0, c.adapter.from_state.timestamp row 0]),
          (c.core.is_valid row 0, [c.adapter.from_state.pc row 0 + 4, c.adapter.from_state.timestamp row 0 + 3])])
      (List.range (c.last_row + 1))
  else
    if index = MemoryBus then
      List.flatMap
        (fun row ↦
          [(2013265920 * c.core.is_valid row 0,
              [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
                c.adapter.reads_aux_0.base.prev_timestamp row 0]),
            (c.core.is_valid row 0,
              [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
                c.adapter.from_state.timestamp row 0]),
            (2013265920 * c.adapter.rs2_as row 0,
              [c.adapter.rs2_as row 0, c.adapter.rs2 row 0, c.core.c_0 row 0, c.core.c_1 row 0, c.core.c_2 row 0,
                c.core.c_3 row 0, c.adapter.reads_aux_1.base.prev_timestamp row 0]),
            (c.adapter.rs2_as row 0,
              [c.adapter.rs2_as row 0, c.adapter.rs2 row 0, c.core.c_0 row 0, c.core.c_1 row 0, c.core.c_2 row 0,
                c.core.c_3 row 0, c.adapter.from_state.timestamp row 0 + 1]),
            (2013265920 * c.core.is_valid row 0,
              [1, c.adapter.rd_ptr row 0, c.adapter.writes_aux.prev_data_0 row 0,
                c.adapter.writes_aux.prev_data_1 row 0, c.adapter.writes_aux.prev_data_2 row 0,
                c.adapter.writes_aux.prev_data_3 row 0, c.adapter.writes_aux.base.prev_timestamp row 0]),
            (c.core.is_valid row 0,
              [1, c.adapter.rd_ptr row 0, c.core.a_0 row 0, c.core.a_1 row 0, c.core.a_2 row 0, c.core.a_3 row 0,
                c.adapter.from_state.timestamp row 0 + 2])])
        (List.range (c.last_row + 1))
    else
      if index = RangeCheckerBus then
        List.flatMap
          (fun row ↦
            [(c.core.is_valid row 0, [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
             (c.core.is_valid row 0, [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
             (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
             (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
             (c.core.is_valid row 0, [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
             (c.core.is_valid row 0, [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12])])
          (List.range (c.last_row + 1))
      else
        if index = ReadInstructionBus then
          List.flatMap
            (fun row ↦
              [(c.core.is_valid row 0,
                  [c.adapter.from_state.pc row 0, (c.core.ctx row 0).instruction.opcode, c.adapter.rd_ptr row 0,
                    c.adapter.rs1_ptr row 0, c.adapter.rs2 row 0, 1, c.adapter.rs2_as row 0, 0, 0])])
            (List.range (c.last_row + 1))
        else
          if index = BitwiseBus then
            List.flatMap
              (fun row ↦
                [(c.core.is_valid row 0, [c.core.x_0 row 0, c.core.y_0 row 0, c.core.x_xor_y_0 row 0, 1]),
                 (c.core.is_valid row 0, [c.core.x_1 row 0, c.core.y_1 row 0, c.core.x_xor_y_1 row 0, 1]),
                 (c.core.is_valid row 0, [c.core.x_2 row 0, c.core.y_2 row 0, c.core.x_xor_y_2 row 0, 1]),
                 (c.core.is_valid row 0, [c.core.x_3 row 0, c.core.y_3 row 0, c.core.x_xor_y_3 row 0, 1]),
                 (c.core.is_valid row 0 - c.adapter.rs2_as row 0, [c.core.c_0 row 0, c.core.c_1 row 0, 0, 0])])
              (List.range (c.last_row + 1))
          else [] := by
  -- unfold and simp specifically at h so that the simplified expression can be taken from the infoview
  unfold VmAirWrapper_alu.extraction.constrain_interactions at h
  simp [openvm_encapsulation] at h
  exact h

section BusRows

@[simp]
def executionBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (-ac.is_valid row 0, [aa.from_state.pc row 0, aa.from_state.timestamp row 0]),
    (ac.is_valid row 0, [aa.from_state.pc row 0 + 4, aa.from_state.timestamp row 0 + 3])
  ]

@[simp]
def memoryBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (2013265920 * ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.reads_aux_0.base.prev_timestamp row 0]),
    (ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.from_state.timestamp row 0]),
    (2013265920 * aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.reads_aux_1.base.prev_timestamp row 0]),
    (aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.from_state.timestamp row 0 + 1]),
    (2013265920 * ac.is_valid row 0, [1, aa.rd_ptr row 0, aa.writes_aux.prev_data_0 row 0, aa.writes_aux.prev_data_1 row 0, aa.writes_aux.prev_data_2 row 0, aa.writes_aux.prev_data_3 row 0, aa.writes_aux.base.prev_timestamp row 0]),
    (ac.is_valid row 0, [1, aa.rd_ptr row 0, ac.a_0 row 0, ac.a_1 row 0, ac.a_2 row 0, ac.a_3 row 0, aa.from_state.timestamp row 0 + 2])
  ]

@[simp]
def rangeBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (ac.is_valid row 0, [aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (ac.is_valid row 0, [aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (aa.rs2_as row 0, [aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (aa.rs2_as row 0, [aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (ac.is_valid row 0, [aa.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (ac.is_valid row 0, [aa.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
  ]

@[simp]
def readInstructionBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (ac.is_valid row 0, [aa.from_state.pc row 0,
                         (ac.ctx row 0).instruction.opcode,
                         aa.rd_ptr row 0,
                         aa.rs1_ptr row 0,
                         aa.rs2 row 0,
                         1,
                         aa.rs2_as row 0,
                         0,
                         0])
  ]

@[simp]
def bitwiseBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (ac.is_valid row 0, [ac.x_0 row 0, ac.y_0 row 0, ac.x_xor_y_0 row 0, 1]),
    (ac.is_valid row 0, [ac.x_1 row 0, ac.y_1 row 0, ac.x_xor_y_1 row 0, 1]),
    (ac.is_valid row 0, [ac.x_2 row 0, ac.y_2 row 0, ac.x_xor_y_2 row 0, 1]),
    (ac.is_valid row 0, [ac.x_3 row 0, ac.y_3 row 0, ac.x_xor_y_3 row 0, 1]),
    (ac.is_valid row 0 - aa.rs2_as row 0, [ac.c_0 row 0, ac.c_1 row 0, 0, 0])
  ]

lemma buses_eq_compact [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (h : VmAirWrapper_alu.extraction.constrain_interactions c)
:
  c.buses =
    fun index ↦
      if index = ExecutionBus then
        List.flatMap
          (fun row ↦ executionBus_row c row)
          (List.range (c.last_row + 1))
      else
      if index = MemoryBus then
        List.flatMap
          (fun row ↦ memoryBus_row c row)
          (List.range (c.last_row + 1))
      else
      if index = RangeCheckerBus then
        List.flatMap
          (fun row ↦ rangeBus_row c row)
          (List.range (c.last_row + 1))
      else
      if index = ReadInstructionBus then
        List.flatMap
          (fun row ↦ readInstructionBus_row c row)
          (List.range (c.last_row + 1))
      else
      if index = BitwiseBus then
        List.flatMap
          (fun row ↦ bitwiseBus_row c row)
          (List.range (c.last_row + 1))
      else []
:= by
  simp [buses_eq c h]

end BusRows

end VmAirWrapper_alu.buses

namespace Interaction

/-- ALU-related ReadInstruction bus assumptions -/
def readInstructionBus_assumptions_ALU
  (mul _ opcode rd rs1 rs2 xd rs2_as xf xg : FBB)
: Prop :=
  ¬ mul = 0 →
    -- rd and rs1 boundaries
    rd.val < 32 ∧ rs1.val < 32 ∧
    -- non-immediate rs2
    (rs2_as = 1 → rs2.val < 32) ∧
    -- immediate rs2
    (rs2_as = 0 →
      -- opcode cannot be SUB
      ¬ opcode = 513 ∧
      -- immediate fits 24 bits
      rs2.val < 2 ^ 24 ∧
      -- immediate is a sign-extended 12-bit value
      (BitVec.ofNat 24 rs2.val).toInt = (BitVec.ofNat 12 rs2.val).toInt) ∧
    -- unused parameters
    xd = 1 ∧ xf = 0 ∧ xg = 0

end Interaction

namespace VmAirWrapper_alu.auxiliaries

lemma byte_xor_as_and
  {a b : ℕ}
  (ub_a : a < 256)
  (ub_b : b < 256)
:
  a ^^^ b = (a + b) - 2 * (a &&& b)
:= by
  have lt_b_and_c := @Nat.and_le_left a b
  have bv_xor_as_and : forall (a b : BitVec 9), a ^^^ b = (a + b) - 2 * (a &&& b) := by bv_decide
  specialize bv_xor_as_and { toFin := ⟨ a, by omega⟩ } { toFin := ⟨ b, by omega⟩ }
  simp [← BitVec.toNat_inj, Fin.add_def] at bv_xor_as_and
  rw [Nat.mod_eq_of_lt (a := 2 * (a &&& b)) (by omega)] at bv_xor_as_and
  have : (512 - 2 * (a &&& b) + (a + b)) % 512 < 256 := by rw [← bv_xor_as_and]; exact Nat.xor_lt_two_pow (n := 8) ub_a ub_b
  have : (512 - 2 * (a &&& b) + (a + b)) % 512 = (a + b) - 2 * (a &&& b) := by omega
  rw [this] at bv_xor_as_and
  exact bv_xor_as_and

lemma byte_xor_as_or
  {a b : ℕ}
  (ub_a : a < 256)
  (ub_b : b < 256)
:
  a ^^^ b = 2 * (a ||| b) - (a + b)
:= by
  have := @Nat.left_le_or a b
  have := @Nat.or_lt_two_pow a b 8 ub_a ub_b
  have bv_xor_as_or : forall (a b : BitVec 9), a ^^^ b = 2 * (a ||| b) - (a + b) := by bv_decide
  specialize bv_xor_as_or { toFin := ⟨ a, by omega⟩ } { toFin := ⟨ b, by omega⟩ }
  simp [← BitVec.toNat_inj, Fin.add_def] at bv_xor_as_or
  rw [Nat.mod_eq_of_lt (a := a + b) (by omega)] at bv_xor_as_or
  have : (512 - (a + b) + 2 * (a ||| b)) % 512 < 256 := by rw [← bv_xor_as_or]; exact Nat.xor_lt_two_pow (n := 8) ub_a ub_b
  have : (512 - (a + b) + 2 * (a ||| b)) % 512 = 2 * (a ||| b) - (a + b) := by omega
  rw [this] at bv_xor_as_or
  exact bv_xor_as_or

lemma FBB_xor_as_and
  {a b c : FBB}
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (h_eq : (b + c - 2 * a).val = b.val ^^^ c.val)
:
  a.val < 256 ∧ a.val = b.val &&& c.val
:= by
  have := @Nat.and_le_left b c
  have := @Nat.and_le_right b c
  rw [byte_xor_as_and ub_b ub_c] at h_eq
  simp [Fin.add_def, Fin.sub_def, Fin.mul_def] at *
  grind

lemma FBB_xor_as_or
  {a b c : FBB}
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (h_eq : (2 * a - b - c).val = b.val ^^^ c.val)
:
  a.val < 256 ∧ a.val = b.val ||| c.val
:= by
  have := @Nat.or_lt_two_pow b c 8 ub_b ub_c
  have := @Nat.left_le_or b c
  have := @Nat.right_le_or b c
  rw [byte_xor_as_or ub_b ub_c] at h_eq
  grind

end VmAirWrapper_alu.auxiliaries
