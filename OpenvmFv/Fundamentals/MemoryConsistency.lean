import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Fundamentals.Transpiler
import OpenvmFv.RV32D.Auxiliaries

import OpenvmFv.Constraints.VmAirWrapper_auipc
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_branch_eq
import OpenvmFv.Constraints.VmAirWrapper_branch_lt
import OpenvmFv.Constraints.VmAirWrapper_divrem
import OpenvmFv.Constraints.VmAirWrapper_jallui
import OpenvmFv.Constraints.VmAirWrapper_jalr
import OpenvmFv.Constraints.VmAirWrapper_load_sign_extend
import OpenvmFv.Constraints.VmAirWrapper_loadstore
import OpenvmFv.Constraints.VmAirWrapper_lt
import OpenvmFv.Constraints.VmAirWrapper_mul
import OpenvmFv.Constraints.VmAirWrapper_mulh
import OpenvmFv.Constraints.VmAirWrapper_shift

import OpenvmFv.Spec.JalLui
import OpenvmFv.Spec.JalR

set_option maxRecDepth 20_000
set_option maxHeartbeats 1_000_000

namespace Consistency

  open InteractionList

  section WfConstraints

    /-- A well formed chip with respect to a measure μ provides:
      - pairs of read-write entries put on the execution bus
      - pairs of read-write entries put on the memory bus
      - the proof that each memory bus read-write entry is for the same pointer
      - a proof that the execution bus entries are rising
      - a proof that the memory bus entries are rising -/
    class WFConstraints (α : Type) (air : α) (μ : List FBB → ℕ) where
      execution_bus_entries : List (List FBB × List FBB)
      memory_bus_entries : List (List FBB × List FBB)
      memory_bus_entries_wf : ∀ a b, (a, b) ∈ memory_bus_entries → (a[1]!.val = b[1]!.val)
      rising_pairs_on_execution_bus : ∀ a b, (a, b) ∈ execution_bus_entries → μ a < μ b
      rising_pairs_on_memory_bus : ∀ a b, (a, b) ∈ memory_bus_entries → μ a < μ b

    /-- A general well-formed chip -/
    structure WFChip (μ : List FBB → ℕ) where
      ChipType : Type
      chip : ChipType
      [inst_wf : WFConstraints ChipType chip μ]

  end WfConstraints

  section Execution

    /-- The overall execution bus -/
    def execution_bus (chips : List (WFChip μ))
    :
      List (List FBB × List FBB)
    :=
      List.flatMap (fun chip ↦ chip.inst_wf.execution_bus_entries) chips

    /-- The execution bus is a rising bus -/
    lemma execution_bus_is_rising_bus (chips : List (WFChip μ))
    :
      ∀ entry ∈ (execution_bus chips), μ entry.1 < μ entry.2
    := by
      intro entry h_in
      unfold execution_bus at h_in
      apply List.exists_of_mem_flatMap at h_in
      obtain ⟨ chip, h_in, h_entry ⟩ := h_in
      exact @WFConstraints.rising_pairs_on_execution_bus chip.ChipType chip.chip μ chip.inst_wf entry.1 entry.2 h_entry

  end Execution

  section Memory

    /-- The overall memory bus -/
    def memory_bus (chips : List (WFChip μ))
    :
      List (List FBB × List FBB)
    :=
      List.flatMap (fun chip ↦ chip.inst_wf.memory_bus_entries) chips

    /-- The memory bus is a rising bus -/
    lemma memory_bus_is_rising_bus
      (chips : List (WFChip μ))
    :
      ∀ entry ∈ (memory_bus chips), μ entry.1 < μ entry.2
    := by
      intro entry h_in
      unfold memory_bus at h_in
      apply List.exists_of_mem_flatMap at h_in
      obtain ⟨ chip, h_in, h_entry ⟩ := h_in
      exact @WFConstraints.rising_pairs_on_memory_bus chip.ChipType chip.chip μ chip.inst_wf entry.1 entry.2 h_entry

    /-- The overall memory bus, quotiented on `ptr` -/
    def memory_bus_per_ptr
      (chips : List (WFChip μ))
      (ptr : Fin OpenVM_address_space_size)
    :
      List (List FBB × List FBB)
    :=
      List.filter (fun (a, _) ↦ a[1]! = ptr.val) (memory_bus chips)

    /-- Each memory bus per-pointer is a sub-bus of the memory bus -/
    lemma memory_bus_per_ptr_is_sublist
      (chips : List (WFChip μ))
      (ptr : Fin OpenVM_address_space_size)
    :
      List.Sublist (memory_bus_per_ptr chips ptr) (memory_bus chips)
    := by
      simp [memory_bus_per_ptr]

    /-- Length of memory bus per-pointer is at most the length of the entire memory bus -/
    lemma memory_bus_per_ptr_length
      (chips : List (WFChip μ))
      (ptr : Fin OpenVM_address_space_size)
    :
      (memory_bus_per_ptr chips ptr).length ≤ (memory_bus chips).length
    := by
      apply List.Sublist.length_le
      apply memory_bus_per_ptr_is_sublist

    /-- The memory bus per-pointer is a rising bus -/
    lemma memory_bus_per_ptr_is_rising_bus
      (chips : List (WFChip μ))
      (ptr : Fin OpenVM_address_space_size)
    :
      ∀ entry ∈ (memory_bus_per_ptr chips ptr), μ entry.1 < μ entry.2
    := by
      intro entry h_in; apply (memory_bus_is_rising_bus chips)
      have := memory_bus_per_ptr_is_sublist chips ptr
      grind

  end Memory

  section ConsistencyProofs

    variable
      -- The chips that participate in the execution
      (chips : List (WFChip μ))
      -- The number of overall lookups on the execution and memory buses,
      -- balancing included, does not exceed BabyBear (guaranteed by the verifier)
      (bus_length : 2 * (execution_bus chips).length +
                    2 * (memory_bus chips).length + 2 < BB_prime)

    include bus_length in
    /-- Consistency of the execution bus -/
    theorem execution_bus_consistency
      -- The execution is not empty
      (execution_not_empty : 0 < (execution_bus chips).length)
      -- When the execution is not empty, execution bus is balanced by single balancers, as per the OpenVM codebase
      (balanced_execution_bus : InteractionList.is_balanced ([((1 : FBB), lb)] ++ (rising_bus μ (execution_bus chips) (execution_bus_is_rising_bus chips)) ++ [((-1 : FBB), rb)]))
    :
      -- The execution bus is accessed in a consistent manner
      ∃ xs, (execution_bus chips).Perm (List.zip (lb :: xs) (xs ++ [rb])) ∧
        List.Pairwise (fun x₁ x₂ ↦ μ x₁ < μ x₂) (lb :: xs ++ [rb])
    := by
      apply rising_bus_with_single_balancer_characterisation
              (h_not_empty := execution_not_empty)
              (h_balance := balanced_execution_bus)
      . simp +arith
        rw [rising_bus_length]
        omega

    include bus_length in
    /-- Consistency of the memory bus per-pointer -/
    theorem memory_bus_consistency_per_ptr
      (ptr : Fin OpenVM_address_space_size)
      -- Memory bus per-pointer is either empty or is balanced by single balancers per-pointer, as per the OpenVM codebase
      (balanced_memory_bus_per_ptr :
        memory_bus_per_ptr chips ptr = [] ∨
        (0 < (memory_bus_per_ptr chips ptr).length ∧
          InteractionList.is_balanced ([((1 : FBB), lb)] ++ (rising_bus μ (memory_bus_per_ptr chips ptr) (memory_bus_per_ptr_is_rising_bus chips ptr)) ++ [((-1 : FBB), rb)])))
    :
      -- The memory at `ptr` is either not accessed during the execution
      (memory_bus_per_ptr chips ptr = []) ∨
        -- or is accessed in a consistent manner
        ∃ xs, (memory_bus_per_ptr chips ptr).Perm (List.zip (lb :: xs) (xs ++ [rb])) ∧
          List.Pairwise (fun x₁ x₂ ↦ μ x₁ < μ x₂) (lb :: xs ++ [rb])
    := by
      obtain h_length | ⟨ h_length, balanced_memory_bus_per_ptr ⟩ := balanced_memory_bus_per_ptr
      . aesop
      . right
        apply rising_bus_with_single_balancer_characterisation
                (h_not_empty := h_length)
                (h_balance := balanced_memory_bus_per_ptr)
        . simp +arith at *
          rw [rising_bus_length]
          have h_len := memory_bus_per_ptr_length chips ptr
          omega

  end ConsistencyProofs

  section Chips

    -- The actual measure takes the timestamp from the execution and the memory bus.
    -- This happens to be the last element of the associated data for both of these buses.
    def μ (data : List FBB) : ℕ :=
      match data with
      | [] => 0
      | _ => data.reverse.head!.val

    section Auipc

      open VmAirWrapper_auipc.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_Auipc
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_auipc FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 1] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_auipc_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.rd_aux_cols.prev_data_0 row 0, air.adapter.rd_aux_cols.prev_data_1 row 0, air.adapter.rd_aux_cols.prev_data_2 row 0, air.adapter.rd_aux_cols.prev_data_3 row 0, air.adapter.rd_aux_cols.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, air.core.rd_data_2 row 0, air.core.rd_data_3 row 0, air.adapter.from_state.timestamp row 0] ),
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_auipc_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            simp [h_in_row, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢

            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_wellformedness h_bus_axioms; omega
        }

    end Auipc

    section BaseALU

      open VmAirWrapper_alu.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_Base_ALU
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_alu FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_alu_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0] ),
                    ] ++
                    (if air.adapter.rs2_as row 0 = 1 then
                      [(
                        [1, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1]
                      )] else []
                    ) ++
                    [
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.from_state.timestamp row 0 + 2] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_alu_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end BaseALU

    section BranchEqual

      open VmAirWrapper_branch_eq.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_BranchEqual
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_branch_eq FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.to_pc row 0, air.adapter.from_state.timestamp row 0 + 2] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_branch_eq_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.from_state.timestamp row 0]),
                      ( [1, air.adapter.rs2_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0 + 1] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_branch_eq_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end BranchEqual

    section BranchLessThan

      open VmAirWrapper_branch_lt.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_BranchLessThan
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_branch_lt FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.to_pc row 0, air.adapter.from_state.timestamp row 0 + 2] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_branch_lt_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.from_state.timestamp row 0]),
                      ( [1, air.adapter.rs2_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0 + 1] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_branch_lt_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

      end BranchLessThan

    section DivRem

      open VmAirWrapper_divrem.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_DivRem
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_divrem FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_divrem_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0] ),
                      ( [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1] ),
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.a row 0 0, air.core.a row 0 1, air.core.a row 0 2, air.core.a row 0 3, air.adapter.from_state.timestamp row 0 + 2] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_divrem_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end DivRem

    section JalLui

      open VmAirWrapper_jallui.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_JalLui
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_jallui FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.inner.from_state.pc row 0, air.adapter.inner.from_state.timestamp row 0],
                        [air.to_pc row 0, air.adapter.inner.from_state.timestamp row 0 + 1] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            have h_nw_eq := JalLui.ValidRows.needs_write_eq_is_valid ExtF air row (by omega) (h_constraints row (by omega)) (h_bus_wellformedness row (by omega))
            simp [
              VmAirWrapper_jallui_constraint_and_interaction_simplification,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.adapter.needs_write row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.inner.rd_ptr row 0, air.adapter.inner.rd_aux_cols.prev_data_0 row 0, air.adapter.inner.rd_aux_cols.prev_data_1 row 0, air.adapter.inner.rd_aux_cols.prev_data_2 row 0, air.adapter.inner.rd_aux_cols.prev_data_3 row 0, air.adapter.inner.rd_aux_cols.base.prev_timestamp row 0],
                        [1, air.adapter.inner.rd_ptr row 0, air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, air.core.rd_data_2 row 0, air.core.rd_data_3 row 0, air.adapter.inner.from_state.timestamp row 0] ),
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_eq ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_jallui_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.inner.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.inner.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end JalLui

    section JalR

      open VmAirWrapper_jalr.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_JalR
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_jalr FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.core.to_pc row 0, air.adapter.from_state.timestamp row 0 + 2] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_jalr_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0, air.adapter.rs1_aux_cols.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0, air.adapter.from_state.timestamp row 0] ),
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.rd_aux_cols.prev_data_0 row 0, air.adapter.rd_aux_cols.prev_data_1 row 0, air.adapter.rd_aux_cols.prev_data_2 row 0, air.adapter.rd_aux_cols.prev_data_3 row 0, air.adapter.rd_aux_cols.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 0, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 1, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 2, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 3, air.adapter.from_state.timestamp row 0 + 1] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            have h_nw_eq := JalR.ValidRows.needs_write_eq_is_valid ExtF air row (by omega) h_constraints h_bus_wellformedness
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_jalr_constraint_and_interaction_simplification,
              h_nw_eq,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end JalR

    section LoadSignExtend

      open VmAirWrapper_load_sign_extend.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_LoadSignExtend
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_load_sign_extend FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0, air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0, air.adapter.rs1_aux_cols.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0, air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0, air.adapter.from_state.timestamp row 0] ),
                      ( [air.read_as row 0, air.read_ptr row 0, air.core.read_data row 0 0, air.core.read_data row 0 1, air.core.read_data row 0 2, air.core.read_data row 0 3, air.adapter.read_data_aux.base.prev_timestamp row 0],
                        [air.read_as row 0, air.read_ptr row 0, air.core.read_data row 0 0, air.core.read_data row 0 1, air.core.read_data row 0 2, air.core.read_data row 0 3, air.adapter.from_state.timestamp row 0 + 1] )
                    ] ++
                    (if air.adapter.needs_write row 0 = 1 then
                      [
                        ( [air.write_as row 0, air.write_ptr row 0, air.core.prev_data_0 row 0, air.core.prev_data_1 row 0, air.core.prev_data_2 row 0, air.core.prev_data_3 row 0, air.adapter.write_base_aux.prev_timestamp row 0],
                          [air.write_as row 0, air.write_ptr row 0, air.core.write_data row 0 0, air.core.write_data row 0 1, air.core.write_data row 0 2, air.core.write_data row 0 3, air.adapter.from_state.timestamp row 0 + 2] )
                      ] else []
                    )
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end LoadSignExtend

    section LoadStore

      open VmAirWrapper_loadstore.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_LoadStore
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_loadstore FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.to_pc row 0, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_loadstore_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0, air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0, air.adapter.rs1_aux_cols.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0, air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0, air.adapter.from_state.timestamp row 0] ),
                      ( [air.read_as row 0, air.read_ptr row 0, air.core.read_data_0 row 0, air.core.read_data_1 row 0, air.core.read_data_2 row 0, air.core.read_data_3 row 0, air.adapter.read_data_aux.base.prev_timestamp row 0],
                        [air.read_as row 0, air.read_ptr row 0, air.core.read_data_0 row 0, air.core.read_data_1 row 0, air.core.read_data_2 row 0, air.core.read_data_3 row 0, air.adapter.from_state.timestamp row 0 + 1] )
                    ] ++
                    (if air.adapter.needs_write row 0 = 1 then
                      [
                        ( [air.write_as row 0, air.write_ptr row 0, air.core.prev_data_0 row 0, air.core.prev_data_1 row 0, air.core.prev_data_2 row 0, air.core.prev_data_3 row 0, air.adapter.write_base_aux.prev_timestamp row 0],
                          [air.write_as row 0, air.write_ptr row 0, air.core.write_data_0 row 0, air.core.write_data_1 row 0, air.core.write_data_2 row 0, air.core.write_data_3 row 0, air.adapter.from_state.timestamp row 0 + 2] )
                      ] else []
                    )
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_loadstore_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end LoadStore

    section Lt

      open VmAirWrapper_lt.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_Lt
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_lt FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_lt_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0] ),
                    ] ++
                    (if air.adapter.rs2_as row 0 = 1 then
                      [(
                        [1, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1]
                      )] else []
                    ) ++
                    [
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.cmp_result row 0, 0, 0, 0, air.adapter.from_state.timestamp row 0 + 2] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_lt_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end Lt

    section Mul

      open VmAirWrapper_mul.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_Mul
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_mul FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_mul_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0] ),
                      ( [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1] ),
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.from_state.timestamp row 0 + 2] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_mul_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end Mul

    section Mulh

      open VmAirWrapper_mulh.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_Mulh
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_mulh FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_mulh_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0] ),
                      ( [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1] ),
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.from_state.timestamp row 0 + 2] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_mulh_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end Mulh

    section Shift

      open VmAirWrapper_shift.constraints

      variable
        (ExtF : Type)
        [Field ExtF]

        instance WFC_Shift
          {air}
          (h_constraints : ∀ row (h : row ≤ air.last_row), allHold air row h)
          (h_bus_axioms : ∀ row ≤ air.last_row, axiomsPerRow air row)
          (h_bus_wellformedness : ∀ row ≤ air.last_row, wf_propertiesToAssumePerRow air row)
        : WFConstraints (Valid_VmAirWrapper_shift FBB ExtF) air μ :=
        {
          execution_bus_entries :=
            (List.range (air.last_row + 1)).filterMap
            (fun row ↦
              if air.core.is_valid row 0 = 1 then
                .some ( [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0],
                        [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3] )
              else
                .none)

          rising_pairs_on_execution_bus
          := by
            intro a b h_in; simp at h_in
            obtain ⟨ row, h_row, h_valid, h_eq_a, h_eq_b ⟩ := h_in
            simp [← h_eq_a, ← h_eq_b, μ]
            specialize h_bus_axioms row (by omega)
            obtain ⟨ h_ex, h_mem, rest ⟩ := h_bus_axioms; clear rest
            simp [
              VmAirWrapper_shift_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide
            ] at h_mem
            omega

          memory_bus_entries :=
            (
              (List.range (air.last_row + 1)).filterMap
              (fun row ↦
                if air.core.is_valid row 0 = 1 then
                  .some (
                    [
                      ( [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0],
                        [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.from_state.timestamp row 0] ),
                    ] ++
                    (if air.adapter.rs2_as row 0 = 1 then
                      [(
                        [1, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0],
                        [1, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1]
                      )] else []
                    ) ++
                    [
                      ( [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0],
                        [1, air.adapter.rd_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0, air.adapter.from_state.timestamp row 0 + 2] )
                    ]
                  )
                else
                  .none)
            ).flatten

          memory_bus_entries_wf
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            grind

          rising_pairs_on_memory_bus
          := by
            intro a b h_in
            simp at h_in
            obtain ⟨ row, ⟨ h_row, h_valid ⟩, h_in_row ⟩ := h_in
            specialize h_constraints row (by omega)
            specialize h_bus_axioms row (by omega)
            specialize h_bus_wellformedness row (by omega)
            rw [allHold_simplified_of_allHold] at h_constraints
            obtain ⟨ ci, h_constraints ⟩ := h_constraints; clear ci
            simp [
              VmAirWrapper_shift_constraint_and_interaction_simplification,
              h_valid,
              show ((2013265920 : FBB) = -1) by decide,
              and_assoc
            ] at h_constraints h_bus_wellformedness h_bus_axioms
            obtain h_eq | h_eq | h_eq := h_in_row <;> simp [h_eq, μ] at h_constraints h_bus_axioms h_bus_wellformedness ⊢
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
            . apply BabyBear.lt_via_diff_and_range_check
                      (c := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0)
                      (d := air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0)
                      (h_c := by clear *- h_bus_wellformedness; grind)
                      (h_d := by clear *- h_bus_wellformedness; grind)
                      (h_diff := by clear *- h_constraints; grind)
              . clear *- h_bus_axioms; omega
        }

    end Shift

  end Chips

end Consistency
