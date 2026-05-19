import VmExtensions.Soundness.Keccakf.Composition

set_option autoImplicit false

namespace Keccakf.Soundness

open KeccakfOpAir
open KeccakfOpAir.constraints
open KeccakfOpAir.Views
open KeccakfOpAir.Soundness
open KeccakfOpAir.WFC
open KeccakfPermAir
open KeccakfOp.Spec
open Keccakf.Interface
open Consistency
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-- A disabled KeccakfOp row is inert: it contributes no bus effects. -/
def RowDisabledAndInert (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  is_valid air row = 0 ∧ ∀ entry, entry ∈ busRow air row → entry.1 = 0

/-- An enabled KeccakfOp row matches the pure KeccakfOp specification:
    the decoded postimage equals Keccak-f[1600] applied to the decoded preimage,
    next_pc equals pc + 4, and end_timestamp equals start_timestamp + 51. -/
def RowMatchesPureSpec
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  (outputOfColumns decodeBusState air row).postimage =
    Keccak.keccakF (inputOfColumns decodeBusState air row).preimage ∧
  (outputOfColumns decodeBusState air row).next_pc =
    (inputOfColumns decodeBusState air row).pc + 4 ∧
  (outputOfColumns decodeBusState air row).end_timestamp =
    (inputOfColumns decodeBusState air row).start_timestamp + TIMESTAMP_DELTA

private theorem spec_of_row_match
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h : keccakf_row_matches_spec air row) :
    RowMatchesPureSpec air row := by
  have h_post := congr_arg KeccakfOpOutput.postimage h
  simp only [execute_postimage] at h_post
  exact ⟨h_post, rfl, rfl⟩

/-- Main Keccak-f composition theorem: assuming the global interaction equations
    hold on both AIRs, all row constraints hold on every row, the per-row bus
    axioms and well-formedness assumptions hold, and the cross-AIR bus balances
    hold, every opcode row is either disabled and inert or enabled and matches
    the pure KeccakfOp specification. The theorem also packages the per-row
    assert-side well-formedness obligations needed by callers. -/
theorem keccakf_matches_spec
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_opAllHold : ∀ row (h_row : row ≤ opAir.last_row),
      allHold_simplified opAir row h_row)
    (h_opAxioms : ∀ row, row ≤ opAir.last_row →
      axiomsPerRow opAir row)
    (h_opWfAssume : ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssumePerRow opAir row)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      KeccakfPermAir.constraints.allHold_simplified permAir row)
    (h_bus7_balanced : InteractionList.is_balanced (combinedBus7Trace opAir permAir))
    (h_bus7_length : (combinedBus7Trace opAir permAir).length < BB_prime)
    {chips : List (WFChip μ)} {lb rb : List FBB}
    (h_opAir_chip : wfc_opAir h_opAllHold h_opAxioms h_opWfAssume ∈ chips)
    (h_bus_length : 2 * (execution_bus chips).length +
                    2 * (memory_bus chips).length + 2 < BB_prime)
    (h_exec_balanced : InteractionList.is_balanced
      ([((1 : FBB), lb)] ++
       InteractionList.rising_bus μ (execution_bus chips)
         (execution_bus_is_rising_bus chips) ++
       [((-1 : FBB), rb)])) :
    ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssertPerRow opAir row ∧
      (RowDisabledAndInert opAir row ∨
        (is_valid opAir row = 1 ∧ RowMatchesPureSpec opAir row)) := by
  intro row h_row
  have h_sound := row_soundness opAir row h_row
    (rows_of_allHold_simplified (h_opAllHold row h_row))
    (h_opAxioms row h_row)
    (h_opWfAssume row h_row)
  have h_comp := keccakf_row_soundness opAir permAir h_opAllHold h_opAxioms h_opWfAssume
    h_permAllHold h_bus7_balanced h_bus7_length h_opAir_chip h_bus_length h_exec_balanced row h_row
  refine ⟨h_sound.1, ?_⟩
  rcases h_sound.2 with h_disabled | h_enabled
  · exact Or.inl h_disabled
  · rcases h_comp with h_v0 | h_spec
    · exact absurd (h_enabled.1 ▸ h_v0) one_ne_zero
    · exact Or.inr ⟨h_enabled.1, spec_of_row_match opAir row h_spec⟩

end Keccakf.Soundness
