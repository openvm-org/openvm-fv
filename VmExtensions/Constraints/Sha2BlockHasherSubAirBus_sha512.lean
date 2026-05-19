/-
  Bus interaction definitions for Sha2BlockHasherSubAir (SHA-512).

  Defines per-bus row functions and typed versions for the two SubAir buses:

  1. **Bitwise Lookup Bus** — range checks on carry values (round rows) and
     final-hash bytes (digest rows).
  2. **Private Bus** (PermutationCheckBus) — block-chaining send/receive
     relating consecutive blocks' hashes.

  This file formalizes the bitwise bus with `axioms/assume/assert`, while the
  private bus is represented directly in raw `(F × List F)` form.

  The SHA-512 proof boundary derives and uses the supported-row theorem
  `privateBusChainingSupported` from raw permutation semantics plus uniqueness
  facts.
-/
import VmExtensions.Extraction.Sha2BlockHasherVmAir_sha512
import VmExtensions.Constraints.Sha2BlockHasherVmAir_sha512
import VmExtensions.Constraints.Sha2WrapperBusEntries_sha512
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2BlockHasherVmAir_sha512.constraints

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

abbrev Sha2BitwiseBus : ℕ := 6
abbrev Sha2WrapperBus : ℕ := 8
abbrev Sha2PrivateBus : ℕ := 9

/-! ## Helper: 16-bit limb composition from bit columns

Composes 16 consecutive bits from `work_vars_a` or `work_vars_e` into a
single field element in little-endian order.
-/

section bus_helpers

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Compose bits `[slot][limb_offset .. limb_offset+15]` of `work_vars_a` into a u16 field element. -/
noncomputable def compose_a_u16 (c : C F ExtF) (slot limb : ℕ) (row : ℕ) : F :=
  (Finset.range 16).sum (fun b => work_vars_a c slot (limb * 16 + b) row * ((2 : F) ^ b))

/-- Compose bits `[slot][limb_offset .. limb_offset+15]` of `work_vars_e` into a u16 field element. -/
noncomputable def compose_e_u16 (c : C F ExtF) (slot limb : ℕ) (row : ℕ) : F :=
  (Finset.range 16).sum (fun b => work_vars_e c slot (limb * 16 + b) row * ((2 : F) ^ b))

end bus_helpers

/-! ## Bus 1: Bitwise Lookup Bus (range checks)

On **round rows**, the AIR sends `(carry_a[i][j], carry_e[i][j], 0, 0)` as a range
lookup for each slot `i` ∈ {0,1,2,3} and limb `j` ∈ {0,1,2,3}. (16 entries per row.)

On the **row before a digest row**, the AIR sends
`(next_final_hash[word][2k], next_final_hash[word][2k+1], 0, 0)` for each
word `i` ∈ {0..7} and pair `k` ∈ {0,1,2,3}. (32 entries per row.)

In both cases the bus entry format is `(multiplicity, [a, b, c, op])` where
`c = 0` and `op = 0`, matching `send_range(x, y)` which calls
`push(x, y, 0, 0, is_lookup=true)`.
-/

section bitwise_bus

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Carry range-check entry for slot `i`, limb `j` on a round row. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def bitwiseBus_carry_entry (c : C F ExtF) (i j : ℕ) (row : ℕ) : F × List F :=
  (is_round_row c row, [carry_a c i j row, carry_e c i j row, 0, 0])

/-- Digest byte range-check entry for word `i`, pair `k` on the row before a digest row.
    The payload uses next-row columns (rotation = 1). -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def bitwiseBus_digest_entry (c : C F ExtF) (word pair : ℕ) (row : ℕ) : F × List F :=
  (next_is_digest_row c row,
   [next_final_hash c word (2 * pair) row,
    next_final_hash c word (2 * pair + 1) row,
    0, 0])

/-- All bitwise lookup bus entries at a given row.
    Round rows contribute 16 carry entries.
    Pre-digest rows contribute 32 digest byte entries. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def bitwiseBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  -- Carry range checks: 4 slots × 4 limbs = 16 entries (gated by is_round_row)
  ((List.range 4).flatMap fun i =>
    (List.range 4).map fun j =>
      bitwiseBus_carry_entry c i j row)
  ++
  -- Digest byte range checks: 8 words × 4 pairs = 32 entries (gated by next_is_digest_row)
  ((List.range 8).flatMap fun word =>
    (List.range 4).map fun pair =>
      bitwiseBus_digest_entry c word pair row)

end bitwise_bus

section bitwise_bus_trace

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- The flattened extracted bitwise-bus trace: all per-row bitwise entries on
    the SHA-512 extracted bitwise bus. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def bitwiseBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (bitwiseBus_row c)

/-- The extracted `constrain_interactions` map agrees with the hand-written
    SHA bitwise-bus model at `Sha2BitwiseBus`. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma bitwiseBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2BitwiseBus = bitwiseBus_trace c := by
  sorry
end bitwise_bus_trace

/-! ## Bus 2: Private Bus (block chaining via PermutationCheckBus)

On **digest rows**, the AIR sends and receives one message each:

- **Send**: `(+is_digest_row, [composed_hash[0..31], next_gbi])`
  where `composed_hash` is the 8 hash words decomposed into 32 u16 limbs
  (from `hash.a` / `hash.e` bits), and `next_gbi` wraps to 1 on the last block.

- **Receive**: `(-is_digest_row, [prev_hash[0..31], global_block_idx])`
  where `prev_hash` holds 8 words × 4 u16 limbs.

The SHA-512 proof derives and uses the supported-row theorem
`privateBusChainingSupported` from raw permutation semantics plus sender-key
uniqueness. The private bus is represented with raw entries rather than per-row
typed `BusEntry` properties.
-/

section private_bus

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Composed hash u16 limb for private bus send.
    For word `i`: if `i < 4`, uses `work_vars_a[3-i]`; if `i ≥ 4`, uses `work_vars_e[7-i]`.
    Limb `j` ∈ {0,1,2,3} selects one of the four 16-bit limbs. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def composed_hash_u16 (c : C F ExtF) (word limb : ℕ) (row : ℕ) : F :=
  if word < 4 then
    compose_a_u16 c (3 - word) limb row
  else
    compose_e_u16 c (7 - word) limb row

/-- Next global block index for the private bus send.
    On the last block (next row is padding), wraps to 1; otherwise increments. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def private_bus_next_gbi (c : C F ExtF) (row : ℕ) : F :=
  next_padding_flag c row + (1 - next_padding_flag c row) * (global_block_idx c row + 1)

/-- Private bus send data: 32 composed-hash u16 limbs followed by next-global-block-index. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def privateBus_send_data (c : C F ExtF) (row : ℕ) : List F :=
  ((List.range 8).flatMap fun word =>
    (List.range 4).map fun limb =>
      composed_hash_u16 c word limb row)
  ++ [private_bus_next_gbi c row]

/-- Private bus receive data: 32 prev-hash u16 limbs followed by `global_block_idx`. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def privateBus_recv_data (c : C F ExtF) (row : ℕ) : List F :=
  ((List.range 8).flatMap fun word =>
    (List.range 4).map fun limb =>
      prev_hash c word limb row)
  ++ [global_block_idx c row]

/-- Private bus send entry (positive multiplicity). -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def privateBus_send_entry (c : C F ExtF) (row : ℕ) : F × List F :=
  (is_digest_row c row, privateBus_send_data c row)

/-- Private bus receive entry (negative multiplicity). -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def privateBus_recv_entry (c : C F ExtF) (row : ℕ) : F × List F :=
  (-(is_digest_row c row), privateBus_recv_data c row)

/-- All private bus entries at a given row: one send + one receive. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def privateBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [privateBus_send_entry c row, privateBus_recv_entry c row]

end private_bus

section private_bus_trace

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

private theorem range_loop_four : List.range.loop 4 [] = [0, 1, 2, 3] := by
  decide

private theorem range_loop_eight : List.range.loop 8 [] = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

/-- The flattened extracted private-bus trace: all per-row private-bus entries on
    `Sha2PrivateBus`. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def privateBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (privateBus_row c)

/-- The extracted `constrain_interactions` map agrees with the hand-written
    SHA private-bus model at `Sha2PrivateBus`. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma privateBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2PrivateBus = privateBus_trace c := by
  sorry
end private_bus_trace

section wrapper_bus

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Wrapper-bus state entry emitted on digest rows. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def wrapperStateEntry (c : C F ExtF) (row : ℕ)
    : Sha2WrapperBus512StateEntry F where
  multiplicity := -(is_digest_row c row)
  message_type := 0
  request_id := request_id c row
  prev_state_u16 := #v[
    prev_hash c 0 0 row, prev_hash c 0 1 row, prev_hash c 0 2 row, prev_hash c 0 3 row,
    prev_hash c 1 0 row, prev_hash c 1 1 row, prev_hash c 1 2 row, prev_hash c 1 3 row,
    prev_hash c 2 0 row, prev_hash c 2 1 row, prev_hash c 2 2 row, prev_hash c 2 3 row,
    prev_hash c 3 0 row, prev_hash c 3 1 row, prev_hash c 3 2 row, prev_hash c 3 3 row,
    prev_hash c 4 0 row, prev_hash c 4 1 row, prev_hash c 4 2 row, prev_hash c 4 3 row,
    prev_hash c 5 0 row, prev_hash c 5 1 row, prev_hash c 5 2 row, prev_hash c 5 3 row,
    prev_hash c 6 0 row, prev_hash c 6 1 row, prev_hash c 6 2 row, prev_hash c 6 3 row,
    prev_hash c 7 0 row, prev_hash c 7 1 row, prev_hash c 7 2 row, prev_hash c 7 3 row]
  new_state_bytes := #v[
    final_hash c 0 0 row, final_hash c 0 1 row, final_hash c 0 2 row, final_hash c 0 3 row,
    final_hash c 0 4 row, final_hash c 0 5 row, final_hash c 0 6 row, final_hash c 0 7 row,
    final_hash c 1 0 row, final_hash c 1 1 row, final_hash c 1 2 row, final_hash c 1 3 row,
    final_hash c 1 4 row, final_hash c 1 5 row, final_hash c 1 6 row, final_hash c 1 7 row,
    final_hash c 2 0 row, final_hash c 2 1 row, final_hash c 2 2 row, final_hash c 2 3 row,
    final_hash c 2 4 row, final_hash c 2 5 row, final_hash c 2 6 row, final_hash c 2 7 row,
    final_hash c 3 0 row, final_hash c 3 1 row, final_hash c 3 2 row, final_hash c 3 3 row,
    final_hash c 3 4 row, final_hash c 3 5 row, final_hash c 3 6 row, final_hash c 3 7 row,
    final_hash c 4 0 row, final_hash c 4 1 row, final_hash c 4 2 row, final_hash c 4 3 row,
    final_hash c 4 4 row, final_hash c 4 5 row, final_hash c 4 6 row, final_hash c 4 7 row,
    final_hash c 5 0 row, final_hash c 5 1 row, final_hash c 5 2 row, final_hash c 5 3 row,
    final_hash c 5 4 row, final_hash c 5 5 row, final_hash c 5 6 row, final_hash c 5 7 row,
    final_hash c 6 0 row, final_hash c 6 1 row, final_hash c 6 2 row, final_hash c 6 3 row,
    final_hash c 6 4 row, final_hash c 6 5 row, final_hash c 6 6 row, final_hash c 6 7 row,
    final_hash c 7 0 row, final_hash c 7 1 row, final_hash c 7 2 row, final_hash c 7 3 row,
    final_hash c 7 4 row, final_hash c 7 5 row, final_hash c 7 6 row, final_hash c 7 7 row]

/-- First 32-byte message wrapper entry, enabled on selector-0 active rows. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def wrapperMsg1Entry (c : C F ExtF) (row : ℕ)
    : Sha2WrapperBus512Msg1Entry F where
  multiplicity :=
    -(wrapperBus_padding_choose2 c row * (is_round_row c row + is_digest_row c row))
  message_type := 1
  request_id := request_id c row
  local_msg_bytes := #v[
    compose_schedule_byte c 0 0 row, compose_schedule_byte c 0 1 row,
    compose_schedule_byte c 0 2 row, compose_schedule_byte c 0 3 row,
    compose_schedule_byte c 0 4 row, compose_schedule_byte c 0 5 row,
    compose_schedule_byte c 0 6 row, compose_schedule_byte c 0 7 row,
    compose_schedule_byte c 1 0 row, compose_schedule_byte c 1 1 row,
    compose_schedule_byte c 1 2 row, compose_schedule_byte c 1 3 row,
    compose_schedule_byte c 1 4 row, compose_schedule_byte c 1 5 row,
    compose_schedule_byte c 1 6 row, compose_schedule_byte c 1 7 row,
    compose_schedule_byte c 2 0 row, compose_schedule_byte c 2 1 row,
    compose_schedule_byte c 2 2 row, compose_schedule_byte c 2 3 row,
    compose_schedule_byte c 2 4 row, compose_schedule_byte c 2 5 row,
    compose_schedule_byte c 2 6 row, compose_schedule_byte c 2 7 row,
    compose_schedule_byte c 3 0 row, compose_schedule_byte c 3 1 row,
    compose_schedule_byte c 3 2 row, compose_schedule_byte c 3 3 row,
    compose_schedule_byte c 3 4 row, compose_schedule_byte c 3 5 row,
    compose_schedule_byte c 3 6 row, compose_schedule_byte c 3 7 row]
  next_msg_bytes := #v[
    compose_next_schedule_byte c 0 0 row, compose_next_schedule_byte c 0 1 row,
    compose_next_schedule_byte c 0 2 row, compose_next_schedule_byte c 0 3 row,
    compose_next_schedule_byte c 0 4 row, compose_next_schedule_byte c 0 5 row,
    compose_next_schedule_byte c 0 6 row, compose_next_schedule_byte c 0 7 row,
    compose_next_schedule_byte c 1 0 row, compose_next_schedule_byte c 1 1 row,
    compose_next_schedule_byte c 1 2 row, compose_next_schedule_byte c 1 3 row,
    compose_next_schedule_byte c 1 4 row, compose_next_schedule_byte c 1 5 row,
    compose_next_schedule_byte c 1 6 row, compose_next_schedule_byte c 1 7 row,
    compose_next_schedule_byte c 2 0 row, compose_next_schedule_byte c 2 1 row,
    compose_next_schedule_byte c 2 2 row, compose_next_schedule_byte c 2 3 row,
    compose_next_schedule_byte c 2 4 row, compose_next_schedule_byte c 2 5 row,
    compose_next_schedule_byte c 2 6 row, compose_next_schedule_byte c 2 7 row,
    compose_next_schedule_byte c 3 0 row, compose_next_schedule_byte c 3 1 row,
    compose_next_schedule_byte c 3 2 row, compose_next_schedule_byte c 3 3 row,
    compose_next_schedule_byte c 3 4 row, compose_next_schedule_byte c 3 5 row,
    compose_next_schedule_byte c 3 6 row, compose_next_schedule_byte c 3 7 row]

/-- Second 32-byte message wrapper entry, enabled on selector-2 active rows. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def wrapperMsg2Entry (c : C F ExtF) (row : ℕ)
    : Sha2WrapperBus512Msg2Entry F where
  multiplicity :=
    -(wrapperBus_choose2 (encoder_idx c 5 row) * (is_round_row c row + is_digest_row c row))
  message_type := 2
  request_id := request_id c row
  local_msg_bytes := #v[
    compose_schedule_byte c 0 0 row, compose_schedule_byte c 0 1 row,
    compose_schedule_byte c 0 2 row, compose_schedule_byte c 0 3 row,
    compose_schedule_byte c 0 4 row, compose_schedule_byte c 0 5 row,
    compose_schedule_byte c 0 6 row, compose_schedule_byte c 0 7 row,
    compose_schedule_byte c 1 0 row, compose_schedule_byte c 1 1 row,
    compose_schedule_byte c 1 2 row, compose_schedule_byte c 1 3 row,
    compose_schedule_byte c 1 4 row, compose_schedule_byte c 1 5 row,
    compose_schedule_byte c 1 6 row, compose_schedule_byte c 1 7 row,
    compose_schedule_byte c 2 0 row, compose_schedule_byte c 2 1 row,
    compose_schedule_byte c 2 2 row, compose_schedule_byte c 2 3 row,
    compose_schedule_byte c 2 4 row, compose_schedule_byte c 2 5 row,
    compose_schedule_byte c 2 6 row, compose_schedule_byte c 2 7 row,
    compose_schedule_byte c 3 0 row, compose_schedule_byte c 3 1 row,
    compose_schedule_byte c 3 2 row, compose_schedule_byte c 3 3 row,
    compose_schedule_byte c 3 4 row, compose_schedule_byte c 3 5 row,
    compose_schedule_byte c 3 6 row, compose_schedule_byte c 3 7 row]
  next_msg_bytes := #v[
    compose_next_schedule_byte c 0 0 row, compose_next_schedule_byte c 0 1 row,
    compose_next_schedule_byte c 0 2 row, compose_next_schedule_byte c 0 3 row,
    compose_next_schedule_byte c 0 4 row, compose_next_schedule_byte c 0 5 row,
    compose_next_schedule_byte c 0 6 row, compose_next_schedule_byte c 0 7 row,
    compose_next_schedule_byte c 1 0 row, compose_next_schedule_byte c 1 1 row,
    compose_next_schedule_byte c 1 2 row, compose_next_schedule_byte c 1 3 row,
    compose_next_schedule_byte c 1 4 row, compose_next_schedule_byte c 1 5 row,
    compose_next_schedule_byte c 1 6 row, compose_next_schedule_byte c 1 7 row,
    compose_next_schedule_byte c 2 0 row, compose_next_schedule_byte c 2 1 row,
    compose_next_schedule_byte c 2 2 row, compose_next_schedule_byte c 2 3 row,
    compose_next_schedule_byte c 2 4 row, compose_next_schedule_byte c 2 5 row,
    compose_next_schedule_byte c 2 6 row, compose_next_schedule_byte c 2 7 row,
    compose_next_schedule_byte c 3 0 row, compose_next_schedule_byte c 3 1 row,
    compose_next_schedule_byte c 3 2 row, compose_next_schedule_byte c 3 3 row,
    compose_next_schedule_byte c 3 4 row, compose_next_schedule_byte c 3 5 row,
    compose_next_schedule_byte c 3 6 row, compose_next_schedule_byte c 3 7 row]

/-- All wrapper-bus entries emitted at a row. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def wrapperBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [(wrapperStateEntry c row).toRaw,
    (wrapperMsg1Entry c row).toRaw,
    (wrapperMsg2Entry c row).toRaw]

end wrapper_bus

section all_interactions

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- The flattened wrapper-bus trace. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
noncomputable def wrapperBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (wrapperBus_row c)

/-- The wrapper-bus entries selected by the extraction agree with `wrapperBus_trace`. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma wrapperBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2WrapperBus = wrapperBus_trace c := by
  sorry

/-- A SHA-side interaction map aligned with the extracted SHA-512 bus numbering:
    bitwise lookup at `Sha2BitwiseBus`, wrapper communication at `Sha2WrapperBus`,
    and private chaining at `Sha2PrivateBus`. -/
@[Sha2BlockHasherVmAir_Sha512Config_constraint_and_interaction_simplification]
def constrain_interactions (c : C F ExtF) : Prop :=
  Circuit.buses c = fun index =>
    if index = Sha2BitwiseBus then bitwiseBus_trace c
    else if index = Sha2WrapperBus then wrapperBus_trace c
    else if index = Sha2PrivateBus then privateBus_trace c
    else []

/-- The extraction interaction map implies the reindexed SHA-side map. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma constrain_interactions_of_extraction
    (c : C F ExtF)
    (h : Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_interactions c) :
    constrain_interactions c := by
  sorry

/-- The bitwise-bus projection of `constrain_interactions`. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma bitwiseBus_trace_of_constraints
    (c : C F ExtF)
    (h : constrain_interactions c) :
    Circuit.buses c Sha2BitwiseBus = bitwiseBus_trace c := by
  unfold constrain_interactions at h
  have hbitwise := congrArg (fun buses => buses Sha2BitwiseBus) h
  simp [Sha2BitwiseBus] at hbitwise
  exact hbitwise

/-- The private-bus projection of `constrain_interactions`. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma privateBus_trace_of_constraints
    (c : C F ExtF)
    (h : constrain_interactions c) :
    Circuit.buses c Sha2PrivateBus = privateBus_trace c := by
  unfold constrain_interactions at h
  have hprivate := congrArg (fun buses => buses Sha2PrivateBus) h
  simp [Sha2BitwiseBus, Sha2WrapperBus, Sha2PrivateBus] at hprivate
  exact hprivate

/-- The wrapper-bus projection of `constrain_interactions`. -/
@[Sha2BlockHasherVmAir_Sha512Config_air_simplification]
lemma wrapperBus_trace_of_constraints
    (c : C F ExtF)
    (h : constrain_interactions c) :
    Circuit.buses c Sha2WrapperBus = wrapperBus_trace c := by
  unfold constrain_interactions at h
  have hwrapper := congrArg (fun buses => buses Sha2WrapperBus) h
  simp [Sha2BitwiseBus, Sha2WrapperBus] at hwrapper
  exact hwrapper

end all_interactions

/-! ## Typed Bus Entries

Convert raw bitwise bus entries to typed `BitwiseBusEntry` structures,
enabling access to `axioms`, `wf_properties`, `wf_assume_cond`, `wf_assert_cond`.
-/

section typed_bitwise

variable {ExtF : Type} [Field ExtF]

/-- Typed bitwise bus entry for carry range check at slot `i`, limb `j`. -/
noncomputable def bitwiseCarryBusEntry {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (i j : ℕ) (row : ℕ) : Interaction.BitwiseBusEntry FBB where
  multiplicity := is_round_row c row
  a := carry_a c i j row
  b := carry_e c i j row
  c := 0
  op := 0

/-- Typed bitwise bus entry for digest byte range check at word `w`, pair `k`,
    using next-row columns. -/
noncomputable def bitwiseDigestBusEntry {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (word pair : ℕ) (row : ℕ) : Interaction.BitwiseBusEntry FBB where
  multiplicity := next_is_digest_row c row
  a := next_final_hash c word (2 * pair) row
  b := next_final_hash c word (2 * pair + 1) row
  c := 0
  op := 0

/-- All typed bitwise bus entries at a row. -/
noncomputable def _bitwiseBus_row {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ) : List (Interaction.BitwiseBusEntry FBB) :=
  -- Carry entries: 4 slots × 4 limbs
  ((List.range 4).flatMap fun i =>
    (List.range 4).map fun j =>
      bitwiseCarryBusEntry c i j row)
  ++
  -- Digest byte entries: 8 words × 4 pairs
  ((List.range 8).flatMap fun word =>
    (List.range 4).map fun pair =>
      bitwiseDigestBusEntry c word pair row)

end typed_bitwise

/-! ## Aggregated Bitwise-Bus Axioms and Well-Formedness Properties

Following the XorinVmAirBus pattern, we define per-row predicates for
axioms, assumed properties, and asserted properties for the bitwise lookup bus.
-/

section aggregated

/-- Axioms on bus entries hold for all bitwise entries at a row. -/
def axioms {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.axioms FBB))

/-- Well-formedness properties that may be assumed (lookup side). -/
def propertiesToAssume {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.assume FBB))

/-- Well-formedness properties that must be asserted (table side). -/
def propertiesToAssert {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.assert FBB))

variable {ExtF : Type} [Field ExtF]

/-- All bitwise-bus axioms hold at a given row. -/
noncomputable def axiomsPerRow {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ) : Prop :=
  axioms (_bitwiseBus_row c row)

/-- All well-formedness properties that can be assumed hold at a given row.
    For the bitwise bus, `wf_assume_cond` is `multiplicity = 1`, so when
    `is_round_row = 1` or `next_is_digest_row = 1`, we may assume
    `a.val < 256 ∧ b.val < 256`. -/
noncomputable def bitwise_lookup_send_properties {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ) : Prop :=
  propertiesToAssume (_bitwiseBus_row c row)

/-- All well-formedness properties that must be asserted hold at a given row. -/
noncomputable def wf_propertiesToAssertPerRow {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ) : Prop :=
  propertiesToAssert (_bitwiseBus_row c row)

end aggregated

/-! ## Bridge: Bus-Level Well-Formedness → Per-Row Properties

Convert a global hypothesis on `Circuit.buses c Sha2BitwiseBus` into the
per-row `bitwise_lookup_send_properties` predicate, for rows within the trace.
-/

section bus_bridge

variable {ExtF : Type} [Field ExtF]

private lemma list_forall_id_map_of_forall_mem {α : Type} {f : α → Prop} {l : List α}
    (h : ∀ e ∈ l, f e) : List.Forall id (l.map f) := by
  induction l with
  | nil => trivial
  | cons a t ih =>
    rw [List.map_cons, List.forall_cons]
    exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun e he => h e (List.mem_cons.mpr (Or.inr he)))⟩

private lemma serialize_typed_eq_raw {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ) :
    (_bitwiseBus_row c row).map
      (fun e : Interaction.BitwiseBusEntry FBB =>
        (e.multiplicity, [e.a, e.b, e.c, e.op])) =
    bitwiseBus_row c row := by
  simp only [_bitwiseBus_row, bitwiseBus_row,
    bitwiseCarryBusEntry, bitwiseDigestBusEntry,
    bitwiseBus_carry_entry, bitwiseBus_digest_entry,
    List.map_append, List.map_flatMap, List.map_map, Function.comp_def]

private lemma typed_entry_zero_fields {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ) (e : Interaction.BitwiseBusEntry FBB)
    (he : e ∈ _bitwiseBus_row c row) : e.c = 0 ∧ e.op = 0 := by
  simp only [_bitwiseBus_row, bitwiseCarryBusEntry, bitwiseDigestBusEntry] at he
  rcases List.mem_append.mp he with hmem | hmem
  · rcases List.mem_flatMap.mp hmem with ⟨_, _, hi⟩
    rcases List.mem_map.mp hi with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl⟩
  · rcases List.mem_flatMap.mp hmem with ⟨_, _, hw⟩
    rcases List.mem_map.mp hw with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Per-row bitwise well-formedness from raw bus-row membership. -/
noncomputable def bitwise_lookup_send_properties_of_raw_wf
    {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ)
    (hwf : ∀ mult a b c_val op,
      (mult, [a, b, c_val, op]) ∈ bitwiseBus_row c row →
      mult = 1 → a.val < 256 ∧ b.val < 256) :
    bitwise_lookup_send_properties c row := by
  unfold bitwise_lookup_send_properties propertiesToAssume
  apply list_forall_id_map_of_forall_mem
  intro e he
  intro hmult
  have ⟨hc_zero, hop_zero⟩ := typed_entry_zero_fields c row e he
  have hraw : (e.multiplicity, [e.a, e.b, e.c, e.op]) ∈ bitwiseBus_row c row := by
    rw [← serialize_typed_eq_raw c row]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hrange := hwf e.multiplicity e.a e.b e.c e.op hraw hmult
  simp only [Interaction.BitwiseBusEntryInstance]
  exact ⟨hrange.1, hrange.2, Or.inl hop_zero,
         by simp [hc_zero, hop_zero]⟩

/-- Bridge: bus-level well-formedness implies per-row `bitwise_lookup_send_properties`
    for any row within the trace. -/
noncomputable def bitwise_lookup_send_properties_of_bus_wf
    {C : Type → Type → Type} [Circuit FBB ExtF C]
    (c : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row c)
    (hci : constrain_interactions c)
    (hwf : ∀ mult a b c_val op,
      (mult, [a, b, c_val, op]) ∈ Circuit.buses c Sha2BitwiseBus →
      mult = 1 → a.val < 256 ∧ b.val < 256) :
    bitwise_lookup_send_properties c row := by
  apply bitwise_lookup_send_properties_of_raw_wf
  intro mult a b c_val op hmem hmult
  apply hwf mult a b c_val op _ hmult
  rw [bitwiseBus_trace_of_constraints c hci]
  exact List.mem_flatMap.mpr
    ⟨row, List.mem_range.mpr (by omega), hmem⟩

end bus_bridge

end Sha2BlockHasherVmAir_sha512.constraints
