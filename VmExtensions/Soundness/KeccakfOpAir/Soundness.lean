import VmExtensions.Soundness.KeccakfOpAir.BusFacts
import VmExtensions.Spec.KeccakfOp

set_option linter.all false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace KeccakfOpAir.Soundness

open KeccakfOpAir.constraints

/-!
# KeccakfOpAir Soundness

Main per-row soundness theorem following the pipeline:
  NonValidRows → ValidRows

## Non-valid rows (is_valid = 0):
  All bus entry multiplicities are zero (from multiplicities_zero).

## Valid rows (is_valid = 1):
  Row constraints + bus axioms → RowContract:
  - All 52 row constraints hold (constraint access via contract_constraint)
  - Range check bounds on decomposition limbs (from RangeCheckAssume)
  - Byte bounds on postimage, pointer limb_3 bound (from BitwiseAssume)

## Constraint structure (52 constraints):
- constraint_0: is_valid binary
- constraint_1: rd_aux timestamp decomposition
- constraints 2..51: buf_aux_0..49 timestamp decomposition

All constraints have the form `is_valid * expr = 0`, so when is_valid = 1,
they give `expr = 0`.
-/

variable {ExtF : Type} [Field ExtF]

/-! ## RowContract: per-row contract for enabled rows -/

-- Bundle of all per-row proof ingredients when is_valid = 1.
-- Carries: constraint access, range check bounds, bitwise bounds, timestamp bound.
-- Timestamp ordering is derived separately via rd_timestamp_ordered / buf_timestamp_ordered.
structure RowContract (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop where
  -- is_valid = 1
  hen : is_valid air row = 1
  -- All 52 raw row constraints hold
  hc : List.Forall (·) (row_constraint_list air row)
  -- Bus-derived: range check bounds on decomposition limbs
  rc : RangeCheckAssume air row
  -- Bus-derived: bitwise/byte bounds
  bw : BitwiseAssume air row
  -- Bus-derived: memory read bounds (preimage bytes, pointer bounds)
  mem_rd : MemoryReadAssume air row
  -- Bus-derived: timestamp is less than timestampBound.
  timestamp_lt : (timestamp air row).val < Keccakf.Interface.timestampBound

/-! ## Constraint accessors -/

-- Extract constraint k from RowContract
lemma contract_constraint {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) (k : ℕ) (hk : k < 52) :
    (row_constraint_list air row)[k]'(by rw [rcl_length]; exact hk) :=
  forall_list_get rc.hc (by rw [rcl_length]; exact hk)

/-! ## Timestamp ordering (derived from RowContract + bounds)

The FBB arithmetic helpers (fbb_lt_of_sub_decomp, decomp_sum_lt_p)
are in FieldLemmas.lean.
-/

-- rd register access: prev_ts < timestamp
lemma rd_timestamp_ordered {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row)
    (h_prev_ts : (rd_aux_prev_ts air row).val < 2^29)
    : (rd_aux_prev_ts air row).val < (timestamp air row).val :=
  fbb_lt_of_sub_decomp (sub_eq_zero.mp (rd_aux_timestamp_lt air row rc.hc rc.hen))
    (decomp_sum_lt_p h_prev_ts rc.rc.rd_aux_lo_bound rc.rc.rd_aux_hi_bound)

-- Buffer word k: prev_ts_k < timestamp + (k+1)
set_option maxHeartbeats 6400000 in
lemma buf_timestamp_ordered {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) (k : ℕ) (hk : k < 50)
    (h_prev_ts : (buf_aux_prev_ts air row k).val < 2^29)
    : (buf_aux_prev_ts air row k).val < (timestamp air row + ((k + 1 : ℕ) : FBB)).val := by
  -- Dispatch to individual buf_aux_K_timestamp_lt lemmas via interval_cases
  -- Each case: fbb_lt_of_sub_decomp (decomposition from constraint) (sum bound from range checks)
  interval_cases k
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_0_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 0 (by omega)) (rc.rc.buf_aux_hi_bound 0 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_1_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 1 (by omega)) (rc.rc.buf_aux_hi_bound 1 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_2_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 2 (by omega)) (rc.rc.buf_aux_hi_bound 2 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_3_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 3 (by omega)) (rc.rc.buf_aux_hi_bound 3 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_4_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 4 (by omega)) (rc.rc.buf_aux_hi_bound 4 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_5_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 5 (by omega)) (rc.rc.buf_aux_hi_bound 5 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_6_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 6 (by omega)) (rc.rc.buf_aux_hi_bound 6 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_7_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 7 (by omega)) (rc.rc.buf_aux_hi_bound 7 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_8_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 8 (by omega)) (rc.rc.buf_aux_hi_bound 8 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_9_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 9 (by omega)) (rc.rc.buf_aux_hi_bound 9 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_10_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 10 (by omega)) (rc.rc.buf_aux_hi_bound 10 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_11_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 11 (by omega)) (rc.rc.buf_aux_hi_bound 11 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_12_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 12 (by omega)) (rc.rc.buf_aux_hi_bound 12 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_13_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 13 (by omega)) (rc.rc.buf_aux_hi_bound 13 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_14_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 14 (by omega)) (rc.rc.buf_aux_hi_bound 14 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_15_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 15 (by omega)) (rc.rc.buf_aux_hi_bound 15 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_16_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 16 (by omega)) (rc.rc.buf_aux_hi_bound 16 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_17_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 17 (by omega)) (rc.rc.buf_aux_hi_bound 17 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_18_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 18 (by omega)) (rc.rc.buf_aux_hi_bound 18 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_19_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 19 (by omega)) (rc.rc.buf_aux_hi_bound 19 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_20_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 20 (by omega)) (rc.rc.buf_aux_hi_bound 20 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_21_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 21 (by omega)) (rc.rc.buf_aux_hi_bound 21 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_22_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 22 (by omega)) (rc.rc.buf_aux_hi_bound 22 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_23_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 23 (by omega)) (rc.rc.buf_aux_hi_bound 23 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_24_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 24 (by omega)) (rc.rc.buf_aux_hi_bound 24 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_25_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 25 (by omega)) (rc.rc.buf_aux_hi_bound 25 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_26_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 26 (by omega)) (rc.rc.buf_aux_hi_bound 26 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_27_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 27 (by omega)) (rc.rc.buf_aux_hi_bound 27 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_28_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 28 (by omega)) (rc.rc.buf_aux_hi_bound 28 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_29_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 29 (by omega)) (rc.rc.buf_aux_hi_bound 29 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_30_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 30 (by omega)) (rc.rc.buf_aux_hi_bound 30 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_31_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 31 (by omega)) (rc.rc.buf_aux_hi_bound 31 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_32_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 32 (by omega)) (rc.rc.buf_aux_hi_bound 32 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_33_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 33 (by omega)) (rc.rc.buf_aux_hi_bound 33 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_34_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 34 (by omega)) (rc.rc.buf_aux_hi_bound 34 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_35_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 35 (by omega)) (rc.rc.buf_aux_hi_bound 35 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_36_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 36 (by omega)) (rc.rc.buf_aux_hi_bound 36 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_37_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 37 (by omega)) (rc.rc.buf_aux_hi_bound 37 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_38_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 38 (by omega)) (rc.rc.buf_aux_hi_bound 38 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_39_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 39 (by omega)) (rc.rc.buf_aux_hi_bound 39 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_40_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 40 (by omega)) (rc.rc.buf_aux_hi_bound 40 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_41_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 41 (by omega)) (rc.rc.buf_aux_hi_bound 41 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_42_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 42 (by omega)) (rc.rc.buf_aux_hi_bound 42 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_43_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 43 (by omega)) (rc.rc.buf_aux_hi_bound 43 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_44_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 44 (by omega)) (rc.rc.buf_aux_hi_bound 44 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_45_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 45 (by omega)) (rc.rc.buf_aux_hi_bound 45 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_46_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 46 (by omega)) (rc.rc.buf_aux_hi_bound 46 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_47_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 47 (by omega)) (rc.rc.buf_aux_hi_bound 47 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_48_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 48 (by omega)) (rc.rc.buf_aux_hi_bound 48 (by omega)))
  · exact fbb_lt_of_sub_decomp (sub_eq_zero.mp (buf_aux_49_timestamp_lt air row rc.hc rc.hen))
      (decomp_sum_lt_p h_prev_ts (rc.rc.buf_aux_lo_bound 49 (by omega)) (rc.rc.buf_aux_hi_bound 49 (by omega)))

/-! ## Main soundness theorem -/

-- Per-row soundness: the row is either disabled (all bus multiplicities zero)
-- or satisfies the full RowContract.
-- Returns wf_propertiesToAssertPerRow in both cases.
theorem row_soundness (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (hc : List.Forall (·) (row_constraint_list air row))
    (h_axioms : axiomsPerRow air row)
    (h_wf_assume : wf_propertiesToAssumePerRow air row)
    : wf_propertiesToAssertPerRow air row
    ∧ ((is_valid air row = 0 ∧ ∀ entry ∈ busRow air row, entry.1 = 0)
    ∨ (is_valid air row = 1 ∧ RowContract air row)) := by
  rcases is_valid_binary air row hc with hen | hen
  · exact ⟨wf_assert_disabled air row hen,
           Or.inl ⟨hen, multiplicities_zero air row hen⟩⟩
  · let h_rc := range_check_assume air row h_wf_assume hen
    let h_bw := bitwise_assume air row h_wf_assume hen
    let h_mem := memory_read_assume air row h_wf_assume hen
    let h_ts := timestamp_bound air row h_axioms hen
    exact ⟨wf_assert_enabled air row hen h_mem h_bw,
           Or.inr ⟨hen, ⟨hen, hc, h_rc, h_bw, h_mem, h_ts⟩⟩⟩

/-! ## Convenience accessors from RowContract -/

-- Postimage byte bound
lemma postimage_byte_lt {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) (k : ℕ) (hk : k < 200) :
    ∃ n : ℕ, postimage air row k = ↑n ∧ n < 256 :=
  rc.bw.postimage_byte_bound k hk

-- Buffer pointer limb_3 bound (ensures buffer_ptr < 2^32)
lemma ptr_limb3_lt {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) :
    ∃ n : ℕ, buffer_ptr_limb_3 air row = ↑n ∧ n < 32 :=
  rc.bw.ptr_limb3_bound

-- Range check: rd_aux decomposition limbs bounded
lemma rd_decomp_lo_bound {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) :
    ∃ n : ℕ, rd_aux_lower_decomp_0 air row = ↑n ∧ n < 2^17 :=
  rc.rc.rd_aux_lo_bound

lemma rd_decomp_hi_bound {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) :
    ∃ n : ℕ, rd_aux_lower_decomp_1 air row = ↑n ∧ n < 2^12 :=
  rc.rc.rd_aux_hi_bound

-- Range check: buf_aux decomposition limbs bounded (parametric)
lemma buf_decomp_lo_bound {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) (k : ℕ) (hk : k < 50) :
    ∃ n : ℕ, buf_aux_lower_decomp_0 air row k = ↑n ∧ n < 2^17 :=
  rc.rc.buf_aux_lo_bound k hk

lemma buf_decomp_hi_bound {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) (k : ℕ) (hk : k < 50) :
    ∃ n : ℕ, buf_aux_lower_decomp_1 air row k = ↑n ∧ n < 2^12 :=
  rc.rc.buf_aux_hi_bound k hk

-- rd timestamp decomposition (field equation)
lemma rd_timestamp_decomp {air : Valid_KeccakfOpAir FBB ExtF} {row : ℕ}
    (rc : RowContract air row) :
    timestamp air row - rd_aux_prev_ts air row - 1 -
      (rd_aux_lower_decomp_0 air row + rd_aux_lower_decomp_1 air row * 131072) = 0 :=
  rd_aux_timestamp_lt air row rc.hc rc.hen

end KeccakfOpAir.Soundness
