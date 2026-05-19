/-
  Layer D: Digest Row Correctness

  Proves that digest_constraints (737–752) on the digest row enforce
  `final_hash = prev_hash + end_state` at the UInt32 level.

  The digest row (row_idx = 16) does NOT expose semantic digest carries in
  dedicated columns. Instead, `eval_digest_row` computes a carry expression
  internally and constrains that carry to be boolean at each 16-bit limb.

  The `carry_a/e` cells on digest rows are only slack values used to satisfy
  the always-on `eval_work_vars` constraints. They are not digest witnesses.

  The work variable mapping on digest rows:
  - word 0 → a[3], word 1 → a[2], word 2 → a[1], word 3 → a[0]
  - word 4 → e[3], word 5 → e[2], word 6 → e[1], word 7 → e[0]

  The private bus does not send `final_hash` directly. It sends the digest row's
  `hash` field, which is used for block chaining and can differ from
  `final_hash` on the wrap-around block.

  Depends on: FieldArithmetic, PerRowTraceFacts, Defs
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Bus.Facts
import VmExtensions.Constraints.Sha2BlockHasherSubAirBus_sha256
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.BitsFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.SelectorFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.TraceFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.PaddingFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.Defs
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.RoundStep.Semantics

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints
open Sha2BlockHasherVmAir_sha256.Soundness.BusFacts

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## D1-D2: Internal carry witnesses for one digest word

Unlike the round-step constraints, the digest row does not expose its carry
values in trace columns. The AIR computes two internal carry expressions per
digest word and only constrains those expressions to be boolean.

The proof layer therefore packages digest carries as existential witnesses,
rather than reading them out of slack-filled `carry_a/e` cells. -/

/-- Witness for the two internal carry values used to check one digest word. -/
structure DigestWordCarryWitness
    (air : C FBB ExtF) (localRow digestRow word : ℕ) where
  carryLo : FBB
  carryHi : FBB
  carryLo_bool : carryLo = 0 ∨ carryLo = 1
  carryHi_bool : carryHi = 0 ∨ carryHi = 1
  lo_eq :
    digestPrevHashLo16 air digestRow word + digestWorkVarLo16 air localRow word =
      digestFinalHashLo16 air digestRow word + carryLo * (2 ^ 16 : ℕ)
  hi_eq :
    digestPrevHashHi16 air digestRow word + digestWorkVarHi16 air localRow word + carryLo =
      digestFinalHashHi16 air digestRow word + carryHi * (2 ^ 16 : ℕ)

private theorem aBitsWord_composeLo16_explicit (air : C FBB ExtF) (row slot : ℕ) :
    composeLo16 (aBitsWord air row slot) =
      work_vars_a air slot 0 row + work_vars_a air slot 1 row * 2 +
      work_vars_a air slot 2 row * 4 + work_vars_a air slot 3 row * 8 +
      work_vars_a air slot 4 row * 16 + work_vars_a air slot 5 row * 32 +
      work_vars_a air slot 6 row * 64 + work_vars_a air slot 7 row * 128 +
      work_vars_a air slot 8 row * 256 + work_vars_a air slot 9 row * 512 +
      work_vars_a air slot 10 row * 1024 + work_vars_a air slot 11 row * 2048 +
      work_vars_a air slot 12 row * 4096 + work_vars_a air slot 13 row * 8192 +
      work_vars_a air slot 14 row * 16384 + work_vars_a air slot 15 row * 32768 := by
  rw [composeLo16]
  rw [show (∑ i : Fin 16, aBitsWord air row slot ⟨i.val, by omega⟩ * (2 : FBB) ^ i.val) =
      ∑ x ∈ Finset.range 16, work_vars_a air slot x row * 2 ^ x by
      simpa [aBitsWord] using
        (Fin.sum_univ_eq_sum_range
          (f := fun x => work_vars_a air slot x row * 2 ^ x)
          (n := 16)).symm]
  norm_num [Finset.sum_range_succ]

private theorem aBitsWord_composeHi16_explicit (air : C FBB ExtF) (row slot : ℕ) :
    composeHi16 (aBitsWord air row slot) =
      work_vars_a air slot 16 row + work_vars_a air slot 17 row * 2 +
      work_vars_a air slot 18 row * 4 + work_vars_a air slot 19 row * 8 +
      work_vars_a air slot 20 row * 16 + work_vars_a air slot 21 row * 32 +
      work_vars_a air slot 22 row * 64 + work_vars_a air slot 23 row * 128 +
      work_vars_a air slot 24 row * 256 + work_vars_a air slot 25 row * 512 +
      work_vars_a air slot 26 row * 1024 + work_vars_a air slot 27 row * 2048 +
      work_vars_a air slot 28 row * 4096 + work_vars_a air slot 29 row * 8192 +
      work_vars_a air slot 30 row * 16384 + work_vars_a air slot 31 row * 32768 := by
  rw [composeHi16]
  rw [show (∑ i : Fin 16, aBitsWord air row slot ⟨i.val + 16, by omega⟩ * (2 : FBB) ^ i.val) =
      ∑ x ∈ Finset.range 16, work_vars_a air slot (x + 16) row * 2 ^ x by
      simpa [aBitsWord] using
        (Fin.sum_univ_eq_sum_range
          (f := fun x => work_vars_a air slot (x + 16) row * 2 ^ x)
          (n := 16)).symm]
  norm_num [Finset.sum_range_succ]

private theorem eBitsWord_composeLo16_explicit (air : C FBB ExtF) (row slot : ℕ) :
    composeLo16 (eBitsWord air row slot) =
      work_vars_e air slot 0 row + work_vars_e air slot 1 row * 2 +
      work_vars_e air slot 2 row * 4 + work_vars_e air slot 3 row * 8 +
      work_vars_e air slot 4 row * 16 + work_vars_e air slot 5 row * 32 +
      work_vars_e air slot 6 row * 64 + work_vars_e air slot 7 row * 128 +
      work_vars_e air slot 8 row * 256 + work_vars_e air slot 9 row * 512 +
      work_vars_e air slot 10 row * 1024 + work_vars_e air slot 11 row * 2048 +
      work_vars_e air slot 12 row * 4096 + work_vars_e air slot 13 row * 8192 +
      work_vars_e air slot 14 row * 16384 + work_vars_e air slot 15 row * 32768 := by
  rw [composeLo16]
  rw [show (∑ i : Fin 16, eBitsWord air row slot ⟨i.val, by omega⟩ * (2 : FBB) ^ i.val) =
      ∑ x ∈ Finset.range 16, work_vars_e air slot x row * 2 ^ x by
      simpa [eBitsWord] using
        (Fin.sum_univ_eq_sum_range
          (f := fun x => work_vars_e air slot x row * 2 ^ x)
          (n := 16)).symm]
  norm_num [Finset.sum_range_succ]

private theorem eBitsWord_composeHi16_explicit (air : C FBB ExtF) (row slot : ℕ) :
    composeHi16 (eBitsWord air row slot) =
      work_vars_e air slot 16 row + work_vars_e air slot 17 row * 2 +
      work_vars_e air slot 18 row * 4 + work_vars_e air slot 19 row * 8 +
      work_vars_e air slot 20 row * 16 + work_vars_e air slot 21 row * 32 +
      work_vars_e air slot 22 row * 64 + work_vars_e air slot 23 row * 128 +
      work_vars_e air slot 24 row * 256 + work_vars_e air slot 25 row * 512 +
      work_vars_e air slot 26 row * 1024 + work_vars_e air slot 27 row * 2048 +
      work_vars_e air slot 28 row * 4096 + work_vars_e air slot 29 row * 8192 +
      work_vars_e air slot 30 row * 16384 + work_vars_e air slot 31 row * 32768 := by
  rw [composeHi16]
  rw [show (∑ i : Fin 16, eBitsWord air row slot ⟨i.val + 16, by omega⟩ * (2 : FBB) ^ i.val) =
      ∑ x ∈ Finset.range 16, work_vars_e air slot (x + 16) row * 2 ^ x by
      simpa [eBitsWord] using
        (Fin.sum_univ_eq_sum_range
          (f := fun x => work_vars_e air slot (x + 16) row * 2 ^ x)
          (n := 16)).symm]
  norm_num [Finset.sum_range_succ]

private theorem digestCarry_mul_pow_eq (x : FBB) :
    ((2013235201 : FBB) * x) * (2 ^ 16 : ℕ) = x := by
  have hinv : (2013235201 : FBB) * (2 ^ 16 : ℕ) = 1 := by
    decide
  calc
    ((2013235201 : FBB) * x) * (2 ^ 16 : ℕ) = x * ((2013235201 : FBB) * (2 ^ 16 : ℕ)) := by
      ring
    _ = x * 1 := by rw [hinv]
    _ = x := by ring

private theorem digestWordCarryWitness_of_polys
    (air : C FBB ExtF) (localRow digestRow word : ℕ)
    (hlo_poly :
      ((2013235201 : FBB) *
          (digestPrevHashLo16 air digestRow word +
            digestWorkVarLo16 air localRow word -
            digestFinalHashLo16 air digestRow word)) *
        (((2013235201 : FBB) *
            (digestPrevHashLo16 air digestRow word +
              digestWorkVarLo16 air localRow word -
              digestFinalHashLo16 air digestRow word)) - 1) = 0)
    (hhi_poly :
      ((2013235201 : FBB) *
          (digestPrevHashHi16 air digestRow word +
            digestWorkVarHi16 air localRow word +
            ((2013235201 : FBB) *
                (digestPrevHashLo16 air digestRow word +
                  digestWorkVarLo16 air localRow word -
                  digestFinalHashLo16 air digestRow word)) -
              digestFinalHashHi16 air digestRow word)) *
        (((2013235201 : FBB) *
            (digestPrevHashHi16 air digestRow word +
              digestWorkVarHi16 air localRow word +
              ((2013235201 : FBB) *
                  (digestPrevHashLo16 air digestRow word +
                    digestWorkVarLo16 air localRow word -
                    digestFinalHashLo16 air digestRow word)) -
                digestFinalHashHi16 air digestRow word)) - 1) = 0) :
    Nonempty (DigestWordCarryWitness air localRow digestRow word) := by
  let carryLo : FBB :=
    (2013235201 : FBB) *
      (digestPrevHashLo16 air digestRow word +
        digestWorkVarLo16 air localRow word -
        digestFinalHashLo16 air digestRow word)
  let carryHi : FBB :=
    (2013235201 : FBB) *
      (digestPrevHashHi16 air digestRow word +
        digestWorkVarHi16 air localRow word + carryLo -
        digestFinalHashHi16 air digestRow word)
  refine ⟨{ carryLo := carryLo
            carryHi := carryHi
            carryLo_bool := ?_
            carryHi_bool := ?_
            lo_eq := ?_
            hi_eq := ?_ }⟩
  · exact bit_boolean_of_sq_eq_zero carryLo (by simpa [carryLo] using hlo_poly)
  · exact bit_boolean_of_sq_eq_zero carryHi (by simpa [carryLo, carryHi] using hhi_poly)
  · let expr :=
      digestPrevHashLo16 air digestRow word +
        digestWorkVarLo16 air localRow word -
        digestFinalHashLo16 air digestRow word
    have hexpr : ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) = expr :=
      digestCarry_mul_pow_eq expr
    calc
      digestPrevHashLo16 air digestRow word + digestWorkVarLo16 air localRow word =
          digestFinalHashLo16 air digestRow word + expr := by
            dsimp [expr]
            ring
      _ = digestFinalHashLo16 air digestRow word + ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) := by
            conv_lhs => rw [hexpr.symm]
      _ = digestFinalHashLo16 air digestRow word + carryLo * (2 ^ 16 : ℕ) := by
            dsimp [carryLo, expr]
  · let expr :=
      digestPrevHashHi16 air digestRow word +
        digestWorkVarHi16 air localRow word + carryLo -
        digestFinalHashHi16 air digestRow word
    have hexpr : ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) = expr :=
      digestCarry_mul_pow_eq expr
    calc
      digestPrevHashHi16 air digestRow word + digestWorkVarHi16 air localRow word + carryLo =
          digestFinalHashHi16 air digestRow word + expr := by
            dsimp [expr]
            ring
      _ = digestFinalHashHi16 air digestRow word + ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) := by
            conv_lhs => rw [hexpr.symm]
      _ = digestFinalHashHi16 air digestRow word + carryHi * (2 ^ 16 : ℕ) := by
            dsimp [carryHi, expr]

/-- Digest constraints provide a limbed-addition witness for each digest word.
    The witness lives only in proof space: it is not stored in dedicated columns. -/
theorem digest_word_carry_witness (air : C FBB ExtF) (row : ℕ) (word : ℕ)
    (hword : word < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hd : digest_constraints air row)
    (hdigest_next : is_digest_row air (nextRow air row) = 1) :
    Nonempty (DigestWordCarryWitness air row (nextRow air row) word) := by
  have hnext_digest : next_is_digest_row air row = 1 := by
    rw [next_is_digest_row_eq_nextRow air hrot row hrow]
    exact hdigest_next
  rcases hd with ⟨h737, h738, h739, h740, h741, h742, h743, h744,
    h745, h746, h747, h748, h749, h750, h751, h752⟩
  have h737 : constraint_737 air row := (constraint_737_of_extraction air row).mp h737
  have h738 : constraint_738 air row := (constraint_738_of_extraction air row).mp h738
  have h739 : constraint_739 air row := (constraint_739_of_extraction air row).mp h739
  have h740 : constraint_740 air row := (constraint_740_of_extraction air row).mp h740
  have h741 : constraint_741 air row := (constraint_741_of_extraction air row).mp h741
  have h742 : constraint_742 air row := (constraint_742_of_extraction air row).mp h742
  have h743 : constraint_743 air row := (constraint_743_of_extraction air row).mp h743
  have h744 : constraint_744 air row := (constraint_744_of_extraction air row).mp h744
  have h745 : constraint_745 air row := (constraint_745_of_extraction air row).mp h745
  have h746 : constraint_746 air row := (constraint_746_of_extraction air row).mp h746
  have h747 : constraint_747 air row := (constraint_747_of_extraction air row).mp h747
  have h748 : constraint_748 air row := (constraint_748_of_extraction air row).mp h748
  have h749 : constraint_749 air row := (constraint_749_of_extraction air row).mp h749
  have h750 : constraint_750 air row := (constraint_750_of_extraction air row).mp h750
  have h751 : constraint_751 air row := (constraint_751_of_extraction air row).mp h751
  have h752 : constraint_752 air row := (constraint_752_of_extraction air row).mp h752
  interval_cases word
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 0
      (by
        simpa [constraint_737, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 0 0 row hrow,
          next_final_hash_eq_nextRow air hrot 0 0 row hrow,
          next_final_hash_eq_nextRow air hrot 0 1 row hrow,
          aBitsWord_composeLo16_explicit air row 3, -mul_eq_zero] using h737)
      (by
        simpa [constraint_738, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 0 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 0 1 row hrow,
          next_final_hash_eq_nextRow air hrot 0 0 row hrow,
          next_final_hash_eq_nextRow air hrot 0 1 row hrow,
          next_final_hash_eq_nextRow air hrot 0 2 row hrow,
          next_final_hash_eq_nextRow air hrot 0 3 row hrow,
          aBitsWord_composeLo16_explicit air row 3,
          aBitsWord_composeHi16_explicit air row 3, -mul_eq_zero] using h738)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 1
      (by
        simpa [constraint_739, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 1 0 row hrow,
          next_final_hash_eq_nextRow air hrot 1 0 row hrow,
          next_final_hash_eq_nextRow air hrot 1 1 row hrow,
          aBitsWord_composeLo16_explicit air row 2, -mul_eq_zero] using h739)
      (by
        simpa [constraint_740, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 1 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 1 1 row hrow,
          next_final_hash_eq_nextRow air hrot 1 0 row hrow,
          next_final_hash_eq_nextRow air hrot 1 1 row hrow,
          next_final_hash_eq_nextRow air hrot 1 2 row hrow,
          next_final_hash_eq_nextRow air hrot 1 3 row hrow,
          aBitsWord_composeLo16_explicit air row 2,
          aBitsWord_composeHi16_explicit air row 2, -mul_eq_zero] using h740)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 2
      (by
        simpa [constraint_741, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 2 0 row hrow,
          next_final_hash_eq_nextRow air hrot 2 0 row hrow,
          next_final_hash_eq_nextRow air hrot 2 1 row hrow,
          aBitsWord_composeLo16_explicit air row 1, -mul_eq_zero] using h741)
      (by
        simpa [constraint_742, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 2 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 2 1 row hrow,
          next_final_hash_eq_nextRow air hrot 2 0 row hrow,
          next_final_hash_eq_nextRow air hrot 2 1 row hrow,
          next_final_hash_eq_nextRow air hrot 2 2 row hrow,
          next_final_hash_eq_nextRow air hrot 2 3 row hrow,
          aBitsWord_composeLo16_explicit air row 1,
          aBitsWord_composeHi16_explicit air row 1, -mul_eq_zero] using h742)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 3
      (by
        simpa [constraint_743, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 3 0 row hrow,
          next_final_hash_eq_nextRow air hrot 3 0 row hrow,
          next_final_hash_eq_nextRow air hrot 3 1 row hrow,
          aBitsWord_composeLo16_explicit air row 0, -mul_eq_zero] using h743)
      (by
        simpa [constraint_744, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 3 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 3 1 row hrow,
          next_final_hash_eq_nextRow air hrot 3 0 row hrow,
          next_final_hash_eq_nextRow air hrot 3 1 row hrow,
          next_final_hash_eq_nextRow air hrot 3 2 row hrow,
          next_final_hash_eq_nextRow air hrot 3 3 row hrow,
          aBitsWord_composeLo16_explicit air row 0,
          aBitsWord_composeHi16_explicit air row 0, -mul_eq_zero] using h744)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 4
      (by
        simpa [constraint_745, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 4 0 row hrow,
          next_final_hash_eq_nextRow air hrot 4 0 row hrow,
          next_final_hash_eq_nextRow air hrot 4 1 row hrow,
          eBitsWord_composeLo16_explicit air row 3, -mul_eq_zero] using h745)
      (by
        simpa [constraint_746, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 4 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 4 1 row hrow,
          next_final_hash_eq_nextRow air hrot 4 0 row hrow,
          next_final_hash_eq_nextRow air hrot 4 1 row hrow,
          next_final_hash_eq_nextRow air hrot 4 2 row hrow,
          next_final_hash_eq_nextRow air hrot 4 3 row hrow,
          eBitsWord_composeLo16_explicit air row 3,
          eBitsWord_composeHi16_explicit air row 3, -mul_eq_zero] using h746)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 5
      (by
        simpa [constraint_747, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 5 0 row hrow,
          next_final_hash_eq_nextRow air hrot 5 0 row hrow,
          next_final_hash_eq_nextRow air hrot 5 1 row hrow,
          eBitsWord_composeLo16_explicit air row 2, -mul_eq_zero] using h747)
      (by
        simpa [constraint_748, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 5 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 5 1 row hrow,
          next_final_hash_eq_nextRow air hrot 5 0 row hrow,
          next_final_hash_eq_nextRow air hrot 5 1 row hrow,
          next_final_hash_eq_nextRow air hrot 5 2 row hrow,
          next_final_hash_eq_nextRow air hrot 5 3 row hrow,
          eBitsWord_composeLo16_explicit air row 2,
          eBitsWord_composeHi16_explicit air row 2, -mul_eq_zero] using h748)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 6
      (by
        simpa [constraint_749, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 6 0 row hrow,
          next_final_hash_eq_nextRow air hrot 6 0 row hrow,
          next_final_hash_eq_nextRow air hrot 6 1 row hrow,
          eBitsWord_composeLo16_explicit air row 1, -mul_eq_zero] using h749)
      (by
        simpa [constraint_750, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 6 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 6 1 row hrow,
          next_final_hash_eq_nextRow air hrot 6 0 row hrow,
          next_final_hash_eq_nextRow air hrot 6 1 row hrow,
          next_final_hash_eq_nextRow air hrot 6 2 row hrow,
          next_final_hash_eq_nextRow air hrot 6 3 row hrow,
          eBitsWord_composeLo16_explicit air row 1,
          eBitsWord_composeHi16_explicit air row 1, -mul_eq_zero] using h750)
  · exact digestWordCarryWitness_of_polys air row (nextRow air row) 7
      (by
        simpa [constraint_751, hnext_digest, digestPrevHashLo16, digestFinalHashLo16,
          digestWorkVarLo16,
          next_prev_hash_eq_nextRow air hrot 7 0 row hrow,
          next_final_hash_eq_nextRow air hrot 7 0 row hrow,
          next_final_hash_eq_nextRow air hrot 7 1 row hrow,
          eBitsWord_composeLo16_explicit air row 0, -mul_eq_zero] using h751)
      (by
        simpa [constraint_752, hnext_digest, digestPrevHashLo16, digestPrevHashHi16,
          digestFinalHashLo16, digestFinalHashHi16,
          digestWorkVarLo16, digestWorkVarHi16,
          next_prev_hash_eq_nextRow air hrot 7 0 row hrow,
          next_prev_hash_eq_nextRow air hrot 7 1 row hrow,
          next_final_hash_eq_nextRow air hrot 7 0 row hrow,
          next_final_hash_eq_nextRow air hrot 7 1 row hrow,
          next_final_hash_eq_nextRow air hrot 7 2 row hrow,
          next_final_hash_eq_nextRow air hrot 7 3 row hrow,
          eBitsWord_composeLo16_explicit air row 0,
          eBitsWord_composeHi16_explicit air row 0, -mul_eq_zero] using h752)

/-! ## D3: Byte-to-limb bridge for final hash -/

private theorem byte_pair_val_eq (lo hi : FBB)
    (hlo : lo.val < 256) (hhi : hi.val < 256) :
    (lo + hi * 256).val = lo.val + hi.val * 256 := by
  have h256 : ((256 : FBB)).val = 256 := by
    exact ZMod.val_natCast_of_lt (by decide : 256 < BB_prime)
  have hmul_lt_nat : hi.val * 256 < BB_prime := by
    have hmul_le : hi.val * 256 ≤ 255 * 256 := by omega
    exact lt_of_le_of_lt hmul_le (by norm_num)
  have hmul : (hi * (256 : FBB)).val = hi.val * 256 := by
    rw [Fin.val_mul]
    change hi.val * ((256 : FBB)).val % BB_prime = hi.val * 256
    rw [h256, Nat.mod_eq_of_lt hmul_lt_nat]
  have hadd_nat : lo.val + hi.val * 256 < BB_prime := by
    have hsum_le : lo.val + hi.val * 256 ≤ 255 + 255 * 256 := by omega
    exact lt_of_le_of_lt hsum_le (by norm_num)
  have hadd : lo.val + (hi * (256 : FBB)).val < BB_prime := by
    simpa [hmul] using hadd_nat
  have hadd' : (lo + hi * (256 : FBB)).val = lo.val + (hi * (256 : FBB)).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt hadd]
  calc
    (lo + hi * 256).val = lo.val + (hi * (256 : FBB)).val := by simpa using hadd'
    _ = lo.val + hi.val * 256 := by rw [hmul]

private theorem u32_two_limb_eq (a b : ℕ) :
    UInt32.ofNat (a + b * 65536) =
      UInt32.ofNat a + UInt32.ofNat b * UInt32.ofNat 65536 := by
  open scoped UInt32.CommRing in
    change (((a + b * 65536 : ℕ)) : UInt32) =
      ((a : ℕ) : UInt32) + ((b : ℕ) : UInt32) * ((65536 : ℕ) : UInt32)
    rw [Nat.cast_add, Nat.cast_mul]

private theorem u32_two_byte_eq (a b : ℕ) :
    UInt32.ofNat (a + b * 256) =
      UInt32.ofNat a + UInt32.ofNat b * UInt32.ofNat 256 := by
  open scoped UInt32.CommRing in
    change (((a + b * 256 : ℕ)) : UInt32) =
      ((a : ℕ) : UInt32) + ((b : ℕ) : UInt32) * ((256 : ℕ) : UInt32)
    rw [Nat.cast_add, Nat.cast_mul]

private theorem u32_four_byte_regroup (a b c d : ℕ) :
    UInt32.ofNat (a + b * 256 + c * 65536 + d * 16777216) =
      UInt32.ofNat a + UInt32.ofNat b * UInt32.ofNat 256 +
      (UInt32.ofNat c + UInt32.ofNat d * UInt32.ofNat 256) * UInt32.ofNat 65536 := by
  open scoped UInt32.CommRing in
    change (((a + b * 256 + c * 65536 + d * 16777216 : ℕ)) : UInt32) =
      (((a : ℕ)) : UInt32) + (((b : ℕ)) : UInt32) * (((256 : ℕ)) : UInt32) +
        ((((c : ℕ)) : UInt32) + (((d : ℕ)) : UInt32) * (((256 : ℕ)) : UInt32)) *
          (((65536 : ℕ)) : UInt32)
    rw [Nat.cast_add, Nat.cast_mul]
    ring_nf
    simp [add_assoc, add_comm, add_left_comm]

/-- digestFinalHashWord equals lo16 + hi16 * 2^16 (as a Word).
    This needs byte-range hypotheses so the two byte-pairs do not wrap in BabyBear. -/
theorem digestFinalHash_eq_limbs (air : C FBB ExtF) (row word : ℕ)
    (hbyte : ∀ byte, byte < 4 → (final_hash air word byte row).val < 256) :
    digestFinalHashWord air row word =
      ((digestFinalHashLo16 air row word).val +
       (digestFinalHashHi16 air row word).val * 2^16).toUInt32 := by
  have h0 := hbyte 0 (by omega)
  have h1 := hbyte 1 (by omega)
  have h2 := hbyte 2 (by omega)
  have h3 := hbyte 3 (by omega)
  let b0 := (final_hash air word 0 row).val
  let b1 := (final_hash air word 1 row).val
  let b2 := (final_hash air word 2 row).val
  let b3 := (final_hash air word 3 row).val
  have hlo :
      (digestFinalHashLo16 air row word).val =
        b0 + b1 * 256 := by
    simpa [digestFinalHashLo16] using
      byte_pair_val_eq (final_hash air word 0 row) (final_hash air word 1 row) h0 h1
  have hhi :
      (digestFinalHashHi16 air row word).val =
        b2 + b3 * 256 := by
    simpa [digestFinalHashHi16] using
      byte_pair_val_eq (final_hash air word 2 row) (final_hash air word 3 row) h2 h3
  have hword :
      digestFinalHashWord air row word = UInt32.ofNat (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) := by
    rw [digestFinalHashWord, bytesLEToWord, foldl_range_add_eq_sum]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [b0, b1, b2, b3]
  have hlimbs :
      UInt32.ofNat b0 + UInt32.ofNat b1 * UInt32.ofNat 256 +
        (UInt32.ofNat b2 + UInt32.ofNat b3 * UInt32.ofNat 256) * UInt32.ofNat 65536 =
        ((digestFinalHashLo16 air row word).val + (digestFinalHashHi16 air row word).val * 2 ^ 16).toUInt32 := by
    rw [← u32_two_byte_eq b0 b1, ← u32_two_byte_eq b2 b3]
    rw [← hlo, ← hhi]
    simpa using (u32_two_limb_eq (b0 + b1 * 256) (b2 + b3 * 256)).symm
  exact hword.trans ((u32_four_byte_regroup b0 b1 b2 b3).trans hlimbs)

/-- digestPrevHashWord equals limb[0] + limb[1] * 2^16 (by definition of limbs16LEToWord). -/
theorem digestPrevHash_eq_limbs (air : C FBB ExtF) (row word : ℕ) :
    digestPrevHashWord air row word =
      ((digestPrevHashLo16 air row word).val +
       (digestPrevHashHi16 air row word).val * 2^16).toUInt32 := by
  rw [digestPrevHashWord, limbs16LEToWord, foldl_range_add_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simpa [digestPrevHashLo16, digestPrevHashHi16] using
    (u32_two_limb_eq (prev_hash air word 0 row).val (prev_hash air word 1 row).val)

theorem compose_a_u16_lo_eq (air : C FBB ExtF) (row slot : ℕ) :
    compose_a_u16 air slot 0 row = composeLo16 (aBitsWord air row slot) := by
  have hsum :
      (∑ x : Fin 16, work_vars_a air slot x.val row * 2 ^ x.val) =
        ∑ x ∈ Finset.range 16, work_vars_a air slot x row * 2 ^ x := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun x => work_vars_a air slot x row * 2 ^ x)
        (n := 16))
  simpa [compose_a_u16, composeLo16, aBitsWord] using hsum.symm

theorem compose_a_u16_hi_eq (air : C FBB ExtF) (row slot : ℕ) :
    compose_a_u16 air slot 1 row = composeHi16 (aBitsWord air row slot) := by
  have hsum :
      (∑ x : Fin 16, work_vars_a air slot (x.val + 16) row * 2 ^ x.val) =
        ∑ x ∈ Finset.range 16, work_vars_a air slot (16 + x) row * 2 ^ x := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun x => work_vars_a air slot (16 + x) row * 2 ^ x)
        (n := 16))
  simpa [compose_a_u16, composeHi16, aBitsWord] using hsum.symm

theorem compose_e_u16_lo_eq (air : C FBB ExtF) (row slot : ℕ) :
    compose_e_u16 air slot 0 row = composeLo16 (eBitsWord air row slot) := by
  have hsum :
      (∑ x : Fin 16, work_vars_e air slot x.val row * 2 ^ x.val) =
        ∑ x ∈ Finset.range 16, work_vars_e air slot x row * 2 ^ x := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun x => work_vars_e air slot x row * 2 ^ x)
        (n := 16))
  simpa [compose_e_u16, composeLo16, eBitsWord] using hsum.symm

theorem compose_e_u16_hi_eq (air : C FBB ExtF) (row slot : ℕ) :
    compose_e_u16 air slot 1 row = composeHi16 (eBitsWord air row slot) := by
  have hsum :
      (∑ x : Fin 16, work_vars_e air slot (x.val + 16) row * 2 ^ x.val) =
        ∑ x ∈ Finset.range 16, work_vars_e air slot (16 + x) row * 2 ^ x := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun x => work_vars_e air slot (16 + x) row * 2 ^ x)
        (n := 16))
  simpa [compose_e_u16, composeHi16, eBitsWord] using hsum.symm

theorem wordU16Limb_of_two_limbs (lo hi : FBB)
    (hlo : lo.val < 2 ^ 16) (hhi : hi.val < 2 ^ 16) :
    wordU16Limb (((lo.val + hi.val * 2 ^ 16).toUInt32)) 0 = lo ∧
    wordU16Limb (((lo.val + hi.val * 2 ^ 16).toUInt32)) 1 = hi := by
  constructor <;> apply Fin.ext <;> simp [wordU16Limb, UInt32.toNat_ofNat] <;> omega

theorem composed_hash_matches_digestChainingHashField
    (air : C FBB ExtF) (row word limb : ℕ)
    (hbb : allWorkVarBitsBoolean air row)
    (hword : word < 8) (hlimb : limb < 2) :
    composed_hash_u16 air word limb row =
      workingVarsU16Limb (digestChainingHashState air row) word limb := by
  have hwordEq :
      workingVarsU16Limb (digestChainingHashState air row) word limb =
        wordU16Limb (digestWorkVarWord air row word) limb := by
    dsimp [digestChainingHashState, carriedState, workingVarsU16Limb, digestWorkVarWord]
    interval_cases word <;> rfl
  have hlimb_cases : limb = 0 ∨ limb = 1 := by
    omega
  have hlo_lt : (digestWorkVarLo16 air row word).val < 2 ^ 16 := by
    by_cases hword4 : word < 4
    · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
        intro i
        exact hbb.1 (3 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarLo16, hword4] using
        composeLo16_val_lt (aBitsWord air row (3 - word)) hbits
    · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
        intro i
        exact hbb.2 (7 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarLo16, hword4] using
        composeLo16_val_lt (eBitsWord air row (7 - word)) hbits
  have hhi_lt : (digestWorkVarHi16 air row word).val < 2 ^ 16 := by
    by_cases hword4 : word < 4
    · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
        intro i
        exact hbb.1 (3 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarHi16, hword4] using
        composeHi16_val_lt (aBitsWord air row (3 - word)) hbits
    · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
        intro i
        exact hbb.2 (7 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarHi16, hword4] using
        composeHi16_val_lt (eBitsWord air row (7 - word)) hbits
  rcases wordU16Limb_of_two_limbs
      (digestWorkVarLo16 air row word)
      (digestWorkVarHi16 air row word)
      hlo_lt hhi_lt with ⟨hlo, hhi⟩
  have hlimbEq :
      wordU16Limb (digestWorkVarWord air row word) limb =
        (if limb = 0 then digestWorkVarLo16 air row word
         else digestWorkVarHi16 air row word) := by
    have hdw :
        digestWorkVarWord air row word =
          ((digestWorkVarLo16 air row word).val +
            (digestWorkVarHi16 air row word).val * 2 ^ 16).toUInt32 := by
      rcases hbb with ⟨ha_bits, he_bits⟩
      by_cases hword4 : word < 4
      · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
          intro i
          exact ha_bits (3 - word) i.val (by omega) i.isLt
        simp [digestWorkVarWord, digestWorkVarLo16, digestWorkVarHi16, hword4]
        rw [aWord_eq_bitsWordToUInt32]
        simpa using bitsWordToUInt32_eq_compose16 (aBitsWord air row (3 - word)) hbits
      · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
          intro i
          exact he_bits (7 - word) i.val (by omega) i.isLt
        simp [digestWorkVarWord, digestWorkVarLo16, digestWorkVarHi16, hword4]
        rw [eWord_eq_bitsWordToUInt32]
        simpa using bitsWordToUInt32_eq_compose16 (eBitsWord air row (7 - word)) hbits
    rw [hdw]
    rcases hlimb_cases with rfl | rfl
    · simpa using hlo
    · simpa using hhi
  have hcomp :
      composed_hash_u16 air word limb row =
        (if limb = 0 then digestWorkVarLo16 air row word
         else digestWorkVarHi16 air row word) := by
    rcases hlimb_cases with rfl | rfl
    · by_cases hword4 : word < 4
      · simpa [composed_hash_u16, digestWorkVarLo16, hword4] using
          (compose_a_u16_lo_eq air row (3 - word))
      · simpa [composed_hash_u16, digestWorkVarLo16, hword4] using
          (compose_e_u16_lo_eq air row (7 - word))
    · by_cases hword4 : word < 4
      · simpa [composed_hash_u16, digestWorkVarHi16, hword4] using
          (compose_a_u16_hi_eq air row (3 - word))
      · simpa [composed_hash_u16, digestWorkVarHi16, hword4] using
          (compose_e_u16_hi_eq air row (7 - word))
  calc
    composed_hash_u16 air word limb row =
        (if limb = 0 then digestWorkVarLo16 air row word
         else digestWorkVarHi16 air row word) := hcomp
    _ = wordU16Limb (digestWorkVarWord air row word) limb := hlimbEq.symm
    _ = workingVarsU16Limb (digestChainingHashState air row) word limb := hwordEq.symm

/-- digestWorkVarWord equals work_var_lo + work_var_hi * 2^16 (from composeBits_eq_lo_plus_hi). -/
theorem digestWorkVar_eq_limbs (air : C FBB ExtF) (row word : ℕ)
    (hbb : allWorkVarBitsBoolean air row) :
    digestWorkVarWord air row word =
      ((digestWorkVarLo16 air row word).val +
       (digestWorkVarHi16 air row word).val * 2^16).toUInt32 := by
  rcases hbb with ⟨ha_bits, he_bits⟩
  by_cases hword : word < 4
  · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
      intro i
      exact ha_bits (3 - word) i.val (by omega) i.isLt
    simp [digestWorkVarWord, digestWorkVarLo16, digestWorkVarHi16, hword]
    rw [aWord_eq_bitsWordToUInt32]
    simpa using bitsWordToUInt32_eq_compose16 (aBitsWord air row (3 - word)) hbits
  · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
      intro i
      exact he_bits (7 - word) i.val (by omega) i.isLt
    simp [digestWorkVarWord, digestWorkVarLo16, digestWorkVarHi16, hword]
    rw [eWord_eq_bitsWordToUInt32]
    simpa using bitsWordToUInt32_eq_compose16 (eBitsWord air row (7 - word)) hbits

private theorem digestFinalHash_limb_range_of_bus
    (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hdigest : is_digest_row air row = 1)
    (h_wf_prev : bitwise_lookup_send_properties air (prevRow air row)) :
    (digestFinalHashLo16 air row word).val < 2 ^ 16 ∧
      (digestFinalHashHi16 air row word).val < 2 ^ 16 := by
  have h0 := digest_final_hash_byte_range_of_bus air row word 0 hword (by omega) hrow hrot hdigest h_wf_prev
  have h1 := digest_final_hash_byte_range_of_bus air row word 1 hword (by omega) hrow hrot hdigest h_wf_prev
  have h2 := digest_final_hash_byte_range_of_bus air row word 2 hword (by omega) hrow hrot hdigest h_wf_prev
  have h3 := digest_final_hash_byte_range_of_bus air row word 3 hword (by omega) hrow hrot hdigest h_wf_prev
  let b0 := (final_hash air word 0 row).val
  let b1 := (final_hash air word 1 row).val
  let b2 := (final_hash air word 2 row).val
  let b3 := (final_hash air word 3 row).val
  have hlo :
      (digestFinalHashLo16 air row word).val = b0 + b1 * 256 := by
    simpa [digestFinalHashLo16] using
      byte_pair_val_eq (final_hash air word 0 row) (final_hash air word 1 row) h0 h1
  have hhi :
      (digestFinalHashHi16 air row word).val = b2 + b3 * 256 := by
    simpa [digestFinalHashHi16] using
      byte_pair_val_eq (final_hash air word 2 row) (final_hash air word 3 row) h2 h3
  have hlo_lt : b0 + b1 * 256 < 2 ^ 16 := by
    dsimp [b0, b1]
    omega
  have hhi_lt : b2 + b3 * 256 < 2 ^ 16 := by
    dsimp [b2, b3]
    omega
  exact ⟨hlo ▸ hlo_lt, hhi ▸ hhi_lt⟩

/-! ## D4: Per-word UInt32 addition -/

/-- A single digest word satisfies the addition constraint at UInt32 level:
    final_hash[w] = prev_hash[w] + work_var_mapped[w] (mod 2^32).

    Combines: `digest_word_carry_witness` + D3 limb bridges
    + limbed_addition_two_inputs from FieldArithmetic. -/
theorem digest_word_addition_uint32 (air : C FBB ExtF) (start : ℕ) (word : ℕ)
    (hword : word < 8)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_prev_range : digestPrevHashLimbRange air (start + 16))
    (h_wf_prev : bitwise_lookup_send_properties air (start + 15)) :
    digestFinalHashWord air (start + 16) word =
      digestPrevHashWord air (start + 16) word +
      digestWorkVarWord air (start + 15) word := by
  let row := start + 15
  let digestRow := start + 16
  have hrow : row ≤ Circuit.last_row air := by
    dsimp [row]
    dsimp [blockWindowSupported] at hwindow
    omega
  have hrow_lt : row < Circuit.last_row air := by
    dsimp [row]
    dsimp [blockWindowSupported] at hwindow
    omega
  have hrow_ne : row ≠ Circuit.last_row air := by
    omega
  have hnextrow : nextRow air row = digestRow := by
    have hrow15_ne : start + 15 ≠ Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    dsimp [row, digestRow]
    simp [nextRow, hrow15_ne, Nat.add_assoc]
  have hdigest_constraints : digest_constraints air row := by
    dsimp [row]
    exact (hc (start + 15)).2.2.2.2.2.2.1
  rcases hshape with ⟨_, _, _, _, hdigest_row⟩
  rcases digest_word_carry_witness air row word hword hrow hrot hdigest_constraints
      (by
        simpa [hnextrow] using hdigest_row) with ⟨hwit⟩
  have hlo_eq :
      digestPrevHashLo16 air digestRow word + digestWorkVarLo16 air row word =
        digestFinalHashLo16 air digestRow word + hwit.carryLo * (2 ^ 16 : ℕ) := by
    simpa [hnextrow] using hwit.lo_eq
  have hhi_eq :
      digestPrevHashHi16 air digestRow word + digestWorkVarHi16 air row word + hwit.carryLo =
        digestFinalHashHi16 air digestRow word + hwit.carryHi * (2 ^ 16 : ℕ) := by
    simpa [hnextrow] using hwit.hi_eq
  have hbb : allWorkVarBitsBoolean air row := by
    dsimp [row]
    exact allWorkVarBitsBoolean_of_constraints air (start + 15) (hc (start + 15)).2.1
  have hprev_lo : (digestPrevHashLo16 air digestRow word).val < 2 ^ 16 := by
    dsimp [digestRow, digestPrevHashLo16]
    exact h_prev_range word 0 hword (by omega)
  have hprev_hi : (digestPrevHashHi16 air digestRow word).val < 2 ^ 16 := by
    dsimp [digestRow, digestPrevHashHi16]
    exact h_prev_range word 1 hword (by omega)
  have hwork_lo : (digestWorkVarLo16 air row word).val < 2 ^ 16 := by
    by_cases hword4 : word < 4
    · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
        intro i
        exact hbb.1 (3 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarLo16, hword4] using
        composeLo16_val_lt (aBitsWord air row (3 - word)) hbits
    · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
        intro i
        exact hbb.2 (7 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarLo16, hword4] using
        composeLo16_val_lt (eBitsWord air row (7 - word)) hbits
  have hwork_hi : (digestWorkVarHi16 air row word).val < 2 ^ 16 := by
    by_cases hword4 : word < 4
    · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
        intro i
        exact hbb.1 (3 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarHi16, hword4] using
        composeHi16_val_lt (aBitsWord air row (3 - word)) hbits
    · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
        intro i
        exact hbb.2 (7 - word) i.val (by omega) i.isLt
      simpa [digestWorkVarHi16, hword4] using
        composeHi16_val_lt (eBitsWord air row (7 - word)) hbits
  have hfinal_range :
      (digestFinalHashLo16 air digestRow word).val < 2 ^ 16 ∧
        (digestFinalHashHi16 air digestRow word).val < 2 ^ 16 := by
    dsimp [row, digestRow] at *
    exact digestFinalHash_limb_range_of_bus air (start + 16) word hword
      (by simpa [blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev
  have hmod :=
    limbed_addition_two_inputs
      (digestPrevHashLo16 air digestRow word)
      (digestPrevHashHi16 air digestRow word)
      (digestWorkVarLo16 air row word)
      (digestWorkVarHi16 air row word)
      (digestFinalHashLo16 air digestRow word)
      (digestFinalHashHi16 air digestRow word)
      hwit.carryLo hwit.carryHi
      hprev_lo hprev_hi hwork_lo hwork_hi hfinal_range.1 hfinal_range.2
      hwit.carryLo_bool hwit.carryHi_bool hlo_eq hhi_eq
  rw [digestFinalHash_eq_limbs air digestRow word
        (fun byte hbyte =>
          digest_final_hash_byte_range_of_bus air digestRow word byte hword hbyte
            (by simpa [blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev),
    digestPrevHash_eq_limbs,
    digestWorkVar_eq_limbs air row word hbb]
  apply UInt32_eq_of_toNat_eq
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmod.symm

/-! ## D5: Prev hash = block start state -/

private theorem composed_hash_eq_digestWorkVarLimb
    (air : C FBB ExtF) (row word limb : ℕ)
    (hword : word < 8) (hlimb : limb < 2) :
    composed_hash_u16 air word limb row =
      (if limb = 0 then digestWorkVarLo16 air row word
       else digestWorkVarHi16 air row word) := by
  rcases (show limb = 0 ∨ limb = 1 by omega) with rfl | rfl
  · by_cases hword4 : word < 4
    · simpa [composed_hash_u16, digestWorkVarLo16, hword4] using
        (compose_a_u16_lo_eq air row (3 - word))
    · simpa [composed_hash_u16, digestWorkVarLo16, hword4] using
        (compose_e_u16_lo_eq air row (7 - word))
  · by_cases hword4 : word < 4
    · simpa [composed_hash_u16, digestWorkVarHi16, hword4] using
        (compose_a_u16_hi_eq air row (3 - word))
    · simpa [composed_hash_u16, digestWorkVarHi16, hword4] using
        (compose_e_u16_hi_eq air row (7 - word))

private theorem composed_hash_u16_range
    (air : C FBB ExtF) (row word limb : ℕ)
    (hbb : allWorkVarBitsBoolean air row)
    (hword : word < 8) (hlimb : limb < 2) :
    (composed_hash_u16 air word limb row).val < 2 ^ 16 := by
  rcases (show limb = 0 ∨ limb = 1 by omega) with rfl | rfl
  · by_cases hword4 : word < 4
    · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
        intro i
        exact hbb.1 (3 - word) i.val (by omega) i.isLt
      simpa [composed_hash_u16, hword4] using
        (compose_a_u16_lo_eq air row (3 - word)).symm ▸
          composeLo16_val_lt (aBitsWord air row (3 - word)) hbits
    · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
        intro i
        exact hbb.2 (7 - word) i.val (by omega) i.isLt
      simpa [composed_hash_u16, hword4] using
        (compose_e_u16_lo_eq air row (7 - word)).symm ▸
          composeLo16_val_lt (eBitsWord air row (7 - word)) hbits
  · by_cases hword4 : word < 4
    · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
        intro i
        exact hbb.1 (3 - word) i.val (by omega) i.isLt
      simpa [composed_hash_u16, hword4] using
        (compose_a_u16_hi_eq air row (3 - word)).symm ▸
          composeHi16_val_lt (aBitsWord air row (3 - word)) hbits
    · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
        intro i
        exact hbb.2 (7 - word) i.val (by omega) i.isLt
      simpa [composed_hash_u16, hword4] using
        (compose_e_u16_hi_eq air row (7 - word)).symm ▸
          composeHi16_val_lt (eBitsWord air row (7 - word)) hbits

private theorem next_row_padding_of_next_padding_eq_one
    (air : C FBB ExtF) (row : ℕ)
    (hf_next : flag_constraints air (nextRow air row))
    (hnext_pad :
      (1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row))) = 1) :
    is_round_row air (nextRow air row) = 0 ∧
      is_digest_row air (nextRow air row) = 0 := by
  have hsum : is_round_row air (nextRow air row) + is_digest_row air (nextRow air row) = 0 := by
    exact sub_eq_self.mp hnext_pad
  rcases is_round_row_boolean air (nextRow air row) hf_next with hround0 | hround1
  · refine ⟨hround0, ?_⟩
    rcases is_digest_row_boolean air (nextRow air row) hf_next with hdigest0 | hdigest1
    · exact hdigest0
    · have : (1 : FBB) = 0 := by simpa [hround0, hdigest1] using hsum
      exact False.elim ((by decide : (1 : FBB) ≠ 0) this)
  · rcases is_digest_row_boolean air (nextRow air row) hf_next with hdigest0 | hdigest1
    · have : (1 : FBB) = 0 := by simpa [hround1, hdigest0] using hsum
      exact False.elim ((by decide : (1 : FBB) ≠ 0) this)
    · have : (2 : FBB) = 0 := by simpa [hround1, hdigest1] using hsum
      exact False.elim ((by decide : (2 : FBB) ≠ 0) this)

private theorem carriedState_eq_of_workvar_bits_eq
    (air : C FBB ExtF) {r1 r2 : ℕ}
    (hbits :
      ∀ slot bit, slot < 4 → bit < 32 →
        work_vars_a air slot bit r1 = work_vars_a air slot bit r2 ∧
        work_vars_e air slot bit r1 = work_vars_e air slot bit r2) :
    carriedState air r1 = carriedState air r2 := by
  have ha : ∀ slot, slot < 4 → aWord air r1 slot = aWord air r2 slot := by
    intro slot hslot
    rw [aWord_eq_bitsWordToUInt32, aWord_eq_bitsWordToUInt32]
    have hword : aBitsWord air r1 slot = aBitsWord air r2 slot := by
      funext i
      exact (hbits slot i.val hslot i.isLt).1
    exact congrArg bitsWordToUInt32 hword
  have he : ∀ slot, slot < 4 → eWord air r1 slot = eWord air r2 slot := by
    intro slot hslot
    rw [eWord_eq_bitsWordToUInt32, eWord_eq_bitsWordToUInt32]
    have hword : eBitsWord air r1 slot = eBitsWord air r2 slot := by
      funext i
      exact (hbits slot i.val hslot i.isLt).2
    exact congrArg bitsWordToUInt32 hword
  rw [carriedState, carriedState, WorkingVars.mk.injEq]
  exact ⟨ha 3 (by omega), ha 2 (by omega), ha 1 (by omega), ha 0 (by omega),
    he 3 (by omega), he 2 (by omega), he 1 (by omega), he 0 (by omega)⟩

private theorem carriedState_eq_next_of_padding
    (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hnext_pad :
      (1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row))) = 1)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    carriedState air row = carriedState air (nextRow air row) := by
  apply carriedState_eq_of_workvar_bits_eq
  intro slot bit hslot hbit
  exact paddingPreservesWorkVars_of_constraints air row hrot hc hrow hnext_pad slot bit hslot hbit

private theorem digest_row_send_key_one_implies_next_padding
    (air : C FBB ExtF) (row : ℕ)
    (htrace_fit : traceLengthFitsField air)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hdigest : is_digest_row air row = 1)
    (hkey : private_bus_next_gbi air row = 1) :
    (1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row))) = 1 := by
  have hrow_lt : row < Circuit.last_row air := digest_row_lt_last_row air row hc hrow hdigest
  rcases hc row with ⟨_, _, ht, _, _, _, _, _⟩
  have hnext_digest0 : is_digest_row air (nextRow air row) = 0 :=
    digest_implies_next_not_digest air row hrow hrot ht hdigest
  have hf_next : flag_constraints air (nextRow air row) := (hc (nextRow air row)).1
  rcases is_round_row_boolean air (nextRow air row) hf_next with hnext_round0 | hnext_round1
  · simpa [hnext_round0, hnext_digest0]
  · have hnext_pad0 : next_padding_flag air row = 0 := by
      simp [next_padding_flag, next_is_round_row_eq_nextRow air hrot row hrow,
        next_is_digest_row_eq_nextRow air hrot row hrow, hnext_round1, hnext_digest0]
    have hgbi_eq_zero : global_block_idx air row = 0 := by
      have hkey' : global_block_idx air row + 1 = 0 + 1 := by
        simpa [private_bus_next_gbi, hnext_pad0] using hkey
      exact add_right_cancel hkey'
    exact False.elim
      (supported_real_row_global_block_idx_ne_zero air htrace_fit hrot hc row hrow (Or.inr hdigest)
        hgbi_eq_zero)

private theorem carriedState_eq_last_row_of_padding_suffix
    (air : C FBB ExtF)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    ∀ row, row < Circuit.last_row air →
      (1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row))) = 1 →
      carriedState air row = carriedState air (Circuit.last_row air) := by
  intro row hrow hnext_pad
  generalize hd : Circuit.last_row air - row = d
  induction d generalizing row with
  | zero =>
      omega
  | succ d ih =>
      have hstep : carriedState air row = carriedState air (nextRow air row) :=
        carriedState_eq_next_of_padding air row hrow.le hnext_pad hrot hc
      by_cases hlast : row + 1 = Circuit.last_row air
      · simpa [nextRow, hrow.ne, hlast] using hstep
      · have hnext_lt : row + 1 < Circuit.last_row air := by omega
        have hf_next : flag_constraints air (nextRow air row) := (hc (nextRow air row)).1
        have hpad_next :
            is_round_row air (nextRow air row) = 0 ∧
              is_digest_row air (nextRow air row) = 0 :=
          next_row_padding_of_next_padding_eq_one air row hf_next hnext_pad
        rcases hc (row + 1) with ⟨hf_row1, _, ht_row1, _, _, _, _, _⟩
        have hpad_row2 := padding_implies_next_padding air (row + 1) hnext_lt hrot ht_row1
          (hc (nextRow air (row + 1))).1
          (by simpa [nextRow, hrow.ne] using hpad_next.1)
          (by simpa [nextRow, hrow.ne] using hpad_next.2)
        have hnext_pad' :
            (1 - (is_round_row air (nextRow air (row + 1)) +
              is_digest_row air (nextRow air (row + 1)))) = 1 := by
          simp [hpad_row2.1, hpad_row2.2]
        have hd' : Circuit.last_row air - (row + 1) = d := by
          omega
        have hrec := ih (row + 1) hnext_lt hnext_pad' hd'
        calc
          carriedState air row = carriedState air (row + 1) := by
            simpa [nextRow, hrow.ne] using hstep
          _ = carriedState air (Circuit.last_row air) := hrec

private theorem digest_prev_hash_eq_start_nonwrap
    (air : C FBB ExtF) (start : ℕ)
    (hstart : start ≠ 0)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (htrace_fit : traceLengthFitsField air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air) :
    digestPrevHashLimbRange air (start + 16) ∧
      digestPrevHashState air (start + 16) = blockStartState air start := by
  let prev := prevRow air start
  have h_private :=
    privateBusChainingSupported_of_rawPermutationSemantics
      air hrot hc h_raw_perm htrace_fit huniq_send
  have hprev_eq : prev = start - 1 := by
    simp [prev, prevRow, hstart]
  have hprev_lt : prev < Circuit.last_row air := by
    dsimp [prev, blockWindowSupported] at *
    omega
  have hprev_next : nextRow air prev = start := by
    rw [hprev_eq]
    have hsub : start - 1 + 1 = start := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hstart))
    have hlt : start - 1 < Circuit.last_row air := by
      simpa [hprev_eq] using hprev_lt
    simp [nextRow, hlt.ne, hsub]
  rcases hshape with ⟨hprev_shape, hround_rows, _, _, hdigest_row⟩
  have hround_start : is_round_row air start = 1 := (hround_rows 0 (by omega)).2.1
  have hdigest_start : is_digest_row air start = 0 := (hround_rows 0 (by omega)).2.2
  have hf_start : flag_constraints air start := (hc start).1
  rcases hc prev with ⟨hf_prev, hbits_prev, ht_prev, _, _, _, _, _⟩
  have hdigest_prev : is_digest_row air prev = 1 := by
    rcases hprev_shape with hsel16 | hsel17
    · exact (is_digest_iff_selector_eq_16 air prev hf_prev).2 hsel16
    · have hround_prev0 : is_round_row air prev = 0 := by
        rcases is_round_row_boolean air prev hf_prev with hround0 | hround1
        · exact hround0
        · rcases (is_round_iff_selector_lt_16 air prev hf_prev).mp hround1 with ⟨n, hn, hseln⟩
          have : (((n : ℕ) : FBB)) = 17 := by
            calc
              (((n : ℕ) : FBB)) = encoder_selector_idx air prev := hseln.symm
              _ = 17 := hsel17
          exact False.elim ((by decide : ∀ n : ℕ, n < 16 → (((n : ℕ) : FBB)) ≠ 17) n hn this)
      have hdigest_prev0 : is_digest_row air prev = 0 := by
        rcases is_digest_row_boolean air prev hf_prev with hdig0 | hdig1
        · exact hdig0
        · have hsel16 := (is_digest_iff_selector_eq_16 air prev hf_prev).mp hdig1
          have : (16 : FBB) = 17 := by
            calc
              (16 : FBB) = encoder_selector_idx air prev := hsel16.symm
              _ = 17 := hsel17
          exact False.elim ((by decide : (16 : FBB) ≠ 17) this)
      have hnext_pad := padding_implies_next_padding air prev hprev_lt hrot ht_prev
        (by simpa [hprev_next] using hf_start)
        hround_prev0 hdigest_prev0
      have : (0 : FBB) = 1 := by simpa [hprev_next, hround_start] using hnext_pad.1.symm
      exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
  have hnext_round_prev : is_round_row air (nextRow air prev) = 1 := by
    simpa [hprev_next] using hround_start
  have hnext_digest_prev : is_digest_row air (nextRow air prev) = 0 := by
    simpa [hprev_next] using hdigest_start
  have hnot_last : next_padding_flag air prev = 0 := by
    simp [next_padding_flag, next_is_round_row_eq_nextRow air hrot prev hprev_lt.le,
      next_is_digest_row_eq_nextRow air hrot prev hprev_lt.le, hnext_round_prev, hnext_digest_prev]
  have hgbi_start : global_block_idx air start = global_block_idx air prev + 1 := by
    simpa [hprev_next] using
      block_idx_transition air prev hprev_lt hrot ht_prev hdigest_prev hnext_round_prev
  have hround_gbi :
      ∀ offset, offset < 16 →
        global_block_idx air (start + offset) = global_block_idx air start := by
    intro offset hoffset
    induction offset with
    | zero =>
        simp
    | succ offset ih =>
        have hrow_lt : start + offset < Circuit.last_row air := by
          dsimp [blockWindowSupported] at hwindow
          omega
        rcases hc (start + offset) with ⟨_, _, ht, _, _, _, _, _⟩
        have hround := (hround_rows offset (by omega)).2.1
        have hstep :
            global_block_idx air (start + (offset + 1)) =
              global_block_idx air (start + offset) := by
          simpa [Nat.add_assoc, nextRow, hrow_lt.ne] using
            block_idx_preserved_on_round air (start + offset) hrow_lt hrot ht hround
        calc
          global_block_idx air (start + (offset + 1)) =
              global_block_idx air (start + offset) := hstep
          _ = global_block_idx air start := ih (by omega)
  have hdigest_gbi : global_block_idx air (start + 16) = global_block_idx air prev + 1 := by
    have hrow15_lt : start + 15 < Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    rcases hc (start + 15) with ⟨_, _, ht15, _, _, _, _, _⟩
    have hround15 : is_round_row air (start + 15) = 1 := (hround_rows 15 (by omega)).2.1
    calc
      global_block_idx air (start + 16) = global_block_idx air (start + 15) := by
        simpa [nextRow, hrow15_lt.ne, Nat.add_assoc] using
          block_idx_preserved_on_round air (start + 15) hrow15_lt hrot ht15 hround15
      _ = global_block_idx air start := hround_gbi 15 (by omega)
      _ = global_block_idx air prev + 1 := hgbi_start
  have hdigest_valid : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  rcases block_chaining_of_private_bus air prev (start + 16) h_private hprev_lt.le hdigest_valid
      hdigest_prev hdigest_row hdigest_gbi hnot_last with ⟨hchain, _⟩
  have hbb_prev : allWorkVarBitsBoolean air prev := allWorkVarBitsBoolean_of_constraints air prev hbits_prev
  have hrange : digestPrevHashLimbRange air (start + 16) := by
    intro word limb hword hlimb
    calc
      (prev_hash air word limb (start + 16)).val =
          (composed_hash_u16 air word limb prev).val := by
            rw [(hchain word limb hword hlimb).symm]
      _ < 2 ^ 16 := composed_hash_u16_range air prev word limb hbb_prev hword hlimb
  have hword_eq :
      ∀ word, word < 8 →
        digestPrevHashWord air (start + 16) word = digestWorkVarWord air prev word := by
    intro word hword
    have hlo :
        digestPrevHashLo16 air (start + 16) word = digestWorkVarLo16 air prev word := by
      calc
        digestPrevHashLo16 air (start + 16) word = prev_hash air word 0 (start + 16) := by rfl
        _ = composed_hash_u16 air word 0 prev := (hchain word 0 hword (by omega)).symm
        _ = digestWorkVarLo16 air prev word := by
            simpa using composed_hash_eq_digestWorkVarLimb air prev word 0 hword (by omega)
    have hhi :
        digestPrevHashHi16 air (start + 16) word = digestWorkVarHi16 air prev word := by
      calc
        digestPrevHashHi16 air (start + 16) word = prev_hash air word 1 (start + 16) := by rfl
        _ = composed_hash_u16 air word 1 prev := (hchain word 1 hword (by omega)).symm
        _ = digestWorkVarHi16 air prev word := by
            simpa using composed_hash_eq_digestWorkVarLimb air prev word 1 hword (by omega)
    rw [digestPrevHash_eq_limbs, digestWorkVar_eq_limbs air prev word hbb_prev, hlo, hhi]
  refine ⟨hrange, ?_⟩
  rw [digestPrevHashState, blockStartState, blockStateRow_zero, carriedState, WorkingVars.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 0 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 1 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 2 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 3 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 4 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 5 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 6 (by omega)
  · simpa [prev, prevRow, hstart, digestWorkVarWord] using hword_eq 7 (by omega)

/-- The wrapped first block (`start = 0`) also gets its chaining state from the
    private bus once the sender with key `1` is identified and its chaining hash
    is transported across the padding suffix to `Circuit.last_row`. -/
private theorem digest_prev_hash_eq_start_wrap
    (air : C FBB ExtF)
    (hwindow : blockWindowSupported air 0)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air 0)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (htrace_fit : traceLengthFitsField air) :
    digestPrevHashLimbRange air 16 ∧
      digestPrevHashState air 16 = blockStartState air 0 := by
  rcases hshape with ⟨_, hround_rows, _, _, hdigest_row⟩
  have hperm :=
    privateBusEnabledReceiveSendPerm_of_rawPermutationSemantics air hrot hc h_raw_perm htrace_fit
  have hcover := privateBusReceiveCovered_of_permutation air hc hperm
  have hdigest_valid : 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  rcases hcover 16 hdigest_valid hdigest_row with ⟨sendRow, hsend_valid, hsend_dig, hmsg⟩
  have hsend_key : private_bus_next_gbi air sendRow = global_block_idx air 16 := by
    exact privateBus_send_eq_recv_implies_key_eq (air := air) (sendRow := sendRow) (recvRow := 16) hmsg
  have hgbi0 : global_block_idx air 0 = 1 := by
    rcases hc 0 with ⟨_, _, ht0, _, _, _, _, _⟩
    rcases ht0 with ⟨_, _, _, _, _, _, _, h278, _, _, _⟩
    have hgbi0_sub : global_block_idx air 0 - 1 = 0 := by
      have h278c : constraint_278 air 0 := (constraint_278_of_extraction air 0).mp h278
      simpa [constraint_278, Circuit.isFirstRow] using h278c
    exact sub_eq_zero.mp hgbi0_sub
  have hround_gbi :
      ∀ offset, offset < 16 →
        global_block_idx air offset = global_block_idx air 0 := by
    intro offset hoffset
    induction offset with
    | zero =>
        simp
    | succ offset ih =>
        have hrow_lt : offset < Circuit.last_row air := by
          dsimp [blockWindowSupported] at hwindow
          omega
        rcases hc offset with ⟨_, _, ht, _, _, _, _, _⟩
        have hround : is_round_row air offset = 1 := by
          simpa [Nat.zero_add] using (hround_rows offset (by omega)).2.1
        have hstep :
            global_block_idx air (offset + 1) = global_block_idx air offset := by
          simpa [nextRow, hrow_lt.ne] using
            block_idx_preserved_on_round air offset hrow_lt hrot ht hround
        calc
          global_block_idx air (offset + 1) = global_block_idx air offset := hstep
          _ = global_block_idx air 0 := ih (by omega)
  have hgbi16 : global_block_idx air 16 = 1 := by
    have hrow15_lt : 15 < Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    rcases hc 15 with ⟨_, _, ht15, _, _, _, _, _⟩
    have hround15 : is_round_row air 15 = 1 := (hround_rows 15 (by omega)).2.1
    calc
      global_block_idx air 16 = global_block_idx air 15 := by
        simpa [nextRow, hrow15_lt.ne] using
          block_idx_preserved_on_round air 15 hrow15_lt hrot ht15 hround15
      _ = global_block_idx air 0 := hround_gbi 15 (by omega)
      _ = 1 := hgbi0
  have hsend_key_one : private_bus_next_gbi air sendRow = 1 := by
    calc
      private_bus_next_gbi air sendRow = global_block_idx air 16 := hsend_key
      _ = 1 := hgbi16
  have hsend_next_pad :
      1 - (is_round_row air (nextRow air sendRow) + is_digest_row air (nextRow air sendRow)) = 1 :=
    digest_row_send_key_one_implies_next_padding
      air sendRow htrace_fit hsend_valid hrot hc hsend_dig hsend_key_one
  have hsend_lt : sendRow < Circuit.last_row air := by
    exact digest_row_lt_last_row air sendRow hc hsend_valid hsend_dig
  have hcarry_last : carriedState air sendRow = carriedState air (Circuit.last_row air) :=
    carriedState_eq_last_row_of_padding_suffix air hrot hc sendRow hsend_lt hsend_next_pad
  have hbb_send : allWorkVarBitsBoolean air sendRow := by
    exact allWorkVarBitsBoolean_of_constraints air sendRow (hc sendRow).2.1
  have hrecv_eq :
      ∀ word limb, word < 8 → limb < 2 →
        prev_hash air word limb 16 = composed_hash_u16 air word limb sendRow := by
    intro word limb hword hlimb
    have hentry := congrArg (fun xs => xs[2 * word + limb]?) hmsg
    simpa [privateBus_send_data_get?_hash air sendRow word limb hword hlimb,
      privateBus_recv_data_get?_prev_hash air 16 word limb hword hlimb] using hentry.symm
  have hrange : digestPrevHashLimbRange air 16 := by
    intro word limb hword hlimb
    calc
      (prev_hash air word limb 16).val = (composed_hash_u16 air word limb sendRow).val := by
        rw [hrecv_eq word limb hword hlimb]
      _ < 2 ^ 16 := composed_hash_u16_range air sendRow word limb hbb_send hword hlimb
  have hword_eq :
      ∀ word, word < 8 →
        digestPrevHashWord air 16 word = digestWorkVarWord air sendRow word := by
    intro word hword
    have hlo : digestPrevHashLo16 air 16 word = digestWorkVarLo16 air sendRow word := by
      calc
        digestPrevHashLo16 air 16 word = prev_hash air word 0 16 := by rfl
        _ = composed_hash_u16 air word 0 sendRow := hrecv_eq word 0 hword (by omega)
        _ = digestWorkVarLo16 air sendRow word := by
            simpa using composed_hash_eq_digestWorkVarLimb air sendRow word 0 hword (by omega)
    have hhi : digestPrevHashHi16 air 16 word = digestWorkVarHi16 air sendRow word := by
      calc
        digestPrevHashHi16 air 16 word = prev_hash air word 1 16 := by rfl
        _ = composed_hash_u16 air word 1 sendRow := hrecv_eq word 1 hword (by omega)
        _ = digestWorkVarHi16 air sendRow word := by
            simpa using composed_hash_eq_digestWorkVarLimb air sendRow word 1 hword (by omega)
    rw [digestPrevHash_eq_limbs, digestWorkVar_eq_limbs air sendRow word hbb_send, hlo, hhi]
  refine ⟨hrange, ?_⟩
  calc
    digestPrevHashState air 16 = carriedState air sendRow := by
      rw [digestPrevHashState, carriedState, WorkingVars.mk.injEq]
      exact ⟨by simpa [digestWorkVarWord] using hword_eq 0 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 1 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 2 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 3 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 4 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 5 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 6 (by omega),
        by simpa [digestWorkVarWord] using hword_eq 7 (by omega)⟩
    _ = carriedState air (Circuit.last_row air) := hcarry_last
    _ = blockStartState air 0 := by
      simp [blockStartState, blockStateRow]

/-- The prev_hash at the digest row equals the block's start state.
    This requires bus/interaction constraints beyond polynomial constraints.
    The wrapped first block additionally needs the field no-wrap bound used to
    rule out spurious `global_block_idx = 0` real rows. -/
theorem digest_prev_hash_eq_start (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air)
    (htrace_fit : traceLengthFitsField air) :
    digestPrevHashLimbRange air (start + 16) ∧
      digestPrevHashState air (start + 16) = blockStartState air start := by
  by_cases hstart : start = 0
  · subst hstart
    exact digest_prev_hash_eq_start_wrap air hwindow hrot hshape hc h_raw_perm htrace_fit
  · exact digest_prev_hash_eq_start_nonwrap air start hstart hwindow hrot hshape hc
      h_raw_perm htrace_fit huniq_send

/-! ## D6: Full digest correctness -/

/-- All 8 words satisfy the local digest addition:
    `final_hash = digestPrevHashState + end_state`.

    This is the exact arithmetic consequence of the digest-row constraints.
    Converting `digestPrevHashState` to `blockStartState` is a separate bus-side
    step handled by `digest_prev_hash_eq_start`. -/
theorem digest_final_hash_correct (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_prev_range : digestPrevHashLimbRange air (start + 16))
    (h_wf_prev : bitwise_lookup_send_properties air (start + 15)) :
    let prevState := digestPrevHashState air (start + 16)
    let endState := carriedState air (start + 15)
    digestFinalHashState air (start + 16) = prevState.add endState := by
  dsimp
  have h0 := digest_word_addition_uint32 air start 0 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h1 := digest_word_addition_uint32 air start 1 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h2 := digest_word_addition_uint32 air start 2 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h3 := digest_word_addition_uint32 air start 3 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h4 := digest_word_addition_uint32 air start 4 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h5 := digest_word_addition_uint32 air start 5 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h6 := digest_word_addition_uint32 air start 6 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h7 := digest_word_addition_uint32 air start 7 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  rw [digestFinalHashState, digestPrevHashState, carriedState, WorkingVars.add, WorkingVars.mk.injEq]
  exact ⟨by simpa [digestWorkVarWord] using h0,
    by simpa [digestWorkVarWord] using h1,
    by simpa [digestWorkVarWord] using h2,
    by simpa [digestWorkVarWord] using h3,
    by simpa [digestWorkVarWord] using h4,
    by simpa [digestWorkVarWord] using h5,
    by simpa [digestWorkVarWord] using h6,
    by simpa [digestWorkVarWord] using h7⟩

/-- Full digest row correctness: prev_hash and final_hash are both correct. -/
theorem digest_row_correct (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air)
    (htrace_fit : traceLengthFitsField air)
    (h_wf_prev : bitwise_lookup_send_properties air (start + 15)) :
    digestPrevHashState air (start + 16) = blockStartState air start ∧
    digestFinalHashState air (start + 16) =
      (blockStartState air start).add (carriedState air (start + 15)) := by
  rcases digest_prev_hash_eq_start air start hwindow hrot hshape hc
      h_raw_perm huniq_send htrace_fit with
    ⟨hprev_range, hprev⟩
  have hfinal := digest_final_hash_correct air start hwindow hrot hshape hc hprev_range h_wf_prev
  refine ⟨hprev, ?_⟩
  simpa [hprev] using hfinal

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
