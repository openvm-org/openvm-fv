/- 
  Layer D: Digest Row Correctness

  Combined SHA-512 digest carry proofs, work-variable projections,
  final-hash bridging, and end-to-end digest-row theorems.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Bus.Facts
import VmExtensions.Constraints.Sha2BlockHasherSubAirBus_sha512
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.BitsFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.SelectorFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.TraceFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.PaddingFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.Defs
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.Semantics

set_option autoImplicit false

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints
open Sha2BlockHasherVmAir_sha512.Soundness.BusFacts

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

-- ============================================================
-- DigestCarryBasics: shared helper lemmas
-- ============================================================

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

theorem compose_a_u16_eq (air : C FBB ExtF) (row slot limb : ℕ)
    (hlimb : limb < 4) :
    compose_a_u16 air slot limb row =
      composeU16Limb (aBitsWord air row slot) ⟨limb, hlimb⟩ := by
  rw [compose_a_u16, composeU16Limb_range_eq]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hidx : limb * 16 + i = i + 16 * limb := by omega
  simp [aBitsWord, Finset.mem_range.mp hi, hidx]

theorem compose_e_u16_eq (air : C FBB ExtF) (row slot limb : ℕ)
    (hlimb : limb < 4) :
    compose_e_u16 air slot limb row =
      composeU16Limb (eBitsWord air row slot) ⟨limb, hlimb⟩ := by
  rw [compose_e_u16, composeU16Limb_range_eq]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hidx : limb * 16 + i = i + 16 * limb := by omega
  simp [eBitsWord, Finset.mem_range.mp hi, hidx]

theorem digestCarry_mul_pow_eq (x : FBB) :
    ((2013235201 : FBB) * x) * (2 ^ 16 : ℕ) = x := by
  have hinv : (2013235201 : FBB) * (2 ^ 16 : ℕ) = 1 := by
    decide
  calc
    ((2013235201 : FBB) * x) * (2 ^ 16 : ℕ) = x * ((2013235201 : FBB) * (2 ^ 16 : ℕ)) := by
      ring
    _ = x * 1 := by rw [hinv]
    _ = x := by ring

theorem next_prev_hash_u16_eq
    (air : C FBB ExtF) (row word limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hlimb : limb < 4) :
    next_prev_hash air word limb row =
      digestPrevHashU16Limb air (nextRow air row) word limb := by
  simpa [digestPrevHashU16Limb, hlimb] using
    next_prev_hash_eq_nextRow air hrot word limb row hrow

-- ============================================================
-- Carry-0 boolean extraction (words 0-7)
-- ============================================================

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word0
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1448 air row := by
  rcases hd with ⟨h1400_1449, _h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1400_1449] at h1400_1449
  tauto

private theorem digest_work_var_u16_expr_word0_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 0 0 row =
      work_vars_a air 3 0 row + work_vars_a air 3 1 row * 2 +
      work_vars_a air 3 2 row * 4 + work_vars_a air 3 3 row * 8 +
      work_vars_a air 3 4 row * 16 + work_vars_a air 3 5 row * 32 +
      work_vars_a air 3 6 row * 64 + work_vars_a air 3 7 row * 128 +
      work_vars_a air 3 8 row * 256 + work_vars_a air 3 9 row * 512 +
      work_vars_a air 3 10 row * 1024 + work_vars_a air 3 11 row * 2048 +
      work_vars_a air 3 12 row * 4096 + work_vars_a air 3 13 row * 8192 +
      work_vars_a air 3 14 row * 16384 + work_vars_a air 3 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

theorem digest_carry0_boolean_word0
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 0 row * (digest_carry0_expr air 0 row - 1)) = 0 := by
  simpa only [constraint_1448, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1448,
    digest_carry0_expr, digest_work_var_u16_expr_word0_limb0, next_digest_final_hash_u16_expr,
    next_is_digest_row, next_prev_hash, next_final_hash, work_vars_a] using
    digest_carry0_raw_word0 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word1
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1452 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.1

private theorem digest_work_var_u16_expr_word1_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 1 0 row =
      work_vars_a air 2 0 row + work_vars_a air 2 1 row * 2 +
      work_vars_a air 2 2 row * 4 + work_vars_a air 2 3 row * 8 +
      work_vars_a air 2 4 row * 16 + work_vars_a air 2 5 row * 32 +
      work_vars_a air 2 6 row * 64 + work_vars_a air 2 7 row * 128 +
      work_vars_a air 2 8 row * 256 + work_vars_a air 2 9 row * 512 +
      work_vars_a air 2 10 row * 1024 + work_vars_a air 2 11 row * 2048 +
      work_vars_a air 2 12 row * 4096 + work_vars_a air 2 13 row * 8192 +
      work_vars_a air 2 14 row * 16384 + work_vars_a air 2 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word1_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 1 0 row =
      Circuit.main air (id := 0) (column := 683) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word1_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 1 0 row =
      Circuit.main air (id := 0) (column := 623) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 624) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

private theorem digest_carry0_boolean_word1_goal
    (air : C FBB ExtF) (row : ℕ) :
    (next_is_digest_row air row *
      (digest_carry0_expr air 1 row * (digest_carry0_expr air 1 row - 1)) = 0) =
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1452 air row := by
  rw [digest_carry0_expr, digest_work_var_u16_expr_word1_limb0, next_prev_hash_word1_limb0,
    next_digest_final_hash_u16_expr_word1_limb0, next_is_digest_row, work_vars_a]
  rfl

theorem digest_carry0_boolean_word1
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 1 row * (digest_carry0_expr air 1 row - 1)) = 0 := by
  rw [digest_carry0_boolean_word1_goal]
  exact digest_carry0_raw_word1 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word2
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1456 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  tauto

private theorem digest_work_var_u16_expr_word2_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 2 0 row =
      work_vars_a air 1 0 row + work_vars_a air 1 1 row * 2 +
      work_vars_a air 1 2 row * 4 + work_vars_a air 1 3 row * 8 +
      work_vars_a air 1 4 row * 16 + work_vars_a air 1 5 row * 32 +
      work_vars_a air 1 6 row * 64 + work_vars_a air 1 7 row * 128 +
      work_vars_a air 1 8 row * 256 + work_vars_a air 1 9 row * 512 +
      work_vars_a air 1 10 row * 1024 + work_vars_a air 1 11 row * 2048 +
      work_vars_a air 1 12 row * 4096 + work_vars_a air 1 13 row * 8192 +
      work_vars_a air 1 14 row * 16384 + work_vars_a air 1 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word2_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 2 0 row =
      Circuit.main air (id := 0) (column := 687) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word2_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 2 0 row =
      Circuit.main air (id := 0) (column := 631) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 632) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry0_boolean_word2
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 2 row * (digest_carry0_expr air 2 row - 1)) = 0 := by
  simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1456, digest_carry0_expr,
    digest_work_var_u16_expr_word2_limb0, next_prev_hash_word2_limb0,
    next_digest_final_hash_u16_expr_word2_limb0, next_is_digest_row, work_vars_a] using
    digest_carry0_raw_word2 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word3
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1460 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  tauto

private theorem digest_work_var_u16_expr_word3_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 3 0 row =
      work_vars_a air 0 0 row + work_vars_a air 0 1 row * 2 +
      work_vars_a air 0 2 row * 4 + work_vars_a air 0 3 row * 8 +
      work_vars_a air 0 4 row * 16 + work_vars_a air 0 5 row * 32 +
      work_vars_a air 0 6 row * 64 + work_vars_a air 0 7 row * 128 +
      work_vars_a air 0 8 row * 256 + work_vars_a air 0 9 row * 512 +
      work_vars_a air 0 10 row * 1024 + work_vars_a air 0 11 row * 2048 +
      work_vars_a air 0 12 row * 4096 + work_vars_a air 0 13 row * 8192 +
      work_vars_a air 0 14 row * 16384 + work_vars_a air 0 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word3_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 3 0 row =
      Circuit.main air (id := 0) (column := 691) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word3_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 3 0 row =
      Circuit.main air (id := 0) (column := 639) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 640) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry0_boolean_word3
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 3 row * (digest_carry0_expr air 3 row - 1)) = 0 := by
  simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1460, digest_carry0_expr,
    digest_work_var_u16_expr_word3_limb0, next_prev_hash_word3_limb0,
    next_digest_final_hash_u16_expr_word3_limb0, next_is_digest_row, work_vars_a] using
    digest_carry0_raw_word3 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word4
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1464 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  tauto

private theorem digest_work_var_u16_expr_word4_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 4 0 row =
      work_vars_e air 3 0 row + work_vars_e air 3 1 row * 2 +
      work_vars_e air 3 2 row * 4 + work_vars_e air 3 3 row * 8 +
      work_vars_e air 3 4 row * 16 + work_vars_e air 3 5 row * 32 +
      work_vars_e air 3 6 row * 64 + work_vars_e air 3 7 row * 128 +
      work_vars_e air 3 8 row * 256 + work_vars_e air 3 9 row * 512 +
      work_vars_e air 3 10 row * 1024 + work_vars_e air 3 11 row * 2048 +
      work_vars_e air 3 12 row * 4096 + work_vars_e air 3 13 row * 8192 +
      work_vars_e air 3 14 row * 16384 + work_vars_e air 3 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word4_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 4 0 row =
      Circuit.main air (id := 0) (column := 695) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word4_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 4 0 row =
      Circuit.main air (id := 0) (column := 647) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 648) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry0_boolean_word4
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 4 row * (digest_carry0_expr air 4 row - 1)) = 0 := by
  simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1464, digest_carry0_expr,
    digest_work_var_u16_expr_word4_limb0, next_prev_hash_word4_limb0,
    next_digest_final_hash_u16_expr_word4_limb0, next_is_digest_row, work_vars_e] using
    digest_carry0_raw_word4 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word5
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1468 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  tauto

private theorem digest_work_var_u16_expr_word5_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 5 0 row =
      work_vars_e air 2 0 row + work_vars_e air 2 1 row * 2 +
      work_vars_e air 2 2 row * 4 + work_vars_e air 2 3 row * 8 +
      work_vars_e air 2 4 row * 16 + work_vars_e air 2 5 row * 32 +
      work_vars_e air 2 6 row * 64 + work_vars_e air 2 7 row * 128 +
      work_vars_e air 2 8 row * 256 + work_vars_e air 2 9 row * 512 +
      work_vars_e air 2 10 row * 1024 + work_vars_e air 2 11 row * 2048 +
      work_vars_e air 2 12 row * 4096 + work_vars_e air 2 13 row * 8192 +
      work_vars_e air 2 14 row * 16384 + work_vars_e air 2 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word5_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 5 0 row =
      Circuit.main air (id := 0) (column := 699) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word5_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 5 0 row =
      Circuit.main air (id := 0) (column := 655) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 656) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry0_boolean_word5
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 5 row * (digest_carry0_expr air 5 row - 1)) = 0 := by
  simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1468, digest_carry0_expr,
    digest_work_var_u16_expr_word5_limb0, next_prev_hash_word5_limb0,
    next_digest_final_hash_u16_expr_word5_limb0, next_is_digest_row, work_vars_e] using
    digest_carry0_raw_word5 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word6
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1472 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  tauto

private theorem digest_work_var_u16_expr_word6_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 6 0 row =
      work_vars_e air 1 0 row + work_vars_e air 1 1 row * 2 +
      work_vars_e air 1 2 row * 4 + work_vars_e air 1 3 row * 8 +
      work_vars_e air 1 4 row * 16 + work_vars_e air 1 5 row * 32 +
      work_vars_e air 1 6 row * 64 + work_vars_e air 1 7 row * 128 +
      work_vars_e air 1 8 row * 256 + work_vars_e air 1 9 row * 512 +
      work_vars_e air 1 10 row * 1024 + work_vars_e air 1 11 row * 2048 +
      work_vars_e air 1 12 row * 4096 + work_vars_e air 1 13 row * 8192 +
      work_vars_e air 1 14 row * 16384 + work_vars_e air 1 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word6_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 6 0 row =
      Circuit.main air (id := 0) (column := 703) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word6_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 6 0 row =
      Circuit.main air (id := 0) (column := 663) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 664) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry0_boolean_word6
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 6 row * (digest_carry0_expr air 6 row - 1)) = 0 := by
  simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1472, digest_carry0_expr,
    digest_work_var_u16_expr_word6_limb0, next_prev_hash_word6_limb0,
    next_digest_final_hash_u16_expr_word6_limb0, next_is_digest_row, work_vars_e] using
    digest_carry0_raw_word6 hd

set_option maxHeartbeats 40000000

private theorem digest_carry0_raw_word7
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1476 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  tauto

private theorem digest_work_var_u16_expr_word7_limb0
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 7 0 row =
      work_vars_e air 0 0 row + work_vars_e air 0 1 row * 2 +
      work_vars_e air 0 2 row * 4 + work_vars_e air 0 3 row * 8 +
      work_vars_e air 0 4 row * 16 + work_vars_e air 0 5 row * 32 +
      work_vars_e air 0 6 row * 64 + work_vars_e air 0 7 row * 128 +
      work_vars_e air 0 8 row * 256 + work_vars_e air 0 9 row * 512 +
      work_vars_e air 0 10 row * 1024 + work_vars_e air 0 11 row * 2048 +
      work_vars_e air 0 12 row * 4096 + work_vars_e air 0 13 row * 8192 +
      work_vars_e air 0 14 row * 16384 + work_vars_e air 0 15 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word7_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 7 0 row =
      Circuit.main air (id := 0) (column := 707) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word7_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 7 0 row =
      Circuit.main air (id := 0) (column := 671) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 672) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry0_boolean_word7
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air 7 row * (digest_carry0_expr air 7 row - 1)) = 0 := by
  simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1476, digest_carry0_expr,
    digest_work_var_u16_expr_word7_limb0, next_prev_hash_word7_limb0,
    next_digest_final_hash_u16_expr_word7_limb0, next_is_digest_row, work_vars_e] using
    digest_carry0_raw_word7 hd

-- ============================================================
-- Carry-1 boolean extraction (words 0-7)
-- ============================================================

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word0
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1449 air row := by
  rcases hd with ⟨h1400_1449, _h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1400_1449] at h1400_1449
  tauto

private theorem digest_work_var_u16_expr_word0_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 0 1 row =
      work_vars_a air 3 16 row +
      work_vars_a air 3 17 row * 2 +
      work_vars_a air 3 18 row * 4 +
      work_vars_a air 3 19 row * 8 +
      work_vars_a air 3 20 row * 16 +
      work_vars_a air 3 21 row * 32 +
      work_vars_a air 3 22 row * 64 +
      work_vars_a air 3 23 row * 128 +
      work_vars_a air 3 24 row * 256 +
      work_vars_a air 3 25 row * 512 +
      work_vars_a air 3 26 row * 1024 +
      work_vars_a air 3 27 row * 2048 +
      work_vars_a air 3 28 row * 4096 +
      work_vars_a air 3 29 row * 8192 +
      work_vars_a air 3 30 row * 16384 +
      work_vars_a air 3 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word0_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 0 0 row =
      Circuit.main air (id := 0) (column := 679) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_prev_hash_word0_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 0 1 row =
      Circuit.main air (id := 0) (column := 680) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word0_limb0
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 0 0 row =
      Circuit.main air (id := 0) (column := 615) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 616) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

private theorem next_digest_final_hash_u16_expr_word0_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 0 1 row =
      Circuit.main air (id := 0) (column := 617) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 618) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word0
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 0 row * (digest_carry1_expr air 0 row - 1)) = 0 := by
  simpa only [constraint_1449, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1449,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word0_limb0,
    digest_work_var_u16_expr_word0_limb1, next_prev_hash_word0_limb0, next_prev_hash_word0_limb1,
    next_digest_final_hash_u16_expr_word0_limb0, next_digest_final_hash_u16_expr_word0_limb1,
    next_is_digest_row, work_vars_a] using
    digest_carry1_raw_word0 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word1
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1453 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.1

private theorem digest_work_var_u16_expr_word1_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 1 1 row =
      work_vars_a air 2 16 row + work_vars_a air 2 17 row * 2 +
      work_vars_a air 2 18 row * 4 + work_vars_a air 2 19 row * 8 +
      work_vars_a air 2 20 row * 16 + work_vars_a air 2 21 row * 32 +
      work_vars_a air 2 22 row * 64 + work_vars_a air 2 23 row * 128 +
      work_vars_a air 2 24 row * 256 + work_vars_a air 2 25 row * 512 +
      work_vars_a air 2 26 row * 1024 + work_vars_a air 2 27 row * 2048 +
      work_vars_a air 2 28 row * 4096 + work_vars_a air 2 29 row * 8192 +
      work_vars_a air 2 30 row * 16384 + work_vars_a air 2 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word1_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 1 1 row =
      Circuit.main air (id := 0) (column := 684) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word1_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 1 1 row =
      Circuit.main air (id := 0) (column := 625) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 626) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word1
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 1 row * (digest_carry1_expr air 1 row - 1)) = 0 := by
  simpa only [constraint_1453, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1453,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word1_limb0,
    digest_work_var_u16_expr_word1_limb1, next_prev_hash_word1_limb0, next_prev_hash_word1_limb1,
    next_digest_final_hash_u16_expr_word1_limb0, next_digest_final_hash_u16_expr_word1_limb1,
    next_is_digest_row, work_vars_a] using
    digest_carry1_raw_word1 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word2
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1457 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.2.2.2.2.1

private theorem digest_work_var_u16_expr_word2_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 2 1 row =
      work_vars_a air 1 16 row +
      work_vars_a air 1 17 row * 2 +
      work_vars_a air 1 18 row * 4 +
      work_vars_a air 1 19 row * 8 +
      work_vars_a air 1 20 row * 16 +
      work_vars_a air 1 21 row * 32 +
      work_vars_a air 1 22 row * 64 +
      work_vars_a air 1 23 row * 128 +
      work_vars_a air 1 24 row * 256 +
      work_vars_a air 1 25 row * 512 +
      work_vars_a air 1 26 row * 1024 +
      work_vars_a air 1 27 row * 2048 +
      work_vars_a air 1 28 row * 4096 +
      work_vars_a air 1 29 row * 8192 +
      work_vars_a air 1 30 row * 16384 +
      work_vars_a air 1 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word2_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 2 1 row =
      Circuit.main air (id := 0) (column := 688) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word2_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 2 1 row =
      Circuit.main air (id := 0) (column := 633) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 634) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word2
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 2 row * (digest_carry1_expr air 2 row - 1)) = 0 := by
  simpa only [constraint_1457, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1457,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word2_limb0,
    digest_work_var_u16_expr_word2_limb1, next_prev_hash_word2_limb0, next_prev_hash_word2_limb1,
    next_digest_final_hash_u16_expr_word2_limb0, next_digest_final_hash_u16_expr_word2_limb1,
    next_is_digest_row, work_vars_a] using
    digest_carry1_raw_word2 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word3
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1461 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.2.2.2.2.2.2.2.2.1

private theorem digest_work_var_u16_expr_word3_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 3 1 row =
      work_vars_a air 0 16 row +
      work_vars_a air 0 17 row * 2 +
      work_vars_a air 0 18 row * 4 +
      work_vars_a air 0 19 row * 8 +
      work_vars_a air 0 20 row * 16 +
      work_vars_a air 0 21 row * 32 +
      work_vars_a air 0 22 row * 64 +
      work_vars_a air 0 23 row * 128 +
      work_vars_a air 0 24 row * 256 +
      work_vars_a air 0 25 row * 512 +
      work_vars_a air 0 26 row * 1024 +
      work_vars_a air 0 27 row * 2048 +
      work_vars_a air 0 28 row * 4096 +
      work_vars_a air 0 29 row * 8192 +
      work_vars_a air 0 30 row * 16384 +
      work_vars_a air 0 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word3_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 3 1 row =
      Circuit.main air (id := 0) (column := 692) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word3_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 3 1 row =
      Circuit.main air (id := 0) (column := 641) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 642) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word3
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 3 row * (digest_carry1_expr air 3 row - 1)) = 0 := by
  simpa only [constraint_1461, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1461,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word3_limb0,
    digest_work_var_u16_expr_word3_limb1, next_prev_hash_word3_limb0, next_prev_hash_word3_limb1,
    next_digest_final_hash_u16_expr_word3_limb0, next_digest_final_hash_u16_expr_word3_limb1,
    next_is_digest_row, work_vars_a] using
    digest_carry1_raw_word3 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word4
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1465 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem digest_work_var_u16_expr_word4_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 4 1 row =
      work_vars_e air 3 16 row +
      work_vars_e air 3 17 row * 2 +
      work_vars_e air 3 18 row * 4 +
      work_vars_e air 3 19 row * 8 +
      work_vars_e air 3 20 row * 16 +
      work_vars_e air 3 21 row * 32 +
      work_vars_e air 3 22 row * 64 +
      work_vars_e air 3 23 row * 128 +
      work_vars_e air 3 24 row * 256 +
      work_vars_e air 3 25 row * 512 +
      work_vars_e air 3 26 row * 1024 +
      work_vars_e air 3 27 row * 2048 +
      work_vars_e air 3 28 row * 4096 +
      work_vars_e air 3 29 row * 8192 +
      work_vars_e air 3 30 row * 16384 +
      work_vars_e air 3 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word4_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 4 1 row =
      Circuit.main air (id := 0) (column := 696) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word4_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 4 1 row =
      Circuit.main air (id := 0) (column := 649) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 650) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word4
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 4 row * (digest_carry1_expr air 4 row - 1)) = 0 := by
  simpa only [constraint_1465, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1465,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word4_limb0,
    digest_work_var_u16_expr_word4_limb1, next_prev_hash_word4_limb0, next_prev_hash_word4_limb1,
    next_digest_final_hash_u16_expr_word4_limb0, next_digest_final_hash_u16_expr_word4_limb1,
    next_is_digest_row, work_vars_e] using
    digest_carry1_raw_word4 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word5
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1469 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem digest_work_var_u16_expr_word5_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 5 1 row =
      work_vars_e air 2 16 row +
      work_vars_e air 2 17 row * 2 +
      work_vars_e air 2 18 row * 4 +
      work_vars_e air 2 19 row * 8 +
      work_vars_e air 2 20 row * 16 +
      work_vars_e air 2 21 row * 32 +
      work_vars_e air 2 22 row * 64 +
      work_vars_e air 2 23 row * 128 +
      work_vars_e air 2 24 row * 256 +
      work_vars_e air 2 25 row * 512 +
      work_vars_e air 2 26 row * 1024 +
      work_vars_e air 2 27 row * 2048 +
      work_vars_e air 2 28 row * 4096 +
      work_vars_e air 2 29 row * 8192 +
      work_vars_e air 2 30 row * 16384 +
      work_vars_e air 2 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word5_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 5 1 row =
      Circuit.main air (id := 0) (column := 700) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word5_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 5 1 row =
      Circuit.main air (id := 0) (column := 657) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 658) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word5
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 5 row * (digest_carry1_expr air 5 row - 1)) = 0 := by
  simpa only [constraint_1469, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1469,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word5_limb0,
    digest_work_var_u16_expr_word5_limb1, next_prev_hash_word5_limb0, next_prev_hash_word5_limb1,
    next_digest_final_hash_u16_expr_word5_limb0, next_digest_final_hash_u16_expr_word5_limb1,
    next_is_digest_row, work_vars_e] using
    digest_carry1_raw_word5 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word6
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1473 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem digest_work_var_u16_expr_word6_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 6 1 row =
      work_vars_e air 1 16 row +
      work_vars_e air 1 17 row * 2 +
      work_vars_e air 1 18 row * 4 +
      work_vars_e air 1 19 row * 8 +
      work_vars_e air 1 20 row * 16 +
      work_vars_e air 1 21 row * 32 +
      work_vars_e air 1 22 row * 64 +
      work_vars_e air 1 23 row * 128 +
      work_vars_e air 1 24 row * 256 +
      work_vars_e air 1 25 row * 512 +
      work_vars_e air 1 26 row * 1024 +
      work_vars_e air 1 27 row * 2048 +
      work_vars_e air 1 28 row * 4096 +
      work_vars_e air 1 29 row * 8192 +
      work_vars_e air 1 30 row * 16384 +
      work_vars_e air 1 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word6_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 6 1 row =
      Circuit.main air (id := 0) (column := 704) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word6_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 6 1 row =
      Circuit.main air (id := 0) (column := 665) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 666) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word6
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 6 row * (digest_carry1_expr air 6 row - 1)) = 0 := by
  simpa only [constraint_1473, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1473,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word6_limb0,
    digest_work_var_u16_expr_word6_limb1, next_prev_hash_word6_limb0, next_prev_hash_word6_limb1,
    next_digest_final_hash_u16_expr_word6_limb0, next_digest_final_hash_u16_expr_word6_limb1,
    next_is_digest_row, work_vars_e] using
    digest_carry1_raw_word6 hd

set_option maxHeartbeats 40000000

private theorem digest_carry1_raw_word7
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1477 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem digest_work_var_u16_expr_word7_limb1
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 7 1 row =
      work_vars_e air 0 16 row +
      work_vars_e air 0 17 row * 2 +
      work_vars_e air 0 18 row * 4 +
      work_vars_e air 0 19 row * 8 +
      work_vars_e air 0 20 row * 16 +
      work_vars_e air 0 21 row * 32 +
      work_vars_e air 0 22 row * 64 +
      work_vars_e air 0 23 row * 128 +
      work_vars_e air 0 24 row * 256 +
      work_vars_e air 0 25 row * 512 +
      work_vars_e air 0 26 row * 1024 +
      work_vars_e air 0 27 row * 2048 +
      work_vars_e air 0 28 row * 4096 +
      work_vars_e air 0 29 row * 8192 +
      work_vars_e air 0 30 row * 16384 +
      work_vars_e air 0 31 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word7_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 7 1 row =
      Circuit.main air (id := 0) (column := 708) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word7_limb1
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 7 1 row =
      Circuit.main air (id := 0) (column := 673) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 674) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry1_boolean_word7
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air 7 row * (digest_carry1_expr air 7 row - 1)) = 0 := by
  simpa only [constraint_1477, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1477,
    digest_carry0_expr, digest_carry1_expr, digest_work_var_u16_expr_word7_limb0,
    digest_work_var_u16_expr_word7_limb1, next_prev_hash_word7_limb0, next_prev_hash_word7_limb1,
    next_digest_final_hash_u16_expr_word7_limb0, next_digest_final_hash_u16_expr_word7_limb1,
    next_is_digest_row, work_vars_e] using
    digest_carry1_raw_word7 hd

-- ============================================================
-- Carry-2 boolean extraction (words 0-7)
-- ============================================================

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word0
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1450 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  exact h1450_1479.1

private theorem digest_work_var_u16_expr_word0_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 0 2 row =
      work_vars_a air 3 32 row +
      work_vars_a air 3 33 row * 2 +
      work_vars_a air 3 34 row * 4 +
      work_vars_a air 3 35 row * 8 +
      work_vars_a air 3 36 row * 16 +
      work_vars_a air 3 37 row * 32 +
      work_vars_a air 3 38 row * 64 +
      work_vars_a air 3 39 row * 128 +
      work_vars_a air 3 40 row * 256 +
      work_vars_a air 3 41 row * 512 +
      work_vars_a air 3 42 row * 1024 +
      work_vars_a air 3 43 row * 2048 +
      work_vars_a air 3 44 row * 4096 +
      work_vars_a air 3 45 row * 8192 +
      work_vars_a air 3 46 row * 16384 +
      work_vars_a air 3 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word0_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 0 2 row =
      Circuit.main air (id := 0) (column := 681) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word0_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 0 2 row =
      Circuit.main air (id := 0) (column := 619) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 620) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word0
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 0 row * (digest_carry2_expr air 0 row - 1)) = 0 := by
  simpa only [constraint_1450, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1450,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word0_limb0, digest_work_var_u16_expr_word0_limb1,
    digest_work_var_u16_expr_word0_limb2, next_prev_hash_word0_limb0,
    next_prev_hash_word0_limb1, next_prev_hash_word0_limb2,
    next_digest_final_hash_u16_expr_word0_limb0, next_digest_final_hash_u16_expr_word0_limb1,
    next_digest_final_hash_u16_expr_word0_limb2, next_is_digest_row, work_vars_a] using
    digest_carry2_raw_word0 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word1
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1454 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  exact h1454_1479.1

private theorem digest_work_var_u16_expr_word1_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 1 2 row =
      work_vars_a air 2 32 row +
      work_vars_a air 2 33 row * 2 +
      work_vars_a air 2 34 row * 4 +
      work_vars_a air 2 35 row * 8 +
      work_vars_a air 2 36 row * 16 +
      work_vars_a air 2 37 row * 32 +
      work_vars_a air 2 38 row * 64 +
      work_vars_a air 2 39 row * 128 +
      work_vars_a air 2 40 row * 256 +
      work_vars_a air 2 41 row * 512 +
      work_vars_a air 2 42 row * 1024 +
      work_vars_a air 2 43 row * 2048 +
      work_vars_a air 2 44 row * 4096 +
      work_vars_a air 2 45 row * 8192 +
      work_vars_a air 2 46 row * 16384 +
      work_vars_a air 2 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word1_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 1 2 row =
      Circuit.main air (id := 0) (column := 685) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word1_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 1 2 row =
      Circuit.main air (id := 0) (column := 627) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 628) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word1
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 1 row * (digest_carry2_expr air 1 row - 1)) = 0 := by
  simpa only [constraint_1454, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1454,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word1_limb0, digest_work_var_u16_expr_word1_limb1,
    digest_work_var_u16_expr_word1_limb2, next_prev_hash_word1_limb0,
    next_prev_hash_word1_limb1, next_prev_hash_word1_limb2,
    next_digest_final_hash_u16_expr_word1_limb0, next_digest_final_hash_u16_expr_word1_limb1,
    next_digest_final_hash_u16_expr_word1_limb2, next_is_digest_row, work_vars_a] using
    digest_carry2_raw_word1 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word2
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1458 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  have h1458_1479 := h1454_1479.2.2.2.2
  exact h1458_1479.1

private theorem digest_work_var_u16_expr_word2_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 2 2 row =
      work_vars_a air 1 32 row +
      work_vars_a air 1 33 row * 2 +
      work_vars_a air 1 34 row * 4 +
      work_vars_a air 1 35 row * 8 +
      work_vars_a air 1 36 row * 16 +
      work_vars_a air 1 37 row * 32 +
      work_vars_a air 1 38 row * 64 +
      work_vars_a air 1 39 row * 128 +
      work_vars_a air 1 40 row * 256 +
      work_vars_a air 1 41 row * 512 +
      work_vars_a air 1 42 row * 1024 +
      work_vars_a air 1 43 row * 2048 +
      work_vars_a air 1 44 row * 4096 +
      work_vars_a air 1 45 row * 8192 +
      work_vars_a air 1 46 row * 16384 +
      work_vars_a air 1 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word2_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 2 2 row =
      Circuit.main air (id := 0) (column := 689) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word2_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 2 2 row =
      Circuit.main air (id := 0) (column := 635) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 636) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word2
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 2 row * (digest_carry2_expr air 2 row - 1)) = 0 := by
  simpa only [constraint_1458, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1458,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word2_limb0, digest_work_var_u16_expr_word2_limb1,
    digest_work_var_u16_expr_word2_limb2, next_prev_hash_word2_limb0,
    next_prev_hash_word2_limb1, next_prev_hash_word2_limb2,
    next_digest_final_hash_u16_expr_word2_limb0, next_digest_final_hash_u16_expr_word2_limb1,
    next_digest_final_hash_u16_expr_word2_limb2, next_is_digest_row, work_vars_a] using
    digest_carry2_raw_word2 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word3
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1462 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  have h1458_1479 := h1454_1479.2.2.2.2
  have h1462_1479 := h1458_1479.2.2.2.2
  exact h1462_1479.1

private theorem digest_work_var_u16_expr_word3_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 3 2 row =
      work_vars_a air 0 32 row +
      work_vars_a air 0 33 row * 2 +
      work_vars_a air 0 34 row * 4 +
      work_vars_a air 0 35 row * 8 +
      work_vars_a air 0 36 row * 16 +
      work_vars_a air 0 37 row * 32 +
      work_vars_a air 0 38 row * 64 +
      work_vars_a air 0 39 row * 128 +
      work_vars_a air 0 40 row * 256 +
      work_vars_a air 0 41 row * 512 +
      work_vars_a air 0 42 row * 1024 +
      work_vars_a air 0 43 row * 2048 +
      work_vars_a air 0 44 row * 4096 +
      work_vars_a air 0 45 row * 8192 +
      work_vars_a air 0 46 row * 16384 +
      work_vars_a air 0 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word3_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 3 2 row =
      Circuit.main air (id := 0) (column := 693) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word3_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 3 2 row =
      Circuit.main air (id := 0) (column := 643) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 644) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word3
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 3 row * (digest_carry2_expr air 3 row - 1)) = 0 := by
  simpa only [constraint_1462, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1462,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word3_limb0, digest_work_var_u16_expr_word3_limb1,
    digest_work_var_u16_expr_word3_limb2, next_prev_hash_word3_limb0,
    next_prev_hash_word3_limb1, next_prev_hash_word3_limb2,
    next_digest_final_hash_u16_expr_word3_limb0, next_digest_final_hash_u16_expr_word3_limb1,
    next_digest_final_hash_u16_expr_word3_limb2, next_is_digest_row, work_vars_a] using
    digest_carry2_raw_word3 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word4
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1466 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  have h1458_1479 := h1454_1479.2.2.2.2
  have h1462_1479 := h1458_1479.2.2.2.2
  have h1466_1479 := h1462_1479.2.2.2.2
  exact h1466_1479.1

private theorem digest_work_var_u16_expr_word4_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 4 2 row =
      work_vars_e air 3 32 row +
      work_vars_e air 3 33 row * 2 +
      work_vars_e air 3 34 row * 4 +
      work_vars_e air 3 35 row * 8 +
      work_vars_e air 3 36 row * 16 +
      work_vars_e air 3 37 row * 32 +
      work_vars_e air 3 38 row * 64 +
      work_vars_e air 3 39 row * 128 +
      work_vars_e air 3 40 row * 256 +
      work_vars_e air 3 41 row * 512 +
      work_vars_e air 3 42 row * 1024 +
      work_vars_e air 3 43 row * 2048 +
      work_vars_e air 3 44 row * 4096 +
      work_vars_e air 3 45 row * 8192 +
      work_vars_e air 3 46 row * 16384 +
      work_vars_e air 3 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word4_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 4 2 row =
      Circuit.main air (id := 0) (column := 697) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word4_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 4 2 row =
      Circuit.main air (id := 0) (column := 651) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 652) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word4
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 4 row * (digest_carry2_expr air 4 row - 1)) = 0 := by
  simpa only [constraint_1466, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1466,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word4_limb0, digest_work_var_u16_expr_word4_limb1,
    digest_work_var_u16_expr_word4_limb2, next_prev_hash_word4_limb0,
    next_prev_hash_word4_limb1, next_prev_hash_word4_limb2,
    next_digest_final_hash_u16_expr_word4_limb0, next_digest_final_hash_u16_expr_word4_limb1,
    next_digest_final_hash_u16_expr_word4_limb2, next_is_digest_row, work_vars_e] using
    digest_carry2_raw_word4 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word5
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1470 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  have h1458_1479 := h1454_1479.2.2.2.2
  have h1462_1479 := h1458_1479.2.2.2.2
  have h1466_1479 := h1462_1479.2.2.2.2
  have h1470_1479 := h1466_1479.2.2.2.2
  exact h1470_1479.1

private theorem digest_work_var_u16_expr_word5_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 5 2 row =
      work_vars_e air 2 32 row +
      work_vars_e air 2 33 row * 2 +
      work_vars_e air 2 34 row * 4 +
      work_vars_e air 2 35 row * 8 +
      work_vars_e air 2 36 row * 16 +
      work_vars_e air 2 37 row * 32 +
      work_vars_e air 2 38 row * 64 +
      work_vars_e air 2 39 row * 128 +
      work_vars_e air 2 40 row * 256 +
      work_vars_e air 2 41 row * 512 +
      work_vars_e air 2 42 row * 1024 +
      work_vars_e air 2 43 row * 2048 +
      work_vars_e air 2 44 row * 4096 +
      work_vars_e air 2 45 row * 8192 +
      work_vars_e air 2 46 row * 16384 +
      work_vars_e air 2 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word5_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 5 2 row =
      Circuit.main air (id := 0) (column := 701) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word5_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 5 2 row =
      Circuit.main air (id := 0) (column := 659) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 660) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word5
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 5 row * (digest_carry2_expr air 5 row - 1)) = 0 := by
  simpa only [constraint_1470, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1470,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word5_limb0, digest_work_var_u16_expr_word5_limb1,
    digest_work_var_u16_expr_word5_limb2, next_prev_hash_word5_limb0,
    next_prev_hash_word5_limb1, next_prev_hash_word5_limb2,
    next_digest_final_hash_u16_expr_word5_limb0, next_digest_final_hash_u16_expr_word5_limb1,
    next_digest_final_hash_u16_expr_word5_limb2, next_is_digest_row, work_vars_e] using
    digest_carry2_raw_word5 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word6
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1474 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  have h1458_1479 := h1454_1479.2.2.2.2
  have h1462_1479 := h1458_1479.2.2.2.2
  have h1466_1479 := h1462_1479.2.2.2.2
  have h1470_1479 := h1466_1479.2.2.2.2
  have h1474_1479 := h1470_1479.2.2.2.2
  exact h1474_1479.1

private theorem digest_work_var_u16_expr_word6_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 6 2 row =
      work_vars_e air 1 32 row +
      work_vars_e air 1 33 row * 2 +
      work_vars_e air 1 34 row * 4 +
      work_vars_e air 1 35 row * 8 +
      work_vars_e air 1 36 row * 16 +
      work_vars_e air 1 37 row * 32 +
      work_vars_e air 1 38 row * 64 +
      work_vars_e air 1 39 row * 128 +
      work_vars_e air 1 40 row * 256 +
      work_vars_e air 1 41 row * 512 +
      work_vars_e air 1 42 row * 1024 +
      work_vars_e air 1 43 row * 2048 +
      work_vars_e air 1 44 row * 4096 +
      work_vars_e air 1 45 row * 8192 +
      work_vars_e air 1 46 row * 16384 +
      work_vars_e air 1 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word6_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 6 2 row =
      Circuit.main air (id := 0) (column := 705) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word6_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 6 2 row =
      Circuit.main air (id := 0) (column := 667) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 668) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word6
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 6 row * (digest_carry2_expr air 6 row - 1)) = 0 := by
  simpa only [constraint_1474, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1474,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word6_limb0, digest_work_var_u16_expr_word6_limb1,
    digest_work_var_u16_expr_word6_limb2, next_prev_hash_word6_limb0,
    next_prev_hash_word6_limb1, next_prev_hash_word6_limb2,
    next_digest_final_hash_u16_expr_word6_limb0, next_digest_final_hash_u16_expr_word6_limb1,
    next_digest_final_hash_u16_expr_word6_limb2, next_is_digest_row, work_vars_e] using
    digest_carry2_raw_word6 hd

set_option maxHeartbeats 40000000

private theorem digest_carry2_raw_word7
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1478 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1454_1479 := h1450_1479.2.2.2.2
  have h1458_1479 := h1454_1479.2.2.2.2
  have h1462_1479 := h1458_1479.2.2.2.2
  have h1466_1479 := h1462_1479.2.2.2.2
  have h1470_1479 := h1466_1479.2.2.2.2
  have h1474_1479 := h1470_1479.2.2.2.2
  have h1478_1479 := h1474_1479.2.2.2.2
  exact h1478_1479.1

private theorem digest_work_var_u16_expr_word7_limb2
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 7 2 row =
      work_vars_e air 0 32 row +
      work_vars_e air 0 33 row * 2 +
      work_vars_e air 0 34 row * 4 +
      work_vars_e air 0 35 row * 8 +
      work_vars_e air 0 36 row * 16 +
      work_vars_e air 0 37 row * 32 +
      work_vars_e air 0 38 row * 64 +
      work_vars_e air 0 39 row * 128 +
      work_vars_e air 0 40 row * 256 +
      work_vars_e air 0 41 row * 512 +
      work_vars_e air 0 42 row * 1024 +
      work_vars_e air 0 43 row * 2048 +
      work_vars_e air 0 44 row * 4096 +
      work_vars_e air 0 45 row * 8192 +
      work_vars_e air 0 46 row * 16384 +
      work_vars_e air 0 47 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word7_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 7 2 row =
      Circuit.main air (id := 0) (column := 709) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word7_limb2
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 7 2 row =
      Circuit.main air (id := 0) (column := 675) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 676) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry2_boolean_word7
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air 7 row * (digest_carry2_expr air 7 row - 1)) = 0 := by
  simpa only [constraint_1478, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1478,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr,
    digest_work_var_u16_expr_word7_limb0, digest_work_var_u16_expr_word7_limb1,
    digest_work_var_u16_expr_word7_limb2, next_prev_hash_word7_limb0,
    next_prev_hash_word7_limb1, next_prev_hash_word7_limb2,
    next_digest_final_hash_u16_expr_word7_limb0, next_digest_final_hash_u16_expr_word7_limb1,
    next_digest_final_hash_u16_expr_word7_limb2, next_is_digest_row, work_vars_e] using
    digest_carry2_raw_word7 hd

-- ============================================================
-- Carry-3 boolean extraction (words 0-7)
-- ============================================================

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word0
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1451 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  exact h1451_1479.1

private theorem digest_work_var_u16_expr_word0_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 0 3 row =
      work_vars_a air 3 48 row +
      work_vars_a air 3 49 row * 2 +
      work_vars_a air 3 50 row * 4 +
      work_vars_a air 3 51 row * 8 +
      work_vars_a air 3 52 row * 16 +
      work_vars_a air 3 53 row * 32 +
      work_vars_a air 3 54 row * 64 +
      work_vars_a air 3 55 row * 128 +
      work_vars_a air 3 56 row * 256 +
      work_vars_a air 3 57 row * 512 +
      work_vars_a air 3 58 row * 1024 +
      work_vars_a air 3 59 row * 2048 +
      work_vars_a air 3 60 row * 4096 +
      work_vars_a air 3 61 row * 8192 +
      work_vars_a air 3 62 row * 16384 +
      work_vars_a air 3 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word0_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 0 3 row =
      Circuit.main air (id := 0) (column := 682) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word0_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 0 3 row =
      Circuit.main air (id := 0) (column := 621) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 622) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word0
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 0 row * (digest_carry3_expr air 0 row - 1)) = 0 := by
  simpa only [constraint_1451, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1451,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word0_limb0, digest_work_var_u16_expr_word0_limb1,
    digest_work_var_u16_expr_word0_limb2, digest_work_var_u16_expr_word0_limb3,
    next_prev_hash_word0_limb0, next_prev_hash_word0_limb1,
    next_prev_hash_word0_limb2, next_prev_hash_word0_limb3,
    next_digest_final_hash_u16_expr_word0_limb0, next_digest_final_hash_u16_expr_word0_limb1,
    next_digest_final_hash_u16_expr_word0_limb2, next_digest_final_hash_u16_expr_word0_limb3,
    next_is_digest_row, work_vars_a] using
    digest_carry3_raw_word0 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word1
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1455 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  exact h1455_1479.1

private theorem digest_work_var_u16_expr_word1_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 1 3 row =
      work_vars_a air 2 48 row +
      work_vars_a air 2 49 row * 2 +
      work_vars_a air 2 50 row * 4 +
      work_vars_a air 2 51 row * 8 +
      work_vars_a air 2 52 row * 16 +
      work_vars_a air 2 53 row * 32 +
      work_vars_a air 2 54 row * 64 +
      work_vars_a air 2 55 row * 128 +
      work_vars_a air 2 56 row * 256 +
      work_vars_a air 2 57 row * 512 +
      work_vars_a air 2 58 row * 1024 +
      work_vars_a air 2 59 row * 2048 +
      work_vars_a air 2 60 row * 4096 +
      work_vars_a air 2 61 row * 8192 +
      work_vars_a air 2 62 row * 16384 +
      work_vars_a air 2 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word1_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 1 3 row =
      Circuit.main air (id := 0) (column := 686) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word1_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 1 3 row =
      Circuit.main air (id := 0) (column := 629) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 630) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word1
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 1 row * (digest_carry3_expr air 1 row - 1)) = 0 := by
  simpa only [constraint_1455, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1455,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word1_limb0, digest_work_var_u16_expr_word1_limb1,
    digest_work_var_u16_expr_word1_limb2, digest_work_var_u16_expr_word1_limb3,
    next_prev_hash_word1_limb0, next_prev_hash_word1_limb1,
    next_prev_hash_word1_limb2, next_prev_hash_word1_limb3,
    next_digest_final_hash_u16_expr_word1_limb0, next_digest_final_hash_u16_expr_word1_limb1,
    next_digest_final_hash_u16_expr_word1_limb2, next_digest_final_hash_u16_expr_word1_limb3,
    next_is_digest_row, work_vars_a] using
    digest_carry3_raw_word1 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word2
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1459 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  have h1459_1479 := h1455_1479.2.2.2.2
  exact h1459_1479.1

private theorem digest_work_var_u16_expr_word2_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 2 3 row =
      work_vars_a air 1 48 row +
      work_vars_a air 1 49 row * 2 +
      work_vars_a air 1 50 row * 4 +
      work_vars_a air 1 51 row * 8 +
      work_vars_a air 1 52 row * 16 +
      work_vars_a air 1 53 row * 32 +
      work_vars_a air 1 54 row * 64 +
      work_vars_a air 1 55 row * 128 +
      work_vars_a air 1 56 row * 256 +
      work_vars_a air 1 57 row * 512 +
      work_vars_a air 1 58 row * 1024 +
      work_vars_a air 1 59 row * 2048 +
      work_vars_a air 1 60 row * 4096 +
      work_vars_a air 1 61 row * 8192 +
      work_vars_a air 1 62 row * 16384 +
      work_vars_a air 1 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word2_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 2 3 row =
      Circuit.main air (id := 0) (column := 690) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word2_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 2 3 row =
      Circuit.main air (id := 0) (column := 637) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 638) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word2
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 2 row * (digest_carry3_expr air 2 row - 1)) = 0 := by
  simpa only [constraint_1459, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1459,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word2_limb0, digest_work_var_u16_expr_word2_limb1,
    digest_work_var_u16_expr_word2_limb2, digest_work_var_u16_expr_word2_limb3,
    next_prev_hash_word2_limb0, next_prev_hash_word2_limb1,
    next_prev_hash_word2_limb2, next_prev_hash_word2_limb3,
    next_digest_final_hash_u16_expr_word2_limb0, next_digest_final_hash_u16_expr_word2_limb1,
    next_digest_final_hash_u16_expr_word2_limb2, next_digest_final_hash_u16_expr_word2_limb3,
    next_is_digest_row, work_vars_a] using
    digest_carry3_raw_word2 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word3
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1463 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  have h1459_1479 := h1455_1479.2.2.2.2
  have h1463_1479 := h1459_1479.2.2.2.2
  exact h1463_1479.1

private theorem digest_work_var_u16_expr_word3_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 3 3 row =
      work_vars_a air 0 48 row +
      work_vars_a air 0 49 row * 2 +
      work_vars_a air 0 50 row * 4 +
      work_vars_a air 0 51 row * 8 +
      work_vars_a air 0 52 row * 16 +
      work_vars_a air 0 53 row * 32 +
      work_vars_a air 0 54 row * 64 +
      work_vars_a air 0 55 row * 128 +
      work_vars_a air 0 56 row * 256 +
      work_vars_a air 0 57 row * 512 +
      work_vars_a air 0 58 row * 1024 +
      work_vars_a air 0 59 row * 2048 +
      work_vars_a air 0 60 row * 4096 +
      work_vars_a air 0 61 row * 8192 +
      work_vars_a air 0 62 row * 16384 +
      work_vars_a air 0 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word3_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 3 3 row =
      Circuit.main air (id := 0) (column := 694) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word3_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 3 3 row =
      Circuit.main air (id := 0) (column := 645) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 646) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word3
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 3 row * (digest_carry3_expr air 3 row - 1)) = 0 := by
  simpa only [constraint_1463, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1463,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word3_limb0, digest_work_var_u16_expr_word3_limb1,
    digest_work_var_u16_expr_word3_limb2, digest_work_var_u16_expr_word3_limb3,
    next_prev_hash_word3_limb0, next_prev_hash_word3_limb1,
    next_prev_hash_word3_limb2, next_prev_hash_word3_limb3,
    next_digest_final_hash_u16_expr_word3_limb0, next_digest_final_hash_u16_expr_word3_limb1,
    next_digest_final_hash_u16_expr_word3_limb2, next_digest_final_hash_u16_expr_word3_limb3,
    next_is_digest_row, work_vars_a] using
    digest_carry3_raw_word3 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word4
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1467 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  have h1459_1479 := h1455_1479.2.2.2.2
  have h1463_1479 := h1459_1479.2.2.2.2
  have h1467_1479 := h1463_1479.2.2.2.2
  exact h1467_1479.1

private theorem digest_work_var_u16_expr_word4_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 4 3 row =
      work_vars_e air 3 48 row +
      work_vars_e air 3 49 row * 2 +
      work_vars_e air 3 50 row * 4 +
      work_vars_e air 3 51 row * 8 +
      work_vars_e air 3 52 row * 16 +
      work_vars_e air 3 53 row * 32 +
      work_vars_e air 3 54 row * 64 +
      work_vars_e air 3 55 row * 128 +
      work_vars_e air 3 56 row * 256 +
      work_vars_e air 3 57 row * 512 +
      work_vars_e air 3 58 row * 1024 +
      work_vars_e air 3 59 row * 2048 +
      work_vars_e air 3 60 row * 4096 +
      work_vars_e air 3 61 row * 8192 +
      work_vars_e air 3 62 row * 16384 +
      work_vars_e air 3 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word4_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 4 3 row =
      Circuit.main air (id := 0) (column := 698) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word4_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 4 3 row =
      Circuit.main air (id := 0) (column := 653) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 654) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word4
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 4 row * (digest_carry3_expr air 4 row - 1)) = 0 := by
  simpa only [constraint_1467, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1467,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word4_limb0, digest_work_var_u16_expr_word4_limb1,
    digest_work_var_u16_expr_word4_limb2, digest_work_var_u16_expr_word4_limb3,
    next_prev_hash_word4_limb0, next_prev_hash_word4_limb1,
    next_prev_hash_word4_limb2, next_prev_hash_word4_limb3,
    next_digest_final_hash_u16_expr_word4_limb0, next_digest_final_hash_u16_expr_word4_limb1,
    next_digest_final_hash_u16_expr_word4_limb2, next_digest_final_hash_u16_expr_word4_limb3,
    next_is_digest_row, work_vars_e] using
    digest_carry3_raw_word4 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word5
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1471 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  have h1459_1479 := h1455_1479.2.2.2.2
  have h1463_1479 := h1459_1479.2.2.2.2
  have h1467_1479 := h1463_1479.2.2.2.2
  have h1471_1479 := h1467_1479.2.2.2.2
  exact h1471_1479.1

private theorem digest_work_var_u16_expr_word5_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 5 3 row =
      work_vars_e air 2 48 row +
      work_vars_e air 2 49 row * 2 +
      work_vars_e air 2 50 row * 4 +
      work_vars_e air 2 51 row * 8 +
      work_vars_e air 2 52 row * 16 +
      work_vars_e air 2 53 row * 32 +
      work_vars_e air 2 54 row * 64 +
      work_vars_e air 2 55 row * 128 +
      work_vars_e air 2 56 row * 256 +
      work_vars_e air 2 57 row * 512 +
      work_vars_e air 2 58 row * 1024 +
      work_vars_e air 2 59 row * 2048 +
      work_vars_e air 2 60 row * 4096 +
      work_vars_e air 2 61 row * 8192 +
      work_vars_e air 2 62 row * 16384 +
      work_vars_e air 2 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word5_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 5 3 row =
      Circuit.main air (id := 0) (column := 702) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word5_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 5 3 row =
      Circuit.main air (id := 0) (column := 661) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 662) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word5
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 5 row * (digest_carry3_expr air 5 row - 1)) = 0 := by
  simpa only [constraint_1471, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1471,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word5_limb0, digest_work_var_u16_expr_word5_limb1,
    digest_work_var_u16_expr_word5_limb2, digest_work_var_u16_expr_word5_limb3,
    next_prev_hash_word5_limb0, next_prev_hash_word5_limb1,
    next_prev_hash_word5_limb2, next_prev_hash_word5_limb3,
    next_digest_final_hash_u16_expr_word5_limb0, next_digest_final_hash_u16_expr_word5_limb1,
    next_digest_final_hash_u16_expr_word5_limb2, next_digest_final_hash_u16_expr_word5_limb3,
    next_is_digest_row, work_vars_e] using
    digest_carry3_raw_word5 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word6
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1475 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  have h1459_1479 := h1455_1479.2.2.2.2
  have h1463_1479 := h1459_1479.2.2.2.2
  have h1467_1479 := h1463_1479.2.2.2.2
  have h1471_1479 := h1467_1479.2.2.2.2
  have h1475_1479 := h1471_1479.2.2.2.2
  exact h1475_1479.1

private theorem digest_work_var_u16_expr_word6_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 6 3 row =
      work_vars_e air 1 48 row +
      work_vars_e air 1 49 row * 2 +
      work_vars_e air 1 50 row * 4 +
      work_vars_e air 1 51 row * 8 +
      work_vars_e air 1 52 row * 16 +
      work_vars_e air 1 53 row * 32 +
      work_vars_e air 1 54 row * 64 +
      work_vars_e air 1 55 row * 128 +
      work_vars_e air 1 56 row * 256 +
      work_vars_e air 1 57 row * 512 +
      work_vars_e air 1 58 row * 1024 +
      work_vars_e air 1 59 row * 2048 +
      work_vars_e air 1 60 row * 4096 +
      work_vars_e air 1 61 row * 8192 +
      work_vars_e air 1 62 row * 16384 +
      work_vars_e air 1 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word6_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 6 3 row =
      Circuit.main air (id := 0) (column := 706) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word6_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 6 3 row =
      Circuit.main air (id := 0) (column := 669) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 670) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word6
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 6 row * (digest_carry3_expr air 6 row - 1)) = 0 := by
  simpa only [constraint_1475, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1475,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word6_limb0, digest_work_var_u16_expr_word6_limb1,
    digest_work_var_u16_expr_word6_limb2, digest_work_var_u16_expr_word6_limb3,
    next_prev_hash_word6_limb0, next_prev_hash_word6_limb1,
    next_prev_hash_word6_limb2, next_prev_hash_word6_limb3,
    next_digest_final_hash_u16_expr_word6_limb0, next_digest_final_hash_u16_expr_word6_limb1,
    next_digest_final_hash_u16_expr_word6_limb2, next_digest_final_hash_u16_expr_word6_limb3,
    next_is_digest_row, work_vars_e] using
    digest_carry3_raw_word6 hd

set_option maxHeartbeats 40000000

private theorem digest_carry3_raw_word7
    {air : C FBB ExtF} {row : ℕ}
    (hd : digest_constraints air row) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1479 air row := by
  rcases hd with ⟨_h1400_1449, h1450_1479⟩
  dsimp [Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1450_1479] at h1450_1479
  have h1451_1479 := h1450_1479.2
  have h1455_1479 := h1451_1479.2.2.2.2
  have h1459_1479 := h1455_1479.2.2.2.2
  have h1463_1479 := h1459_1479.2.2.2.2
  have h1467_1479 := h1463_1479.2.2.2.2
  have h1471_1479 := h1467_1479.2.2.2.2
  have h1475_1479 := h1471_1479.2.2.2.2
  have h1479_1479 := h1475_1479.2.2.2.2
  exact h1479_1479

private theorem digest_work_var_u16_expr_word7_limb3
    (air : C FBB ExtF) (row : ℕ) :
    digest_work_var_u16_expr air 7 3 row =
      work_vars_e air 0 48 row +
      work_vars_e air 0 49 row * 2 +
      work_vars_e air 0 50 row * 4 +
      work_vars_e air 0 51 row * 8 +
      work_vars_e air 0 52 row * 16 +
      work_vars_e air 0 53 row * 32 +
      work_vars_e air 0 54 row * 64 +
      work_vars_e air 0 55 row * 128 +
      work_vars_e air 0 56 row * 256 +
      work_vars_e air 0 57 row * 512 +
      work_vars_e air 0 58 row * 1024 +
      work_vars_e air 0 59 row * 2048 +
      work_vars_e air 0 60 row * 4096 +
      work_vars_e air 0 61 row * 8192 +
      work_vars_e air 0 62 row * 16384 +
      work_vars_e air 0 63 row * 32768 := by
  rw [digest_work_var_u16_expr]
  norm_num [Finset.sum_range_succ]

private theorem next_prev_hash_word7_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_prev_hash air 7 3 row =
      Circuit.main air (id := 0) (column := 710) (row := row) (rotation := 1) := by
  norm_num [next_prev_hash]

private theorem next_digest_final_hash_u16_expr_word7_limb3
    (air : C FBB ExtF) (row : ℕ) :
    next_digest_final_hash_u16_expr air 7 3 row =
      Circuit.main air (id := 0) (column := 677) (row := row) (rotation := 1) +
        Circuit.main air (id := 0) (column := 678) (row := row) (rotation := 1) * 256 := by
  norm_num [next_digest_final_hash_u16_expr, next_final_hash]

theorem digest_carry3_boolean_word7
    (air : C FBB ExtF) (row : ℕ)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air 7 row * (digest_carry3_expr air 7 row - 1)) = 0 := by
  simpa only [constraint_1479, Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1479,
    digest_carry0_expr, digest_carry1_expr, digest_carry2_expr, digest_carry3_expr,
    digest_work_var_u16_expr_word7_limb0, digest_work_var_u16_expr_word7_limb1,
    digest_work_var_u16_expr_word7_limb2, digest_work_var_u16_expr_word7_limb3,
    next_prev_hash_word7_limb0, next_prev_hash_word7_limb1,
    next_prev_hash_word7_limb2, next_prev_hash_word7_limb3,
    next_digest_final_hash_u16_expr_word7_limb0, next_digest_final_hash_u16_expr_word7_limb1,
    next_digest_final_hash_u16_expr_word7_limb2, next_digest_final_hash_u16_expr_word7_limb3,
    next_is_digest_row, work_vars_e] using
    digest_carry3_raw_word7 hd

-- ============================================================
-- Work-variable expression projection (words 0-7)
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word0
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 0 limb row =
      digestWorkVarU16Limb air row 0 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_a_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_a_u16_eq air row 3 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word1
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 1 limb row =
      digestWorkVarU16Limb air row 1 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_a_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_a_u16_eq air row 2 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word2
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 2 limb row =
      digestWorkVarU16Limb air row 2 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_a_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_a_u16_eq air row 1 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word3
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 3 limb row =
      digestWorkVarU16Limb air row 3 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_a_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_a_u16_eq air row 0 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word4
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 4 limb row =
      digestWorkVarU16Limb air row 4 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_e_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_e_u16_eq air row 3 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word5
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 5 limb row =
      digestWorkVarU16Limb air row 5 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_e_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_e_u16_eq air row 2 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word6
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 6 limb row =
      digestWorkVarU16Limb air row 6 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_e_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_e_u16_eq air row 1 limb hlimb

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq_word7
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air 7 limb row =
      digestWorkVarU16Limb air row 7 limb := by
  simpa [digest_work_var_u16_expr, digestWorkVarU16Limb, compose_e_u16, hlimb,
      Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    compose_e_u16_eq air row 0 limb hlimb

-- ============================================================
-- Final-hash expression projection
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem next_digest_final_hash_u16_expr_eq
    (air : C FBB ExtF) (row word limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hlimb : limb < 4) :
    next_digest_final_hash_u16_expr air word limb row =
      digestFinalHashU16Limb air (nextRow air row) word limb := by
  simp [next_digest_final_hash_u16_expr, digestFinalHashU16Limb, hlimb,
    next_final_hash_eq_nextRow air hrot word (2 * limb) row hrow,
    next_final_hash_eq_nextRow air hrot word (2 * limb + 1) row hrow]

-- ============================================================
-- Carry-0 boolean dispatcher
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem digest_carry0_boolean
    (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry0_expr air word row * (digest_carry0_expr air word row - 1)) = 0 := by
  interval_cases word
  · simpa using digest_carry0_boolean_word0 air row hd
  · simpa using digest_carry0_boolean_word1 air row hd
  · simpa using digest_carry0_boolean_word2 air row hd
  · simpa using digest_carry0_boolean_word3 air row hd
  · simpa using digest_carry0_boolean_word4 air row hd
  · simpa using digest_carry0_boolean_word5 air row hd
  · simpa using digest_carry0_boolean_word6 air row hd
  · simpa using digest_carry0_boolean_word7 air row hd

-- ============================================================
-- Carry-1 boolean dispatcher
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem digest_carry1_boolean
    (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry1_expr air word row * (digest_carry1_expr air word row - 1)) = 0 := by
  interval_cases word
  · simpa using digest_carry1_boolean_word0 air row hd
  · simpa using digest_carry1_boolean_word1 air row hd
  · simpa using digest_carry1_boolean_word2 air row hd
  · simpa using digest_carry1_boolean_word3 air row hd
  · simpa using digest_carry1_boolean_word4 air row hd
  · simpa using digest_carry1_boolean_word5 air row hd
  · simpa using digest_carry1_boolean_word6 air row hd
  · simpa using digest_carry1_boolean_word7 air row hd

-- ============================================================
-- Carry-2 boolean dispatcher
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem digest_carry2_boolean
    (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry2_expr air word row * (digest_carry2_expr air word row - 1)) = 0 := by
  interval_cases word
  · simpa using digest_carry2_boolean_word0 air row hd
  · simpa using digest_carry2_boolean_word1 air row hd
  · simpa using digest_carry2_boolean_word2 air row hd
  · simpa using digest_carry2_boolean_word3 air row hd
  · simpa using digest_carry2_boolean_word4 air row hd
  · simpa using digest_carry2_boolean_word5 air row hd
  · simpa using digest_carry2_boolean_word6 air row hd
  · simpa using digest_carry2_boolean_word7 air row hd

-- ============================================================
-- Carry-3 boolean dispatcher
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem digest_carry3_boolean
    (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hd : digest_constraints air row) :
    next_is_digest_row air row *
      (digest_carry3_expr air word row * (digest_carry3_expr air word row - 1)) = 0 := by
  interval_cases word
  · simpa using digest_carry3_boolean_word0 air row hd
  · simpa using digest_carry3_boolean_word1 air row hd
  · simpa using digest_carry3_boolean_word2 air row hd
  · simpa using digest_carry3_boolean_word3 air row hd
  · simpa using digest_carry3_boolean_word4 air row hd
  · simpa using digest_carry3_boolean_word5 air row hd
  · simpa using digest_carry3_boolean_word6 air row hd
  · simpa using digest_carry3_boolean_word7 air row hd

-- ============================================================
-- Work-variable expression dispatcher
-- ============================================================

set_option maxHeartbeats 40000000 in
theorem digest_work_var_u16_expr_eq
    (air : C FBB ExtF) (row word limb : ℕ)
    (hword : word < 8)
    (hlimb : limb < 4) :
    digest_work_var_u16_expr air word limb row =
      digestWorkVarU16Limb air row word limb := by
  interval_cases word
  · simpa using digest_work_var_u16_expr_eq_word0 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word1 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word2 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word3 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word4 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word5 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word6 air row limb hlimb
  · simpa using digest_work_var_u16_expr_eq_word7 air row limb hlimb

-- ============================================================
-- DigestWordCarryWitness structure
-- ============================================================

/-- Proof witness for the four recursive digest carries of one SHA-512 word. -/
structure DigestWordCarryWitness
    (air : C FBB ExtF) (localRow digestRow word : ℕ) where
  carry0 : FBB
  carry1 : FBB
  carry2 : FBB
  carry3 : FBB
  carry0_bool : carry0 = 0 ∨ carry0 = 1
  carry1_bool : carry1 = 0 ∨ carry1 = 1
  carry2_bool : carry2 = 0 ∨ carry2 = 1
  carry3_bool : carry3 = 0 ∨ carry3 = 1
  limb0_eq :
    digestPrevHashU16Limb air digestRow word 0 + digestWorkVarU16Limb air localRow word 0 =
      digestFinalHashU16Limb air digestRow word 0 + carry0 * (2 ^ 16 : ℕ)
  limb1_eq :
    digestPrevHashU16Limb air digestRow word 1 + digestWorkVarU16Limb air localRow word 1 + carry0 =
      digestFinalHashU16Limb air digestRow word 1 + carry1 * (2 ^ 16 : ℕ)
  limb2_eq :
    digestPrevHashU16Limb air digestRow word 2 + digestWorkVarU16Limb air localRow word 2 + carry1 =
      digestFinalHashU16Limb air digestRow word 2 + carry2 * (2 ^ 16 : ℕ)
  limb3_eq :
    digestPrevHashU16Limb air digestRow word 3 + digestWorkVarU16Limb air localRow word 3 + carry2 =
      digestFinalHashU16Limb air digestRow word 3 + carry3 * (2 ^ 16 : ℕ)

-- ============================================================
-- Carry witness extraction
-- ============================================================

theorem digest_word_carry_witness (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hd : digest_constraints air row)
    (hdigest_next : is_digest_row air (nextRow air row) = 1) :
    Nonempty (DigestWordCarryWitness air row (nextRow air row) word) := by
  have hnext_digest : next_is_digest_row air row = 1 := by
    rw [next_is_digest_row_eq_nextRow air hrot row hrow]
    exact hdigest_next
  let c0 : FBB := digest_carry0_expr air word row
  let c1 : FBB := digest_carry1_expr air word row
  let c2 : FBB := digest_carry2_expr air word row
  let c3 : FBB := digest_carry3_expr air word row
  have hc0_poly :
      next_is_digest_row air row *
        (digest_carry0_expr air word row * (digest_carry0_expr air word row - 1)) = 0 := by
    exact digest_carry0_boolean air row word hword hd
  have hc1_poly :
      next_is_digest_row air row *
        (digest_carry1_expr air word row * (digest_carry1_expr air word row - 1)) = 0 := by
    exact digest_carry1_boolean air row word hword hd
  have hc2_poly :
      next_is_digest_row air row *
        (digest_carry2_expr air word row * (digest_carry2_expr air word row - 1)) = 0 := by
    exact digest_carry2_boolean air row word hword hd
  have hc3_poly :
      next_is_digest_row air row *
        (digest_carry3_expr air word row * (digest_carry3_expr air word row - 1)) = 0 := by
    exact digest_carry3_boolean air row word hword hd
  have hc0_bool : c0 = 0 ∨ c0 = 1 := by
    exact bit_boolean_of_sq_eq_zero c0 (by simpa [c0, hnext_digest] using hc0_poly)
  have hc1_bool : c1 = 0 ∨ c1 = 1 := by
    exact bit_boolean_of_sq_eq_zero c1 (by simpa [c1, hnext_digest] using hc1_poly)
  have hc2_bool : c2 = 0 ∨ c2 = 1 := by
    exact bit_boolean_of_sq_eq_zero c2 (by simpa [c2, hnext_digest] using hc2_poly)
  have hc3_bool : c3 = 0 ∨ c3 = 1 := by
    exact bit_boolean_of_sq_eq_zero c3 (by simpa [c3, hnext_digest] using hc3_poly)
  have h0_raw :
      next_prev_hash air word 0 row + digest_work_var_u16_expr air word 0 row =
        next_digest_final_hash_u16_expr air word 0 row + c0 * (2 ^ 16 : ℕ) := by
    let expr : FBB :=
      next_prev_hash air word 0 row + digest_work_var_u16_expr air word 0 row -
        next_digest_final_hash_u16_expr air word 0 row
    have hexpr : ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) = expr :=
      digestCarry_mul_pow_eq expr
    calc
      next_prev_hash air word 0 row + digest_work_var_u16_expr air word 0 row =
          next_digest_final_hash_u16_expr air word 0 row + expr := by
            dsimp [expr]
            ring
      _ = next_digest_final_hash_u16_expr air word 0 row +
          ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) := by
            conv_lhs => rw [hexpr.symm]
      _ = next_digest_final_hash_u16_expr air word 0 row + c0 * (2 ^ 16 : ℕ) := by
            simp [c0, expr, digest_carry0_expr]
  have h1_raw :
      next_prev_hash air word 1 row + digest_work_var_u16_expr air word 1 row + c0 =
        next_digest_final_hash_u16_expr air word 1 row + c1 * (2 ^ 16 : ℕ) := by
    let expr : FBB :=
      next_prev_hash air word 1 row + digest_work_var_u16_expr air word 1 row + c0 -
        next_digest_final_hash_u16_expr air word 1 row
    have hexpr : ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) = expr :=
      digestCarry_mul_pow_eq expr
    calc
      next_prev_hash air word 1 row + digest_work_var_u16_expr air word 1 row + c0 =
          next_digest_final_hash_u16_expr air word 1 row + expr := by
            dsimp [expr]
            ring
      _ = next_digest_final_hash_u16_expr air word 1 row +
          ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) := by
            conv_lhs => rw [hexpr.symm]
      _ = next_digest_final_hash_u16_expr air word 1 row + c1 * (2 ^ 16 : ℕ) := by
            simp [c0, c1, expr, digest_carry0_expr, digest_carry1_expr]
  have h2_raw :
      next_prev_hash air word 2 row + digest_work_var_u16_expr air word 2 row + c1 =
        next_digest_final_hash_u16_expr air word 2 row + c2 * (2 ^ 16 : ℕ) := by
    let expr : FBB :=
      next_prev_hash air word 2 row + digest_work_var_u16_expr air word 2 row + c1 -
        next_digest_final_hash_u16_expr air word 2 row
    have hexpr : ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) = expr :=
      digestCarry_mul_pow_eq expr
    calc
      next_prev_hash air word 2 row + digest_work_var_u16_expr air word 2 row + c1 =
          next_digest_final_hash_u16_expr air word 2 row + expr := by
            dsimp [expr]
            ring
      _ = next_digest_final_hash_u16_expr air word 2 row +
          ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) := by
            conv_lhs => rw [hexpr.symm]
      _ = next_digest_final_hash_u16_expr air word 2 row + c2 * (2 ^ 16 : ℕ) := by
            simp [c0, c1, c2, expr, digest_carry0_expr, digest_carry1_expr, digest_carry2_expr]
  have h3_raw :
      next_prev_hash air word 3 row + digest_work_var_u16_expr air word 3 row + c2 =
        next_digest_final_hash_u16_expr air word 3 row + c3 * (2 ^ 16 : ℕ) := by
    let expr : FBB :=
      next_prev_hash air word 3 row + digest_work_var_u16_expr air word 3 row + c2 -
        next_digest_final_hash_u16_expr air word 3 row
    have hexpr : ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) = expr :=
      digestCarry_mul_pow_eq expr
    calc
      next_prev_hash air word 3 row + digest_work_var_u16_expr air word 3 row + c2 =
          next_digest_final_hash_u16_expr air word 3 row + expr := by
            dsimp [expr]
            ring
      _ = next_digest_final_hash_u16_expr air word 3 row +
          ((2013235201 : FBB) * expr) * (2 ^ 16 : ℕ) := by
            conv_lhs => rw [hexpr.symm]
      _ = next_digest_final_hash_u16_expr air word 3 row + c3 * (2 ^ 16 : ℕ) := by
            simp [c0, c1, c2, c3, expr, digest_carry0_expr, digest_carry1_expr,
              digest_carry2_expr, digest_carry3_expr]
  have h0_eq :
      digestPrevHashU16Limb air (nextRow air row) word 0 + digestWorkVarU16Limb air row word 0 =
        digestFinalHashU16Limb air (nextRow air row) word 0 + c0 * (2 ^ 16 : ℕ) := by
    simpa [next_prev_hash_u16_eq air row word 0 hrow hrot (by omega),
      digest_work_var_u16_expr_eq air row word 0 hword (by omega),
      next_digest_final_hash_u16_expr_eq air row word 0 hrow hrot (by omega)] using h0_raw
  have h1_eq :
      digestPrevHashU16Limb air (nextRow air row) word 1 + digestWorkVarU16Limb air row word 1 + c0 =
        digestFinalHashU16Limb air (nextRow air row) word 1 + c1 * (2 ^ 16 : ℕ) := by
    simpa [next_prev_hash_u16_eq air row word 1 hrow hrot (by omega),
      digest_work_var_u16_expr_eq air row word 1 hword (by omega),
      next_digest_final_hash_u16_expr_eq air row word 1 hrow hrot (by omega)] using h1_raw
  have h2_eq :
      digestPrevHashU16Limb air (nextRow air row) word 2 + digestWorkVarU16Limb air row word 2 + c1 =
        digestFinalHashU16Limb air (nextRow air row) word 2 + c2 * (2 ^ 16 : ℕ) := by
    simpa [next_prev_hash_u16_eq air row word 2 hrow hrot (by omega),
      digest_work_var_u16_expr_eq air row word 2 hword (by omega),
      next_digest_final_hash_u16_expr_eq air row word 2 hrow hrot (by omega)] using h2_raw
  have h3_eq :
      digestPrevHashU16Limb air (nextRow air row) word 3 + digestWorkVarU16Limb air row word 3 + c2 =
        digestFinalHashU16Limb air (nextRow air row) word 3 + c3 * (2 ^ 16 : ℕ) := by
    simpa [next_prev_hash_u16_eq air row word 3 hrow hrot (by omega),
      digest_work_var_u16_expr_eq air row word 3 hword (by omega),
      next_digest_final_hash_u16_expr_eq air row word 3 hrow hrot (by omega)] using h3_raw
  exact ⟨{ carry0 := c0
           carry1 := c1
           carry2 := c2
           carry3 := c3
           carry0_bool := hc0_bool
           carry1_bool := hc1_bool
           carry2_bool := hc2_bool
           carry3_bool := hc3_bool
           limb0_eq := h0_eq
           limb1_eq := h1_eq
           limb2_eq := h2_eq
           limb3_eq := h3_eq }⟩

-- ============================================================
-- Digest carry recomposition
-- ============================================================

theorem digestPrevHash_eq_limbs (air : C FBB ExtF) (row word : ℕ) :
    digestPrevHashWord air row word =
      ((digestPrevHashU16Limb air row word 0).val +
       (digestPrevHashU16Limb air row word 1).val * 2 ^ 16 +
       (digestPrevHashU16Limb air row word 2).val * 2 ^ 32 +
       (digestPrevHashU16Limb air row word 3).val * 2 ^ 48).toUInt64 := by
  rw [digestPrevHashWord, limbs16LEToWord, foldl_range_add_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [digestPrevHashU16Limb, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem digestWorkVar_eq_limbs (air : C FBB ExtF) (row word : ℕ)
    (hbb : allWorkVarBitsBoolean air row) :
    digestWorkVarWord air row word =
      ((digestWorkVarU16Limb air row word 0).val +
       (digestWorkVarU16Limb air row word 1).val * 2 ^ 16 +
       (digestWorkVarU16Limb air row word 2).val * 2 ^ 32 +
       (digestWorkVarU16Limb air row word 3).val * 2 ^ 48).toUInt64 := by
  rcases hbb with ⟨ha_bits, he_bits⟩
  by_cases hword : word < 4
  · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
      intro i
      exact ha_bits (3 - word) i.val (by omega) i.isLt
    simp [digestWorkVarWord, digestWorkVarU16Limb, hword]
    rw [aWord_eq_bitsWordToUInt64]
    simpa using bitsWordToUInt64_eq_compose16 (aBitsWord air row (3 - word)) hbits
  · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
      intro i
      exact he_bits (7 - word) i.val (by omega) i.isLt
    simp [digestWorkVarWord, digestWorkVarU16Limb, hword]
    rw [eWord_eq_bitsWordToUInt64]
    simpa using bitsWordToUInt64_eq_compose16 (eBitsWord air row (7 - word)) hbits

theorem composed_hash_eq_digestWorkVarLimb
    (air : C FBB ExtF) (row word limb : ℕ)
    (hword : word < 8) (hlimb : limb < 4) :
    composed_hash_u16 air word limb row =
      digestWorkVarU16Limb air row word limb := by
  by_cases hword4 : word < 4
  · simp [composed_hash_u16, digestWorkVarU16Limb, hlimb, hword4]
    simpa using compose_a_u16_eq air row (3 - word) limb hlimb
  · simp [composed_hash_u16, digestWorkVarU16Limb, hlimb, hword4]
    simpa using compose_e_u16_eq air row (7 - word) limb hlimb

theorem digestWorkVarU16Limb_range
    (air : C FBB ExtF) (row word limb : ℕ)
    (hbb : allWorkVarBitsBoolean air row)
    (hword : word < 8) (hlimb : limb < 4) :
    (digestWorkVarU16Limb air row word limb).val < 2 ^ 16 := by
  rcases hbb with ⟨ha_bits, he_bits⟩
  by_cases hword4 : word < 4
  · have hbits : isBitsWord (aBitsWord air row (3 - word)) := by
      intro i
      exact ha_bits (3 - word) i.val (by omega) i.isLt
    simp [digestWorkVarU16Limb, hlimb, hword4]
    exact composeU16Limb_val_lt (aBitsWord air row (3 - word)) hbits ⟨limb, hlimb⟩
  · have hbits : isBitsWord (eBitsWord air row (7 - word)) := by
      intro i
      exact he_bits (7 - word) i.val (by omega) i.isLt
    simp [digestWorkVarU16Limb, hlimb, hword4]
    exact composeU16Limb_val_lt (eBitsWord air row (7 - word)) hbits ⟨limb, hlimb⟩

theorem composed_hash_u16_range
    (air : C FBB ExtF) (row word limb : ℕ)
    (hbb : allWorkVarBitsBoolean air row)
    (hword : word < 8) (hlimb : limb < 4) :
    (composed_hash_u16 air word limb row).val < 2 ^ 16 := by
  rw [composed_hash_eq_digestWorkVarLimb air row word limb hword hlimb]
  exact digestWorkVarU16Limb_range air row word limb hbb hword hlimb

-- ============================================================
-- Final-hash range bridging and UInt64 digest-word addition
-- ============================================================

private theorem digestFinalHashU16Limb_range_of_bus
    (air : C FBB ExtF) (row word limb : ℕ)
    (hword : word < 8) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hdigest : is_digest_row air row = 1)
    (h_wf_prev : bitwise_lookup_send_properties air (prevRow air row)) :
    (digestFinalHashU16Limb air row word limb).val < 2 ^ 16 := by
  have hb0 := digest_final_hash_byte_range_of_bus air row word (2 * limb) hword (by omega) hrow hrot hdigest h_wf_prev
  have hb1 := digest_final_hash_byte_range_of_bus air row word (2 * limb + 1) hword (by omega) hrow hrot hdigest h_wf_prev
  have hpair :
      (digestFinalHashU16Limb air row word limb).val =
        (final_hash air word (2 * limb) row).val +
          (final_hash air word (2 * limb + 1) row).val * 256 := by
    simpa [digestFinalHashU16Limb, hlimb] using
      byte_pair_val_eq (final_hash air word (2 * limb) row) (final_hash air word (2 * limb + 1) row) hb0 hb1
  have hlt :
      (final_hash air word (2 * limb) row).val +
        (final_hash air word (2 * limb + 1) row).val * 256 < 2 ^ 16 := by
    omega
  exact hpair ▸ hlt

private theorem digestFinalHash_eq_limbs_of_bus
    (air : C FBB ExtF) (row word : ℕ)
    (hword : word < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hdigest : is_digest_row air row = 1)
    (h_wf_prev : bitwise_lookup_send_properties air (prevRow air row)) :
    digestFinalHashWord air row word =
      ((digestFinalHashU16Limb air row word 0).val +
       (digestFinalHashU16Limb air row word 1).val * 2 ^ 16 +
       (digestFinalHashU16Limb air row word 2).val * 2 ^ 32 +
       (digestFinalHashU16Limb air row word 3).val * 2 ^ 48).toUInt64 := by
  have hb0 := digest_final_hash_byte_range_of_bus air row word 0 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb1 := digest_final_hash_byte_range_of_bus air row word 1 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb2 := digest_final_hash_byte_range_of_bus air row word 2 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb3 := digest_final_hash_byte_range_of_bus air row word 3 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb4 := digest_final_hash_byte_range_of_bus air row word 4 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb5 := digest_final_hash_byte_range_of_bus air row word 5 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb6 := digest_final_hash_byte_range_of_bus air row word 6 hword (by omega) hrow hrot hdigest h_wf_prev
  have hb7 := digest_final_hash_byte_range_of_bus air row word 7 hword (by omega) hrow hrot hdigest h_wf_prev
  have h0 :
      (digestFinalHashU16Limb air row word 0).val =
        (final_hash air word 0 row).val + (final_hash air word 1 row).val * 256 := by
    simpa [digestFinalHashU16Limb] using
      byte_pair_val_eq (final_hash air word 0 row) (final_hash air word 1 row) hb0 hb1
  have h1 :
      (digestFinalHashU16Limb air row word 1).val =
        (final_hash air word 2 row).val + (final_hash air word 3 row).val * 256 := by
    simpa [digestFinalHashU16Limb] using
      byte_pair_val_eq (final_hash air word 2 row) (final_hash air word 3 row) hb2 hb3
  have h2 :
      (digestFinalHashU16Limb air row word 2).val =
        (final_hash air word 4 row).val + (final_hash air word 5 row).val * 256 := by
    simpa [digestFinalHashU16Limb] using
      byte_pair_val_eq (final_hash air word 4 row) (final_hash air word 5 row) hb4 hb5
  have h3 :
      (digestFinalHashU16Limb air row word 3).val =
        (final_hash air word 6 row).val + (final_hash air word 7 row).val * 256 := by
    simpa [digestFinalHashU16Limb] using
      byte_pair_val_eq (final_hash air word 6 row) (final_hash air word 7 row) hb6 hb7
  have hnat :
      (final_hash air word 0 row).val +
          (final_hash air word 1 row).val * 256 +
          (final_hash air word 2 row).val * 65536 +
          (final_hash air word 3 row).val * 16777216 +
          (final_hash air word 4 row).val * 4294967296 +
          (final_hash air word 5 row).val * 1099511627776 +
          (final_hash air word 6 row).val * 281474976710656 +
          (final_hash air word 7 row).val * 72057594037927936 =
        (digestFinalHashU16Limb air row word 0).val +
          (digestFinalHashU16Limb air row word 1).val * 2 ^ 16 +
          (digestFinalHashU16Limb air row word 2).val * 2 ^ 32 +
          (digestFinalHashU16Limb air row word 3).val * 2 ^ 48 := by
    rw [h0, h1, h2, h3]
    ring
  rw [digestFinalHashWord, bytesLEToWord, foldl_range_add_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simpa using congrArg UInt64.ofNat hnat

theorem digest_word_addition_uint64 (air : C FBB ExtF) (start : ℕ) (word : ℕ)
    (hword : word < 8)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_prev_range : digestPrevHashLimbRange air (start + 20))
    (h_wf_prev : bitwise_lookup_send_properties air (start + 19)) :
    digestFinalHashWord air (start + 20) word =
      digestPrevHashWord air (start + 20) word +
      digestWorkVarWord air (start + 19) word := by
  let row := start + 19
  let digestRow := start + 20
  have hrow : row ≤ Circuit.last_row air := by
    dsimp [row]
    dsimp [blockWindowSupported] at hwindow
    omega
  have hrow_lt : row < Circuit.last_row air := by
    dsimp [row]
    dsimp [blockWindowSupported] at hwindow
    omega
  have hnextrow : nextRow air row = digestRow := by
    have hne : start + 19 ≠ Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    dsimp [row, digestRow]
    simp [nextRow, hne, Nat.add_assoc]
  have hdigest_constraints : digest_constraints air row := by
    dsimp [row]
    exact digest_constraints_of_blockHasherConstraints air hc (start + 19)
  rcases hshape with ⟨_, _, _, _, hdigest_row⟩
  rcases digest_word_carry_witness air row word hword hrow hrot hdigest_constraints
      (by simpa [digestRow, hnextrow] using hdigest_row) with ⟨hwit⟩
  let c0 : FBB := hwit.carry0
  let c1 : FBB := hwit.carry1
  let c2 : FBB := hwit.carry2
  let c3 : FBB := hwit.carry3
  have hc0_bool : c0 = 0 ∨ c0 = 1 := by
    simpa [c0] using hwit.carry0_bool
  have hc1_bool : c1 = 0 ∨ c1 = 1 := by
    simpa [c1] using hwit.carry1_bool
  have hc2_bool : c2 = 0 ∨ c2 = 1 := by
    simpa [c2] using hwit.carry2_bool
  have hc3_bool : c3 = 0 ∨ c3 = 1 := by
    simpa [c3] using hwit.carry3_bool
  have hc0_range : c0.val < 2 ^ 8 := by
    rcases hc0_bool with hc0 | hc0 <;> rw [hc0] <;> norm_num
  have hc1_range : c1.val < 2 ^ 8 := by
    rcases hc1_bool with hc1 | hc1 <;> rw [hc1] <;> norm_num
  have hc2_range : c2.val < 2 ^ 8 := by
    rcases hc2_bool with hc2 | hc2 <;> rw [hc2] <;> norm_num
  have hc3_range : c3.val < 2 ^ 8 := by
    rcases hc3_bool with hc3 | hc3 <;> rw [hc3] <;> norm_num
  have h0_eq :
      digestPrevHashU16Limb air digestRow word 0 + digestWorkVarU16Limb air row word 0 =
        digestFinalHashU16Limb air digestRow word 0 + c0 * (2 ^ 16 : ℕ) := by
    simpa [c0, digestRow, hnextrow] using hwit.limb0_eq
  have h1_eq :
      digestPrevHashU16Limb air digestRow word 1 + digestWorkVarU16Limb air row word 1 + c0 =
        digestFinalHashU16Limb air digestRow word 1 + c1 * (2 ^ 16 : ℕ) := by
    simpa [c0, c1, digestRow, hnextrow] using hwit.limb1_eq
  have h2_eq :
      digestPrevHashU16Limb air digestRow word 2 + digestWorkVarU16Limb air row word 2 + c1 =
        digestFinalHashU16Limb air digestRow word 2 + c2 * (2 ^ 16 : ℕ) := by
    simpa [c1, c2, digestRow, hnextrow] using hwit.limb2_eq
  have h3_eq :
      digestPrevHashU16Limb air digestRow word 3 + digestWorkVarU16Limb air row word 3 + c2 =
        digestFinalHashU16Limb air digestRow word 3 + c3 * (2 ^ 16 : ℕ) := by
    simpa [c2, c3, digestRow, hnextrow] using hwit.limb3_eq
  let p0 := digestPrevHashU16Limb air digestRow word 0
  let p1 := digestPrevHashU16Limb air digestRow word 1
  let p2 := digestPrevHashU16Limb air digestRow word 2
  let p3 := digestPrevHashU16Limb air digestRow word 3
  let w0 := digestWorkVarU16Limb air row word 0
  let w1 := digestWorkVarU16Limb air row word 1
  let w2 := digestWorkVarU16Limb air row word 2
  let w3 := digestWorkVarU16Limb air row word 3
  let r0 := digestFinalHashU16Limb air digestRow word 0
  let r1 := digestFinalHashU16Limb air digestRow word 1
  let r2 := digestFinalHashU16Limb air digestRow word 2
  let r3 := digestFinalHashU16Limb air digestRow word 3
  have hbb : allWorkVarBitsBoolean air row := by
    dsimp [row]
    exact allWorkVarBitsBoolean_of_constraints air (start + 19)
      (workvar_bit_boolean_constraints_of_blockHasherConstraints air hc (start + 19))
  have hp0 : p0.val < 2 ^ 16 := by
    simpa [p0, digestRow] using h_prev_range word 0 hword (by omega)
  have hp1 : p1.val < 2 ^ 16 := by
    simpa [p1, digestRow] using h_prev_range word 1 hword (by omega)
  have hp2 : p2.val < 2 ^ 16 := by
    simpa [p2, digestRow] using h_prev_range word 2 hword (by omega)
  have hp3 : p3.val < 2 ^ 16 := by
    simpa [p3, digestRow] using h_prev_range word 3 hword (by omega)
  have hw0 : w0.val < 2 ^ 16 := by
    simpa [w0] using digestWorkVarU16Limb_range air row word 0 hbb hword (by omega)
  have hw1 : w1.val < 2 ^ 16 := by
    simpa [w1] using digestWorkVarU16Limb_range air row word 1 hbb hword (by omega)
  have hw2 : w2.val < 2 ^ 16 := by
    simpa [w2] using digestWorkVarU16Limb_range air row word 2 hbb hword (by omega)
  have hw3 : w3.val < 2 ^ 16 := by
    simpa [w3] using digestWorkVarU16Limb_range air row word 3 hbb hword (by omega)
  have hr0 : r0.val < 2 ^ 16 := by
    simpa [r0, digestRow] using
      digestFinalHashU16Limb_range_of_bus air digestRow word 0 hword (by omega)
        (by simpa [digestRow, blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev
  have hr1 : r1.val < 2 ^ 16 := by
    simpa [r1, digestRow] using
      digestFinalHashU16Limb_range_of_bus air digestRow word 1 hword (by omega)
        (by simpa [digestRow, blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev
  have hr2 : r2.val < 2 ^ 16 := by
    simpa [r2, digestRow] using
      digestFinalHashU16Limb_range_of_bus air digestRow word 2 hword (by omega)
        (by simpa [digestRow, blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev
  have hr3 : r3.val < 2 ^ 16 := by
    simpa [r3, digestRow] using
      digestFinalHashU16Limb_range_of_bus air digestRow word 3 hword (by omega)
        (by simpa [digestRow, blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev
  have hbounds :
      ∀ x ∈ [p0, p1, p2, p3, w0, w1, w2, w3,
              (0 : FBB), (0 : FBB), (0 : FBB), (0 : FBB),
              (0 : FBB), (0 : FBB), (0 : FBB), (0 : FBB),
              (0 : FBB), (0 : FBB), (0 : FBB), (0 : FBB),
              (0 : FBB), (0 : FBB), (0 : FBB), (0 : FBB)],
            x.val < 2 ^ 16 := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp0
    · exact hp1
    · exact hp2
    · exact hp3
    · exact hw0
    · exact hw1
    · exact hw2
    · exact hw3
    · norm_num
  have hmod :=
    limbed_addition_six_uint64
      p0 p1 p2 p3
      w0 w1 w2 w3
      0 0 0 0
      0 0 0 0
      0 0 0 0
      0 0 0 0
      r0 r1 r2 r3 c0 c1 c2 c3
      hbounds hr0 hr1 hr2 hr3 hc0_range hc1_range hc2_range hc3_range
      (by simpa [p0, w0, r0] using h0_eq)
      (by simpa [p1, w1, r1] using h1_eq)
      (by simpa [p2, w2, r2] using h2_eq)
      (by simpa [p3, w3, r3] using h3_eq)
  rw [digestFinalHash_eq_limbs_of_bus air digestRow word hword
        (by simpa [digestRow, blockWindowSupported] using hwindow) hrot hdigest_row h_wf_prev,
    digestPrevHash_eq_limbs,
    digestWorkVar_eq_limbs air row word hbb]
  simpa [digestRow, row, p0, p1, p2, p3, w0, w1, w2, w3, r0, r1, r2, r3]
    using hmod.symm

-- ============================================================
-- End-to-end digest-row theorems
-- ============================================================

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
      ∀ slot bit, slot < 4 → bit < 64 →
        work_vars_a air slot bit r1 = work_vars_a air slot bit r2 ∧
        work_vars_e air slot bit r1 = work_vars_e air slot bit r2) :
    carriedState air r1 = carriedState air r2 := by
  have ha : ∀ slot, slot < 4 → aWord air r1 slot = aWord air r2 slot := by
    intro slot hslot
    rw [aWord_eq_bitsWordToUInt64, aWord_eq_bitsWordToUInt64]
    have hword : aBitsWord air r1 slot = aBitsWord air r2 slot := by
      funext i
      exact (hbits slot i.val hslot i.isLt).1
    exact congrArg bitsWordToUInt64 hword
  have he : ∀ slot, slot < 4 → eWord air r1 slot = eWord air r2 slot := by
    intro slot hslot
    rw [eWord_eq_bitsWordToUInt64, eWord_eq_bitsWordToUInt64]
    have hword : eBitsWord air r1 slot = eBitsWord air r2 slot := by
      funext i
      exact (hbits slot i.val hslot i.isLt).2
    exact congrArg bitsWordToUInt64 hword
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
  rcases hc row with ⟨_, _, ht, _, _, _, _⟩
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
        rcases hc (row + 1) with ⟨hf_row1, _, ht_row1, _, _, _, _⟩
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
    digestPrevHashLimbRange air (start + 20) ∧
      digestPrevHashState air (start + 20) = blockStartState air start := by
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
  rcases hc prev with ⟨hf_prev, hbits_prev, ht_prev, _, _, _, _⟩
  have hdigest_prev : is_digest_row air prev = 1 := by
    rcases hprev_shape with hsel20 | hsel21
    · exact (is_digest_iff_selector_eq_20 air prev hf_prev).2 hsel20
    · have hround_prev0 : is_round_row air prev = 0 := by
        rcases is_round_row_boolean air prev hf_prev with hround0 | hround1
        · exact hround0
        · rcases (is_round_iff_selector_lt_20 air prev hf_prev).mp hround1 with ⟨n, hn, hseln⟩
          have : (((n : ℕ) : FBB)) = 21 := by
            calc
              (((n : ℕ) : FBB)) = encoder_selector_idx air prev := hseln.symm
              _ = 21 := hsel21
          exact False.elim ((by decide : ∀ n : ℕ, n < 20 → (((n : ℕ) : FBB)) ≠ 21) n hn this)
      have hdigest_prev0 : is_digest_row air prev = 0 := by
        rcases is_digest_row_boolean air prev hf_prev with hdig0 | hdig1
        · exact hdig0
        · have hsel20 := (is_digest_iff_selector_eq_20 air prev hf_prev).mp hdig1
          have : (20 : FBB) = 21 := by
            calc
              (20 : FBB) = encoder_selector_idx air prev := hsel20.symm
              _ = 21 := hsel21
          exact False.elim ((by decide : (20 : FBB) ≠ 21) this)
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
      ∀ offset, offset < 20 →
        global_block_idx air (start + offset) = global_block_idx air start := by
    intro offset hoffset
    induction offset with
    | zero =>
        simp
    | succ offset ih =>
        have hrow_lt : start + offset < Circuit.last_row air := by
          dsimp [blockWindowSupported] at hwindow
          omega
        rcases hc (start + offset) with ⟨_, _, ht, _, _, _, _⟩
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
  have hdigest_gbi : global_block_idx air (start + 20) = global_block_idx air prev + 1 := by
    have hrow19_lt : start + 19 < Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    rcases hc (start + 19) with ⟨_, _, ht19, _, _, _, _⟩
    have hround19 : is_round_row air (start + 19) = 1 := (hround_rows 19 (by omega)).2.1
    calc
      global_block_idx air (start + 20) = global_block_idx air (start + 19) := by
        simpa [nextRow, hrow19_lt.ne, Nat.add_assoc] using
          block_idx_preserved_on_round air (start + 19) hrow19_lt hrot ht19 hround19
      _ = global_block_idx air start := hround_gbi 19 (by omega)
      _ = global_block_idx air prev + 1 := hgbi_start
  have hdigest_valid : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  rcases block_chaining_of_private_bus air prev (start + 20) h_private hprev_lt.le hdigest_valid
      hdigest_prev hdigest_row hdigest_gbi hnot_last with ⟨hchain, _⟩
  have hbb_prev : allWorkVarBitsBoolean air prev := allWorkVarBitsBoolean_of_constraints air prev hbits_prev
  have hrange : digestPrevHashLimbRange air (start + 20) := by
    intro word limb hword hlimb
    calc
      (prev_hash air word limb (start + 20)).val =
          (composed_hash_u16 air word limb prev).val := by
            rw [(hchain word limb hword hlimb).symm]
      _ < 2 ^ 16 := composed_hash_u16_range air prev word limb hbb_prev hword hlimb
  have hword_eq :
      ∀ word, word < 8 →
        digestPrevHashWord air (start + 20) word = digestWorkVarWord air prev word := by
    intro word hword
    have h0 :
        digestPrevHashU16Limb air (start + 20) word 0 = digestWorkVarU16Limb air prev word 0 := by
      calc
        digestPrevHashU16Limb air (start + 20) word 0 = prev_hash air word 0 (start + 20) := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 0 prev := (hchain word 0 hword (by omega)).symm
        _ = digestWorkVarU16Limb air prev word 0 := by
          simpa using composed_hash_eq_digestWorkVarLimb air prev word 0 hword (by omega)
    have h1 :
        digestPrevHashU16Limb air (start + 20) word 1 = digestWorkVarU16Limb air prev word 1 := by
      calc
        digestPrevHashU16Limb air (start + 20) word 1 = prev_hash air word 1 (start + 20) := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 1 prev := (hchain word 1 hword (by omega)).symm
        _ = digestWorkVarU16Limb air prev word 1 := by
          simpa using composed_hash_eq_digestWorkVarLimb air prev word 1 hword (by omega)
    have h2 :
        digestPrevHashU16Limb air (start + 20) word 2 = digestWorkVarU16Limb air prev word 2 := by
      calc
        digestPrevHashU16Limb air (start + 20) word 2 = prev_hash air word 2 (start + 20) := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 2 prev := (hchain word 2 hword (by omega)).symm
        _ = digestWorkVarU16Limb air prev word 2 := by
          simpa using composed_hash_eq_digestWorkVarLimb air prev word 2 hword (by omega)
    have h3 :
        digestPrevHashU16Limb air (start + 20) word 3 = digestWorkVarU16Limb air prev word 3 := by
      calc
        digestPrevHashU16Limb air (start + 20) word 3 = prev_hash air word 3 (start + 20) := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 3 prev := (hchain word 3 hword (by omega)).symm
        _ = digestWorkVarU16Limb air prev word 3 := by
          simpa using composed_hash_eq_digestWorkVarLimb air prev word 3 hword (by omega)
    rw [digestPrevHash_eq_limbs, digestWorkVar_eq_limbs air prev word hbb_prev, h0, h1, h2, h3]
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

private theorem digest_prev_hash_eq_start_wrap
    (air : C FBB ExtF)
    (hwindow : blockWindowSupported air 0)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air 0)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (htrace_fit : traceLengthFitsField air) :
    digestPrevHashLimbRange air 20 ∧
      digestPrevHashState air 20 = blockStartState air 0 := by
  rcases hshape with ⟨_, hround_rows, _, _, hdigest_row⟩
  have hperm :=
    privateBusEnabledReceiveSendPerm_of_rawPermutationSemantics air hrot hc h_raw_perm htrace_fit
  have hcover := privateBusReceiveCovered_of_permutation air hc hperm
  have hdigest_valid : 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  rcases hcover 20 hdigest_valid hdigest_row with ⟨sendRow, hsend_valid, hsend_dig, hmsg⟩
  have hsend_key : private_bus_next_gbi air sendRow = global_block_idx air 20 := by
    exact privateBus_send_eq_recv_implies_key_eq (air := air) (sendRow := sendRow) (recvRow := 20) hmsg
  have hgbi0 : global_block_idx air 0 = 1 := by
    have ht0 : trace_shape_constraints air 0 :=
      trace_shape_constraints_of_blockHasherConstraints air hc 0
    exact first_row_global_block_idx_one_of_trace_shape air ht0
  have hround_gbi :
      ∀ offset, offset < 20 →
        global_block_idx air offset = global_block_idx air 0 := by
    intro offset hoffset
    induction offset with
    | zero =>
        simp
    | succ offset ih =>
        have hrow_lt : offset < Circuit.last_row air := by
          dsimp [blockWindowSupported] at hwindow
          omega
        rcases hc offset with ⟨_, _, ht, _, _, _, _⟩
        have hround : is_round_row air offset = 1 := by
          simpa [Nat.zero_add] using (hround_rows offset (by omega)).2.1
        have hstep :
            global_block_idx air (offset + 1) = global_block_idx air offset := by
          simpa [nextRow, hrow_lt.ne] using
            block_idx_preserved_on_round air offset hrow_lt hrot ht hround
        calc
          global_block_idx air (offset + 1) = global_block_idx air offset := hstep
          _ = global_block_idx air 0 := ih (by omega)
  have hgbi20 : global_block_idx air 20 = 1 := by
    have hrow19_lt : 19 < Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    rcases hc 19 with ⟨_, _, ht19, _, _, _, _⟩
    have hround19 : is_round_row air 19 = 1 := (hround_rows 19 (by omega)).2.1
    calc
      global_block_idx air 20 = global_block_idx air 19 := by
        simpa [nextRow, hrow19_lt.ne] using
          block_idx_preserved_on_round air 19 hrow19_lt hrot ht19 hround19
      _ = global_block_idx air 0 := hround_gbi 19 (by omega)
      _ = 1 := hgbi0
  have hsend_key_one : private_bus_next_gbi air sendRow = 1 := by
    calc
      private_bus_next_gbi air sendRow = global_block_idx air 20 := hsend_key
      _ = 1 := hgbi20
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
      ∀ word limb, word < 8 → limb < 4 →
        prev_hash air word limb 20 = composed_hash_u16 air word limb sendRow := by
    intro word limb hword hlimb
    have hentry := congrArg (fun xs => xs[4 * word + limb]?) hmsg
    simpa [privateBus_send_data_get?_hash air sendRow word limb hword hlimb,
      privateBus_recv_data_get?_prev_hash air 20 word limb hword hlimb] using hentry.symm
  have hrange : digestPrevHashLimbRange air 20 := by
    intro word limb hword hlimb
    calc
      (prev_hash air word limb 20).val = (composed_hash_u16 air word limb sendRow).val := by
        rw [hrecv_eq word limb hword hlimb]
      _ < 2 ^ 16 := composed_hash_u16_range air sendRow word limb hbb_send hword hlimb
  have hword_eq :
      ∀ word, word < 8 →
        digestPrevHashWord air 20 word = digestWorkVarWord air sendRow word := by
    intro word hword
    have h0 :
        digestPrevHashU16Limb air 20 word 0 = digestWorkVarU16Limb air sendRow word 0 := by
      calc
        digestPrevHashU16Limb air 20 word 0 = prev_hash air word 0 20 := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 0 sendRow := hrecv_eq word 0 hword (by omega)
        _ = digestWorkVarU16Limb air sendRow word 0 := by
            simpa using composed_hash_eq_digestWorkVarLimb air sendRow word 0 hword (by omega)
    have h1 :
        digestPrevHashU16Limb air 20 word 1 = digestWorkVarU16Limb air sendRow word 1 := by
      calc
        digestPrevHashU16Limb air 20 word 1 = prev_hash air word 1 20 := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 1 sendRow := hrecv_eq word 1 hword (by omega)
        _ = digestWorkVarU16Limb air sendRow word 1 := by
            simpa using composed_hash_eq_digestWorkVarLimb air sendRow word 1 hword (by omega)
    have h2 :
        digestPrevHashU16Limb air 20 word 2 = digestWorkVarU16Limb air sendRow word 2 := by
      calc
        digestPrevHashU16Limb air 20 word 2 = prev_hash air word 2 20 := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 2 sendRow := hrecv_eq word 2 hword (by omega)
        _ = digestWorkVarU16Limb air sendRow word 2 := by
            simpa using composed_hash_eq_digestWorkVarLimb air sendRow word 2 hword (by omega)
    have h3 :
        digestPrevHashU16Limb air 20 word 3 = digestWorkVarU16Limb air sendRow word 3 := by
      calc
        digestPrevHashU16Limb air 20 word 3 = prev_hash air word 3 20 := by
          simp [digestPrevHashU16Limb]
        _ = composed_hash_u16 air word 3 sendRow := hrecv_eq word 3 hword (by omega)
        _ = digestWorkVarU16Limb air sendRow word 3 := by
            simpa using composed_hash_eq_digestWorkVarLimb air sendRow word 3 hword (by omega)
    rw [digestPrevHash_eq_limbs, digestWorkVar_eq_limbs air sendRow word hbb_send, h0, h1, h2, h3]
  refine ⟨hrange, ?_⟩
  calc
    digestPrevHashState air 20 = carriedState air sendRow := by
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

theorem digest_prev_hash_eq_start (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air)
    (htrace_fit : traceLengthFitsField air) :
    digestPrevHashLimbRange air (start + 20) ∧
      digestPrevHashState air (start + 20) = blockStartState air start := by
  by_cases hstart : start = 0
  · subst hstart
    exact digest_prev_hash_eq_start_wrap air hwindow hrot hshape hc h_raw_perm htrace_fit
  · exact digest_prev_hash_eq_start_nonwrap air start hstart hwindow hrot hshape hc
      h_raw_perm htrace_fit huniq_send

theorem digest_final_hash_correct (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_prev_range : digestPrevHashLimbRange air (start + 20))
    (h_wf_prev : bitwise_lookup_send_properties air (start + 19)) :
    let prevState := digestPrevHashState air (start + 20)
    let endState := carriedState air (start + 19)
    digestFinalHashState air (start + 20) = prevState.add endState := by
  dsimp
  have h0 := digest_word_addition_uint64 air start 0 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h1 := digest_word_addition_uint64 air start 1 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h2 := digest_word_addition_uint64 air start 2 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h3 := digest_word_addition_uint64 air start 3 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h4 := digest_word_addition_uint64 air start 4 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h5 := digest_word_addition_uint64 air start 5 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h6 := digest_word_addition_uint64 air start 6 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  have h7 := digest_word_addition_uint64 air start 7 (by omega) hwindow hrot hshape hc h_prev_range h_wf_prev
  rw [digestFinalHashState, digestPrevHashState, carriedState, WorkingVars.add, WorkingVars.mk.injEq]
  exact ⟨by simpa [digestWorkVarWord] using h0,
    by simpa [digestWorkVarWord] using h1,
    by simpa [digestWorkVarWord] using h2,
    by simpa [digestWorkVarWord] using h3,
    by simpa [digestWorkVarWord] using h4,
    by simpa [digestWorkVarWord] using h5,
    by simpa [digestWorkVarWord] using h6,
    by simpa [digestWorkVarWord] using h7⟩

theorem digest_row_correct (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air)
    (htrace_fit : traceLengthFitsField air)
    (h_wf_prev : bitwise_lookup_send_properties air (start + 19)) :
    digestPrevHashState air (start + 20) = blockStartState air start ∧
    digestFinalHashState air (start + 20) =
      (blockStartState air start).add (carriedState air (start + 19)) := by
  rcases digest_prev_hash_eq_start air start hwindow hrot hshape hc
      h_raw_perm huniq_send htrace_fit with
    ⟨hprev_range, hprev⟩
  have hfinal := digest_final_hash_correct air start hwindow hrot hshape hc hprev_range h_wf_prev
  refine ⟨hprev, ?_⟩
  simpa [hprev] using hfinal

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
