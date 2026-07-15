/-
  Layer C: Round Step (Single-Round Semantics)
  Round-constant lookup, single-round semantic bridge, and the shared
  low/high-limb rewrite layer used by the round-step update proofs.
  Depends on: Core
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.RoundStep.Core
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.SelectorCore

set_option autoImplicit false

set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem aWord_eq_bitsWordToUInt32 (air : C FBB ExtF) (row slot : ℕ) :
    aWord air row slot = bitsWordToUInt32 (aBitsWord air row slot) := by
  rw [aWord, bitsLEToWord, bitsWordToUInt32, foldl_range_add_eq_sum]
  have hrhs :
      (∑ i : Fin 32, (aBitsWord air row slot i).val * 2 ^ i.val : ℕ) =
        (Finset.sum (Finset.range 32) (fun i => (work_vars_a air slot i row).val * 2 ^ i) : ℕ) := by
    calc
      (∑ i : Fin 32, (aBitsWord air row slot i).val * 2 ^ i.val : ℕ)
          = Finset.sum (Finset.range 32)
              (fun i => if hi : i < 32 then (aBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0) := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (f := fun i =>
                    if hi : i < 32 then (aBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0)
                  (n := 32))
      _ = Finset.sum (Finset.range 32) (fun i => (work_vars_a air slot i row).val * 2 ^ i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi32 : i < 32 := Finset.mem_range.mp hi
            simp [hi32, aBitsWord]
  simpa using congrArg UInt32.ofNat hrhs.symm

theorem eWord_eq_bitsWordToUInt32 (air : C FBB ExtF) (row slot : ℕ) :
    eWord air row slot = bitsWordToUInt32 (eBitsWord air row slot) := by
  rw [eWord, bitsLEToWord, bitsWordToUInt32, foldl_range_add_eq_sum]
  have hrhs :
      (∑ i : Fin 32, (eBitsWord air row slot i).val * 2 ^ i.val : ℕ) =
        (Finset.sum (Finset.range 32) (fun i => (work_vars_e air slot i row).val * 2 ^ i) : ℕ) := by
    calc
      (∑ i : Fin 32, (eBitsWord air row slot i).val * 2 ^ i.val : ℕ)
          = Finset.sum (Finset.range 32)
              (fun i => if hi : i < 32 then (eBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0) := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (f := fun i =>
                    if hi : i < 32 then (eBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0)
                  (n := 32))
      _ = Finset.sum (Finset.range 32) (fun i => (work_vars_e air slot i row).val * 2 ^ i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi32 : i < 32 := Finset.mem_range.mp hi
            simp [hi32, eBitsWord]
  simpa using congrArg UInt32.ofNat hrhs.symm

def roundConstantLookupPoly
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : FBB)
    (d0 d1 d2 d3 d4 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4
  ((2 - s) * (1 - s) * 1006632961) * c0 +
  (d4 * (2 - s)) * c1 +
  (encoder_choose2 d4) * c2 +
  (d3 * (2 - s)) * c3 +
  (d3 * d4) * c4 +
  (encoder_choose2 d3) * c5 +
  (d2 * (2 - s)) * c6 +
  (d2 * d4) * c7 +
  (d2 * d3) * c8 +
  (encoder_choose2 d2) * c9 +
  (d1 * (2 - s)) * c10 +
  (d1 * d4) * c11 +
  (d1 * d3) * c12 +
  (d1 * d2) * c13 +
  (encoder_choose2 d1) * c14 +
  (d0 * (2 - s)) * c15

def roundConstantPolyAtNext (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  match slot, limb with
  | 0, 0 =>
      roundConstantLookupPoly
        12184 49755 43672 23924 27073 11375 20818 3059
        2693 29524 59553 59417 49430 3251 33518 65530
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 0, 1 =>
      roundConstantLookupPoly
        17034 14678 55303 29374 58523 11753 38974 50912
        10167 25866 41663 53650 6564 14620 29839 37054
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 1, 0 =>
      roundConstantLookupPoly
        17553 4593 23297 45566 18310 33962 50797 37191
        8504 2747 26187 1572 27656 43594 25455 27883
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 1, 1 =>
      roundConstantLookupPoly
        28983 23025 4739 32990 61374 19060 43057 54695
        11803 30314 43034 54937 7735 20184 30885 42064
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 2, 0 =>
      roundConstantLookupPoly
        64463 33444 34238 1703 40390 43484 10184 25425
        28156 51502 35696 13701 30540 51791 30740 41975
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 2, 1 =>
      roundConstantLookupPoly
        46528 37439 9265 39900 4033 23728 45059 1738
        19756 33218 49739 62478 10056 23452 33992 48889
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 3, 0 =>
      roundConstantLookupPoly
        56229 24277 32195 61812 41420 35034 32711 10599
        3347 11397 20899 41072 48309 28659 520 30962
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | 3, 1 =>
      roundConstantLookupPoly
        59829 43804 21772 49563 9228 30457 48985 5161
        21304 37490 51052 4202 13488 26670 36039 50801
        (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
        (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
        (encoder_idx_next air 4 row)
  | _, _ => 0
theorem concatABits_boolean
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    isBitsWord (concatABitsWord air row j) := by
  by_cases hj : j < 4
  · intro i
    simp [concatABitsWord, hj]
    exact hbb.1 j i.val hj i.isLt
  · intro i
    simp [concatABitsWord, hj]
    exact hbb_next.1 (j - 4) i.val (by omega) i.isLt

theorem concatEBits_boolean
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    isBitsWord (concatEBitsWord air row j) := by
  by_cases hj : j < 4
  · intro i
    simp [concatEBitsWord, hj]
    exact hbb.2 j i.val hj i.isLt
  · intro i
    simp [concatEBitsWord, hj]
    exact hbb_next.2 (j - 4) i.val (by omega) i.isLt

theorem concatAWord_eq_bitsWordToUInt32
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    concatAWord air row j = bitsWordToUInt32 (concatABitsWord air row j) := by
  by_cases hj : j < 4
  · simp [concatAWord, concatABitsWord, hj, aWord_eq_bitsWordToUInt32]
  · simp [concatAWord, concatABitsWord, hj, aWord_eq_bitsWordToUInt32]

theorem concatEWord_eq_bitsWordToUInt32
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    concatEWord air row j = bitsWordToUInt32 (concatEBitsWord air row j) := by
  by_cases hj : j < 4
  · simp [concatEWord, concatEBitsWord, hj, eWord_eq_bitsWordToUInt32]
  · simp [concatEWord, concatEBitsWord, hj, eWord_eq_bitsWordToUInt32]

private def roundConstantPolyAtDigits
    (slot limb : ℕ) (d0 d1 d2 d3 d4 : FBB) : FBB :=
  match slot, limb with
  | 0, 0 =>
      roundConstantLookupPoly
        12184 49755 43672 23924 27073 11375 20818 3059
        2693 29524 59553 59417 49430 3251 33518 65530
        d0 d1 d2 d3 d4
  | 0, 1 =>
      roundConstantLookupPoly
        17034 14678 55303 29374 58523 11753 38974 50912
        10167 25866 41663 53650 6564 14620 29839 37054
        d0 d1 d2 d3 d4
  | 1, 0 =>
      roundConstantLookupPoly
        17553 4593 23297 45566 18310 33962 50797 37191
        8504 2747 26187 1572 27656 43594 25455 27883
        d0 d1 d2 d3 d4
  | 1, 1 =>
      roundConstantLookupPoly
        28983 23025 4739 32990 61374 19060 43057 54695
        11803 30314 43034 54937 7735 20184 30885 42064
        d0 d1 d2 d3 d4
  | 2, 0 =>
      roundConstantLookupPoly
        64463 33444 34238 1703 40390 43484 10184 25425
        28156 51502 35696 13701 30540 51791 30740 41975
        d0 d1 d2 d3 d4
  | 2, 1 =>
      roundConstantLookupPoly
        46528 37439 9265 39900 4033 23728 45059 1738
        19756 33218 49739 62478 10056 23452 33992 48889
        d0 d1 d2 d3 d4
  | 3, 0 =>
      roundConstantLookupPoly
        56229 24277 32195 61812 41420 35034 32711 10599
        3347 11397 20899 41072 48309 28659 520 30962
        d0 d1 d2 d3 d4
  | 3, 1 =>
      roundConstantLookupPoly
        59829 43804 21772 49563 9228 30457 48985 5161
        21304 37490 51052 4202 13488 26670 36039 50801
        d0 d1 d2 d3 d4
  | _, _ => 0

private theorem roundConstant_lookup_fin_00 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 0 0 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 0 0 := by
  decide +kernel

private theorem roundConstant_lookup_fin_01 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 0 1 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 0 1 := by
  decide +kernel

private theorem roundConstant_lookup_fin_10 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 1 0 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 1 0 := by
  decide +kernel

private theorem roundConstant_lookup_fin_11 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 1 1 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 1 1 := by
  decide +kernel

private theorem roundConstant_lookup_fin_20 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 2 0 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 2 0 := by
  decide +kernel

private theorem roundConstant_lookup_fin_21 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 2 1 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 2 1 := by
  decide +kernel

private theorem roundConstant_lookup_fin_30 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 3 0 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 3 0 := by
  decide +kernel

private theorem roundConstant_lookup_fin_31 :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits 3 1 (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val 3 1 := by
  decide +kernel

private theorem roundConstant_lookup_fin
    (slot limb : ℕ) (hslot : slot < 4) (hlimb : limb < 2) :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      ∀ row_idx : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (row_idx.val : FBB) →
        roundConstantPolyAtDigits slot limb (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = k_limb_at row_idx.val slot limb := by
  interval_cases slot <;> interval_cases limb
  · exact roundConstant_lookup_fin_00
  · exact roundConstant_lookup_fin_01
  · exact roundConstant_lookup_fin_10
  · exact roundConstant_lookup_fin_11
  · exact roundConstant_lookup_fin_20
  · exact roundConstant_lookup_fin_21
  · exact roundConstant_lookup_fin_30
  · exact roundConstant_lookup_fin_31

private theorem roundConstantPolyAtNext_eq_digits
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 2)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    roundConstantPolyAtNext air row slot limb =
      roundConstantPolyAtDigits slot limb
        (encoder_idx air 0 (nextRow air row))
        (encoder_idx air 1 (nextRow air row))
        (encoder_idx air 2 (nextRow air row))
        (encoder_idx air 3 (nextRow air row))
        (encoder_idx air 4 (nextRow air row)) := by
  interval_cases slot <;> interval_cases limb <;>
    simp [roundConstantPolyAtNext, roundConstantPolyAtDigits,
      encoder_idx_next_eq_nextRow air hrot 0 row hrow,
      encoder_idx_next_eq_nextRow air hrot 1 row hrow,
      encoder_idx_next_eq_nextRow air hrot 2 row hrow,
      encoder_idx_next_eq_nextRow air hrot 3 row hrow,
      encoder_idx_next_eq_nextRow air hrot 4 row hrow]

theorem roundConstantPolyAtNext_eq_k_limb_at
    (air : C FBB ExtF) (row slot limb row_idx : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 2)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    roundConstantPolyAtNext air row slot limb = k_limb_at row_idx slot limb := by
  have hf := hflags_next
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, h10, _, _, _, _, _⟩
  have hd0 := encoder_digits_ternary air (nextRow air row) hflags_next 0 (by omega)
  have hd1 := encoder_digits_ternary air (nextRow air row) hflags_next 1 (by omega)
  have hd2 := encoder_digits_ternary air (nextRow air row) hflags_next 2 (by omega)
  have hd3 := encoder_digits_ternary air (nextRow air row) hflags_next 3 (by omega)
  have hd4 := encoder_digits_ternary air (nextRow air row) hflags_next 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 (nextRow air row)) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 (nextRow air row)) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 (nextRow air row)) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 (nextRow air row)) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 (nextRow air row)) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air (nextRow air row) hflags_next
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 :=
    nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc10 : encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 := by
    have h10c : constraint_10 air (nextRow air row) :=
      (constraint_10_of_extraction air (nextRow air row)).mp h10
    simpa [encoderConstraint10Poly, constraint_10, encoder_choose2, h0, h1, h2] using h10c
  let idx : Fin 16 := ⟨row_idx, hidx_bound⟩
  have hsel :
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = (idx.val : FBB) := by
    simpa [idx, encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
      encoderSelectorPoly, h0, h1, h2, h3, h4] using hidx
  have hlookup :=
    roundConstant_lookup_fin slot limb hslot hlimb n0 n1 n2 n3 n4 htotal_le hc10 idx hsel
  rw [roundConstantPolyAtNext_eq_digits air row slot limb hslot hlimb hrot hrow]
  simpa [h0, h1, h2, h3, h4] using hlookup

theorem k_limb_at_lt
    (row_idx slot limb : ℕ)
    (hidx_bound : row_idx < 16)
    (hslot : slot < 4)
    (hlimb : limb < 2) :
    (k_limb_at row_idx slot limb).val < 2 ^ 16 := by
  interval_cases row_idx <;> interval_cases slot <;> interval_cases limb <;> decide +kernel

theorem k_word_eq_limbs
    (row_idx slot : ℕ)
    (hidx_bound : row_idx < 16)
    (hslot : slot < 4) :
    sha256K[row_idx * 4 + slot]! =
      ((k_limb_at row_idx slot 0).val + (k_limb_at row_idx slot 1).val * 2 ^ 16).toUInt32 := by
  interval_cases row_idx <;> interval_cases slot <;> decide +kernel

/-! ## Field lemmas (formerly RoundStepFieldLemmas) -/

theorem composeLo16_explicit (bits : BitsWord) :
    composeLo16 bits =
      bits ⟨0, by omega⟩ + bits ⟨1, by omega⟩ * 2 +
      bits ⟨2, by omega⟩ * 4 + bits ⟨3, by omega⟩ * 8 +
      bits ⟨4, by omega⟩ * 16 + bits ⟨5, by omega⟩ * 32 +
      bits ⟨6, by omega⟩ * 64 + bits ⟨7, by omega⟩ * 128 +
      bits ⟨8, by omega⟩ * 256 + bits ⟨9, by omega⟩ * 512 +
      bits ⟨10, by omega⟩ * 1024 + bits ⟨11, by omega⟩ * 2048 +
      bits ⟨12, by omega⟩ * 4096 + bits ⟨13, by omega⟩ * 8192 +
      bits ⟨14, by omega⟩ * 16384 + bits ⟨15, by omega⟩ * 32768 := by
  rw [composeLo16_range_eq]
  norm_num [Finset.sum_range_succ]

theorem composeHi16_explicit (bits : BitsWord) :
    composeHi16 bits =
      bits ⟨16, by omega⟩ + bits ⟨17, by omega⟩ * 2 +
      bits ⟨18, by omega⟩ * 4 + bits ⟨19, by omega⟩ * 8 +
      bits ⟨20, by omega⟩ * 16 + bits ⟨21, by omega⟩ * 32 +
      bits ⟨22, by omega⟩ * 64 + bits ⟨23, by omega⟩ * 128 +
      bits ⟨24, by omega⟩ * 256 + bits ⟨25, by omega⟩ * 512 +
      bits ⟨26, by omega⟩ * 1024 + bits ⟨27, by omega⟩ * 2048 +
      bits ⟨28, by omega⟩ * 4096 + bits ⟨29, by omega⟩ * 8192 +
      bits ⟨30, by omega⟩ * 16384 + bits ⟨31, by omega⟩ * 32768 := by
  rw [composeHi16_range_eq]
  norm_num [Finset.sum_range_succ]

theorem fieldCh_poly (x y z : BitsWord) (hx : isBitsWord x) :
    fieldCh x y z = fun i => x i * y i + (1 - x i) * z i := by
  funext i
  rcases hx i with hxi | hxi <;> simp [fieldCh, fieldXor, fieldAnd, fieldNot, *]

theorem fieldMaj_poly (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    fieldMaj x y z =
      fun i => x i * y i + x i * z i + y i * z i - 2 * x i * y i * z i := by
  funext i
  rcases hx i with hx0 | hx1 <;>
    rcases hy i with hy0 | hy1 <;>
    rcases hz i with hz0 | hz1 <;>
    simp [fieldMaj, fieldXor, fieldAnd, *]

theorem fieldBigSigma0_poly (x : BitsWord) :
    fieldBigSigma0 x =
      fun i =>
        x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩ *
            x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩ *
            x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩ +
          x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩ *
              (1 - x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩) *
              (1 - x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩ *
              (1 - x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩) *
              (1 - x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩ := by
  funext i
  simpa [fieldBigSigma0, fieldRotr] using
    (fieldXor3_poly
      (x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩)
      (x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩)
      (x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩))

theorem fieldBigSigma1_poly (x : BitsWord) :
    fieldBigSigma1 x =
      fun i =>
        x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩ *
            x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩ *
            x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩ +
          x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩ *
              (1 - x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩) *
              (1 - x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩ *
              (1 - x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩) *
              (1 - x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩ := by
  funext i
  simpa [fieldBigSigma1, fieldRotr] using
    (fieldXor3_poly
      (x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩)
      (x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩)
      (x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩))

abbrev lo16Expr (bits : BitsWord) : FBB :=
  bits ⟨0, by decide⟩ +
    bits ⟨1, by decide⟩ * 2 +
    bits ⟨2, by decide⟩ * 4 +
    bits ⟨3, by decide⟩ * 8 +
    bits ⟨4, by decide⟩ * 16 +
    bits ⟨5, by decide⟩ * 32 +
    bits ⟨6, by decide⟩ * 64 +
    bits ⟨7, by decide⟩ * 128 +
    bits ⟨8, by decide⟩ * 256 +
    bits ⟨9, by decide⟩ * 512 +
    bits ⟨10, by decide⟩ * 1024 +
    bits ⟨11, by decide⟩ * 2048 +
    bits ⟨12, by decide⟩ * 4096 +
    bits ⟨13, by decide⟩ * 8192 +
    bits ⟨14, by decide⟩ * 16384 +
    bits ⟨15, by decide⟩ * 32768

theorem composeLo16_eq_lo16Expr (bits : BitsWord) :
    composeLo16 bits = lo16Expr bits := by
  rw [composeLo16_explicit]

abbrev round_step_a_lo_sigma1_bit (air : C FBB ExtF) (row slot : ℕ) (i : Fin 16) : FBB :=
  rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩ *
      rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩ *
      rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩ +
    rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩) *
        rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩) *
        rawConcatEBitsWord air row (slot + 3) ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩

abbrev round_step_a_lo_sigma1_rhs (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  round_step_a_lo_sigma1_bit air row slot ⟨0, by decide⟩ +
    round_step_a_lo_sigma1_bit air row slot ⟨1, by decide⟩ * 2 +
    round_step_a_lo_sigma1_bit air row slot ⟨2, by decide⟩ * 4 +
    round_step_a_lo_sigma1_bit air row slot ⟨3, by decide⟩ * 8 +
    round_step_a_lo_sigma1_bit air row slot ⟨4, by decide⟩ * 16 +
    round_step_a_lo_sigma1_bit air row slot ⟨5, by decide⟩ * 32 +
    round_step_a_lo_sigma1_bit air row slot ⟨6, by decide⟩ * 64 +
    round_step_a_lo_sigma1_bit air row slot ⟨7, by decide⟩ * 128 +
    round_step_a_lo_sigma1_bit air row slot ⟨8, by decide⟩ * 256 +
    round_step_a_lo_sigma1_bit air row slot ⟨9, by decide⟩ * 512 +
    round_step_a_lo_sigma1_bit air row slot ⟨10, by decide⟩ * 1024 +
    round_step_a_lo_sigma1_bit air row slot ⟨11, by decide⟩ * 2048 +
    round_step_a_lo_sigma1_bit air row slot ⟨12, by decide⟩ * 4096 +
    round_step_a_lo_sigma1_bit air row slot ⟨13, by decide⟩ * 8192 +
    round_step_a_lo_sigma1_bit air row slot ⟨14, by decide⟩ * 16384 +
    round_step_a_lo_sigma1_bit air row slot ⟨15, by decide⟩ * 32768

theorem round_step_a_lo_sigma1_eq (air : C FBB ExtF) (row slot : ℕ) :
    composeLo16 (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) =
      round_step_a_lo_sigma1_rhs air row slot := by
  rw [composeLo16_explicit]
  simp [round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
    fieldBigSigma1_poly, rawConcatEBitsWord]

abbrev round_step_a_lo_ch_bit (air : C FBB ExtF) (row slot : ℕ) (i : Fin 16) : FBB :=
  rawConcatEBitsWord air row (slot + 3) ⟨i.val, by omega⟩ *
      rawConcatEBitsWord air row (slot + 2) ⟨i.val, by omega⟩ +
    (1 - rawConcatEBitsWord air row (slot + 3) ⟨i.val, by omega⟩) *
      rawConcatEBitsWord air row (slot + 1) ⟨i.val, by omega⟩

abbrev round_step_a_lo_ch_rhs (air : C FBB ExtF) (row slot : ℕ)
    (_hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3))) : FBB :=
  round_step_a_lo_ch_bit air row slot ⟨0, by decide⟩ +
    round_step_a_lo_ch_bit air row slot ⟨1, by decide⟩ * 2 +
    round_step_a_lo_ch_bit air row slot ⟨2, by decide⟩ * 4 +
    round_step_a_lo_ch_bit air row slot ⟨3, by decide⟩ * 8 +
    round_step_a_lo_ch_bit air row slot ⟨4, by decide⟩ * 16 +
    round_step_a_lo_ch_bit air row slot ⟨5, by decide⟩ * 32 +
    round_step_a_lo_ch_bit air row slot ⟨6, by decide⟩ * 64 +
    round_step_a_lo_ch_bit air row slot ⟨7, by decide⟩ * 128 +
    round_step_a_lo_ch_bit air row slot ⟨8, by decide⟩ * 256 +
    round_step_a_lo_ch_bit air row slot ⟨9, by decide⟩ * 512 +
    round_step_a_lo_ch_bit air row slot ⟨10, by decide⟩ * 1024 +
    round_step_a_lo_ch_bit air row slot ⟨11, by decide⟩ * 2048 +
    round_step_a_lo_ch_bit air row slot ⟨12, by decide⟩ * 4096 +
    round_step_a_lo_ch_bit air row slot ⟨13, by decide⟩ * 8192 +
    round_step_a_lo_ch_bit air row slot ⟨14, by decide⟩ * 16384 +
    round_step_a_lo_ch_bit air row slot ⟨15, by decide⟩ * 32768

theorem round_step_a_lo_ch_eq (air : C FBB ExtF) (row slot : ℕ)
    (hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3))) :
    composeLo16 (fieldCh (rawConcatEBitsWord air row (slot + 3))
        (rawConcatEBitsWord air row (slot + 2))
        (rawConcatEBitsWord air row (slot + 1))) =
      round_step_a_lo_ch_rhs air row slot hrawE_bits := by
  rw [composeLo16_explicit, fieldCh_poly _ _ _ hrawE_bits]

abbrev round_step_a_lo_sigma0_bit (air : C FBB ExtF) (row slot : ℕ) (i : Fin 16) : FBB :=
  rawConcatABitsWord air row (slot + 3) ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩ *
      rawConcatABitsWord air row (slot + 3) ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩ *
      rawConcatABitsWord air row (slot + 3) ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩ +
    rawConcatABitsWord air row (slot + 3) ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - rawConcatABitsWord air row (slot + 3) ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - rawConcatABitsWord air row (slot + 3) ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - rawConcatABitsWord air row (slot + 3) ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩) *
        rawConcatABitsWord air row (slot + 3) ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - rawConcatABitsWord air row (slot + 3) ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - rawConcatABitsWord air row (slot + 3) ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - rawConcatABitsWord air row (slot + 3) ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩) *
        rawConcatABitsWord air row (slot + 3) ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩

abbrev round_step_a_lo_sigma0_rhs (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  round_step_a_lo_sigma0_bit air row slot ⟨0, by decide⟩ +
    round_step_a_lo_sigma0_bit air row slot ⟨1, by decide⟩ * 2 +
    round_step_a_lo_sigma0_bit air row slot ⟨2, by decide⟩ * 4 +
    round_step_a_lo_sigma0_bit air row slot ⟨3, by decide⟩ * 8 +
    round_step_a_lo_sigma0_bit air row slot ⟨4, by decide⟩ * 16 +
    round_step_a_lo_sigma0_bit air row slot ⟨5, by decide⟩ * 32 +
    round_step_a_lo_sigma0_bit air row slot ⟨6, by decide⟩ * 64 +
    round_step_a_lo_sigma0_bit air row slot ⟨7, by decide⟩ * 128 +
    round_step_a_lo_sigma0_bit air row slot ⟨8, by decide⟩ * 256 +
    round_step_a_lo_sigma0_bit air row slot ⟨9, by decide⟩ * 512 +
    round_step_a_lo_sigma0_bit air row slot ⟨10, by decide⟩ * 1024 +
    round_step_a_lo_sigma0_bit air row slot ⟨11, by decide⟩ * 2048 +
    round_step_a_lo_sigma0_bit air row slot ⟨12, by decide⟩ * 4096 +
    round_step_a_lo_sigma0_bit air row slot ⟨13, by decide⟩ * 8192 +
    round_step_a_lo_sigma0_bit air row slot ⟨14, by decide⟩ * 16384 +
    round_step_a_lo_sigma0_bit air row slot ⟨15, by decide⟩ * 32768

theorem round_step_a_lo_sigma0_eq (air : C FBB ExtF) (row slot : ℕ) :
    composeLo16 (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) =
      round_step_a_lo_sigma0_rhs air row slot := by
  rw [composeLo16_explicit]
  simp [round_step_a_lo_sigma0_rhs, round_step_a_lo_sigma0_bit,
    fieldBigSigma0_poly, rawConcatABitsWord]

abbrev round_step_a_lo_maj_bit (air : C FBB ExtF) (row slot : ℕ) (i : Fin 16) : FBB :=
  rawConcatABitsWord air row (slot + 3) ⟨i.val, by omega⟩ *
      rawConcatABitsWord air row (slot + 2) ⟨i.val, by omega⟩ +
    rawConcatABitsWord air row (slot + 3) ⟨i.val, by omega⟩ *
      rawConcatABitsWord air row (slot + 1) ⟨i.val, by omega⟩ +
    rawConcatABitsWord air row (slot + 2) ⟨i.val, by omega⟩ *
      rawConcatABitsWord air row (slot + 1) ⟨i.val, by omega⟩ -
    2 * rawConcatABitsWord air row (slot + 3) ⟨i.val, by omega⟩ *
      rawConcatABitsWord air row (slot + 2) ⟨i.val, by omega⟩ *
      rawConcatABitsWord air row (slot + 1) ⟨i.val, by omega⟩

abbrev round_step_a_lo_maj_rhs (air : C FBB ExtF) (row slot : ℕ)
    (_hrawA3_bits : isBitsWord (rawConcatABitsWord air row (slot + 3)))
    (_hrawA2_bits : isBitsWord (rawConcatABitsWord air row (slot + 2)))
    (_hrawA1_bits : isBitsWord (rawConcatABitsWord air row (slot + 1))) : FBB :=
  round_step_a_lo_maj_bit air row slot ⟨0, by decide⟩ +
    round_step_a_lo_maj_bit air row slot ⟨1, by decide⟩ * 2 +
    round_step_a_lo_maj_bit air row slot ⟨2, by decide⟩ * 4 +
    round_step_a_lo_maj_bit air row slot ⟨3, by decide⟩ * 8 +
    round_step_a_lo_maj_bit air row slot ⟨4, by decide⟩ * 16 +
    round_step_a_lo_maj_bit air row slot ⟨5, by decide⟩ * 32 +
    round_step_a_lo_maj_bit air row slot ⟨6, by decide⟩ * 64 +
    round_step_a_lo_maj_bit air row slot ⟨7, by decide⟩ * 128 +
    round_step_a_lo_maj_bit air row slot ⟨8, by decide⟩ * 256 +
    round_step_a_lo_maj_bit air row slot ⟨9, by decide⟩ * 512 +
    round_step_a_lo_maj_bit air row slot ⟨10, by decide⟩ * 1024 +
    round_step_a_lo_maj_bit air row slot ⟨11, by decide⟩ * 2048 +
    round_step_a_lo_maj_bit air row slot ⟨12, by decide⟩ * 4096 +
    round_step_a_lo_maj_bit air row slot ⟨13, by decide⟩ * 8192 +
    round_step_a_lo_maj_bit air row slot ⟨14, by decide⟩ * 16384 +
    round_step_a_lo_maj_bit air row slot ⟨15, by decide⟩ * 32768

theorem round_step_a_lo_maj_eq (air : C FBB ExtF) (row slot : ℕ)
    (hrawA3_bits : isBitsWord (rawConcatABitsWord air row (slot + 3)))
    (hrawA2_bits : isBitsWord (rawConcatABitsWord air row (slot + 2)))
    (hrawA1_bits : isBitsWord (rawConcatABitsWord air row (slot + 1))) :
    composeLo16 (fieldMaj (rawConcatABitsWord air row (slot + 3))
        (rawConcatABitsWord air row (slot + 2))
        (rawConcatABitsWord air row (slot + 1))) =
      round_step_a_lo_maj_rhs air row slot hrawA3_bits hrawA2_bits hrawA1_bits := by
  rw [composeLo16_explicit, fieldMaj_poly _ _ _ hrawA3_bits hrawA2_bits hrawA1_bits]

private theorem round_step_a_lo_eq_expanded_source (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row)
    (hrawA3_bits : isBitsWord (rawConcatABitsWord air row (slot + 3)))
    (hrawA2_bits : isBitsWord (rawConcatABitsWord air row (slot + 2)))
    (hrawA1_bits : isBitsWord (rawConcatABitsWord air row (slot + 1)))
    (hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3))) :
    lo16Expr (rawConcatEBitsWord air row slot) +
      round_step_a_lo_sigma1_rhs air row slot +
      round_step_a_lo_ch_rhs air row slot hrawE_bits +
      round_step_a_lo_sigma0_rhs air row slot +
      round_step_a_lo_maj_rhs air row slot hrawA3_bits hrawA2_bits hrawA1_bits +
      lo16Expr (nextScheduleBitsWord air row slot) * next_is_round_row air row +
      roundConstantPolyAtNext air row slot 0 -
        (lo16Expr (nextABitsWord air row slot) +
          next_carry_a air slot 0 row * 65536) = 0 := by
  have hslot' : roundStepALoConstraint air row slot := round_step_a_lo air row slot hslot hrs
  interval_cases slot
  · simpa only [roundStepALoConstraint, constraint_721, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      round_step_a_lo_sigma0_rhs, round_step_a_lo_sigma0_bit,
      round_step_a_lo_maj_rhs, round_step_a_lo_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepALoConstraint, constraint_725, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      round_step_a_lo_sigma0_rhs, round_step_a_lo_sigma0_bit,
      round_step_a_lo_maj_rhs, round_step_a_lo_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepALoConstraint, constraint_729, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      round_step_a_lo_sigma0_rhs, round_step_a_lo_sigma0_bit,
      round_step_a_lo_maj_rhs, round_step_a_lo_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepALoConstraint, constraint_733, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      round_step_a_lo_sigma0_rhs, round_step_a_lo_sigma0_bit,
      round_step_a_lo_maj_rhs, round_step_a_lo_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'

theorem round_step_a_lo_eq_expanded (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16)
    (hrawA3_bits : isBitsWord (rawConcatABitsWord air row (slot + 3)))
    (hrawA2_bits : isBitsWord (rawConcatABitsWord air row (slot + 2)))
    (hrawA1_bits : isBitsWord (rawConcatABitsWord air row (slot + 1)))
    (hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3))) :
    lo16Expr (rawConcatEBitsWord air row slot) +
      round_step_a_lo_sigma1_rhs air row slot +
      round_step_a_lo_ch_rhs air row slot hrawE_bits +
      k_limb_at row_idx slot 0 +
      lo16Expr (nextScheduleBitsWord air row slot) +
      round_step_a_lo_sigma0_rhs air row slot +
      round_step_a_lo_maj_rhs air row slot hrawA3_bits hrawA2_bits hrawA1_bits -
        (lo16Expr (nextABitsWord air row slot) +
          next_carry_a air slot 0 row * (2 ^ 16 : ℕ)) = 0 := by
  have hk :
      roundConstantPolyAtNext air row slot 0 = k_limb_at row_idx slot 0 :=
    roundConstantPolyAtNext_eq_k_limb_at air row slot 0 row_idx
      hslot (by omega) hrot hrow hflags_next hidx hidx_bound
  have hsrc := round_step_a_lo_eq_expanded_source air row slot hslot hrs hrawA3_bits hrawA2_bits
    hrawA1_bits hrawE_bits
  have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by
    norm_num
  rw [hround_next, hk, ← hpow] at hsrc
  simp only [mul_one] at hsrc
  set e := lo16Expr (rawConcatEBitsWord air row slot)
  set sigma1 := round_step_a_lo_sigma1_rhs air row slot
  set ch := round_step_a_lo_ch_rhs air row slot hrawE_bits
  set sigma0 := round_step_a_lo_sigma0_rhs air row slot
  set maj := round_step_a_lo_maj_rhs air row slot hrawA3_bits hrawA2_bits hrawA1_bits
  set sched := lo16Expr (nextScheduleBitsWord air row slot)
  set nextA := lo16Expr (nextABitsWord air row slot) + next_carry_a air slot 0 row * (2 ^ 16 : ℕ)
  have hperm : e + sigma1 + ch + sigma0 + maj + sched + k_limb_at row_idx slot 0 =
      e + sigma1 + ch + k_limb_at row_idx slot 0 + sched + sigma0 + maj := by
    ac_rfl
  rw [hperm] at hsrc
  simpa [e, sigma1, ch, sigma0, maj, sched, nextA] using hsrc

theorem round_step_a_lo_eq_raw (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeLo16 (rawConcatEBitsWord air row slot) +
      composeLo16 (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) +
      composeLo16 (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 0 +
      composeLo16 (nextScheduleBitsWord air row slot) +
      composeLo16 (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) +
      composeLo16 (fieldMaj (rawConcatABitsWord air row (slot + 3))
          (rawConcatABitsWord air row (slot + 2))
          (rawConcatABitsWord air row (slot + 1))) =
    composeLo16 (nextABitsWord air row slot) +
      next_carry_a air slot 0 row * (2 ^ 16 : ℕ) := by
  have hrawA1_bits : isBitsWord (rawConcatABitsWord air row (slot + 1)) := by
    simpa [rawConcatABitsWord_eq_concatABitsWord air row (slot + 1) hrot hrow] using
      concatABits_boolean air row (slot + 1) (by omega) hbb hbb_next
  have hrawA2_bits : isBitsWord (rawConcatABitsWord air row (slot + 2)) := by
    simpa [rawConcatABitsWord_eq_concatABitsWord air row (slot + 2) hrot hrow] using
      concatABits_boolean air row (slot + 2) (by omega) hbb hbb_next
  have hrawA3_bits : isBitsWord (rawConcatABitsWord air row (slot + 3)) := by
    simpa [rawConcatABitsWord_eq_concatABitsWord air row (slot + 3) hrot hrow] using
      concatABits_boolean air row (slot + 3) (by omega) hbb hbb_next
  have hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3)) := by
    simpa [rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow] using
      concatEBits_boolean air row (slot + 3) (by omega) hbb hbb_next
  have hexpanded := round_step_a_lo_eq_expanded air row slot row_idx hslot hrow hrot hrs
    hbb_next hround_next hflags_next hidx hidx_bound hrawA3_bits hrawA2_bits hrawA1_bits
    hrawE_bits
  rw [← composeLo16_eq_lo16Expr (rawConcatEBitsWord air row slot),
    ← round_step_a_lo_sigma1_eq air row slot,
    ← round_step_a_lo_ch_eq air row slot hrawE_bits,
    ← composeLo16_eq_lo16Expr (nextScheduleBitsWord air row slot),
    ← round_step_a_lo_sigma0_eq air row slot,
    ← round_step_a_lo_maj_eq air row slot hrawA3_bits hrawA2_bits hrawA1_bits,
    ← composeLo16_eq_lo16Expr (nextABitsWord air row slot)] at hexpanded
  exact sub_eq_zero.mp hexpanded

abbrev hi16Expr (bits : BitsWord) : FBB :=
  bits ⟨16, by decide⟩ +
    bits ⟨17, by decide⟩ * 2 +
    bits ⟨18, by decide⟩ * 4 +
    bits ⟨19, by decide⟩ * 8 +
    bits ⟨20, by decide⟩ * 16 +
    bits ⟨21, by decide⟩ * 32 +
    bits ⟨22, by decide⟩ * 64 +
    bits ⟨23, by decide⟩ * 128 +
    bits ⟨24, by decide⟩ * 256 +
    bits ⟨25, by decide⟩ * 512 +
    bits ⟨26, by decide⟩ * 1024 +
    bits ⟨27, by decide⟩ * 2048 +
    bits ⟨28, by decide⟩ * 4096 +
    bits ⟨29, by decide⟩ * 8192 +
    bits ⟨30, by decide⟩ * 16384 +
    bits ⟨31, by decide⟩ * 32768

theorem composeHi16_eq_hi16Expr (bits : BitsWord) :
    composeHi16 bits = hi16Expr bits := by
  rw [composeHi16_explicit]

abbrev round_step_a_hi_sigma1_bit (bits : BitsWord) (i : ℕ) : FBB :=
  bits ⟨(i + 6) % 32, Nat.mod_lt _ (by omega)⟩ *
      bits ⟨(i + 11) % 32, Nat.mod_lt _ (by omega)⟩ *
      bits ⟨(i + 25) % 32, Nat.mod_lt _ (by omega)⟩ +
    bits ⟨(i + 6) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - bits ⟨(i + 11) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - bits ⟨(i + 25) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - bits ⟨(i + 6) % 32, Nat.mod_lt _ (by omega)⟩) *
        bits ⟨(i + 11) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - bits ⟨(i + 25) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - bits ⟨(i + 6) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - bits ⟨(i + 11) % 32, Nat.mod_lt _ (by omega)⟩) *
        bits ⟨(i + 25) % 32, Nat.mod_lt _ (by omega)⟩

abbrev round_step_a_hi_sigma1_rhs (bits : BitsWord) : FBB :=
  round_step_a_hi_sigma1_bit bits 16 +
    round_step_a_hi_sigma1_bit bits 17 * 2 +
    round_step_a_hi_sigma1_bit bits 18 * 4 +
    round_step_a_hi_sigma1_bit bits 19 * 8 +
    round_step_a_hi_sigma1_bit bits 20 * 16 +
    round_step_a_hi_sigma1_bit bits 21 * 32 +
    round_step_a_hi_sigma1_bit bits 22 * 64 +
    round_step_a_hi_sigma1_bit bits 23 * 128 +
    round_step_a_hi_sigma1_bit bits 24 * 256 +
    round_step_a_hi_sigma1_bit bits 25 * 512 +
    round_step_a_hi_sigma1_bit bits 26 * 1024 +
    round_step_a_hi_sigma1_bit bits 27 * 2048 +
    round_step_a_hi_sigma1_bit bits 28 * 4096 +
    round_step_a_hi_sigma1_bit bits 29 * 8192 +
    round_step_a_hi_sigma1_bit bits 30 * 16384 +
    round_step_a_hi_sigma1_bit bits 31 * 32768

theorem round_step_a_hi_sigma1_eq (bits : BitsWord) :
    composeHi16 (fieldBigSigma1 bits) = round_step_a_hi_sigma1_rhs bits := by
  rw [composeHi16_explicit]
  simp [round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit, fieldBigSigma1_poly]

abbrev round_step_a_hi_sigma0_bit (bits : BitsWord) (i : ℕ) : FBB :=
  bits ⟨(i + 2) % 32, Nat.mod_lt _ (by omega)⟩ *
      bits ⟨(i + 13) % 32, Nat.mod_lt _ (by omega)⟩ *
      bits ⟨(i + 22) % 32, Nat.mod_lt _ (by omega)⟩ +
    bits ⟨(i + 2) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - bits ⟨(i + 13) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - bits ⟨(i + 22) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - bits ⟨(i + 2) % 32, Nat.mod_lt _ (by omega)⟩) *
        bits ⟨(i + 13) % 32, Nat.mod_lt _ (by omega)⟩ *
        (1 - bits ⟨(i + 22) % 32, Nat.mod_lt _ (by omega)⟩) +
    (1 - bits ⟨(i + 2) % 32, Nat.mod_lt _ (by omega)⟩) *
        (1 - bits ⟨(i + 13) % 32, Nat.mod_lt _ (by omega)⟩) *
        bits ⟨(i + 22) % 32, Nat.mod_lt _ (by omega)⟩

abbrev round_step_a_hi_sigma0_rhs (bits : BitsWord) : FBB :=
  round_step_a_hi_sigma0_bit bits 16 +
    round_step_a_hi_sigma0_bit bits 17 * 2 +
    round_step_a_hi_sigma0_bit bits 18 * 4 +
    round_step_a_hi_sigma0_bit bits 19 * 8 +
    round_step_a_hi_sigma0_bit bits 20 * 16 +
    round_step_a_hi_sigma0_bit bits 21 * 32 +
    round_step_a_hi_sigma0_bit bits 22 * 64 +
    round_step_a_hi_sigma0_bit bits 23 * 128 +
    round_step_a_hi_sigma0_bit bits 24 * 256 +
    round_step_a_hi_sigma0_bit bits 25 * 512 +
    round_step_a_hi_sigma0_bit bits 26 * 1024 +
    round_step_a_hi_sigma0_bit bits 27 * 2048 +
    round_step_a_hi_sigma0_bit bits 28 * 4096 +
    round_step_a_hi_sigma0_bit bits 29 * 8192 +
    round_step_a_hi_sigma0_bit bits 30 * 16384 +
    round_step_a_hi_sigma0_bit bits 31 * 32768

theorem round_step_a_hi_sigma0_eq (bits : BitsWord) :
    composeHi16 (fieldBigSigma0 bits) = round_step_a_hi_sigma0_rhs bits := by
  rw [composeHi16_explicit]
  simp [round_step_a_hi_sigma0_rhs, round_step_a_hi_sigma0_bit, fieldBigSigma0_poly]

abbrev round_step_a_hi_ch_bit (x y z : BitsWord) (i : Fin 16) : FBB :=
  x ⟨i.val + 16, by omega⟩ * y ⟨i.val + 16, by omega⟩ +
    (1 - x ⟨i.val + 16, by omega⟩) * z ⟨i.val + 16, by omega⟩

abbrev round_step_a_hi_ch_rhs (x y z : BitsWord) : FBB :=
  round_step_a_hi_ch_bit x y z ⟨0, by decide⟩ +
    round_step_a_hi_ch_bit x y z ⟨1, by decide⟩ * 2 +
    round_step_a_hi_ch_bit x y z ⟨2, by decide⟩ * 4 +
    round_step_a_hi_ch_bit x y z ⟨3, by decide⟩ * 8 +
    round_step_a_hi_ch_bit x y z ⟨4, by decide⟩ * 16 +
    round_step_a_hi_ch_bit x y z ⟨5, by decide⟩ * 32 +
    round_step_a_hi_ch_bit x y z ⟨6, by decide⟩ * 64 +
    round_step_a_hi_ch_bit x y z ⟨7, by decide⟩ * 128 +
    round_step_a_hi_ch_bit x y z ⟨8, by decide⟩ * 256 +
    round_step_a_hi_ch_bit x y z ⟨9, by decide⟩ * 512 +
    round_step_a_hi_ch_bit x y z ⟨10, by decide⟩ * 1024 +
    round_step_a_hi_ch_bit x y z ⟨11, by decide⟩ * 2048 +
    round_step_a_hi_ch_bit x y z ⟨12, by decide⟩ * 4096 +
    round_step_a_hi_ch_bit x y z ⟨13, by decide⟩ * 8192 +
    round_step_a_hi_ch_bit x y z ⟨14, by decide⟩ * 16384 +
    round_step_a_hi_ch_bit x y z ⟨15, by decide⟩ * 32768

theorem round_step_a_hi_ch_eq (x y z : BitsWord) (hx : isBitsWord x) :
    composeHi16 (fieldCh x y z) = round_step_a_hi_ch_rhs x y z := by
  rw [composeHi16_explicit, fieldCh_poly _ _ _ hx]

abbrev round_step_a_hi_maj_bit (x y z : BitsWord) (i : Fin 16) : FBB :=
  x ⟨i.val + 16, by omega⟩ * y ⟨i.val + 16, by omega⟩ +
    x ⟨i.val + 16, by omega⟩ * z ⟨i.val + 16, by omega⟩ +
    y ⟨i.val + 16, by omega⟩ * z ⟨i.val + 16, by omega⟩ -
    2 * x ⟨i.val + 16, by omega⟩ * y ⟨i.val + 16, by omega⟩ * z ⟨i.val + 16, by omega⟩

abbrev round_step_a_hi_maj_rhs (x y z : BitsWord) : FBB :=
  round_step_a_hi_maj_bit x y z ⟨0, by decide⟩ +
    round_step_a_hi_maj_bit x y z ⟨1, by decide⟩ * 2 +
    round_step_a_hi_maj_bit x y z ⟨2, by decide⟩ * 4 +
    round_step_a_hi_maj_bit x y z ⟨3, by decide⟩ * 8 +
    round_step_a_hi_maj_bit x y z ⟨4, by decide⟩ * 16 +
    round_step_a_hi_maj_bit x y z ⟨5, by decide⟩ * 32 +
    round_step_a_hi_maj_bit x y z ⟨6, by decide⟩ * 64 +
    round_step_a_hi_maj_bit x y z ⟨7, by decide⟩ * 128 +
    round_step_a_hi_maj_bit x y z ⟨8, by decide⟩ * 256 +
    round_step_a_hi_maj_bit x y z ⟨9, by decide⟩ * 512 +
    round_step_a_hi_maj_bit x y z ⟨10, by decide⟩ * 1024 +
    round_step_a_hi_maj_bit x y z ⟨11, by decide⟩ * 2048 +
    round_step_a_hi_maj_bit x y z ⟨12, by decide⟩ * 4096 +
    round_step_a_hi_maj_bit x y z ⟨13, by decide⟩ * 8192 +
    round_step_a_hi_maj_bit x y z ⟨14, by decide⟩ * 16384 +
    round_step_a_hi_maj_bit x y z ⟨15, by decide⟩ * 32768

theorem round_step_a_hi_maj_eq (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    composeHi16 (fieldMaj x y z) = round_step_a_hi_maj_rhs x y z := by
  rw [composeHi16_explicit, fieldMaj_poly _ _ _ hx hy hz]

private theorem round_step_a_hi_eq_expanded_source (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row)
    :
    next_carry_a air slot 0 row +
      hi16Expr (rawConcatEBitsWord air row slot) +
      round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row (slot + 3)) +
      round_step_a_hi_ch_rhs
        (rawConcatEBitsWord air row (slot + 3))
        (rawConcatEBitsWord air row (slot + 2))
        (rawConcatEBitsWord air row (slot + 1)) +
      round_step_a_hi_sigma0_rhs (rawConcatABitsWord air row (slot + 3)) +
      round_step_a_hi_maj_rhs
        (rawConcatABitsWord air row (slot + 3))
        (rawConcatABitsWord air row (slot + 2))
        (rawConcatABitsWord air row (slot + 1)) +
      hi16Expr (nextScheduleBitsWord air row slot) * next_is_round_row air row +
      roundConstantPolyAtNext air row slot 1 -
        (hi16Expr (nextABitsWord air row slot) +
          next_carry_a air slot 1 row * 65536) = 0 := by
  have hslot' : roundStepAHiConstraint air row slot := round_step_a_hi air row slot hslot hrs
  interval_cases slot
  · simpa only [roundStepAHiConstraint, constraint_722, roundConstantPolyAtNext,
      hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
      round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
      round_step_a_hi_sigma0_rhs, round_step_a_hi_sigma0_bit,
      round_step_a_hi_maj_rhs, round_step_a_hi_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepAHiConstraint, constraint_726, roundConstantPolyAtNext,
      hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
      round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
      round_step_a_hi_sigma0_rhs, round_step_a_hi_sigma0_bit,
      round_step_a_hi_maj_rhs, round_step_a_hi_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepAHiConstraint, constraint_730, roundConstantPolyAtNext,
      hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
      round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
      round_step_a_hi_sigma0_rhs, round_step_a_hi_sigma0_bit,
      round_step_a_hi_maj_rhs, round_step_a_hi_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepAHiConstraint, constraint_734, roundConstantPolyAtNext,
      hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
      round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
      round_step_a_hi_sigma0_rhs, round_step_a_hi_sigma0_bit,
      round_step_a_hi_maj_rhs, round_step_a_hi_maj_bit,
      nextScheduleBitsWord, nextABitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord,
      roundConstantLookupPoly, encoder_choose2] using hslot'

theorem round_step_a_hi_eq_expanded (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    hi16Expr (rawConcatEBitsWord air row slot) +
      round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row (slot + 3)) +
      round_step_a_hi_ch_rhs
        (rawConcatEBitsWord air row (slot + 3))
        (rawConcatEBitsWord air row (slot + 2))
        (rawConcatEBitsWord air row (slot + 1)) +
      k_limb_at row_idx slot 1 +
      hi16Expr (nextScheduleBitsWord air row slot) +
      round_step_a_hi_sigma0_rhs (rawConcatABitsWord air row (slot + 3)) +
      round_step_a_hi_maj_rhs
        (rawConcatABitsWord air row (slot + 3))
        (rawConcatABitsWord air row (slot + 2))
        (rawConcatABitsWord air row (slot + 1)) +
      next_carry_a air slot 0 row -
        (hi16Expr (nextABitsWord air row slot) +
          next_carry_a air slot 1 row * (2 ^ 16 : ℕ)) = 0 := by
  have hk :
      roundConstantPolyAtNext air row slot 1 = k_limb_at row_idx slot 1 :=
    roundConstantPolyAtNext_eq_k_limb_at air row slot 1 row_idx
      hslot (by omega) hrot hrow hflags_next hidx hidx_bound
  have hsrc := round_step_a_hi_eq_expanded_source air row slot hslot hrs
  have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by
    norm_num
  rw [hround_next, hk, ← hpow] at hsrc
  simp only [mul_one] at hsrc
  set e := hi16Expr (rawConcatEBitsWord air row slot)
  set sigma1 := round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row (slot + 3))
  set ch := round_step_a_hi_ch_rhs
    (rawConcatEBitsWord air row (slot + 3))
    (rawConcatEBitsWord air row (slot + 2))
    (rawConcatEBitsWord air row (slot + 1))
  set sigma0 := round_step_a_hi_sigma0_rhs (rawConcatABitsWord air row (slot + 3))
  set maj := round_step_a_hi_maj_rhs
    (rawConcatABitsWord air row (slot + 3))
    (rawConcatABitsWord air row (slot + 2))
    (rawConcatABitsWord air row (slot + 1))
  set sched := hi16Expr (nextScheduleBitsWord air row slot)
  set nextA := hi16Expr (nextABitsWord air row slot) +
    next_carry_a air slot 1 row * (2 ^ 16 : ℕ)
  have hperm :
      next_carry_a air slot 0 row + e + sigma1 + ch + sigma0 + maj + sched +
          k_limb_at row_idx slot 1 =
        e + sigma1 + ch + k_limb_at row_idx slot 1 + sched + sigma0 + maj +
          next_carry_a air slot 0 row := by
    ac_rfl
  rw [hperm] at hsrc
  simpa [e, sigma1, ch, sigma0, maj, sched, nextA] using hsrc

theorem round_step_a_hi_eq_raw (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeHi16 (rawConcatEBitsWord air row slot) +
      composeHi16 (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) +
      composeHi16 (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 1 +
      composeHi16 (nextScheduleBitsWord air row slot) +
      composeHi16 (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) +
      composeHi16 (fieldMaj (rawConcatABitsWord air row (slot + 3))
          (rawConcatABitsWord air row (slot + 2))
          (rawConcatABitsWord air row (slot + 1))) +
      next_carry_a air slot 0 row =
    composeHi16 (nextABitsWord air row slot) +
      next_carry_a air slot 1 row * (2 ^ 16 : ℕ) := by
  have hrawA1_bits : isBitsWord (rawConcatABitsWord air row (slot + 1)) := by
    simpa [rawConcatABitsWord_eq_concatABitsWord air row (slot + 1) hrot hrow] using
      concatABits_boolean air row (slot + 1) (by omega) hbb hbb_next
  have hrawA2_bits : isBitsWord (rawConcatABitsWord air row (slot + 2)) := by
    simpa [rawConcatABitsWord_eq_concatABitsWord air row (slot + 2) hrot hrow] using
      concatABits_boolean air row (slot + 2) (by omega) hbb hbb_next
  have hrawA3_bits : isBitsWord (rawConcatABitsWord air row (slot + 3)) := by
    simpa [rawConcatABitsWord_eq_concatABitsWord air row (slot + 3) hrot hrow] using
      concatABits_boolean air row (slot + 3) (by omega) hbb hbb_next
  have hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3)) := by
    simpa [rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow] using
      concatEBits_boolean air row (slot + 3) (by omega) hbb hbb_next
  have hexpanded := round_step_a_hi_eq_expanded air row slot row_idx hslot hrow hrot hrs hbb
    hbb_next hround_next hflags_next hidx hidx_bound
  rw [← composeHi16_eq_hi16Expr (rawConcatEBitsWord air row slot),
    ← round_step_a_hi_sigma1_eq (rawConcatEBitsWord air row (slot + 3)),
    ← round_step_a_hi_ch_eq
      (rawConcatEBitsWord air row (slot + 3))
      (rawConcatEBitsWord air row (slot + 2))
      (rawConcatEBitsWord air row (slot + 1))
      hrawE_bits,
    ← composeHi16_eq_hi16Expr (nextScheduleBitsWord air row slot),
    ← round_step_a_hi_sigma0_eq (rawConcatABitsWord air row (slot + 3)),
    ← round_step_a_hi_maj_eq
      (rawConcatABitsWord air row (slot + 3))
      (rawConcatABitsWord air row (slot + 2))
      (rawConcatABitsWord air row (slot + 1))
      hrawA3_bits hrawA2_bits hrawA1_bits,
    ← composeHi16_eq_hi16Expr (nextABitsWord air row slot)] at hexpanded
  exact sub_eq_zero.mp hexpanded

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
