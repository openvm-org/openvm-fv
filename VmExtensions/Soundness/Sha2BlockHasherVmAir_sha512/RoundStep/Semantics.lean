/-
  Layer C: Round Step (Semantics)

  Basic bit/word bridge lemmas shared by the SHA-512 round-step files.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.Core
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.SelectorCore

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem aWord_eq_bitsWordToUInt64 (air : C FBB ExtF) (row slot : ℕ) :
    aWord air row slot = bitsWordToUInt64 (aBitsWord air row slot) := by
  rw [aWord, bitsLEToWord, bitsWordToUInt64, foldl_range_add_eq_sum]
  have hrhs :
      (∑ i : Fin 64, (aBitsWord air row slot i).val * 2 ^ i.val : ℕ) =
        (Finset.sum (Finset.range 64) (fun i => (work_vars_a air slot i row).val * 2 ^ i) : ℕ) := by
    calc
      (∑ i : Fin 64, (aBitsWord air row slot i).val * 2 ^ i.val : ℕ)
          = Finset.sum (Finset.range 64)
              (fun i => if hi : i < 64 then (aBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0) := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (f := fun i =>
                    if hi : i < 64 then (aBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0)
                  (n := 64))
      _ = Finset.sum (Finset.range 64) (fun i => (work_vars_a air slot i row).val * 2 ^ i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi64 : i < 64 := Finset.mem_range.mp hi
            simp [hi64, aBitsWord]
  simpa using congrArg UInt64.ofNat hrhs.symm

theorem eWord_eq_bitsWordToUInt64 (air : C FBB ExtF) (row slot : ℕ) :
    eWord air row slot = bitsWordToUInt64 (eBitsWord air row slot) := by
  rw [eWord, bitsLEToWord, bitsWordToUInt64, foldl_range_add_eq_sum]
  have hrhs :
      (∑ i : Fin 64, (eBitsWord air row slot i).val * 2 ^ i.val : ℕ) =
        (Finset.sum (Finset.range 64) (fun i => (work_vars_e air slot i row).val * 2 ^ i) : ℕ) := by
    calc
      (∑ i : Fin 64, (eBitsWord air row slot i).val * 2 ^ i.val : ℕ)
          = Finset.sum (Finset.range 64)
              (fun i => if hi : i < 64 then (eBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0) := by
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (f := fun i =>
                    if hi : i < 64 then (eBitsWord air row slot ⟨i, hi⟩).val * 2 ^ i else 0)
                  (n := 64))
      _ = Finset.sum (Finset.range 64) (fun i => (work_vars_e air slot i row).val * 2 ^ i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi64 : i < 64 := Finset.mem_range.mp hi
            simp [hi64, eBitsWord]
  simpa using congrArg UInt64.ofNat hrhs.symm

def roundConstantLookupPoly
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 : FBB)
    (d0 d1 d2 d3 d4 d5 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4 + d5
  ((2 - s) * (1 - s) * 1006632961) * c0 +
    (d5 * (2 - s)) * c1 +
    (Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2 d5) * c2 +
    (d4 * (2 - s)) * c3 +
    (d4 * d5) * c4 +
    (Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2 d4) * c5 +
    (d3 * (2 - s)) * c6 +
    (d3 * d5) * c7 +
    (d3 * d4) * c8 +
    (Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2 d3) * c9 +
    (d2 * (2 - s)) * c10 +
    (d2 * d5) * c11 +
    (d2 * d4) * c12 +
    (d2 * d3) * c13 +
    (Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2 d2) * c14 +
    (d1 * (2 - s)) * c15 +
    (d1 * d5) * c16 +
    (d1 * d4) * c17 +
    (d1 * d3) * c18 +
    (d1 * d2) * c19

def roundConstantAirPolyAtDigits
    (slot limb : ℕ) (d0 d1 d2 d3 d4 d5 : FBB) : FBB :=
  match slot, limb with
  | 0, 0 =>
      roundConstantLookupPoly
        44578 46392 578 35183 19154 629 57259 36802 12284 25566
        868 21016 53448 23139 45820 7720 24988 28602 32132 17078
        d0 d1 d2 d3 d4 d5
  | 0, 1 =>
      roundConstantLookupPoly
        55080 62280 41731 62075 40689 22827 61030 15784 18130 35759
        19697 55023 47314 50633 24047 9059 59942 29207 8964 52030
        d0 d1 d2 d3 d4 d5
  | 0, 2 =>
      roundConstantLookupPoly
        12184 49755 43672 23924 27073 11375 20818 3059 2693 29524
        59553 59417 49430 3251 33518 65530 16078 26538 30709 54462
        d0 d1 d2 d3 d4 d5
  | 0, 3 =>
      roundConstantLookupPoly
        17034 14678 55303 29374 58523 11753 38974 50912 10167 25866
        41663 53650 6564 14620 29839 37054 51751 1776 10459 19653
        d0 d1 d2 d3 d4 d5
  | 1, 0 =>
      roundConstantLookupPoly
        26061 53273 28606 38577 9699 58499 12816 42789 51494 45736
        12289 43280 43859 35531 12128 48617 49671 39078 9363 32298
        d0 d1 d2 d3 d4 d5
  | 1, 1 =>
      roundConstantLookupPoly
        9199 46597 17776 15126 14415 28326 11700 37642 23590 15479
        48194 21861 20801 58177 17175 56962 8640 41672 16583 64613
        d0 d1 d2 d3 d4 d5
  | 1, 2 =>
      roundConstantLookupPoly
        17553 4593 23297 45566 18310 33962 50797 37191 8504 2747
        26187 1572 27656 43594 25455 27883 47303 32197 43899 10652
        d0 d1 d2 d3 d4 d5
  | 1, 3 =>
      roundConstantLookupPoly
        28983 23025 4739 32990 61374 19060 43057 54695 11803 30314
        43034 54937 7735 20184 30885 42064 53638 2659 13002 22911
        d0 d1 d2 d3 d4 d5
  | 2, 0 =>
      roundConstantLookupPoly
        15151 20379 45708 4661 54709 64468 8511 33391 10989 44774
        38801 8234 60313 58227 43890 30997 60190 3502 48828 64236
        d0 d1 d2 d3 d4 d5
  | 2, 1 =>
      roundConstantLookupPoly
        60493 44825 20196 9671 35724 48449 39163 57347 23236 18413
        53496 22385 57230 30563 41456 45766 52704 48889 5577 15062
        d0 d1 d2 d3 d4 d5
  | 2, 2 =>
      roundConstantLookupPoly
        64463 33444 34238 1703 40390 43484 10184 25425 28156 51502
        35696 13701 30540 51791 30740 41975 32214 38916 48650 28587
        d0 d1 d2 d3 d4 d5
  | 2, 3 =>
      roundConstantLookupPoly
        46528 37439 9265 39900 4033 23728 45059 1738 19756 33218
        49739 62478 10056 23452 33992 48889 60122 4415 15518 24523
        d0 d1 d2 d3 d4 d5
  | 3, 0 =>
      roundConstantLookupPoly
        56252 33048 46306 9876 40037 21429 3812 28272 46047 13627
        48688 53688 18600 47267 14828 21291 53624 18203 3404 22551
        d0 d1 d2 d3 d4 d5
  | 3, 1 =>
      roundConstantLookupPoly
        33161 55917 54783 53097 30636 33553 48879 2574 40341 5250
        1620 12987 57755 54962 6756 58226 61038 4892 39952 19015
        d0 d1 d2 d3 d4 d5
  | 3, 2 =>
      roundConstantLookupPoly
        56229 24277 32195 61812 41420 35034 32711 10599 3347 11397
        20899 41072 48309 28659 520 30962 20351 2869 26564 6540
        d0 d1 d2 d3 d4 d5
  | 3, 3 =>
      roundConstantLookupPoly
        59829 43804 21772 49563 9228 30457 48985 5161 21304 37490
        51052 4202 13488 26670 36039 50801 62845 7025 17181 27716
        d0 d1 d2 d3 d4 d5
  | _, _ => 0

def roundConstantAirPolyAtNext (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  roundConstantAirPolyAtDigits slot limb
    (encoder_idx_next air 0 row) (encoder_idx_next air 1 row)
    (encoder_idx_next air 2 row) (encoder_idx_next air 3 row)
    (encoder_idx_next air 4 row) (encoder_idx_next air 5 row)

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

theorem concatAWord_eq_bitsWordToUInt64
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    concatAWord air row j = bitsWordToUInt64 (concatABitsWord air row j) := by
  by_cases hj : j < 4
  · simp [concatAWord, concatABitsWord, hj, aWord_eq_bitsWordToUInt64]
  · simp [concatAWord, concatABitsWord, hj, aWord_eq_bitsWordToUInt64]

theorem concatEWord_eq_bitsWordToUInt64
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    concatEWord air row j = bitsWordToUInt64 (concatEBitsWord air row j) := by
  by_cases hj : j < 4
  · simp [concatEWord, concatEBitsWord, hj, eWord_eq_bitsWordToUInt64]
  · simp [concatEWord, concatEBitsWord, hj, eWord_eq_bitsWordToUInt64]

private theorem roundConstant_lookup_fin
    (slot limb : ℕ) (hslot : slot < 4) (hlimb : limb < 4) :
    ∀ n0 n1 n2 n3 n4 n5 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val + n5.val ≤ 2 →
      encoderConstraint11Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 0 →
      ∀ row_idx : Fin 22,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = (row_idx.val : FBB) →
        roundConstantAirPolyAtDigits slot limb
          (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) =
          if h : row_idx.val < 20 then k_limb_at row_idx.val slot limb else 0 := by
  interval_cases slot <;> interval_cases limb <;> decide

theorem roundConstantPolyAtNext_eq_airPolyAtNext
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hflags_next : flag_constraints air (nextRow air row)) :
    roundConstantPolyAtNext air row slot limb = roundConstantAirPolyAtNext air row slot limb := by
  have hf_next := hflags_next
  rcases hf_next with ⟨_, _, _, _, _, _, _, _, _, _, _, h11, _, _, _, _, _⟩
  have hd0 := encoder_digits_ternary air (nextRow air row) hflags_next 0 (by omega)
  have hd1 := encoder_digits_ternary air (nextRow air row) hflags_next 1 (by omega)
  have hd2 := encoder_digits_ternary air (nextRow air row) hflags_next 2 (by omega)
  have hd3 := encoder_digits_ternary air (nextRow air row) hflags_next 3 (by omega)
  have hd4 := encoder_digits_ternary air (nextRow air row) hflags_next 4 (by omega)
  have hd5 := encoder_digits_ternary air (nextRow air row) hflags_next 5 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 (nextRow air row)) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 (nextRow air row)) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 (nextRow air row)) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 (nextRow air row)) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 (nextRow air row)) hd4 with ⟨n4, h4⟩
  rcases ternary_as_fin3 (encoder_idx air 5 (nextRow air row)) hd5 with ⟨n5, h5⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val + n5.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4, h5] using
      encoder_digit_sum_ternary air (nextRow air row) hflags_next
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc11 :
      encoderConstraint11Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 0 := by
    simpa [encoderConstraint11Poly, constraint_11,
      Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2, encoder_choose2,
      h0, h1, h2, h3, h4, h5] using h11
  rcases encoder_selector_valid air (nextRow air row) hflags_next with ⟨row_idx, hidx_le, hidx⟩
  let row_idx_fin : Fin 22 := ⟨row_idx, by omega⟩
  have hselector :
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = (row_idx_fin.val : FBB) := by
    simpa [row_idx_fin, encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
      encoderSelectorPoly, h0, h1, h2, h3, h4, h5] using hidx
  have hair_digits :
      roundConstantAirPolyAtDigits slot limb
        (encoder_idx air 0 (nextRow air row))
        (encoder_idx air 1 (nextRow air row))
        (encoder_idx air 2 (nextRow air row))
        (encoder_idx air 3 (nextRow air row))
        (encoder_idx air 4 (nextRow air row))
        (encoder_idx air 5 (nextRow air row)) =
          if h : row_idx < 20 then k_limb_at row_idx slot limb else 0 := by
    simpa [row_idx_fin, h0, h1, h2, h3, h4, h5] using
      roundConstant_lookup_fin slot limb hslot hlimb
        n0 n1 n2 n3 n4 n5 htotal_le hc11 row_idx_fin hselector
  have hair :
      roundConstantAirPolyAtNext air row slot limb =
        if h : row_idx < 20 then k_limb_at row_idx slot limb else 0 := by
    rw [roundConstantAirPolyAtNext]
    simpa [encoder_idx_next_eq_nextRow air hrot 0 row hrow,
      encoder_idx_next_eq_nextRow air hrot 1 row hrow,
      encoder_idx_next_eq_nextRow air hrot 2 row hrow,
      encoder_idx_next_eq_nextRow air hrot 3 row hrow,
      encoder_idx_next_eq_nextRow air hrot 4 row hrow,
      encoder_idx_next_eq_nextRow air hrot 5 row hrow] using hair_digits
  have hidx_lt : row_idx < BB_prime := by
    omega
  have hdecoded :
      roundConstantPolyAtNext air row slot limb =
        if h : row_idx < 20 then k_limb_at row_idx slot limb else 0 := by
    let idx := (encoder_selector_idx air (nextRow air row)).val
    have hidx_eq : idx = row_idx := by
      have hval := congrArg Fin.val hidx
      change idx = row_idx % BB_prime at hval
      rw [Nat.mod_eq_of_lt hidx_lt] at hval
      exact hval
    dsimp [roundConstantPolyAtNext]
    rw [show (encoder_selector_idx air (nextRow air row)).val = row_idx by
      simpa [idx] using hidx_eq]
    simp [hslot, hlimb]
  exact hdecoded.trans hair.symm

theorem roundConstantPolyAtNext_eq_k_limb_at
    (air : C FBB ExtF) (row slot limb row_idx : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20) :
    roundConstantPolyAtNext air row slot limb = k_limb_at row_idx slot limb := by
  let idx := (encoder_selector_idx air (nextRow air row)).val
  have hidx_eq : idx = row_idx := by
    have hval := congrArg Fin.val hidx
    change idx = row_idx % BB_prime at hval
    rw [Nat.mod_eq_of_lt (lt_trans hidx_bound (by norm_num))] at hval
    exact hval
  dsimp [roundConstantPolyAtNext]
  rw [show (encoder_selector_idx air (nextRow air row)).val = row_idx by
    simpa [idx] using hidx_eq]
  simp [hslot, hlimb, hidx_bound]

theorem k_limb_at_lt
    (row_idx slot limb : ℕ)
    (hidx_bound : row_idx < 20)
    (hslot : slot < 4)
    (hlimb : limb < 4) :
    (k_limb_at row_idx slot limb).val < 2 ^ 16 := by
  let n : ℕ := ((sha512K[row_idx * 4 + slot]!.toNat / 2 ^ (16 * limb)) % 2 ^ 16)
  have hn_lt : n < 2 ^ 16 := by
    dsimp [n]
    exact Nat.mod_lt _ (by positivity)
  have hn_prime : n < BB_prime := lt_trans hn_lt (by norm_num)
  have hval : (k_limb_at row_idx slot limb).val = n := by
    dsimp [n]
    rw [k_limb_at]
    exact ZMod.val_natCast_of_lt hn_prime
  exact hval ▸ hn_lt

theorem k_word_eq_limbs
    (row_idx slot : ℕ)
    (hidx_bound : row_idx < 20)
    (hslot : slot < 4) :
    sha512K[row_idx * 4 + slot]! =
      ((k_limb_at row_idx slot 0).val +
          (k_limb_at row_idx slot 1).val * 2 ^ 16 +
          (k_limb_at row_idx slot 2).val * 2 ^ 32 +
          (k_limb_at row_idx slot 3).val * 2 ^ 48).toUInt64 := by
  interval_cases row_idx <;> interval_cases slot <;> decide

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
