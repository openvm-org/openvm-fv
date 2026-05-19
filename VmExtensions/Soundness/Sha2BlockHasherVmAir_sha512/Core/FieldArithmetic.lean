import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts

set_option autoImplicit false

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear

/-!
Layer 0: Field arithmetic bridge

This is the first SHA-512 slice of the SHA-256 arithmetic bridge. It keeps to
the already-established SHA-512 helper surface:
- boolean and ternary facts over BabyBear cells;
- closure of the field bitwise gadgets over 64-bit bit-vectors;
- reassembly lemmas for 64-bit words from 4 little-endian u16 limbs;
- small no-wrap carry helpers shared by schedule and round proofs.
-/

/-! ## 0A: Bit booleanness -/

theorem bit_boolean_of_sq_eq_zero (x : FBB) (h : x * (x - 1) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with hx | hx
  · exact Or.inl hx
  · exact Or.inr (sub_eq_zero.mp hx)

theorem ternary_of_cube_eq_zero (x : FBB) (h : x * (x - 1) * (x - 2) = 0) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases mul_eq_zero.mp h with h01 | h2
  · rcases mul_eq_zero.mp h01 with hx | h1
    · exact Or.inl hx
    · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h2))

/-! ## 0B: Bitwise operations on boolean field elements -/

theorem fieldXor_boolean_closed (x y : FBB) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    fieldXor x y = 0 ∨ fieldXor x y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [fieldXor]

theorem fieldXor3_poly (x y z : FBB) :
    fieldXor (fieldXor x y) z =
      x * y * z +
      x * (1 - y) * (1 - z) +
      (1 - x) * y * (1 - z) +
      (1 - x) * (1 - y) * z := by
  simp [fieldXor]
  ring

theorem fieldAnd_boolean_closed (x y : FBB) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    fieldAnd x y = 0 ∨ fieldAnd x y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [fieldAnd]

theorem fieldNot_boolean_closed (x : FBB) (hx : x = 0 ∨ x = 1) :
    fieldNot x = 0 ∨ fieldNot x = 1 := by
  rcases hx with rfl | rfl <;> simp [fieldNot]

/-! ## 0C: Bitwise operations lift to BitsWord -/

theorem fieldRotr_preserves_boolean (x : BitsWord) (n : ℕ) (hx : isBitsWord x) :
    isBitsWord (fieldRotr x n) := by
  intro i
  simpa [fieldRotr] using hx ⟨(i.val + n) % 64, Nat.mod_lt _ (by omega)⟩

theorem fieldShr_preserves_boolean (x : BitsWord) (n : ℕ) (hx : isBitsWord x) :
    isBitsWord (fieldShr x n) := by
  intro i
  by_cases h : i.val + n < 64
  · simpa [fieldShr, h] using hx ⟨i.val + n, h⟩
  · simp [fieldShr, h]

/-! ## 0D: Bit composition: field -> UInt64 -/

private theorem composeU16Limb_eq_nat_sum (bits : BitsWord) (hb : isBitsWord bits) (limb : Fin 4) :
    composeU16Limb bits limb =
      ((∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val : ℕ) : FBB) := by
  rw [composeU16Limb, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases hb ⟨i.val + 16 * limb.val, by omega⟩ with hbit | hbit <;> simp [hbit]

private theorem composeBits_eq_nat_sum (bits : BitsWord) (hb : isBitsWord bits) :
    composeBits bits =
      ((∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) : FBB) := by
  rw [composeBits, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases hb i with hbit | hbit <;> simp [hbit]

private theorem composeU16Limb_nat_sum_lt
    (bits : BitsWord) (hb : isBitsWord bits) (limb : Fin 4) :
    (∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val : ℕ) < 2 ^ 16 := by
  have hle :
      (∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val : ℕ) ≤
        ∑ i : Fin 16, 2 ^ i.val := by
    refine Finset.sum_le_sum ?_
    intro i _
    rcases hb ⟨i.val + 16 * limb.val, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

private theorem composeBits_nat_sum_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) < 2 ^ 64 := by
  have hle :
      (∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) ≤
        ∑ i : Fin 64, 2 ^ i.val := by
    refine Finset.sum_le_sum ?_
    intro i _
    rcases hb i with hbit | hbit <;> simp [hbit]
  have hpow : (∑ i : Fin 64, 2 ^ i.val : ℕ) < 2 ^ 64 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

theorem composeU16Limb_val_lt (bits : BitsWord) (hb : isBitsWord bits) (limb : Fin 4) :
    (composeU16Limb bits limb).val < 2 ^ 16 := by
  have hs_lt :
      (∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val : ℕ) < 2 ^ 16 :=
    composeU16Limb_nat_sum_lt bits hb limb
  have hs_prime :
      (∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val : ℕ) < BB_prime := by
    exact lt_trans hs_lt (by norm_num)
  have hval :
      (composeU16Limb bits limb).val =
        ∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val := by
    have hcast := congrArg Fin.val (composeU16Limb_eq_nat_sum bits hb limb)
    change
      (composeU16Limb bits limb).val =
        (∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hs_prime] at hcast
    exact hcast
  calc
    (composeU16Limb bits limb).val =
        ∑ i : Fin 16, (bits ⟨i.val + 16 * limb.val, by omega⟩).val * 2 ^ i.val := hval
    _ < 2 ^ 16 := hs_lt

theorem composeLo16_val_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (composeLo16 bits).val < 2 ^ 16 := by
  simpa [composeLo16] using composeU16Limb_val_lt bits hb ⟨0, by decide⟩

theorem composeHi16_val_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (composeHi16 bits).val < 2 ^ 16 := by
  simpa [composeHi16] using composeU16Limb_val_lt bits hb ⟨3, by decide⟩

theorem composeU16Limb_range_eq (bits : BitsWord) (limb : Fin 4) :
    composeU16Limb bits limb =
      ∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 16 * limb.val, by omega⟩ * 2 ^ i else 0) := by
  have hsum :
      (∑ i : Fin 16, bits ⟨i.val + 16 * limb.val, by omega⟩ * 2 ^ i.val) =
        ∑ i ∈ Finset.range 16,
          (if hi : i < 16 then bits ⟨i + 16 * limb.val, by omega⟩ * 2 ^ i else 0) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun i => if hi : i < 16 then bits ⟨i + 16 * limb.val, by omega⟩ * 2 ^ i else 0)
        (n := 16))
  rw [composeU16Limb]
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem composeLo16_range_eq (bits : BitsWord) :
    composeLo16 bits =
      ∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i, lt_trans hi (by decide)⟩ * 2 ^ i else 0) := by
  simpa [composeLo16] using composeU16Limb_range_eq bits ⟨0, by decide⟩

theorem composeHi16_range_eq (bits : BitsWord) :
    composeHi16 bits =
      ∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 48, by omega⟩ * 2 ^ i else 0) := by
  simpa [composeHi16] using composeU16Limb_range_eq bits ⟨3, by decide⟩

theorem composeBits_eq_bitsWordToUInt64 (bits : BitsWord) (hb : isBitsWord bits) :
    composeBits bits = ((bitsWordToUInt64 bits).toNat : FBB) := by
  let total : ℕ := ∑ i : Fin 64, (bits i).val * 2 ^ i.val
  have htotal_lt : total < 2 ^ 64 := by
    change (∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) < 2 ^ 64
    exact composeBits_nat_sum_lt bits hb
  have hcompose : composeBits bits = (total : FBB) := by
    change composeBits bits = (((∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ)) : FBB)
    exact composeBits_eq_nat_sum bits hb
  have hword_nat : (bitsWordToUInt64 bits).toNat = total := by
    have hnat_mod : (bitsWordToUInt64 bits).toNat = total % 2 ^ 64 := by
      change ((total).toUInt64).toNat = total % 2 ^ 64
      exact UInt64.toNat_ofNat (n := total)
    rw [Nat.mod_eq_of_lt htotal_lt] at hnat_mod
    exact hnat_mod
  calc
    composeBits bits = (total : FBB) := hcompose
    _ = (((bitsWordToUInt64 bits).toNat : ℕ) : FBB) := by rw [← hword_nat]

/-- A boolean bit-word reassembles from its four little-endian 16-bit limbs. -/
theorem bitsWordToUInt64_eq_compose16 (bits : BitsWord) (hb : isBitsWord bits) :
    bitsWordToUInt64 bits =
      ((composeU16Limb bits ⟨0, by decide⟩).val +
          (composeU16Limb bits ⟨1, by decide⟩).val * 2 ^ 16 +
          (composeU16Limb bits ⟨2, by decide⟩).val * 2 ^ 32 +
          (composeU16Limb bits ⟨3, by decide⟩).val * 2 ^ 48).toUInt64 := by
  let limb0 : ℕ := ∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val
  let limb1 : ℕ := ∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val
  let limb2 : ℕ := ∑ i : Fin 16, (bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val
  let limb3 : ℕ := ∑ i : Fin 16, (bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val
  have hlimb0_lt_nat : limb0 < 2 ^ 16 := by
    dsimp [limb0]
    have hle :
        (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) ≤
          ∑ i : Fin 16, 2 ^ i.val := by
      refine Finset.sum_le_sum ?_
      intro i _
      rcases hb ⟨i.val, by omega⟩ with hbit | hbit <;> simp [hbit]
    have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
      norm_num [Fin.sum_univ_eq_sum_range]
    exact lt_of_le_of_lt hle hpow
  have hlimb1_lt_nat : limb1 < 2 ^ 16 := by
    dsimp [limb1]
    have hle :
        (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) ≤
          ∑ i : Fin 16, 2 ^ i.val := by
      refine Finset.sum_le_sum ?_
      intro i _
      rcases hb ⟨i.val + 16, by omega⟩ with hbit | hbit <;> simp [hbit]
    have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
      norm_num [Fin.sum_univ_eq_sum_range]
    exact lt_of_le_of_lt hle hpow
  have hlimb2_lt_nat : limb2 < 2 ^ 16 := by
    dsimp [limb2]
    have hle :
        (∑ i : Fin 16, (bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val : ℕ) ≤
          ∑ i : Fin 16, 2 ^ i.val := by
      refine Finset.sum_le_sum ?_
      intro i _
      rcases hb ⟨i.val + 32, by omega⟩ with hbit | hbit <;> simp [hbit]
    have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
      norm_num [Fin.sum_univ_eq_sum_range]
    exact lt_of_le_of_lt hle hpow
  have hlimb3_lt_nat : limb3 < 2 ^ 16 := by
    dsimp [limb3]
    have hle :
        (∑ i : Fin 16, (bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val : ℕ) ≤
          ∑ i : Fin 16, 2 ^ i.val := by
      refine Finset.sum_le_sum ?_
      intro i _
      rcases hb ⟨i.val + 48, by omega⟩ with hbit | hbit <;> simp [hbit]
    have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
      norm_num [Fin.sum_univ_eq_sum_range]
    exact lt_of_le_of_lt hle hpow
  have hlimb0_lt : limb0 < BB_prime := lt_trans hlimb0_lt_nat (by norm_num)
  have hlimb1_lt : limb1 < BB_prime := lt_trans hlimb1_lt_nat (by norm_num)
  have hlimb2_lt : limb2 < BB_prime := lt_trans hlimb2_lt_nat (by norm_num)
  have hlimb3_lt : limb3 < BB_prime := lt_trans hlimb3_lt_nat (by norm_num)
  have hlimb0_val : (composeU16Limb bits ⟨0, by decide⟩).val = limb0 := by
    have hcast := congrArg Fin.val (composeU16Limb_eq_nat_sum bits hb ⟨0, by decide⟩)
    dsimp [limb0] at hcast
    change
      (composeU16Limb bits ⟨0, by decide⟩).val =
        (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hlimb0_lt] at hcast
    exact hcast
  have hlimb1_val : (composeU16Limb bits ⟨1, by decide⟩).val = limb1 := by
    have hcast := congrArg Fin.val (composeU16Limb_eq_nat_sum bits hb ⟨1, by decide⟩)
    dsimp [limb1] at hcast
    change
      (composeU16Limb bits ⟨1, by decide⟩).val =
        (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hlimb1_lt] at hcast
    exact hcast
  have hlimb2_val : (composeU16Limb bits ⟨2, by decide⟩).val = limb2 := by
    have hcast := congrArg Fin.val (composeU16Limb_eq_nat_sum bits hb ⟨2, by decide⟩)
    dsimp [limb2] at hcast
    change
      (composeU16Limb bits ⟨2, by decide⟩).val =
        (∑ i : Fin 16, (bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hlimb2_lt] at hcast
    exact hcast
  have hlimb3_val : (composeU16Limb bits ⟨3, by decide⟩).val = limb3 := by
    have hcast := congrArg Fin.val (composeU16Limb_eq_nat_sum bits hb ⟨3, by decide⟩)
    dsimp [limb3] at hcast
    change
      (composeU16Limb bits ⟨3, by decide⟩).val =
        (∑ i : Fin 16, (bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hlimb3_lt] at hcast
    exact hcast
  have hsum :
      (∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) =
        limb0 + limb1 * 2 ^ 16 + limb2 * 2 ^ 32 + limb3 * 2 ^ 48 := by
    change
      (∑ i : Fin (16 + 48), (bits i).val * 2 ^ i.val : ℕ) =
        limb0 + limb1 * 2 ^ 16 + limb2 * 2 ^ 32 + limb3 * 2 ^ 48
    rw [Fin.sum_univ_add]
    have h0 :
        (∑ i : Fin 16, (bits (Fin.castAdd 48 i)).val * 2 ^ (Fin.castAdd 48 i).val : ℕ) = limb0 := by
      dsimp [limb0]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hcast : Fin.castAdd 48 i = ⟨i.val, by omega⟩ := by
        ext
        simp [Fin.castAdd]
      rw [hcast]
    have h123 :
        (∑ i : Fin 48, (bits (Fin.natAdd 16 i)).val * 2 ^ (Fin.natAdd 16 i).val : ℕ) =
          limb1 * 2 ^ 16 + limb2 * 2 ^ 32 + limb3 * 2 ^ 48 := by
      change
        (∑ i : Fin (16 + 32), (bits (Fin.natAdd 16 i)).val * 2 ^ (Fin.natAdd 16 i).val : ℕ) =
          limb1 * 2 ^ 16 + limb2 * 2 ^ 32 + limb3 * 2 ^ 48
      rw [Fin.sum_univ_add]
      have h1 :
          (∑ i : Fin 16,
              (bits (Fin.natAdd 16 (Fin.castAdd 32 i))).val *
                2 ^ (Fin.natAdd 16 (Fin.castAdd 32 i)).val : ℕ) =
            limb1 * 2 ^ 16 := by
        calc
          (∑ i : Fin 16,
              (bits (Fin.natAdd 16 (Fin.castAdd 32 i))).val *
                2 ^ (Fin.natAdd 16 (Fin.castAdd 32 i)).val : ℕ) =
              ∑ i : Fin 16, ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) * 2 ^ 16 := by
                refine Finset.sum_congr rfl ?_
                intro i _
                have hcast : Fin.natAdd 16 (Fin.castAdd 32 i) = ⟨i.val + 16, by omega⟩ := by
                  ext
                  simp [Fin.natAdd, Fin.castAdd]
                  omega
                have hp : (2 ^ (i.val + 16) : ℕ) = 2 ^ i.val * 2 ^ 16 := by
                  rw [Nat.pow_add]
                calc
                  (bits (Fin.natAdd 16 (Fin.castAdd 32 i))).val *
                      2 ^ (Fin.natAdd 16 (Fin.castAdd 32 i)).val =
                    (bits ⟨i.val + 16, by omega⟩).val * (2 ^ i.val * 2 ^ 16) := by
                      rw [hcast, hp]
                  _ = ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) * 2 ^ 16 := by
                      ac_rfl
          _ = limb1 * 2 ^ 16 := by
              calc
                (∑ i : Fin 16, ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) * 2 ^ 16 : ℕ) =
                    ∑ i : Fin 16, (2 ^ 16) * ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _
                      ring
                _ = (2 ^ 16) * limb1 := by
                      dsimp [limb1]
                      rw [Finset.mul_sum]
                _ = limb1 * 2 ^ 16 := by rw [Nat.mul_comm]
      have h23 :
          (∑ i : Fin 32,
              (bits (Fin.natAdd 16 (Fin.natAdd 16 i))).val *
                2 ^ (Fin.natAdd 16 (Fin.natAdd 16 i)).val : ℕ) =
            limb2 * 2 ^ 32 + limb3 * 2 ^ 48 := by
        change
          (∑ i : Fin (16 + 16),
              (bits (Fin.natAdd 16 (Fin.natAdd 16 i))).val *
                2 ^ (Fin.natAdd 16 (Fin.natAdd 16 i)).val : ℕ) =
            limb2 * 2 ^ 32 + limb3 * 2 ^ 48
        rw [Fin.sum_univ_add]
        have h2 :
            (∑ i : Fin 16,
                (bits (Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i)))).val *
                  2 ^ (Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i))).val : ℕ) =
              limb2 * 2 ^ 32 := by
          calc
            (∑ i : Fin 16,
                (bits (Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i)))).val *
                  2 ^ (Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i))).val : ℕ) =
                ∑ i : Fin 16, ((bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val) * 2 ^ 32 := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hcast :
                      Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i)) = ⟨i.val + 32, by omega⟩ := by
                    ext
                    simp [Fin.natAdd, Fin.castAdd]
                    omega
                  have hp : (2 ^ (i.val + 32) : ℕ) = 2 ^ i.val * 2 ^ 32 := by
                    rw [Nat.pow_add]
                  calc
                    (bits (Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i)))).val *
                        2 ^ (Fin.natAdd 16 (Fin.natAdd 16 (Fin.castAdd 16 i))).val =
                      (bits ⟨i.val + 32, by omega⟩).val * (2 ^ i.val * 2 ^ 32) := by
                        rw [hcast, hp]
                    _ = ((bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val) * 2 ^ 32 := by
                        ac_rfl
            _ = limb2 * 2 ^ 32 := by
                calc
                  (∑ i : Fin 16, ((bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val) * 2 ^ 32 : ℕ) =
                      ∑ i : Fin 16, (2 ^ 32) * ((bits ⟨i.val + 32, by omega⟩).val * 2 ^ i.val) := by
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ring
                  _ = (2 ^ 32) * limb2 := by
                        dsimp [limb2]
                        rw [Finset.mul_sum]
                  _ = limb2 * 2 ^ 32 := by rw [Nat.mul_comm]
        have h3 :
            (∑ i : Fin 16,
                (bits (Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i)))).val *
                  2 ^ (Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i))).val : ℕ) =
              limb3 * 2 ^ 48 := by
          calc
            (∑ i : Fin 16,
                (bits (Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i)))).val *
                  2 ^ (Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i))).val : ℕ) =
                ∑ i : Fin 16, ((bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val) * 2 ^ 48 := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hcast :
                      Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i)) = ⟨i.val + 48, by omega⟩ := by
                    ext
                    simp [Fin.natAdd]
                    omega
                  have hp : (2 ^ (i.val + 48) : ℕ) = 2 ^ i.val * 2 ^ 48 := by
                    rw [Nat.pow_add]
                  calc
                    (bits (Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i)))).val *
                        2 ^ (Fin.natAdd 16 (Fin.natAdd 16 (Fin.natAdd 16 i))).val =
                      (bits ⟨i.val + 48, by omega⟩).val * (2 ^ i.val * 2 ^ 48) := by
                        rw [hcast, hp]
                    _ = ((bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val) * 2 ^ 48 := by
                        ac_rfl
            _ = limb3 * 2 ^ 48 := by
                calc
                  (∑ i : Fin 16, ((bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val) * 2 ^ 48 : ℕ) =
                      ∑ i : Fin 16, (2 ^ 48) * ((bits ⟨i.val + 48, by omega⟩).val * 2 ^ i.val) := by
                        refine Finset.sum_congr rfl ?_
                        intro i _
                        ring
                  _ = (2 ^ 48) * limb3 := by
                        dsimp [limb3]
                        rw [Finset.mul_sum]
                  _ = limb3 * 2 ^ 48 := by rw [Nat.mul_comm]
        rw [h2, h3]
      rw [h1, h23]
      omega
    rw [h0, h123]
    omega
  rw [bitsWordToUInt64, hsum, hlimb0_val, hlimb1_val, hlimb2_val, hlimb3_val]

theorem foldl_range_add_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      Finset.sum (Finset.range n) f := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      simp [Nat.add_comm]

private theorem nat_sum_bool_eq_ofBits {n : Nat} (f : Fin n → Bool) :
    (∑ i : Fin n, (f i).toNat * 2 ^ i.val : ℕ) = Nat.ofBits f := by
  induction n with
  | zero =>
      simp [Nat.ofBits]
  | succ n ih =>
      rw [Fin.sum_univ_succ, Nat.ofBits_succ]
      have hrest :
          (∑ i : Fin n, (f i.succ).toNat * 2 ^ i.succ.val : ℕ) =
            2 * ∑ i : Fin n, (f i.succ).toNat * 2 ^ i.val := by
        calc
          (∑ i : Fin n, (f i.succ).toNat * 2 ^ i.succ.val : ℕ) =
              ∑ i : Fin n, 2 * ((f i.succ).toNat * 2 ^ i.val) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                simp [Fin.val_succ, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]
          _ = 2 * ∑ i : Fin n, (f i.succ).toNat * 2 ^ i.val := by
                rw [Finset.mul_sum]
      rw [hrest]
      change
        (f 0).toNat * 2 ^ (0 : Nat) + 2 * ∑ i : Fin n, ((f ∘ Fin.succ) i).toNat * 2 ^ i.val =
          2 * Nat.ofBits (f ∘ Fin.succ) + (f 0).toNat
      rw [ih (f ∘ Fin.succ)]
      omega

private def bitsAsBool (bits : BitsWord) : Fin 64 → Bool :=
  fun i => if bits i = 1 then true else false

private theorem bitsAsBool_spec (bits : BitsWord) (hb : isBitsWord bits) (i : Fin 64) :
    (bits i).val = (bitsAsBool bits i).toNat := by
  rcases hb i with h0 | h1
  · simp [bitsAsBool, h0]
  · simp [bitsAsBool, h1]

private theorem bitsWordToUInt64_eq_ofFnLE (bits : BitsWord) (hb : isBitsWord bits) :
    bitsWordToUInt64 bits = UInt64.ofBitVec (BitVec.ofFnLE (bitsAsBool bits)) := by
  apply UInt64.ext
  let total : ℕ := ∑ i : Fin 64, (bits i).val * 2 ^ i.val
  have hlt : total < 2 ^ 64 := by
    change (∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) < 2 ^ 64
    exact composeBits_nat_sum_lt bits hb
  have hleft' : (total.toUInt64).toNat = total % 2 ^ 64 := by
    simpa using (UInt64.toNat_ofNat (n := total))
  have hleft : (bitsWordToUInt64 bits).toNat = total := by
    change (total.toUInt64).toNat = total
    rw [hleft', Nat.mod_eq_of_lt hlt]
  have hsum : total = Nat.ofBits (bitsAsBool bits) := by
    dsimp [total]
    calc
      (∑ i : Fin 64, (bits i).val * 2 ^ i.val : ℕ) =
          ∑ i : Fin 64, (bitsAsBool bits i).toNat * 2 ^ i.val := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [bitsAsBool_spec bits hb i]
      _ = Nat.ofBits (bitsAsBool bits) := nat_sum_bool_eq_ofBits (bitsAsBool bits)
  rw [hleft, hsum]
  simp

theorem fieldCh_isBitsWord (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    isBitsWord (fieldCh x y z) := by
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldAnd_boolean_closed _ _ (hx i) (hy i))
    (fieldAnd_boolean_closed _ _ (fieldNot_boolean_closed _ (hx i)) (hz i))

private theorem bitvec_ofFnLE_fieldCh (f g h : Fin 64 → Bool) :
    BitVec.ofFnLE (fun i => Bool.xor (f i && g i) ((!f i) && h i)) =
      (BitVec.ofFnLE f &&& BitVec.ofFnLE g) ^^^
        ((~~~ BitVec.ofFnLE f) &&& BitVec.ofFnLE h) := by
  ext i
  simp

private theorem bitsAsBool_fieldCh (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsAsBool (fieldCh x y z) =
      fun i => Bool.xor (bitsAsBool x i && bitsAsBool y i) ((!bitsAsBool x i) && bitsAsBool z i) := by
  funext i
  rcases hx i with hx0 | hx1
  · rcases hy i with hy0 | hy1
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx0, hy0, hz0]
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx0, hy0, hz1]
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx0, hy1, hz0]
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx0, hy1, hz1]
  · rcases hy i with hy0 | hy1
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx1, hy0, hz0]
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx1, hy0, hz1]
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx1, hy1, hz0]
      · simp [bitsAsBool, fieldCh, fieldXor, fieldAnd, fieldNot, hx1, hy1, hz1]

theorem fieldMaj_isBitsWord (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    isBitsWord (fieldMaj x y z) := by
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _
      (fieldAnd_boolean_closed _ _ (hx i) (hy i))
      (fieldAnd_boolean_closed _ _ (hx i) (hz i)))
    (fieldAnd_boolean_closed _ _ (hy i) (hz i))

private theorem bitvec_ofFnLE_fieldMaj (f g h : Fin 64 → Bool) :
    BitVec.ofFnLE (fun i => Bool.xor (Bool.xor (f i && g i) (f i && h i)) (g i && h i)) =
      (BitVec.ofFnLE f &&& BitVec.ofFnLE g) ^^^
        (BitVec.ofFnLE f &&& BitVec.ofFnLE h) ^^^
        (BitVec.ofFnLE g &&& BitVec.ofFnLE h) := by
  ext i
  simp

private theorem bitsAsBool_fieldMaj (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsAsBool (fieldMaj x y z) =
      fun i => Bool.xor (Bool.xor (bitsAsBool x i && bitsAsBool y i)
        (bitsAsBool x i && bitsAsBool z i)) (bitsAsBool y i && bitsAsBool z i) := by
  funext i
  rcases hx i with hx0 | hx1
  · rcases hy i with hy0 | hy1
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx0, hy0, hz0]
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx0, hy0, hz1]
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx0, hy1, hz0]
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx0, hy1, hz1]
  · rcases hy i with hy0 | hy1
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx1, hy0, hz0]
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx1, hy0, hz1]
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx1, hy1, hz0]
      · simp [bitsAsBool, fieldMaj, fieldXor, fieldAnd, hx1, hy1, hz1]

private theorem bitvec_ofFnLE_xor3 (f g h : Fin 64 → Bool) :
    BitVec.ofFnLE (fun i => Bool.xor (Bool.xor (f i) (g i)) (h i)) =
      BitVec.ofFnLE f ^^^ BitVec.ofFnLE g ^^^ BitVec.ofFnLE h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

private theorem bitsAsBool_fieldXor3 (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsAsBool (fun i => fieldXor (fieldXor (x i) (y i)) (z i)) =
      fun i => Bool.xor (Bool.xor (bitsAsBool x i) (bitsAsBool y i)) (bitsAsBool z i) := by
  funext i
  rcases hx i with hx0 | hx1
  · rcases hy i with hy0 | hy1
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldXor, hx0, hy0, hz0]
      · simp [bitsAsBool, fieldXor, hx0, hy0, hz1]
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldXor, hx0, hy1, hz0]
      · simp [bitsAsBool, fieldXor, hx0, hy1, hz1]
  · rcases hy i with hy0 | hy1
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldXor, hx1, hy0, hz0]
      · simp [bitsAsBool, fieldXor, hx1, hy0, hz1]
    · rcases hz i with hz0 | hz1
      · simp [bitsAsBool, fieldXor, hx1, hy1, hz0]
      · simp [bitsAsBool, fieldXor, hx1, hy1, hz1]

private theorem bitsAsBool_fieldRotr (x : BitsWord) (n : Nat) (hx : isBitsWord x) :
    bitsAsBool (fieldRotr x n) =
      fun i => bitsAsBool x ⟨(i.val + n) % 64, Nat.mod_lt _ (by omega)⟩ := by
  funext i
  rcases hx ⟨(i.val + n) % 64, Nat.mod_lt _ (by omega)⟩ with h0 | h1
  · simp [bitsAsBool, fieldRotr, h0]
  · simp [bitsAsBool, fieldRotr, h1]

private theorem bitsAsBool_fieldShr (x : BitsWord) (n : Nat) (hx : isBitsWord x) :
    bitsAsBool (fieldShr x n) =
      fun i => if h : i.val + n < 64 then bitsAsBool x ⟨i.val + n, h⟩ else false := by
  funext i
  by_cases h : i.val + n < 64
  · rcases hx ⟨i.val + n, h⟩ with h0 | h1
    · simp [bitsAsBool, fieldShr, h, h0]
    · simp [bitsAsBool, fieldShr, h, h1]
  · simp [bitsAsBool, fieldShr, h]

private theorem bitvec_ofFnLE_fieldRotr (f : Fin 64 → Bool) (n : Nat) (hn : n < 64) :
    BitVec.ofFnLE (fun i => f ⟨(i.val + n) % 64, Nat.mod_lt _ (by omega)⟩) =
      (BitVec.ofFnLE f).rotateRight n := by
  have hn' : n % 64 = n := Nat.mod_eq_of_lt hn
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 64 - n
  · have hlt : n + i < 64 := by omega
    have hidx : (⟨(n + i) % 64, by omega⟩ : Fin 64) = ⟨n + i, hlt⟩ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hlt]
    simp [BitVec.getLsbD_ofFnLE, BitVec.rotateRight, BitVec.rotateRightAux, h, hi, hn',
      Nat.add_comm]
    simpa [hlt] using congrArg f hidx
  · have hge : ¬ n + i < 64 := by omega
    have hlt2 : i - (64 - n) < 64 := by omega
    have hm : (n + i) % 64 = i - (64 - n) := by omega
    have hidx : (⟨(n + i) % 64, by omega⟩ : Fin 64) = ⟨i - (64 - n), hlt2⟩ := by
      apply Fin.ext
      exact hm
    simp [BitVec.getLsbD_ofFnLE, BitVec.rotateRight, BitVec.rotateRightAux, h, hi, hge, hn',
      Nat.add_comm]
    simpa using congrArg f hidx

private theorem bitvec_ofFnLE_fieldShr (f : Fin 64 → Bool) (n : Nat) :
    BitVec.ofFnLE (fun i => if h : i.val + n < 64 then f ⟨i.val + n, h⟩ else false) =
      BitVec.ofFnLE f >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i + n < 64
  · simpa [BitVec.getLsbD_ofFnLE, h, hi, Nat.add_comm] using rfl
  · simpa [BitVec.getLsbD_ofFnLE, h, hi, Nat.add_comm] using rfl

theorem fieldBigSigma0_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldBigSigma0 x) := by
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _
      ((fieldRotr_preserves_boolean x 28 hx) i)
      ((fieldRotr_preserves_boolean x 34 hx) i))
    ((fieldRotr_preserves_boolean x 39 hx) i)

theorem fieldBigSigma1_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldBigSigma1 x) := by
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _
      ((fieldRotr_preserves_boolean x 14 hx) i)
      ((fieldRotr_preserves_boolean x 18 hx) i))
    ((fieldRotr_preserves_boolean x 41 hx) i)

private theorem fieldSmallSigma0_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldSmallSigma0 x) := by
  have hrot1 := fieldRotr_preserves_boolean x 1 hx
  have hrot8 := fieldRotr_preserves_boolean x 8 hx
  have hshr7 := fieldShr_preserves_boolean x 7 hx
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _ (hrot1 i) (hrot8 i))
    (hshr7 i)

private theorem fieldSmallSigma1_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldSmallSigma1 x) := by
  have hrot19 := fieldRotr_preserves_boolean x 19 hx
  have hrot61 := fieldRotr_preserves_boolean x 61 hx
  have hshr6 := fieldShr_preserves_boolean x 6 hx
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _ (hrot19 i) (hrot61 i))
    (hshr6 i)

private theorem bitsAsBool_fieldSmallSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldSmallSigma0 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 1) % 64, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 8) % 64, Nat.mod_lt _ (by omega)⟩))
        (if h : i.val + 7 < 64 then bitsAsBool x ⟨i.val + 7, h⟩ else false) := by
  calc
    bitsAsBool (fieldSmallSigma0 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 1) i)
          (bitsAsBool (fieldRotr x 8) i)) (bitsAsBool (fieldShr x 7) i) := by
            simpa [fieldSmallSigma0] using
              bitsAsBool_fieldXor3 (fieldRotr x 1) (fieldRotr x 8) (fieldShr x 7)
                (fieldRotr_preserves_boolean x 1 hx)
                (fieldRotr_preserves_boolean x 8 hx)
                (fieldShr_preserves_boolean x 7 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 1 hx, bitsAsBool_fieldRotr x 8 hx,
        bitsAsBool_fieldShr x 7 hx]

private theorem bitsAsBool_fieldSmallSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldSmallSigma1 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 19) % 64, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 61) % 64, Nat.mod_lt _ (by omega)⟩))
        (if h : i.val + 6 < 64 then bitsAsBool x ⟨i.val + 6, h⟩ else false) := by
  calc
    bitsAsBool (fieldSmallSigma1 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 19) i)
          (bitsAsBool (fieldRotr x 61) i)) (bitsAsBool (fieldShr x 6) i) := by
            simpa [fieldSmallSigma1] using
              bitsAsBool_fieldXor3 (fieldRotr x 19) (fieldRotr x 61) (fieldShr x 6)
                (fieldRotr_preserves_boolean x 19 hx)
                (fieldRotr_preserves_boolean x 61 hx)
                (fieldShr_preserves_boolean x 6 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 19 hx, bitsAsBool_fieldRotr x 61 hx,
        bitsAsBool_fieldShr x 6 hx]

private theorem bitsAsBool_fieldBigSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldBigSigma0 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩))
        (bitsAsBool x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) := by
  calc
    bitsAsBool (fieldBigSigma0 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 28) i)
          (bitsAsBool (fieldRotr x 34) i)) (bitsAsBool (fieldRotr x 39) i) := by
            simpa [fieldBigSigma0] using
              bitsAsBool_fieldXor3 (fieldRotr x 28) (fieldRotr x 34) (fieldRotr x 39)
                (fieldRotr_preserves_boolean x 28 hx)
                (fieldRotr_preserves_boolean x 34 hx)
                (fieldRotr_preserves_boolean x 39 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 28 hx, bitsAsBool_fieldRotr x 34 hx,
        bitsAsBool_fieldRotr x 39 hx]

private theorem bitsAsBool_fieldBigSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldBigSigma1 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩))
        (bitsAsBool x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) := by
  calc
    bitsAsBool (fieldBigSigma1 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 14) i)
          (bitsAsBool (fieldRotr x 18) i)) (bitsAsBool (fieldRotr x 41) i) := by
            simpa [fieldBigSigma1] using
              bitsAsBool_fieldXor3 (fieldRotr x 14) (fieldRotr x 18) (fieldRotr x 41)
                (fieldRotr_preserves_boolean x 14 hx)
                (fieldRotr_preserves_boolean x 18 hx)
                (fieldRotr_preserves_boolean x 41 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 14 hx, bitsAsBool_fieldRotr x 18 hx,
        bitsAsBool_fieldRotr x 41 hx]

/-- Field-level Ch on boolean bit-words = UInt64 Ch, bit by bit. -/
theorem fieldCh_eq_ch (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsWordToUInt64 (fieldCh x y z) = ch (bitsWordToUInt64 x) (bitsWordToUInt64 y) (bitsWordToUInt64 z) := by
  rw [bitsWordToUInt64_eq_ofFnLE (fieldCh x y z) (fieldCh_isBitsWord x y z hx hy hz),
    bitsWordToUInt64_eq_ofFnLE x hx,
    bitsWordToUInt64_eq_ofFnLE y hy,
    bitsWordToUInt64_eq_ofFnLE z hz]
  congr 1
  simpa [bitsAsBool_fieldCh x y z hx hy hz] using
    bitvec_ofFnLE_fieldCh (bitsAsBool x) (bitsAsBool y) (bitsAsBool z)

/-- Field-level Maj on boolean bit-words = UInt64 Maj, bit by bit. -/
theorem fieldMaj_eq_maj (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsWordToUInt64 (fieldMaj x y z) = maj (bitsWordToUInt64 x) (bitsWordToUInt64 y) (bitsWordToUInt64 z) := by
  rw [bitsWordToUInt64_eq_ofFnLE (fieldMaj x y z) (fieldMaj_isBitsWord x y z hx hy hz),
    bitsWordToUInt64_eq_ofFnLE x hx,
    bitsWordToUInt64_eq_ofFnLE y hy,
    bitsWordToUInt64_eq_ofFnLE z hz]
  congr 1
  simpa [bitsAsBool_fieldMaj x y z hx hy hz] using
    bitvec_ofFnLE_fieldMaj (bitsAsBool x) (bitsAsBool y) (bitsAsBool z)

/-- Field-level Σ₀ on boolean bit-words = UInt64 Σ₀. -/
theorem fieldBigSigma0_eq_bigSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt64 (fieldBigSigma0 x) = bigSigma0 (bitsWordToUInt64 x) := by
  rw [bitsWordToUInt64_eq_ofFnLE (fieldBigSigma0 x) (fieldBigSigma0_isBitsWord x hx),
    bitsWordToUInt64_eq_ofFnLE x hx]
  apply UInt64.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldBigSigma0 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩))
            (bitsAsBool x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 28 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 34 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 39 := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 28 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 34 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 39 (by decide)]
    _ = (bigSigma0 (UInt64.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [bigSigma0, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-- Field-level Σ₁ on boolean bit-words = UInt64 Σ₁. -/
theorem fieldBigSigma1_eq_bigSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt64 (fieldBigSigma1 x) = bigSigma1 (bitsWordToUInt64 x) := by
  rw [bitsWordToUInt64_eq_ofFnLE (fieldBigSigma1 x) (fieldBigSigma1_isBitsWord x hx),
    bitsWordToUInt64_eq_ofFnLE x hx]
  apply UInt64.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldBigSigma1 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩))
            (bitsAsBool x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 14 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 18 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 41 := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 14 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 18 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 41 (by decide)]
    _ = (bigSigma1 (UInt64.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [bigSigma1, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-- Field-level σ₀ on boolean bit-words = UInt64 σ₀. -/
theorem fieldSmallSigma0_eq_smallSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt64 (fieldSmallSigma0 x) = smallSigma0 (bitsWordToUInt64 x) := by
  rw [bitsWordToUInt64_eq_ofFnLE (fieldSmallSigma0 x) (fieldSmallSigma0_isBitsWord x hx),
    bitsWordToUInt64_eq_ofFnLE x hx]
  apply UInt64.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldSmallSigma0 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 1) % 64, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 8) % 64, Nat.mod_lt _ (by omega)⟩))
            (if h : i.val + 7 < 64 then bitsAsBool x ⟨i.val + 7, h⟩ else false)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 1 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 8 ^^^
          (BitVec.ofFnLE (bitsAsBool x) >>> 7) := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 1 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 8 (by decide)]
            rw [bitvec_ofFnLE_fieldShr (bitsAsBool x) 7]
    _ = (smallSigma0 (UInt64.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [smallSigma0, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-- Field-level σ₁ on boolean bit-words = UInt64 σ₁. -/
theorem fieldSmallSigma1_eq_smallSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt64 (fieldSmallSigma1 x) = smallSigma1 (bitsWordToUInt64 x) := by
  rw [bitsWordToUInt64_eq_ofFnLE (fieldSmallSigma1 x) (fieldSmallSigma1_isBitsWord x hx),
    bitsWordToUInt64_eq_ofFnLE x hx]
  apply UInt64.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldSmallSigma1 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 19) % 64, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 61) % 64, Nat.mod_lt _ (by omega)⟩))
            (if h : i.val + 6 < 64 then bitsAsBool x ⟨i.val + 6, h⟩ else false)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 19 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 61 ^^^
          (BitVec.ofFnLE (bitsAsBool x) >>> 6) := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 19 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 61 (by decide)]
            rw [bitvec_ofFnLE_fieldShr (bitsAsBool x) 6]
    _ = (smallSigma1 (UInt64.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [smallSigma1, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-! ## Small field/nat bridges for carry proofs -/

theorem babybear_add_no_wrap (a b : FBB) (h : a.val + b.val < BB_prime) :
    (a + b).val = a.val + b.val := by
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

private theorem carry_mul_65536_val (carry : FBB) (hcarry : carry = 0 ∨ carry = 1) :
    (carry * (2 ^ 16 : ℕ)).val = carry.val * 2 ^ 16 := by
  rcases hcarry with rfl | rfl <;> norm_num

theorem small_carry_mul_65536_val (carry : FBB) (hcarry : carry.val < 4) :
    (carry * (2 ^ 16 : ℕ)).val = carry.val * 2 ^ 16 := by
  have hpow : (((2 ^ 16 : ℕ) : FBB)).val = 2 ^ 16 := by
    exact ZMod.val_natCast_of_lt (by norm_num : 2 ^ 16 < BB_prime)
  have hmul_lt : carry.val * 2 ^ 16 < BB_prime := by
    have hle : carry.val * 2 ^ 16 ≤ 3 * 2 ^ 16 := by omega
    exact lt_of_le_of_lt hle (by norm_num)
  rw [Fin.val_mul]
  change carry.val * (((2 ^ 16 : ℕ) : FBB)).val % BB_prime = carry.val * 2 ^ 16
  rw [hpow, Nat.mod_eq_of_lt hmul_lt]

theorem byte_carry_mul_65536_val (carry : FBB) (hcarry : carry.val < 2 ^ 8) :
    (carry * (2 ^ 16 : ℕ)).val = carry.val * 2 ^ 16 := by
  have hpow : (((2 ^ 16 : ℕ) : FBB)).val = 2 ^ 16 := by
    exact ZMod.val_natCast_of_lt (by norm_num : 2 ^ 16 < BB_prime)
  have hmul_lt : carry.val * 2 ^ 16 < BB_prime := by
    have hle : carry.val * 2 ^ 16 ≤ (2 ^ 8 - 1) * 2 ^ 16 := by omega
    exact lt_of_le_of_lt hle (by norm_num)
  rw [Fin.val_mul]
  change carry.val * (((2 ^ 16 : ℕ) : FBB)).val % BB_prime = carry.val * 2 ^ 16
  rw [hpow, Nat.mod_eq_of_lt hmul_lt]

theorem UInt64_eq_of_toNat_eq {x y : UInt64} (h : x.toNat = y.toNat) : x = y :=
  (UInt64.toNat_inj).mp h


set_option maxHeartbeats 10000000

/-! ## 0F: 4-limb carry-chain addition (mod 2^64)

The AIR checks SHA-512 round-step word additions limb-by-limb with carry
propagation. These theorems combine 4 Nat-level carry-chain equations into
a single Nat-level congruence modulo 2^64, then lift to `UInt64`.
-/

/-- Core telescoping: 4 Nat-level carry-chain equations combine into a
    packed equality up to a multiple of 2^64. -/
theorem carry_chain_four_limb
    (A0 A1 A2 A3 R0 R1 R2 R3 c0 c1 c2 c3 : ℕ)
    (h0 : A0 = R0 + c0 * 65536)
    (h1 : A1 + c0 = R1 + c1 * 65536)
    (h2 : A2 + c1 = R2 + c2 * 65536)
    (h3 : A3 + c2 = R3 + c3 * 65536) :
    A0 + A1 * 65536 + A2 * 4294967296 + A3 * 281474976710656 =
      R0 + R1 * 65536 + R2 * 4294967296 + R3 * 281474976710656 +
        c3 * 18446744073709551616 := by
  omega

/-- Modular version: sum mod 2^64 equals result mod 2^64. -/
theorem carry_chain_four_limb_mod
    (A0 A1 A2 A3 R0 R1 R2 R3 c0 c1 c2 c3 : ℕ)
    (h0 : A0 = R0 + c0 * 65536)
    (h1 : A1 + c0 = R1 + c1 * 65536)
    (h2 : A2 + c1 = R2 + c2 * 65536)
    (h3 : A3 + c2 = R3 + c3 * 65536) :
    (A0 + A1 * 65536 + A2 * 4294967296 + A3 * 281474976710656) %
      18446744073709551616 =
    (R0 + R1 * 65536 + R2 * 4294967296 + R3 * 281474976710656) %
      18446744073709551616 := by
  have := carry_chain_four_limb A0 A1 A2 A3 R0 R1 R2 R3 c0 c1 c2 c3 h0 h1 h2 h3
  omega

private theorem u64_sum7_toNat (a b c d e f g : ℕ)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) (hd : d < 2 ^ 64)
    (he : e < 2 ^ 64) (hf : f < 2 ^ 64) (hg : g < 2 ^ 64) :
    ((((((a.toUInt64 + b.toUInt64) + c.toUInt64) + d.toUInt64) + e.toUInt64) + f.toUInt64) +
        g.toUInt64).toNat =
      (a + b + c + d + e + f + g) % 2 ^ 64 := by
  simp [UInt64.toNat_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

private theorem u64_sum6_toNat (a b c d e f : ℕ)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64)
    (hd : d < 2 ^ 64) (he : e < 2 ^ 64) (hf : f < 2 ^ 64) :
    (((((a.toUInt64 + b.toUInt64) + c.toUInt64) + d.toUInt64) + e.toUInt64) +
        f.toUInt64).toNat =
      (a + b + c + d + e + f) % 2 ^ 64 := by
  simp [UInt64.toNat_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

private theorem pack_u16x4_sum7
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
     e0 e1 e2 e3 f0 f1 f2 f3 g0 g1 g2 g3 : ℕ) :
    ((a0 + b0 + c0 + d0 + e0 + f0 + g0) +
        (a1 + b1 + c1 + d1 + e1 + f1 + g1) * 2 ^ 16 +
        (a2 + b2 + c2 + d2 + e2 + f2 + g2) * 2 ^ 32 +
        (a3 + b3 + c3 + d3 + e3 + f3 + g3) * 2 ^ 48) =
      ((a0 + a1 * 2 ^ 16 + a2 * 2 ^ 32 + a3 * 2 ^ 48) +
        (b0 + b1 * 2 ^ 16 + b2 * 2 ^ 32 + b3 * 2 ^ 48) +
        (c0 + c1 * 2 ^ 16 + c2 * 2 ^ 32 + c3 * 2 ^ 48) +
        (d0 + d1 * 2 ^ 16 + d2 * 2 ^ 32 + d3 * 2 ^ 48) +
        (e0 + e1 * 2 ^ 16 + e2 * 2 ^ 32 + e3 * 2 ^ 48) +
        (f0 + f1 * 2 ^ 16 + f2 * 2 ^ 32 + f3 * 2 ^ 48) +
        (g0 + g1 * 2 ^ 16 + g2 * 2 ^ 32 + g3 * 2 ^ 48)) := by
  omega

private theorem pack_u16x4_sum6
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3
     e0 e1 e2 e3 f0 f1 f2 f3 : ℕ) :
    ((a0 + b0 + c0 + d0 + e0 + f0) +
        (a1 + b1 + c1 + d1 + e1 + f1) * 2 ^ 16 +
        (a2 + b2 + c2 + d2 + e2 + f2) * 2 ^ 32 +
        (a3 + b3 + c3 + d3 + e3 + f3) * 2 ^ 48) =
      ((a0 + a1 * 2 ^ 16 + a2 * 2 ^ 32 + a3 * 2 ^ 48) +
        (b0 + b1 * 2 ^ 16 + b2 * 2 ^ 32 + b3 * 2 ^ 48) +
        (c0 + c1 * 2 ^ 16 + c2 * 2 ^ 32 + c3 * 2 ^ 48) +
        (d0 + d1 * 2 ^ 16 + d2 * 2 ^ 32 + d3 * 2 ^ 48) +
        (e0 + e1 * 2 ^ 16 + e2 * 2 ^ 32 + e3 * 2 ^ 48) +
        (f0 + f1 * 2 ^ 16 + f2 * 2 ^ 32 + f3 * 2 ^ 48)) := by
  omega

private theorem limb_eq_nat_of_field_eq
    (carryIn t0 t1 t2 t3 t4 t5 t6 out carryOut : FBB)
    (hcarry_in : carryIn.val < 2 ^ 8)
    (ht0 : t0.val < 2 ^ 16)
    (ht1 : t1.val < 2 ^ 16)
    (ht2 : t2.val < 2 ^ 16)
    (ht3 : t3.val < 2 ^ 16)
    (ht4 : t4.val < 2 ^ 16)
    (ht5 : t5.val < 2 ^ 16)
    (ht6 : t6.val < 2 ^ 16)
    (hout : out.val < 2 ^ 16)
    (hcarry_out : carryOut.val < 2 ^ 8)
    (heq :
      carryIn + t0 + t1 + t2 + t3 + t4 + t5 + t6 =
        out + carryOut * (2 ^ 16 : ℕ)) :
    carryIn.val + t0.val + t1.val + t2.val + t3.val + t4.val + t5.val + t6.val =
      out.val + carryOut.val * 2 ^ 16 := by
  have h01 :
      (carryIn + t0).val = carryIn.val + t0.val := by
    rw [babybear_add_no_wrap _ _ (by omega)]
  have h012 :
      (carryIn + t0 + t1).val = carryIn.val + t0.val + t1.val := by
    have hmid : (carryIn + t0).val + t1.val < BB_prime := by
      rw [h01]
      omega
    rw [babybear_add_no_wrap _ _ hmid, h01]
  have h0123 :
      (carryIn + t0 + t1 + t2).val =
        carryIn.val + t0.val + t1.val + t2.val := by
    have hmid : (carryIn + t0 + t1).val + t2.val < BB_prime := by
      rw [h012]
      omega
    rw [babybear_add_no_wrap _ _ hmid, h012]
  have h01234 :
      (carryIn + t0 + t1 + t2 + t3).val =
        carryIn.val + t0.val + t1.val + t2.val + t3.val := by
    have hmid : (carryIn + t0 + t1 + t2).val + t3.val < BB_prime := by
      rw [h0123]
      omega
    rw [babybear_add_no_wrap _ _ hmid, h0123]
  have h012345 :
      (carryIn + t0 + t1 + t2 + t3 + t4).val =
        carryIn.val + t0.val + t1.val + t2.val + t3.val + t4.val := by
    have hmid : (carryIn + t0 + t1 + t2 + t3).val + t4.val < BB_prime := by
      rw [h01234]
      omega
    rw [babybear_add_no_wrap _ _ hmid, h01234]
  have h0123456 :
      (carryIn + t0 + t1 + t2 + t3 + t4 + t5).val =
        carryIn.val + t0.val + t1.val + t2.val + t3.val + t4.val + t5.val := by
    have hmid : (carryIn + t0 + t1 + t2 + t3 + t4).val + t5.val < BB_prime := by
      rw [h012345]
      omega
    rw [babybear_add_no_wrap _ _ hmid, h012345]
  have h01234567 :
      (carryIn + t0 + t1 + t2 + t3 + t4 + t5 + t6).val =
        carryIn.val + t0.val + t1.val + t2.val + t3.val + t4.val + t5.val + t6.val := by
    have hmid : (carryIn + t0 + t1 + t2 + t3 + t4 + t5).val + t6.val < BB_prime := by
      rw [h0123456]
      omega
    rw [babybear_add_no_wrap _ _ hmid, h0123456]
  have hcarry_mul :
      (carryOut * (2 ^ 16 : ℕ)).val = carryOut.val * 2 ^ 16 := by
    exact byte_carry_mul_65536_val carryOut hcarry_out
  have hrhs :
      (out + carryOut * (2 ^ 16 : ℕ)).val =
        out.val + (carryOut * (2 ^ 16 : ℕ)).val := by
    rw [babybear_add_no_wrap _ _ (by rw [hcarry_mul]; omega)]
  have h := congrArg Fin.val heq
  rw [h01234567, hrhs, hcarry_mul] at h
  exact h

private theorem four_u16_pack_lt_u64
    (l0 l1 l2 l3 : ℕ)
    (h0 : l0 < 2 ^ 16) (h1 : l1 < 2 ^ 16)
    (h2 : l2 < 2 ^ 16) (h3 : l3 < 2 ^ 16) :
    l0 + l1 * 2 ^ 16 + l2 * 2 ^ 32 + l3 * 2 ^ 48 < 2 ^ 64 := by
  omega

/-- Seven-input limbed carry addition exported at the `UInt64` level. -/
theorem limbed_addition_seven_uint64
    (in0_0 in0_1 in0_2 in0_3 in1_0 in1_1 in1_2 in1_3
     in2_0 in2_1 in2_2 in2_3 in3_0 in3_1 in3_2 in3_3
     in4_0 in4_1 in4_2 in4_3 in5_0 in5_1 in5_2 in5_3
     in6_0 in6_1 in6_2 in6_3 r0 r1 r2 r3 carry0 carry1 carry2 carry3 : FBB)
    (hbounds : ∀ x ∈ [in0_0, in0_1, in0_2, in0_3, in1_0, in1_1, in1_2, in1_3,
                       in2_0, in2_1, in2_2, in2_3, in3_0, in3_1, in3_2, in3_3,
                       in4_0, in4_1, in4_2, in4_3, in5_0, in5_1, in5_2, in5_3,
                       in6_0, in6_1, in6_2, in6_3], x.val < 2 ^ 16)
    (hr0 : r0.val < 2 ^ 16) (hr1 : r1.val < 2 ^ 16)
    (hr2 : r2.val < 2 ^ 16) (hr3 : r3.val < 2 ^ 16)
    (hcarry0 : carry0.val < 2 ^ 8) (hcarry1 : carry1.val < 2 ^ 8)
    (hcarry2 : carry2.val < 2 ^ 8) (hcarry3 : carry3.val < 2 ^ 8)
    (h0 : in0_0 + in1_0 + in2_0 + in3_0 + in4_0 + in5_0 + in6_0 =
            r0 + carry0 * (2 ^ 16 : ℕ))
    (h1 : in0_1 + in1_1 + in2_1 + in3_1 + in4_1 + in5_1 + in6_1 + carry0 =
            r1 + carry1 * (2 ^ 16 : ℕ))
    (h2 : in0_2 + in1_2 + in2_2 + in3_2 + in4_2 + in5_2 + in6_2 + carry1 =
            r2 + carry2 * (2 ^ 16 : ℕ))
    (h3 : in0_3 + in1_3 + in2_3 + in3_3 + in4_3 + in5_3 + in6_3 + carry2 =
            r3 + carry3 * (2 ^ 16 : ℕ)) :
    (((((( (in0_0.val + in0_1.val * 2 ^ 16 + in0_2.val * 2 ^ 32 + in0_3.val * 2 ^ 48).toUInt64 +
            (in1_0.val + in1_1.val * 2 ^ 16 + in1_2.val * 2 ^ 32 + in1_3.val * 2 ^ 48).toUInt64) +
            (in2_0.val + in2_1.val * 2 ^ 16 + in2_2.val * 2 ^ 32 + in2_3.val * 2 ^ 48).toUInt64) +
            (in3_0.val + in3_1.val * 2 ^ 16 + in3_2.val * 2 ^ 32 + in3_3.val * 2 ^ 48).toUInt64) +
            (in4_0.val + in4_1.val * 2 ^ 16 + in4_2.val * 2 ^ 32 + in4_3.val * 2 ^ 48).toUInt64) +
            (in5_0.val + in5_1.val * 2 ^ 16 + in5_2.val * 2 ^ 32 + in5_3.val * 2 ^ 48).toUInt64) +
            (in6_0.val + in6_1.val * 2 ^ 16 + in6_2.val * 2 ^ 32 + in6_3.val * 2 ^ 48).toUInt64) =
      (r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48).toUInt64 := by
  have hin0_0 : in0_0.val < 2 ^ 16 := hbounds in0_0 (by simp)
  have hin0_1 : in0_1.val < 2 ^ 16 := hbounds in0_1 (by simp)
  have hin0_2 : in0_2.val < 2 ^ 16 := hbounds in0_2 (by simp)
  have hin0_3 : in0_3.val < 2 ^ 16 := hbounds in0_3 (by simp)
  have hin1_0 : in1_0.val < 2 ^ 16 := hbounds in1_0 (by simp)
  have hin1_1 : in1_1.val < 2 ^ 16 := hbounds in1_1 (by simp)
  have hin1_2 : in1_2.val < 2 ^ 16 := hbounds in1_2 (by simp)
  have hin1_3 : in1_3.val < 2 ^ 16 := hbounds in1_3 (by simp)
  have hin2_0 : in2_0.val < 2 ^ 16 := hbounds in2_0 (by simp)
  have hin2_1 : in2_1.val < 2 ^ 16 := hbounds in2_1 (by simp)
  have hin2_2 : in2_2.val < 2 ^ 16 := hbounds in2_2 (by simp)
  have hin2_3 : in2_3.val < 2 ^ 16 := hbounds in2_3 (by simp)
  have hin3_0 : in3_0.val < 2 ^ 16 := hbounds in3_0 (by simp)
  have hin3_1 : in3_1.val < 2 ^ 16 := hbounds in3_1 (by simp)
  have hin3_2 : in3_2.val < 2 ^ 16 := hbounds in3_2 (by simp)
  have hin3_3 : in3_3.val < 2 ^ 16 := hbounds in3_3 (by simp)
  have hin4_0 : in4_0.val < 2 ^ 16 := hbounds in4_0 (by simp)
  have hin4_1 : in4_1.val < 2 ^ 16 := hbounds in4_1 (by simp)
  have hin4_2 : in4_2.val < 2 ^ 16 := hbounds in4_2 (by simp)
  have hin4_3 : in4_3.val < 2 ^ 16 := hbounds in4_3 (by simp)
  have hin5_0 : in5_0.val < 2 ^ 16 := hbounds in5_0 (by simp)
  have hin5_1 : in5_1.val < 2 ^ 16 := hbounds in5_1 (by simp)
  have hin5_2 : in5_2.val < 2 ^ 16 := hbounds in5_2 (by simp)
  have hin5_3 : in5_3.val < 2 ^ 16 := hbounds in5_3 (by simp)
  have hin6_0 : in6_0.val < 2 ^ 16 := hbounds in6_0 (by simp)
  have hin6_1 : in6_1.val < 2 ^ 16 := hbounds in6_1 (by simp)
  have hin6_2 : in6_2.val < 2 ^ 16 := hbounds in6_2 (by simp)
  have hin6_3 : in6_3.val < 2 ^ 16 := hbounds in6_3 (by simp)
  have h0_field :
      (0 : FBB) + in0_0 + in1_0 + in2_0 + in3_0 + in4_0 + in5_0 + in6_0 =
        r0 + carry0 * (2 ^ 16 : ℕ) := by
    simpa using h0
  have h1_field :
      carry0 + in0_1 + in1_1 + in2_1 + in3_1 + in4_1 + in5_1 + in6_1 =
        r1 + carry1 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using h1
  have h2_field :
      carry1 + in0_2 + in1_2 + in2_2 + in3_2 + in4_2 + in5_2 + in6_2 =
        r2 + carry2 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using h2
  have h3_field :
      carry2 + in0_3 + in1_3 + in2_3 + in3_3 + in4_3 + in5_3 + in6_3 =
        r3 + carry3 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using h3
  have h0_nat :
      in0_0.val + in1_0.val + in2_0.val + in3_0.val + in4_0.val + in5_0.val + in6_0.val =
        r0.val + carry0.val * 2 ^ 16 := by
    simpa using
      limb_eq_nat_of_field_eq 0 in0_0 in1_0 in2_0 in3_0 in4_0 in5_0 in6_0 r0 carry0
      (by simp) hin0_0 hin1_0 hin2_0 hin3_0 hin4_0 hin5_0 hin6_0 hr0 hcarry0 h0_field
  have h1_nat :
      in0_1.val + in1_1.val + in2_1.val + in3_1.val + in4_1.val + in5_1.val + in6_1.val +
          carry0.val =
        r1.val + carry1.val * 2 ^ 16 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      limb_eq_nat_of_field_eq carry0 in0_1 in1_1 in2_1 in3_1 in4_1 in5_1 in6_1 r1 carry1
        hcarry0 hin0_1 hin1_1 hin2_1 hin3_1 hin4_1 hin5_1 hin6_1 hr1 hcarry1 h1_field
  have h2_nat :
      in0_2.val + in1_2.val + in2_2.val + in3_2.val + in4_2.val + in5_2.val + in6_2.val +
          carry1.val =
        r2.val + carry2.val * 2 ^ 16 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      limb_eq_nat_of_field_eq carry1 in0_2 in1_2 in2_2 in3_2 in4_2 in5_2 in6_2 r2 carry2
        hcarry1 hin0_2 hin1_2 hin2_2 hin3_2 hin4_2 hin5_2 hin6_2 hr2 hcarry2 h2_field
  have h3_nat :
      in0_3.val + in1_3.val + in2_3.val + in3_3.val + in4_3.val + in5_3.val + in6_3.val +
          carry2.val =
        r3.val + carry3.val * 2 ^ 16 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      limb_eq_nat_of_field_eq carry2 in0_3 in1_3 in2_3 in3_3 in4_3 in5_3 in6_3 r3 carry3
        hcarry2 hin0_3 hin1_3 hin2_3 hin3_3 hin4_3 hin5_3 hin6_3 hr3 hcarry3 h3_field
  have hchain :
      ((in0_0.val + in1_0.val + in2_0.val + in3_0.val + in4_0.val + in5_0.val + in6_0.val) +
          (in0_1.val + in1_1.val + in2_1.val + in3_1.val + in4_1.val + in5_1.val + in6_1.val) *
            2 ^ 16 +
          (in0_2.val + in1_2.val + in2_2.val + in3_2.val + in4_2.val + in5_2.val + in6_2.val) *
            2 ^ 32 +
          (in0_3.val + in1_3.val + in2_3.val + in3_3.val + in4_3.val + in5_3.val + in6_3.val) *
            2 ^ 48) % 2 ^ 64 =
        (r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48) % 2 ^ 64 := by
    exact carry_chain_four_limb_mod
      (in0_0.val + in1_0.val + in2_0.val + in3_0.val + in4_0.val + in5_0.val + in6_0.val)
      (in0_1.val + in1_1.val + in2_1.val + in3_1.val + in4_1.val + in5_1.val + in6_1.val)
      (in0_2.val + in1_2.val + in2_2.val + in3_2.val + in4_2.val + in5_2.val + in6_2.val)
      (in0_3.val + in1_3.val + in2_3.val + in3_3.val + in4_3.val + in5_3.val + in6_3.val)
      r0.val r1.val r2.val r3.val carry0.val carry1.val carry2.val carry3.val
      h0_nat h1_nat h2_nat h3_nat
  have hmod :
      ((in0_0.val + in0_1.val * 2 ^ 16 + in0_2.val * 2 ^ 32 + in0_3.val * 2 ^ 48) +
          (in1_0.val + in1_1.val * 2 ^ 16 + in1_2.val * 2 ^ 32 + in1_3.val * 2 ^ 48) +
          (in2_0.val + in2_1.val * 2 ^ 16 + in2_2.val * 2 ^ 32 + in2_3.val * 2 ^ 48) +
          (in3_0.val + in3_1.val * 2 ^ 16 + in3_2.val * 2 ^ 32 + in3_3.val * 2 ^ 48) +
          (in4_0.val + in4_1.val * 2 ^ 16 + in4_2.val * 2 ^ 32 + in4_3.val * 2 ^ 48) +
          (in5_0.val + in5_1.val * 2 ^ 16 + in5_2.val * 2 ^ 32 + in5_3.val * 2 ^ 48) +
          (in6_0.val + in6_1.val * 2 ^ 16 + in6_2.val * 2 ^ 32 + in6_3.val * 2 ^ 48)) % 2 ^ 64 =
        (r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48) % 2 ^ 64 := by
    rw [← pack_u16x4_sum7]
    exact hchain
  have hin0_lt :
      in0_0.val + in0_1.val * 2 ^ 16 + in0_2.val * 2 ^ 32 + in0_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin0_0 hin0_1 hin0_2 hin0_3
  have hin1_lt :
      in1_0.val + in1_1.val * 2 ^ 16 + in1_2.val * 2 ^ 32 + in1_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin1_0 hin1_1 hin1_2 hin1_3
  have hin2_lt :
      in2_0.val + in2_1.val * 2 ^ 16 + in2_2.val * 2 ^ 32 + in2_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin2_0 hin2_1 hin2_2 hin2_3
  have hin3_lt :
      in3_0.val + in3_1.val * 2 ^ 16 + in3_2.val * 2 ^ 32 + in3_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin3_0 hin3_1 hin3_2 hin3_3
  have hin4_lt :
      in4_0.val + in4_1.val * 2 ^ 16 + in4_2.val * 2 ^ 32 + in4_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin4_0 hin4_1 hin4_2 hin4_3
  have hin5_lt :
      in5_0.val + in5_1.val * 2 ^ 16 + in5_2.val * 2 ^ 32 + in5_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin5_0 hin5_1 hin5_2 hin5_3
  have hin6_lt :
      in6_0.val + in6_1.val * 2 ^ 16 + in6_2.val * 2 ^ 32 + in6_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin6_0 hin6_1 hin6_2 hin6_3
  have hr_lt : r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hr0 hr1 hr2 hr3
  apply UInt64_eq_of_toNat_eq
  rw [u64_sum7_toNat _ _ _ _ _ _ _ hin0_lt hin1_lt hin2_lt hin3_lt hin4_lt hin5_lt hin6_lt]
  simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hr_lt] using hmod

/-- Six-input limbed carry addition exported at the `UInt64` level. -/
theorem limbed_addition_six_uint64
    (in0_0 in0_1 in0_2 in0_3 in1_0 in1_1 in1_2 in1_3
     in2_0 in2_1 in2_2 in2_3 in3_0 in3_1 in3_2 in3_3
     in4_0 in4_1 in4_2 in4_3 in5_0 in5_1 in5_2 in5_3
     r0 r1 r2 r3 carry0 carry1 carry2 carry3 : FBB)
    (hbounds : ∀ x ∈ [in0_0, in0_1, in0_2, in0_3, in1_0, in1_1, in1_2, in1_3,
                       in2_0, in2_1, in2_2, in2_3, in3_0, in3_1, in3_2, in3_3,
                       in4_0, in4_1, in4_2, in4_3, in5_0, in5_1, in5_2, in5_3],
                      x.val < 2 ^ 16)
    (hr0 : r0.val < 2 ^ 16) (hr1 : r1.val < 2 ^ 16)
    (hr2 : r2.val < 2 ^ 16) (hr3 : r3.val < 2 ^ 16)
    (hcarry0 : carry0.val < 2 ^ 8) (hcarry1 : carry1.val < 2 ^ 8)
    (hcarry2 : carry2.val < 2 ^ 8) (hcarry3 : carry3.val < 2 ^ 8)
    (h0 : in0_0 + in1_0 + in2_0 + in3_0 + in4_0 + in5_0 =
            r0 + carry0 * (2 ^ 16 : ℕ))
    (h1 : in0_1 + in1_1 + in2_1 + in3_1 + in4_1 + in5_1 + carry0 =
            r1 + carry1 * (2 ^ 16 : ℕ))
    (h2 : in0_2 + in1_2 + in2_2 + in3_2 + in4_2 + in5_2 + carry1 =
            r2 + carry2 * (2 ^ 16 : ℕ))
    (h3 : in0_3 + in1_3 + in2_3 + in3_3 + in4_3 + in5_3 + carry2 =
            r3 + carry3 * (2 ^ 16 : ℕ)) :
    ((((((in0_0.val + in0_1.val * 2 ^ 16 + in0_2.val * 2 ^ 32 + in0_3.val * 2 ^ 48).toUInt64 +
          (in1_0.val + in1_1.val * 2 ^ 16 + in1_2.val * 2 ^ 32 + in1_3.val * 2 ^ 48).toUInt64) +
          (in2_0.val + in2_1.val * 2 ^ 16 + in2_2.val * 2 ^ 32 + in2_3.val * 2 ^ 48).toUInt64) +
          (in3_0.val + in3_1.val * 2 ^ 16 + in3_2.val * 2 ^ 32 + in3_3.val * 2 ^ 48).toUInt64) +
          (in4_0.val + in4_1.val * 2 ^ 16 + in4_2.val * 2 ^ 32 + in4_3.val * 2 ^ 48).toUInt64) +
          (in5_0.val + in5_1.val * 2 ^ 16 + in5_2.val * 2 ^ 32 + in5_3.val * 2 ^ 48).toUInt64) =
      (r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48).toUInt64 := by
  have hin0_0 : in0_0.val < 2 ^ 16 := hbounds in0_0 (by simp)
  have hin0_1 : in0_1.val < 2 ^ 16 := hbounds in0_1 (by simp)
  have hin0_2 : in0_2.val < 2 ^ 16 := hbounds in0_2 (by simp)
  have hin0_3 : in0_3.val < 2 ^ 16 := hbounds in0_3 (by simp)
  have hin1_0 : in1_0.val < 2 ^ 16 := hbounds in1_0 (by simp)
  have hin1_1 : in1_1.val < 2 ^ 16 := hbounds in1_1 (by simp)
  have hin1_2 : in1_2.val < 2 ^ 16 := hbounds in1_2 (by simp)
  have hin1_3 : in1_3.val < 2 ^ 16 := hbounds in1_3 (by simp)
  have hin2_0 : in2_0.val < 2 ^ 16 := hbounds in2_0 (by simp)
  have hin2_1 : in2_1.val < 2 ^ 16 := hbounds in2_1 (by simp)
  have hin2_2 : in2_2.val < 2 ^ 16 := hbounds in2_2 (by simp)
  have hin2_3 : in2_3.val < 2 ^ 16 := hbounds in2_3 (by simp)
  have hin3_0 : in3_0.val < 2 ^ 16 := hbounds in3_0 (by simp)
  have hin3_1 : in3_1.val < 2 ^ 16 := hbounds in3_1 (by simp)
  have hin3_2 : in3_2.val < 2 ^ 16 := hbounds in3_2 (by simp)
  have hin3_3 : in3_3.val < 2 ^ 16 := hbounds in3_3 (by simp)
  have hin4_0 : in4_0.val < 2 ^ 16 := hbounds in4_0 (by simp)
  have hin4_1 : in4_1.val < 2 ^ 16 := hbounds in4_1 (by simp)
  have hin4_2 : in4_2.val < 2 ^ 16 := hbounds in4_2 (by simp)
  have hin4_3 : in4_3.val < 2 ^ 16 := hbounds in4_3 (by simp)
  have hin5_0 : in5_0.val < 2 ^ 16 := hbounds in5_0 (by simp)
  have hin5_1 : in5_1.val < 2 ^ 16 := hbounds in5_1 (by simp)
  have hin5_2 : in5_2.val < 2 ^ 16 := hbounds in5_2 (by simp)
  have hin5_3 : in5_3.val < 2 ^ 16 := hbounds in5_3 (by simp)
  have h0_field :
      (0 : FBB) + in0_0 + in1_0 + in2_0 + in3_0 + in4_0 + in5_0 + 0 =
        r0 + carry0 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc] using h0
  have h1_field :
      carry0 + in0_1 + in1_1 + in2_1 + in3_1 + in4_1 + in5_1 + 0 =
        r1 + carry1 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using h1
  have h2_field :
      carry1 + in0_2 + in1_2 + in2_2 + in3_2 + in4_2 + in5_2 + 0 =
        r2 + carry2 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using h2
  have h3_field :
      carry2 + in0_3 + in1_3 + in2_3 + in3_3 + in4_3 + in5_3 + 0 =
        r3 + carry3 * (2 ^ 16 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using h3
  have h0_nat :
      in0_0.val + in1_0.val + in2_0.val + in3_0.val + in4_0.val + in5_0.val =
        r0.val + carry0.val * 2 ^ 16 := by
    simpa using
      limb_eq_nat_of_field_eq 0 in0_0 in1_0 in2_0 in3_0 in4_0 in5_0 0 r0 carry0
      (by simp) hin0_0 hin1_0 hin2_0 hin3_0 hin4_0 hin5_0 (by simp) hr0 hcarry0 h0_field
  have h1_nat :
      in0_1.val + in1_1.val + in2_1.val + in3_1.val + in4_1.val + in5_1.val + carry0.val =
        r1.val + carry1.val * 2 ^ 16 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      limb_eq_nat_of_field_eq carry0 in0_1 in1_1 in2_1 in3_1 in4_1 in5_1 0 r1 carry1
        hcarry0 hin0_1 hin1_1 hin2_1 hin3_1 hin4_1 hin5_1 (by simp) hr1 hcarry1 h1_field
  have h2_nat :
      in0_2.val + in1_2.val + in2_2.val + in3_2.val + in4_2.val + in5_2.val + carry1.val =
        r2.val + carry2.val * 2 ^ 16 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      limb_eq_nat_of_field_eq carry1 in0_2 in1_2 in2_2 in3_2 in4_2 in5_2 0 r2 carry2
        hcarry1 hin0_2 hin1_2 hin2_2 hin3_2 hin4_2 hin5_2 (by simp) hr2 hcarry2 h2_field
  have h3_nat :
      in0_3.val + in1_3.val + in2_3.val + in3_3.val + in4_3.val + in5_3.val + carry2.val =
        r3.val + carry3.val * 2 ^ 16 := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      limb_eq_nat_of_field_eq carry2 in0_3 in1_3 in2_3 in3_3 in4_3 in5_3 0 r3 carry3
        hcarry2 hin0_3 hin1_3 hin2_3 hin3_3 hin4_3 hin5_3 (by simp) hr3 hcarry3 h3_field
  have hchain :
      ((in0_0.val + in1_0.val + in2_0.val + in3_0.val + in4_0.val + in5_0.val) +
          (in0_1.val + in1_1.val + in2_1.val + in3_1.val + in4_1.val + in5_1.val) * 2 ^ 16 +
          (in0_2.val + in1_2.val + in2_2.val + in3_2.val + in4_2.val + in5_2.val) * 2 ^ 32 +
          (in0_3.val + in1_3.val + in2_3.val + in3_3.val + in4_3.val + in5_3.val) * 2 ^ 48) %
        2 ^ 64 =
        (r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48) % 2 ^ 64 := by
    exact carry_chain_four_limb_mod
      (in0_0.val + in1_0.val + in2_0.val + in3_0.val + in4_0.val + in5_0.val)
      (in0_1.val + in1_1.val + in2_1.val + in3_1.val + in4_1.val + in5_1.val)
      (in0_2.val + in1_2.val + in2_2.val + in3_2.val + in4_2.val + in5_2.val)
      (in0_3.val + in1_3.val + in2_3.val + in3_3.val + in4_3.val + in5_3.val)
      r0.val r1.val r2.val r3.val carry0.val carry1.val carry2.val carry3.val
      h0_nat h1_nat h2_nat h3_nat
  have hmod :
      ((in0_0.val + in0_1.val * 2 ^ 16 + in0_2.val * 2 ^ 32 + in0_3.val * 2 ^ 48) +
          (in1_0.val + in1_1.val * 2 ^ 16 + in1_2.val * 2 ^ 32 + in1_3.val * 2 ^ 48) +
          (in2_0.val + in2_1.val * 2 ^ 16 + in2_2.val * 2 ^ 32 + in2_3.val * 2 ^ 48) +
          (in3_0.val + in3_1.val * 2 ^ 16 + in3_2.val * 2 ^ 32 + in3_3.val * 2 ^ 48) +
          (in4_0.val + in4_1.val * 2 ^ 16 + in4_2.val * 2 ^ 32 + in4_3.val * 2 ^ 48) +
          (in5_0.val + in5_1.val * 2 ^ 16 + in5_2.val * 2 ^ 32 + in5_3.val * 2 ^ 48)) % 2 ^ 64 =
        (r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48) % 2 ^ 64 := by
    rw [← pack_u16x4_sum6]
    exact hchain
  have hin0_lt :
      in0_0.val + in0_1.val * 2 ^ 16 + in0_2.val * 2 ^ 32 + in0_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin0_0 hin0_1 hin0_2 hin0_3
  have hin1_lt :
      in1_0.val + in1_1.val * 2 ^ 16 + in1_2.val * 2 ^ 32 + in1_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin1_0 hin1_1 hin1_2 hin1_3
  have hin2_lt :
      in2_0.val + in2_1.val * 2 ^ 16 + in2_2.val * 2 ^ 32 + in2_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin2_0 hin2_1 hin2_2 hin2_3
  have hin3_lt :
      in3_0.val + in3_1.val * 2 ^ 16 + in3_2.val * 2 ^ 32 + in3_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin3_0 hin3_1 hin3_2 hin3_3
  have hin4_lt :
      in4_0.val + in4_1.val * 2 ^ 16 + in4_2.val * 2 ^ 32 + in4_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin4_0 hin4_1 hin4_2 hin4_3
  have hin5_lt :
      in5_0.val + in5_1.val * 2 ^ 16 + in5_2.val * 2 ^ 32 + in5_3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hin5_0 hin5_1 hin5_2 hin5_3
  have hr_lt : r0.val + r1.val * 2 ^ 16 + r2.val * 2 ^ 32 + r3.val * 2 ^ 48 < 2 ^ 64 := by
    exact four_u16_pack_lt_u64 _ _ _ _ hr0 hr1 hr2 hr3
  apply UInt64_eq_of_toNat_eq
  rw [u64_sum6_toNat _ _ _ _ _ _ hin0_lt hin1_lt hin2_lt hin3_lt hin4_lt hin5_lt]
  simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hr_lt] using hmod

/-- Seven packed Nat inputs add to a `UInt64` modulo `2^64`. -/
theorem packed_addition_seven_uint64
    (in0 in1 in2 in3 in4 in5 in6 r : ℕ)
    (hin0 : in0 < 2 ^ 64) (hin1 : in1 < 2 ^ 64) (hin2 : in2 < 2 ^ 64) (hin3 : in3 < 2 ^ 64)
    (hin4 : in4 < 2 ^ 64) (hin5 : in5 < 2 ^ 64) (hin6 : in6 < 2 ^ 64)
    (hr : r < 2 ^ 64)
    (hmod : (in0 + in1 + in2 + in3 + in4 + in5 + in6) % 2 ^ 64 = r % 2 ^ 64) :
    ((((((in0.toUInt64 + in1.toUInt64) + in2.toUInt64) + in3.toUInt64) + in4.toUInt64) +
        in5.toUInt64) + in6.toUInt64) =
      r.toUInt64 := by
  apply UInt64_eq_of_toNat_eq
  rw [u64_sum7_toNat _ _ _ _ _ _ _ hin0 hin1 hin2 hin3 hin4 hin5 hin6]
  simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hr] using hmod

/-- Six packed Nat inputs add to a `UInt64` modulo `2^64`. -/
theorem packed_addition_six_uint64
    (in0 in1 in2 in3 in4 in5 r : ℕ)
    (hin0 : in0 < 2 ^ 64) (hin1 : in1 < 2 ^ 64) (hin2 : in2 < 2 ^ 64)
    (hin3 : in3 < 2 ^ 64) (hin4 : in4 < 2 ^ 64) (hin5 : in5 < 2 ^ 64)
    (hr : r < 2 ^ 64)
    (hmod : (in0 + in1 + in2 + in3 + in4 + in5) % 2 ^ 64 = r % 2 ^ 64) :
    (((((in0.toUInt64 + in1.toUInt64) + in2.toUInt64) + in3.toUInt64) + in4.toUInt64) +
        in5.toUInt64) =
      r.toUInt64 := by
  apply UInt64_eq_of_toNat_eq
  rw [u64_sum6_toNat _ _ _ _ _ _ hin0 hin1 hin2 hin3 hin4 hin5]
  simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt hr] using hmod

theorem natCast_ne_zero_of_lt_BB_prime {n : ℕ}
    (hn_lt : n < BB_prime)
    (hn_ne : n ≠ 0) :
    ((n : ℕ) : FBB) ≠ 0 := by
  intro hzero
  have hval := congrArg Fin.val hzero
  simp [Nat.mod_eq_of_lt hn_lt] at hval
  exact hn_ne hval

end Sha2BlockHasherVmAir_sha512.BlockSpec
