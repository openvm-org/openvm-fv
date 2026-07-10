/-
  Layer 0: Field Arithmetic Bridge

  Generic lemmas relating BabyBear field-level operations to UInt32 operations.
  These are the foundational bridge that all subsequent layers depend on.

  No constraint dependencies — purely algebraic.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear

/-! ## 0A: Bit booleanness -/

/-- The core algebraic fact: `x * (x - 1) = 0` in BabyBear implies `x ∈ {0, 1}`. -/
theorem bit_boolean_of_sq_eq_zero (x : FBB) (h : x * (x - 1) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with hx | hx
  · exact Or.inl hx
  · exact Or.inr (sub_eq_zero.mp hx)

/-- The ternary analogue: `x * (x - 1) * (x - 2) = 0` implies `x ∈ {0, 1, 2}`. -/
theorem ternary_of_cube_eq_zero (x : FBB) (h : x * (x - 1) * (x - 2) = 0) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases mul_eq_zero.mp h with h01 | h2
  · rcases mul_eq_zero.mp h01 with hx | h1
    · exact Or.inl hx
    · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h2))

/-! ## 0B: Bitwise operations on boolean field elements -/

/-- Field XOR preserves booleanness. -/
theorem fieldXor_boolean_closed (x y : FBB) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    fieldXor x y = 0 ∨ fieldXor x y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [fieldXor]

/-- Nested field XOR agrees with the 3-bit XOR truth-table polynomial. -/
theorem fieldXor3_poly (x y z : FBB) :
    fieldXor (fieldXor x y) z =
      x * y * z +
      x * (1 - y) * (1 - z) +
      (1 - x) * y * (1 - z) +
      (1 - x) * (1 - y) * z := by
  simp [fieldXor]
  ring

/-- Field AND preserves booleanness. -/
theorem fieldAnd_boolean_closed (x y : FBB) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    fieldAnd x y = 0 ∨ fieldAnd x y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [fieldAnd]

/-- Field NOT preserves booleanness. -/
theorem fieldNot_boolean_closed (x : FBB) (hx : x = 0 ∨ x = 1) :
    fieldNot x = 0 ∨ fieldNot x = 1 := by
  rcases hx with rfl | rfl <;> simp [fieldNot]

/-! ## 0C: Bitwise operations lift to BitsWord -/

/-- fieldRotr preserves isBitsWord. -/
theorem fieldRotr_preserves_boolean (x : BitsWord) (n : ℕ) (hx : isBitsWord x) :
    isBitsWord (fieldRotr x n) := by
  intro i
  simpa [fieldRotr] using hx ⟨(i.val + n) % 32, Nat.mod_lt _ (by omega)⟩

/-- fieldShr preserves isBitsWord. -/
theorem fieldShr_preserves_boolean (x : BitsWord) (n : ℕ) (hx : isBitsWord x) :
    isBitsWord (fieldShr x n) := by
  intro i
  by_cases h : i.val + n < 32
  · simpa [fieldShr, h] using hx ⟨i.val + n, h⟩
  · simp [fieldShr, h]

/-! ## 0D: Bit composition: field ↔ UInt32 -/

private theorem composeLo16_eq_nat_sum (bits : BitsWord) (hb : isBitsWord bits) :
    composeLo16 bits =
      ((∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) : FBB) := by
  rw [composeLo16, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases hb ⟨i.val, by omega⟩ with hbit | hbit <;> simp [hbit]

private theorem composeHi16_eq_nat_sum (bits : BitsWord) (hb : isBitsWord bits) :
    composeHi16 bits =
      ((∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) : FBB) := by
  rw [composeHi16, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases hb ⟨i.val + 16, by omega⟩ with hbit | hbit <;> simp [hbit]

private theorem composeBits_eq_nat_sum (bits : BitsWord) (hb : isBitsWord bits) :
    composeBits bits =
      ((∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) : FBB) := by
  rw [composeBits, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rcases hb i with hbit | hbit <;> simp [hbit]

private theorem composeLo16_nat_sum_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) < 2 ^ 16 := by
  have hle :
      (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) ≤
        ∑ i : Fin 16, 2 ^ i.val := by
    refine Finset.sum_le_sum ?_
    intro i _
    rcases hb ⟨i.val, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

private theorem composeHi16_nat_sum_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) < 2 ^ 16 := by
  have hle :
      (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) ≤
        ∑ i : Fin 16, 2 ^ i.val := by
    refine Finset.sum_le_sum ?_
    intro i _
    rcases hb ⟨i.val + 16, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

private theorem composeBits_nat_sum_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) < 2 ^ 32 := by
  have hle :
      (∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) ≤
        ∑ i : Fin 32, 2 ^ i.val := by
    refine Finset.sum_le_sum ?_
    intro i _
    rcases hb i with hbit | hbit <;> simp [hbit]
  have hpow : (∑ i : Fin 32, 2 ^ i.val : ℕ) < 2 ^ 32 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

/-- If all bits are boolean, composeLo16 produces a value < 2^16. -/
theorem composeLo16_val_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (composeLo16 bits).val < 2 ^ 16 := by
  have hs_lt :
      (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) < 2 ^ 16 :=
    composeLo16_nat_sum_lt bits hb
  have hs_prime :
      (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) < BB_prime := by
    exact lt_trans hs_lt (by norm_num)
  have hval :
      (composeLo16 bits).val =
        ∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val := by
    have hcast := congrArg Fin.val (composeLo16_eq_nat_sum bits hb)
    change
      (composeLo16 bits).val =
        (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hs_prime] at hcast
    exact hcast
  calc
    (composeLo16 bits).val =
        ∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val := hval
    _ < 2 ^ 16 := hs_lt

/-- Rewrite `composeLo16` as a `Finset.range 16` sum. -/
theorem composeLo16_range_eq (bits : BitsWord) :
    composeLo16 bits =
      ∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i, lt_trans hi (by decide)⟩ * 2 ^ i else 0) := by
  have hsum :
      (∑ i : Fin 16, bits ⟨i.val, by omega⟩ * 2 ^ i.val) =
        ∑ i ∈ Finset.range 16,
          (if hi : i < 16 then bits ⟨i, lt_trans hi (by decide)⟩ * 2 ^ i else 0) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun i => if hi : i < 16 then bits ⟨i, lt_trans hi (by decide)⟩ * 2 ^ i else 0)
        (n := 16))
  rw [composeLo16]
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- If all bits are boolean, composeHi16 produces a value < 2^16. -/
theorem composeHi16_val_lt (bits : BitsWord) (hb : isBitsWord bits) :
    (composeHi16 bits).val < 2 ^ 16 := by
  have hs_lt :
      (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) < 2 ^ 16 :=
    composeHi16_nat_sum_lt bits hb
  have hs_prime :
      (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) < BB_prime := by
    exact lt_trans hs_lt (by norm_num)
  have hval :
      (composeHi16 bits).val =
        ∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val := by
    have hcast := congrArg Fin.val (composeHi16_eq_nat_sum bits hb)
    change
      (composeHi16 bits).val =
        (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hs_prime] at hcast
    exact hcast
  calc
    (composeHi16 bits).val =
        ∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val := hval
    _ < 2 ^ 16 := hs_lt

/-- Rewrite `composeHi16` as a `Finset.range 16` sum. -/
theorem composeHi16_range_eq (bits : BitsWord) :
    composeHi16 bits =
      ∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 16, by omega⟩ * 2 ^ i else 0) := by
  have hsum :
      (∑ i : Fin 16, bits ⟨i.val + 16, by omega⟩ * 2 ^ i.val) =
        ∑ i ∈ Finset.range 16,
          (if hi : i < 16 then bits ⟨i + 16, by omega⟩ * 2 ^ i else 0) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun i => if hi : i < 16 then bits ⟨i + 16, by omega⟩ * 2 ^ i else 0)
        (n := 16))
  rw [composeHi16]
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- If all bits are boolean, composeBits agrees with bitsWordToUInt32
    (modulo the BabyBear embedding of ℕ). -/
theorem composeBits_eq_bitsWordToUInt32 (bits : BitsWord) (hb : isBitsWord bits) :
    composeBits bits = ((bitsWordToUInt32 bits).toNat : FBB) := by
  let total : ℕ := ∑ i : Fin 32, (bits i).val * 2 ^ i.val
  have htotal_lt : total < 2 ^ 32 := by
    change (∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) < 2 ^ 32
    exact composeBits_nat_sum_lt bits hb
  have hcompose : composeBits bits = (total : FBB) := by
    change composeBits bits = (((∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ)) : FBB)
    exact composeBits_eq_nat_sum bits hb
  have hword_nat : (bitsWordToUInt32 bits).toNat = total := by
    have hnat_mod : (bitsWordToUInt32 bits).toNat = total % 2 ^ 32 := by
      change ((total).toUInt32).toNat = total % 2 ^ 32
      simpa using (UInt32.toNat_ofNat (n := total))
    rw [Nat.mod_eq_of_lt htotal_lt] at hnat_mod
    exact hnat_mod
  calc
    composeBits bits = (total : FBB) := hcompose
    _ = (((bitsWordToUInt32 bits).toNat : ℕ) : FBB) := by rw [hword_nat]

/-- A boolean bit-word reassembles from its low/high 16-bit limbs. -/
theorem bitsWordToUInt32_eq_compose16 (bits : BitsWord) (hb : isBitsWord bits) :
    bitsWordToUInt32 bits =
      ((composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16).toUInt32 := by
  let lo : ℕ := ∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val
  let hi : ℕ := ∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val
  have hlo_field : composeLo16 bits = (lo : FBB) := by
    dsimp [lo]
    rw [composeLo16, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rcases hb ⟨i.val, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hhi_field : composeHi16 bits = (hi : FBB) := by
    dsimp [hi]
    rw [composeHi16, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rcases hb ⟨i.val + 16, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hlo_lt_nat : lo < 2 ^ 16 := by
    dsimp [lo]
    have hle :
        (∑ i : Fin 16, (bits ⟨i.val, by omega⟩).val * 2 ^ i.val : ℕ) ≤
          ∑ i : Fin 16, 2 ^ i.val := by
      refine Finset.sum_le_sum ?_
      intro i _
      rcases hb ⟨i.val, by omega⟩ with hbit | hbit <;> simp [hbit]
    have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
      norm_num [Fin.sum_univ_eq_sum_range]
    exact lt_of_le_of_lt hle hpow
  have hhi_lt_nat : hi < 2 ^ 16 := by
    dsimp [hi]
    have hle :
        (∑ i : Fin 16, (bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val : ℕ) ≤
          ∑ i : Fin 16, 2 ^ i.val := by
      refine Finset.sum_le_sum ?_
      intro i _
      rcases hb ⟨i.val + 16, by omega⟩ with hbit | hbit <;> simp [hbit]
    have hpow : (∑ i : Fin 16, 2 ^ i.val : ℕ) < 2 ^ 16 := by
      norm_num [Fin.sum_univ_eq_sum_range]
    exact lt_of_le_of_lt hle hpow
  have hlo_lt : lo < BB_prime := lt_trans hlo_lt_nat (by norm_num)
  have hhi_lt : hi < BB_prime := lt_trans hhi_lt_nat (by norm_num)
  have hlo_val : (composeLo16 bits).val = lo := by
    have hcast := congrArg Fin.val hlo_field
    change (composeLo16 bits).val = lo % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hlo_lt] at hcast
    exact hcast
  have hhi_val : (composeHi16 bits).val = hi := by
    have hcast := congrArg Fin.val hhi_field
    change (composeHi16 bits).val = hi % BB_prime at hcast
    rw [Nat.mod_eq_of_lt hhi_lt] at hcast
    exact hcast
  have hsum :
      (∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) = lo + hi * 2 ^ 16 := by
    change
      (∑ i : Fin (16 + 16), (bits i).val * 2 ^ i.val : ℕ) =
        lo + hi * 2 ^ 16
    rw [Fin.sum_univ_add]
    have hfirst :
        (∑ i : Fin 16, (bits (Fin.castAdd 16 i)).val * 2 ^ (Fin.castAdd 16 i).val : ℕ) = lo := by
      dsimp [lo]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hcast : Fin.castAdd 16 i = ⟨i.val, by omega⟩ := by
        ext
        simp [Fin.castAdd]
      rw [hcast]
    have hsecond :
        (∑ i : Fin 16, (bits (Fin.natAdd 16 i)).val * 2 ^ (Fin.natAdd 16 i).val : ℕ) =
          hi * 2 ^ 16 := by
      calc
        (∑ i : Fin 16, (bits (Fin.natAdd 16 i)).val * 2 ^ (Fin.natAdd 16 i).val : ℕ)
            = ∑ i : Fin 16, ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) * 2 ^ 16 := by
                refine Finset.sum_congr rfl ?_
                intro i _
                have hcast : Fin.natAdd 16 i = ⟨i.val + 16, by omega⟩ := by
                  ext
                  simp [Fin.natAdd]
                  omega
                have hp : (2 ^ (i.val + 16) : ℕ) = 2 ^ i.val * 2 ^ 16 := by
                  rw [Nat.pow_add]
                calc
                  (bits (Fin.natAdd 16 i)).val * 2 ^ (Fin.natAdd 16 i).val
                      = (bits ⟨i.val + 16, by omega⟩).val * (2 ^ i.val * 2 ^ 16) := by
                          rw [hcast, hp]
                  _ = ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) * 2 ^ 16 := by
                          ac_rfl
        _ = hi * 2 ^ 16 := by
            calc
              (∑ i : Fin 16, ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) * 2 ^ 16 : ℕ)
                  = ∑ i : Fin 16, (2 ^ 16) * ((bits ⟨i.val + 16, by omega⟩).val * 2 ^ i.val) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _
                      ring
              _ = (2 ^ 16) * hi := by
                    dsimp [hi]
                    rw [Finset.mul_sum]
              _ = hi * 2 ^ 16 := by rw [Nat.mul_comm]
    rw [hfirst, hsecond]
  rw [bitsWordToUInt32, hsum, hlo_val, hhi_val]

theorem foldl_range_add_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      Finset.sum (Finset.range n) f := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      simp [Nat.add_comm]


/-! ## 0E: Limbed carry addition

NOTE: All limbed addition theorems require that input limb `.val < 2^16`.
This is always satisfied when limbs come from `composeLo16` / `composeHi16` of boolean bits.
Without bounds, the ZMod equations don't imply ℕ equations (BabyBear wrap-around).

Different AIR gadgets use different carry encodings:
- digest-row carries are boolean;
- message-schedule carries are 2-bit values (`< 4`);
- round-step carries are byte-range values (`< 256`). -/

/-- Key sub-lemma: a BabyBear field sum that fits in ℕ gives an exact ℕ equation.
    If a.val + b.val < BB_prime, then (a + b).val = a.val + b.val. -/
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

private theorem byte_carry_mul_65536_val (carry : FBB) (hcarry : carry.val < 2 ^ 8) :
    (carry * (2 ^ 16 : ℕ)).val = carry.val * 2 ^ 16 := by
  have hpow : (((2 ^ 16 : ℕ) : FBB)).val = 2 ^ 16 := by
    exact ZMod.val_natCast_of_lt (by norm_num : 2 ^ 16 < BB_prime)
  have hmul_lt : carry.val * 2 ^ 16 < BB_prime := by
    have hle : carry.val * 2 ^ 16 ≤ (2 ^ 8 - 1) * 2 ^ 16 := by omega
    exact lt_of_le_of_lt hle (by norm_num)
  rw [Fin.val_mul]
  change carry.val * (((2 ^ 16 : ℕ) : FBB)).val % BB_prime = carry.val * 2 ^ 16
  rw [hpow, Nat.mod_eq_of_lt hmul_lt]

/-- Two-input limbed carry addition is correct (with bounds). -/
theorem limbed_addition_two_inputs
    (a_lo a_hi b_lo b_hi r_lo r_hi carry_lo carry_hi : FBB)
    (ha_lo : a_lo.val < 2^16) (ha_hi : a_hi.val < 2^16)
    (hb_lo : b_lo.val < 2^16) (hb_hi : b_hi.val < 2^16)
    (hr_lo : r_lo.val < 2^16) (hr_hi : r_hi.val < 2^16)
    (hc_lo : carry_lo = 0 ∨ carry_lo = 1)
    (hc_hi : carry_hi = 0 ∨ carry_hi = 1)
    (h_lo : a_lo + b_lo = r_lo + carry_lo * (2 ^ 16 : ℕ))
    (h_hi : a_hi + b_hi + carry_lo = r_hi + carry_hi * (2 ^ 16 : ℕ)) :
    (a_lo.val + a_hi.val * 2 ^ 16 + b_lo.val + b_hi.val * 2 ^ 16) % 2 ^ 32 =
    (r_lo.val + r_hi.val * 2 ^ 16) % 2 ^ 32 := by
  have hcarry_lo_val : carry_lo.val ≤ 1 := by
    rcases hc_lo with rfl | rfl <;> norm_num
  have hcarry_hi_val : carry_hi.val ≤ 1 := by
    rcases hc_hi with rfl | rfl <;> norm_num
  have h_lo_lhs_lt : a_lo.val + b_lo.val < BB_prime := by
    have : a_lo.val + b_lo.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_rhs_lt : r_lo.val + carry_lo.val * 2 ^ 16 < BB_prime := by
    have : r_lo.val + carry_lo.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + 1 * 2 ^ 16 := by omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_lhs_lt : a_hi.val + b_hi.val + carry_lo.val < BB_prime := by
    have : a_hi.val + b_hi.val + carry_lo.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) + 1 := by omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_rhs_lt : r_hi.val + carry_hi.val * 2 ^ 16 < BB_prime := by
    have : r_hi.val + carry_hi.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + 1 * 2 ^ 16 := by omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_nat : a_lo.val + b_lo.val = r_lo.val + carry_lo.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_lo
    rw [babybear_add_no_wrap _ _ h_lo_lhs_lt] at h
    have hcarry := carry_mul_65536_val carry_lo hc_lo
    have hsum :
        (r_lo + carry_lo * (2 ^ 16 : ℕ)).val =
          r_lo.val + (carry_lo * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_lo_rhs_lt)]
    rw [hsum, hcarry] at h
    exact h
  have h_hi_nat : a_hi.val + b_hi.val + carry_lo.val = r_hi.val + carry_hi.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_hi
    have hsum_l : (a_hi + b_hi + carry_lo).val = a_hi.val + b_hi.val + carry_lo.val := by
      have h1 : (a_hi + b_hi).val = a_hi.val + b_hi.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : a_hi.val + b_hi.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have hmid_lt : (a_hi + b_hi).val + carry_lo.val < BB_prime := by
        rw [h1]
        exact h_hi_lhs_lt
      rw [babybear_add_no_wrap _ _ hmid_lt]
      rw [h1]
    rw [hsum_l] at h
    have hcarry := carry_mul_65536_val carry_hi hc_hi
    have hsum_r :
        (r_hi + carry_hi * (2 ^ 16 : ℕ)).val =
          r_hi.val + (carry_hi * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_hi_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  omega

/-- Three-input limbed carry addition with 2-bit carries.
    This is the shape used by the message-schedule recurrence, where each
    carry is encoded by two boolean cells and therefore ranges over `0..3`. -/
theorem limbed_addition_three_inputs
    (a_lo a_hi b_lo b_hi c_lo c_hi r_lo r_hi carry_lo carry_hi : FBB)
    (ha_lo : a_lo.val < 2^16) (ha_hi : a_hi.val < 2^16)
    (hb_lo : b_lo.val < 2^16) (hb_hi : b_hi.val < 2^16)
    (hc_lo : c_lo.val < 2^16) (hc_hi : c_hi.val < 2^16)
    (hr_lo : r_lo.val < 2^16) (hr_hi : r_hi.val < 2^16)
    (hcarry_lo : carry_lo.val < 4)
    (hcarry_hi : carry_hi.val < 4)
    (h_lo : a_lo + b_lo + c_lo = r_lo + carry_lo * (2 ^ 16 : ℕ))
    (h_hi : a_hi + b_hi + c_hi + carry_lo = r_hi + carry_hi * (2 ^ 16 : ℕ)) :
    ((a_lo.val + a_hi.val * 2^16) + (b_lo.val + b_hi.val * 2^16) +
     (c_lo.val + c_hi.val * 2^16)) % 2^32 =
    (r_lo.val + r_hi.val * 2^16) % 2^32 := by
  have h_lo_lhs_lt : a_lo.val + b_lo.val + c_lo.val < BB_prime := by
    have : a_lo.val + b_lo.val + c_lo.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) + (2 ^ 16 - 1) := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_rhs_lt : r_lo.val + carry_lo.val * 2 ^ 16 < BB_prime := by
    have : r_lo.val + carry_lo.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + 3 * 2 ^ 16 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_lhs_lt : a_hi.val + b_hi.val + c_hi.val + carry_lo.val < BB_prime := by
    have : a_hi.val + b_hi.val + c_hi.val + carry_lo.val ≤
        (2 ^ 16 - 1) + (2 ^ 16 - 1) + (2 ^ 16 - 1) + 3 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_rhs_lt : r_hi.val + carry_hi.val * 2 ^ 16 < BB_prime := by
    have : r_hi.val + carry_hi.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + 3 * 2 ^ 16 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_nat : a_lo.val + b_lo.val + c_lo.val = r_lo.val + carry_lo.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_lo
    have hsum_l : (a_lo + b_lo + c_lo).val = a_lo.val + b_lo.val + c_lo.val := by
      have h1 : (a_lo + b_lo).val = a_lo.val + b_lo.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : a_lo.val + b_lo.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have hmid_lt : (a_lo + b_lo).val + c_lo.val < BB_prime := by
        rw [h1]
        exact h_lo_lhs_lt
      rw [babybear_add_no_wrap _ _ hmid_lt]
      rw [h1]
    rw [hsum_l] at h
    have hcarry := small_carry_mul_65536_val carry_lo hcarry_lo
    have hsum_r :
        (r_lo + carry_lo * (2 ^ 16 : ℕ)).val =
          r_lo.val + (carry_lo * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_lo_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  have h_hi_nat : a_hi.val + b_hi.val + c_hi.val + carry_lo.val = r_hi.val + carry_hi.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_hi
    have hsum_l : (a_hi + b_hi + c_hi + carry_lo).val =
        a_hi.val + b_hi.val + c_hi.val + carry_lo.val := by
      have h1 : (a_hi + b_hi).val = a_hi.val + b_hi.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : a_hi.val + b_hi.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have h2 : (a_hi + b_hi + c_hi).val = a_hi.val + b_hi.val + c_hi.val := by
        have hmid_lt : (a_hi + b_hi).val + c_hi.val < BB_prime := by
          rw [h1]
          have : a_hi.val + b_hi.val + c_hi.val ≤
              (2 ^ 16 - 1) + (2 ^ 16 - 1) + (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt]
        rw [h1]
      have hlast_lt : (a_hi + b_hi + c_hi).val + carry_lo.val < BB_prime := by
        rw [h2]
        exact h_hi_lhs_lt
      rw [babybear_add_no_wrap _ _ hlast_lt]
      rw [h2]
    rw [hsum_l] at h
    have hcarry := small_carry_mul_65536_val carry_hi hcarry_hi
    have hsum_r :
        (r_hi + carry_hi * (2 ^ 16 : ℕ)).val =
          r_hi.val + (carry_hi * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_hi_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  omega

/-- Seven-input limbed carry addition (used for the `a` update).
    Requires all input limb `.val < 2^16` and byte-range carries. -/
theorem limbed_addition_seven
    (in0_lo in0_hi in1_lo in1_hi in2_lo in2_hi in3_lo in3_hi
     in4_lo in4_hi in5_lo in5_hi in6_lo in6_hi
     r_lo r_hi carry_lo carry_hi : FBB)
    (hbounds : ∀ x ∈ [in0_lo, in0_hi, in1_lo, in1_hi, in2_lo, in2_hi, in3_lo, in3_hi,
                       in4_lo, in4_hi, in5_lo, in5_hi, in6_lo, in6_hi], x.val < 2^16)
    (hr_lo : r_lo.val < 2^16) (hr_hi : r_hi.val < 2^16)
    (hcarry_lo : carry_lo.val < 2^8)
    (hcarry_hi : carry_hi.val < 2^8)
    (h_lo : in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo + in6_lo =
            r_lo + carry_lo * (2 ^ 16 : ℕ))
    (h_hi : in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + in6_hi + carry_lo =
            r_hi + carry_hi * (2 ^ 16 : ℕ)) :
    ((in0_lo.val + in0_hi.val * 2^16) + (in1_lo.val + in1_hi.val * 2^16) +
     (in2_lo.val + in2_hi.val * 2^16) + (in3_lo.val + in3_hi.val * 2^16) +
     (in4_lo.val + in4_hi.val * 2^16) + (in5_lo.val + in5_hi.val * 2^16) +
     (in6_lo.val + in6_hi.val * 2^16)) % 2^32 =
    (r_lo.val + r_hi.val * 2^16) % 2^32 := by
  have hin0_lo : in0_lo.val < 2 ^ 16 := hbounds in0_lo (by simp)
  have hin0_hi : in0_hi.val < 2 ^ 16 := hbounds in0_hi (by simp)
  have hin1_lo : in1_lo.val < 2 ^ 16 := hbounds in1_lo (by simp)
  have hin1_hi : in1_hi.val < 2 ^ 16 := hbounds in1_hi (by simp)
  have hin2_lo : in2_lo.val < 2 ^ 16 := hbounds in2_lo (by simp)
  have hin2_hi : in2_hi.val < 2 ^ 16 := hbounds in2_hi (by simp)
  have hin3_lo : in3_lo.val < 2 ^ 16 := hbounds in3_lo (by simp)
  have hin3_hi : in3_hi.val < 2 ^ 16 := hbounds in3_hi (by simp)
  have hin4_lo : in4_lo.val < 2 ^ 16 := hbounds in4_lo (by simp)
  have hin4_hi : in4_hi.val < 2 ^ 16 := hbounds in4_hi (by simp)
  have hin5_lo : in5_lo.val < 2 ^ 16 := hbounds in5_lo (by simp)
  have hin5_hi : in5_hi.val < 2 ^ 16 := hbounds in5_hi (by simp)
  have hin6_lo : in6_lo.val < 2 ^ 16 := hbounds in6_lo (by simp)
  have hin6_hi : in6_hi.val < 2 ^ 16 := hbounds in6_hi (by simp)
  have h_lo_lhs_lt :
      in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val + in6_lo.val <
        BB_prime := by
    have :
        in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val + in6_lo.val ≤
          7 * (2 ^ 16 - 1) := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_rhs_lt : r_lo.val + carry_lo.val * 2 ^ 16 < BB_prime := by
    have : r_lo.val + carry_lo.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + (2 ^ 8 - 1) * 2 ^ 16 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_lhs_lt :
      in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + in6_hi.val +
          carry_lo.val <
        BB_prime := by
    have :
        in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + in6_hi.val +
            carry_lo.val ≤
          7 * (2 ^ 16 - 1) + (2 ^ 8 - 1) := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_rhs_lt : r_hi.val + carry_hi.val * 2 ^ 16 < BB_prime := by
    have : r_hi.val + carry_hi.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + (2 ^ 8 - 1) * 2 ^ 16 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_nat :
      in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val + in6_lo.val =
        r_lo.val + carry_lo.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_lo
    have hsum_l :
        (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo + in6_lo).val =
          in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val + in6_lo.val := by
      have h1 : (in0_lo + in1_lo).val = in0_lo.val + in1_lo.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : in0_lo.val + in1_lo.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have h2 :
          (in0_lo + in1_lo + in2_lo).val = in0_lo.val + in1_lo.val + in2_lo.val := by
        have hmid_lt : (in0_lo + in1_lo).val + in2_lo.val < BB_prime := by
          rw [h1]
          have : in0_lo.val + in1_lo.val + in2_lo.val ≤ 3 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h1]
      have h3 :
          (in0_lo + in1_lo + in2_lo + in3_lo).val =
            in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val := by
        have hmid_lt : (in0_lo + in1_lo + in2_lo).val + in3_lo.val < BB_prime := by
          rw [h2]
          have : in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val ≤ 4 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h2]
      have h4 :
          (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo).val =
            in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val := by
        have hmid_lt : (in0_lo + in1_lo + in2_lo + in3_lo).val + in4_lo.val < BB_prime := by
          rw [h3]
          have :
              in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val ≤
                5 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h3]
      have h5 :
          (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo).val =
            in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val := by
        have hmid_lt : (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo).val + in5_lo.val < BB_prime := by
          rw [h4]
          have :
              in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val ≤
                6 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h4]
      have hlast_lt :
          (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo).val + in6_lo.val < BB_prime := by
        rw [h5]
        exact h_lo_lhs_lt
      rw [babybear_add_no_wrap _ _ hlast_lt, h5]
    rw [hsum_l] at h
    have hcarry := byte_carry_mul_65536_val carry_lo hcarry_lo
    have hsum_r :
        (r_lo + carry_lo * (2 ^ 16 : ℕ)).val =
          r_lo.val + (carry_lo * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_lo_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  have h_hi_nat :
      in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + in6_hi.val +
          carry_lo.val =
        r_hi.val + carry_hi.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_hi
    have hsum_l :
        (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + in6_hi + carry_lo).val =
          in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + in6_hi.val +
            carry_lo.val := by
      have h1 : (in0_hi + in1_hi).val = in0_hi.val + in1_hi.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : in0_hi.val + in1_hi.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have h2 :
          (in0_hi + in1_hi + in2_hi).val = in0_hi.val + in1_hi.val + in2_hi.val := by
        have hmid_lt : (in0_hi + in1_hi).val + in2_hi.val < BB_prime := by
          rw [h1]
          have : in0_hi.val + in1_hi.val + in2_hi.val ≤ 3 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h1]
      have h3 :
          (in0_hi + in1_hi + in2_hi + in3_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val := by
        have hmid_lt : (in0_hi + in1_hi + in2_hi).val + in3_hi.val < BB_prime := by
          rw [h2]
          have : in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val ≤ 4 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h2]
      have h4 :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val := by
        have hmid_lt : (in0_hi + in1_hi + in2_hi + in3_hi).val + in4_hi.val < BB_prime := by
          rw [h3]
          have :
              in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val ≤
                5 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h3]
      have h5 :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val := by
        have hmid_lt : (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi).val + in5_hi.val < BB_prime := by
          rw [h4]
          have :
              in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val ≤
                6 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h4]
      have h6 :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + in6_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + in6_hi.val := by
        have hmid_lt :
            (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi).val + in6_hi.val < BB_prime := by
          rw [h5]
          have :
              in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + in6_hi.val ≤
                7 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h5]
      have hlast_lt :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + in6_hi).val + carry_lo.val <
            BB_prime := by
        rw [h6]
        exact h_hi_lhs_lt
      rw [babybear_add_no_wrap _ _ hlast_lt, h6]
    rw [hsum_l] at h
    have hcarry := byte_carry_mul_65536_val carry_hi hcarry_hi
    have hsum_r :
        (r_hi + carry_hi * (2 ^ 16 : ℕ)).val =
          r_hi.val + (carry_hi * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_hi_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  omega

/-- Six-input limbed carry addition (used for the `e` update).
    Requires all input limb `.val < 2^16` and byte-range carries. -/
theorem limbed_addition_six
    (in0_lo in0_hi in1_lo in1_hi in2_lo in2_hi in3_lo in3_hi
     in4_lo in4_hi in5_lo in5_hi
     r_lo r_hi carry_lo carry_hi : FBB)
    (hbounds : ∀ x ∈ [in0_lo, in0_hi, in1_lo, in1_hi, in2_lo, in2_hi, in3_lo, in3_hi,
                       in4_lo, in4_hi, in5_lo, in5_hi], x.val < 2^16)
    (hr_lo : r_lo.val < 2^16) (hr_hi : r_hi.val < 2^16)
    (hcarry_lo : carry_lo.val < 2^8)
    (hcarry_hi : carry_hi.val < 2^8)
    (h_lo : in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo =
            r_lo + carry_lo * (2 ^ 16 : ℕ))
    (h_hi : in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + carry_lo =
            r_hi + carry_hi * (2 ^ 16 : ℕ)) :
    ((in0_lo.val + in0_hi.val * 2^16) + (in1_lo.val + in1_hi.val * 2^16) +
     (in2_lo.val + in2_hi.val * 2^16) + (in3_lo.val + in3_hi.val * 2^16) +
     (in4_lo.val + in4_hi.val * 2^16) + (in5_lo.val + in5_hi.val * 2^16)) % 2^32 =
    (r_lo.val + r_hi.val * 2^16) % 2^32 := by
  have hin0_lo : in0_lo.val < 2 ^ 16 := hbounds in0_lo (by simp)
  have hin0_hi : in0_hi.val < 2 ^ 16 := hbounds in0_hi (by simp)
  have hin1_lo : in1_lo.val < 2 ^ 16 := hbounds in1_lo (by simp)
  have hin1_hi : in1_hi.val < 2 ^ 16 := hbounds in1_hi (by simp)
  have hin2_lo : in2_lo.val < 2 ^ 16 := hbounds in2_lo (by simp)
  have hin2_hi : in2_hi.val < 2 ^ 16 := hbounds in2_hi (by simp)
  have hin3_lo : in3_lo.val < 2 ^ 16 := hbounds in3_lo (by simp)
  have hin3_hi : in3_hi.val < 2 ^ 16 := hbounds in3_hi (by simp)
  have hin4_lo : in4_lo.val < 2 ^ 16 := hbounds in4_lo (by simp)
  have hin4_hi : in4_hi.val < 2 ^ 16 := hbounds in4_hi (by simp)
  have hin5_lo : in5_lo.val < 2 ^ 16 := hbounds in5_lo (by simp)
  have hin5_hi : in5_hi.val < 2 ^ 16 := hbounds in5_hi (by simp)
  have h_lo_lhs_lt :
      in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val < BB_prime := by
    have :
        in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val ≤
          6 * (2 ^ 16 - 1) := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_rhs_lt : r_lo.val + carry_lo.val * 2 ^ 16 < BB_prime := by
    have : r_lo.val + carry_lo.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + (2 ^ 8 - 1) * 2 ^ 16 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_lhs_lt :
      in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + carry_lo.val <
        BB_prime := by
    have :
        in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + carry_lo.val ≤
          6 * (2 ^ 16 - 1) + (2 ^ 8 - 1) := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_hi_rhs_lt : r_hi.val + carry_hi.val * 2 ^ 16 < BB_prime := by
    have : r_hi.val + carry_hi.val * 2 ^ 16 ≤ (2 ^ 16 - 1) + (2 ^ 8 - 1) * 2 ^ 16 := by
      omega
    exact lt_of_le_of_lt this (by norm_num)
  have h_lo_nat :
      in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val =
        r_lo.val + carry_lo.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_lo
    have hsum_l :
        (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo).val =
          in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val + in5_lo.val := by
      have h1 : (in0_lo + in1_lo).val = in0_lo.val + in1_lo.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : in0_lo.val + in1_lo.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have h2 :
          (in0_lo + in1_lo + in2_lo).val = in0_lo.val + in1_lo.val + in2_lo.val := by
        have hmid_lt : (in0_lo + in1_lo).val + in2_lo.val < BB_prime := by
          rw [h1]
          have : in0_lo.val + in1_lo.val + in2_lo.val ≤ 3 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h1]
      have h3 :
          (in0_lo + in1_lo + in2_lo + in3_lo).val =
            in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val := by
        have hmid_lt : (in0_lo + in1_lo + in2_lo).val + in3_lo.val < BB_prime := by
          rw [h2]
          have : in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val ≤ 4 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h2]
      have h4 :
          (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo).val =
            in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val := by
        have hmid_lt : (in0_lo + in1_lo + in2_lo + in3_lo).val + in4_lo.val < BB_prime := by
          rw [h3]
          have :
              in0_lo.val + in1_lo.val + in2_lo.val + in3_lo.val + in4_lo.val ≤
                5 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h3]
      have hlast_lt :
          (in0_lo + in1_lo + in2_lo + in3_lo + in4_lo).val + in5_lo.val < BB_prime := by
        rw [h4]
        exact h_lo_lhs_lt
      rw [babybear_add_no_wrap _ _ hlast_lt, h4]
    rw [hsum_l] at h
    have hcarry := byte_carry_mul_65536_val carry_lo hcarry_lo
    have hsum_r :
        (r_lo + carry_lo * (2 ^ 16 : ℕ)).val =
          r_lo.val + (carry_lo * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_lo_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  have h_hi_nat :
      in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + carry_lo.val =
        r_hi.val + carry_hi.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_hi
    have hsum_l :
        (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + carry_lo).val =
          in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val + carry_lo.val := by
      have h1 : (in0_hi + in1_hi).val = in0_hi.val + in1_hi.val := by
        rw [babybear_add_no_wrap _ _ (by
          have : in0_hi.val + in1_hi.val ≤ (2 ^ 16 - 1) + (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num))]
      have h2 :
          (in0_hi + in1_hi + in2_hi).val = in0_hi.val + in1_hi.val + in2_hi.val := by
        have hmid_lt : (in0_hi + in1_hi).val + in2_hi.val < BB_prime := by
          rw [h1]
          have : in0_hi.val + in1_hi.val + in2_hi.val ≤ 3 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h1]
      have h3 :
          (in0_hi + in1_hi + in2_hi + in3_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val := by
        have hmid_lt : (in0_hi + in1_hi + in2_hi).val + in3_hi.val < BB_prime := by
          rw [h2]
          have : in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val ≤ 4 * (2 ^ 16 - 1) := by omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h2]
      have h4 :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val := by
        have hmid_lt : (in0_hi + in1_hi + in2_hi + in3_hi).val + in4_hi.val < BB_prime := by
          rw [h3]
          have :
              in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val ≤
                5 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h3]
      have h5 :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi).val =
            in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val := by
        have hmid_lt : (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi).val + in5_hi.val < BB_prime := by
          rw [h4]
          have :
              in0_hi.val + in1_hi.val + in2_hi.val + in3_hi.val + in4_hi.val + in5_hi.val ≤
                6 * (2 ^ 16 - 1) := by
            omega
          exact lt_of_le_of_lt this (by norm_num)
        rw [babybear_add_no_wrap _ _ hmid_lt, h4]
      have hlast_lt :
          (in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi).val + carry_lo.val < BB_prime := by
        rw [h5]
        exact h_hi_lhs_lt
      rw [babybear_add_no_wrap _ _ hlast_lt, h5]
    rw [hsum_l] at h
    have hcarry := byte_carry_mul_65536_val carry_hi hcarry_hi
    have hsum_r :
        (r_hi + carry_hi * (2 ^ 16 : ℕ)).val =
          r_hi.val + (carry_hi * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; exact h_hi_rhs_lt)]
    rw [hsum_r, hcarry] at h
    exact h
  omega

theorem UInt32_eq_of_toNat_eq {x y : UInt32} (h : x.toNat = y.toNat) : x = y :=
  (UInt32.toNat_inj).mp h

private theorem u32_sum7_toNat (a b c d e f g : ℕ)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hf : f < 2 ^ 32) (hg : g < 2 ^ 32) :
    ((((((a.toUInt32 + b.toUInt32) + c.toUInt32) + d.toUInt32) + e.toUInt32) + f.toUInt32) +
        g.toUInt32).toNat =
      (a + b + c + d + e + f + g) % 2 ^ 32 := by
  simp [UInt32.toNat_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

private theorem u32_sum6_toNat (a b c d e f : ℕ)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32)
    (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hf : f < 2 ^ 32) :
    (((((a.toUInt32 + b.toUInt32) + c.toUInt32) + d.toUInt32) + e.toUInt32) +
        f.toUInt32).toNat =
      (a + b + c + d + e + f) % 2 ^ 32 := by
  simp [UInt32.toNat_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

/-- Seven-input limbed carry addition exported at the `UInt32` level. -/
theorem limbed_addition_seven_uint32
    (in0_lo in0_hi in1_lo in1_hi in2_lo in2_hi in3_lo in3_hi
     in4_lo in4_hi in5_lo in5_hi in6_lo in6_hi
     r_lo r_hi carry_lo carry_hi : FBB)
    (hbounds : ∀ x ∈ [in0_lo, in0_hi, in1_lo, in1_hi, in2_lo, in2_hi, in3_lo, in3_hi,
                       in4_lo, in4_hi, in5_lo, in5_hi, in6_lo, in6_hi], x.val < 2^16)
    (hr_lo : r_lo.val < 2^16) (hr_hi : r_hi.val < 2^16)
    (hcarry_lo : carry_lo.val < 2^8)
    (hcarry_hi : carry_hi.val < 2^8)
    (h_lo : in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo + in6_lo =
            r_lo + carry_lo * (2 ^ 16 : ℕ))
    (h_hi : in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + in6_hi + carry_lo =
            r_hi + carry_hi * (2 ^ 16 : ℕ)) :
    (((((( (in0_lo.val + in0_hi.val * 2 ^ 16).toUInt32 +
            (in1_lo.val + in1_hi.val * 2 ^ 16).toUInt32) +
            (in2_lo.val + in2_hi.val * 2 ^ 16).toUInt32) +
            (in3_lo.val + in3_hi.val * 2 ^ 16).toUInt32) +
            (in4_lo.val + in4_hi.val * 2 ^ 16).toUInt32) +
            (in5_lo.val + in5_hi.val * 2 ^ 16).toUInt32) +
            (in6_lo.val + in6_hi.val * 2 ^ 16).toUInt32) =
      (r_lo.val + r_hi.val * 2 ^ 16).toUInt32 := by
  have hmod := limbed_addition_seven
    in0_lo in0_hi in1_lo in1_hi in2_lo in2_hi in3_lo in3_hi
    in4_lo in4_hi in5_lo in5_hi in6_lo in6_hi
    r_lo r_hi carry_lo carry_hi hbounds hr_lo hr_hi hcarry_lo hcarry_hi h_lo h_hi
  have hin0_lo : in0_lo.val < 2 ^ 16 := hbounds in0_lo (by simp)
  have hin0_hi : in0_hi.val < 2 ^ 16 := hbounds in0_hi (by simp)
  have hin1_lo : in1_lo.val < 2 ^ 16 := hbounds in1_lo (by simp)
  have hin1_hi : in1_hi.val < 2 ^ 16 := hbounds in1_hi (by simp)
  have hin2_lo : in2_lo.val < 2 ^ 16 := hbounds in2_lo (by simp)
  have hin2_hi : in2_hi.val < 2 ^ 16 := hbounds in2_hi (by simp)
  have hin3_lo : in3_lo.val < 2 ^ 16 := hbounds in3_lo (by simp)
  have hin3_hi : in3_hi.val < 2 ^ 16 := hbounds in3_hi (by simp)
  have hin4_lo : in4_lo.val < 2 ^ 16 := hbounds in4_lo (by simp)
  have hin4_hi : in4_hi.val < 2 ^ 16 := hbounds in4_hi (by simp)
  have hin5_lo : in5_lo.val < 2 ^ 16 := hbounds in5_lo (by simp)
  have hin5_hi : in5_hi.val < 2 ^ 16 := hbounds in5_hi (by simp)
  have hin6_lo : in6_lo.val < 2 ^ 16 := hbounds in6_lo (by simp)
  have hin6_hi : in6_hi.val < 2 ^ 16 := hbounds in6_hi (by simp)
  have hin0_lt : in0_lo.val + in0_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin1_lt : in1_lo.val + in1_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin2_lt : in2_lo.val + in2_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin3_lt : in3_lo.val + in3_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin4_lt : in4_lo.val + in4_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin5_lt : in5_lo.val + in5_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin6_lt : in6_lo.val + in6_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hr_lt : r_lo.val + r_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  apply UInt32_eq_of_toNat_eq
  rw [u32_sum7_toNat _ _ _ _ _ _ _ hin0_lt hin1_lt hin2_lt hin3_lt hin4_lt hin5_lt hin6_lt]
  simpa [UInt32.toNat_ofNat, Nat.mod_eq_of_lt hr_lt] using hmod

/-- Six-input limbed carry addition exported at the `UInt32` level. -/
theorem limbed_addition_six_uint32
    (in0_lo in0_hi in1_lo in1_hi in2_lo in2_hi in3_lo in3_hi
     in4_lo in4_hi in5_lo in5_hi
     r_lo r_hi carry_lo carry_hi : FBB)
    (hbounds : ∀ x ∈ [in0_lo, in0_hi, in1_lo, in1_hi, in2_lo, in2_hi, in3_lo, in3_hi,
                       in4_lo, in4_hi, in5_lo, in5_hi], x.val < 2^16)
    (hr_lo : r_lo.val < 2^16) (hr_hi : r_hi.val < 2^16)
    (hcarry_lo : carry_lo.val < 2^8)
    (hcarry_hi : carry_hi.val < 2^8)
    (h_lo : in0_lo + in1_lo + in2_lo + in3_lo + in4_lo + in5_lo =
            r_lo + carry_lo * (2 ^ 16 : ℕ))
    (h_hi : in0_hi + in1_hi + in2_hi + in3_hi + in4_hi + in5_hi + carry_lo =
            r_hi + carry_hi * (2 ^ 16 : ℕ)) :
    ((((((in0_lo.val + in0_hi.val * 2 ^ 16).toUInt32 +
          (in1_lo.val + in1_hi.val * 2 ^ 16).toUInt32) +
          (in2_lo.val + in2_hi.val * 2 ^ 16).toUInt32) +
          (in3_lo.val + in3_hi.val * 2 ^ 16).toUInt32) +
          (in4_lo.val + in4_hi.val * 2 ^ 16).toUInt32) +
          (in5_lo.val + in5_hi.val * 2 ^ 16).toUInt32) =
      (r_lo.val + r_hi.val * 2 ^ 16).toUInt32 := by
  have hmod := limbed_addition_six
    in0_lo in0_hi in1_lo in1_hi in2_lo in2_hi in3_lo in3_hi
    in4_lo in4_hi in5_lo in5_hi
    r_lo r_hi carry_lo carry_hi hbounds hr_lo hr_hi hcarry_lo hcarry_hi h_lo h_hi
  have hin0_lo : in0_lo.val < 2 ^ 16 := hbounds in0_lo (by simp)
  have hin0_hi : in0_hi.val < 2 ^ 16 := hbounds in0_hi (by simp)
  have hin1_lo : in1_lo.val < 2 ^ 16 := hbounds in1_lo (by simp)
  have hin1_hi : in1_hi.val < 2 ^ 16 := hbounds in1_hi (by simp)
  have hin2_lo : in2_lo.val < 2 ^ 16 := hbounds in2_lo (by simp)
  have hin2_hi : in2_hi.val < 2 ^ 16 := hbounds in2_hi (by simp)
  have hin3_lo : in3_lo.val < 2 ^ 16 := hbounds in3_lo (by simp)
  have hin3_hi : in3_hi.val < 2 ^ 16 := hbounds in3_hi (by simp)
  have hin4_lo : in4_lo.val < 2 ^ 16 := hbounds in4_lo (by simp)
  have hin4_hi : in4_hi.val < 2 ^ 16 := hbounds in4_hi (by simp)
  have hin5_lo : in5_lo.val < 2 ^ 16 := hbounds in5_lo (by simp)
  have hin5_hi : in5_hi.val < 2 ^ 16 := hbounds in5_hi (by simp)
  have hin0_lt : in0_lo.val + in0_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin1_lt : in1_lo.val + in1_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin2_lt : in2_lo.val + in2_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin3_lt : in3_lo.val + in3_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin4_lt : in4_lo.val + in4_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hin5_lt : in5_lo.val + in5_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  have hr_lt : r_lo.val + r_hi.val * 2 ^ 16 < 2 ^ 32 := by omega
  apply UInt32_eq_of_toNat_eq
  rw [u32_sum6_toNat _ _ _ _ _ _ hin0_lt hin1_lt hin2_lt hin3_lt hin4_lt hin5_lt]
  simpa [UInt32.toNat_ofNat, Nat.mod_eq_of_lt hr_lt] using hmod

/-! ## 0F: SHA-256 operations: field ↔ UInt32

Each theorem follows from 0B + 0C (bitwise ops are correct on boolean inputs)
+ 0D (composition is correct). -/

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

private def bitsAsBool (bits : BitsWord) : Fin 32 → Bool :=
  fun i => if bits i = 1 then true else false

private theorem bitsAsBool_spec (bits : BitsWord) (hb : isBitsWord bits) (i : Fin 32) :
    (bits i).val = (bitsAsBool bits i).toNat := by
  rcases hb i with h0 | h1
  · simp [bitsAsBool, h0]
  · simp [bitsAsBool, h1]

private theorem bitsWordToUInt32_eq_ofFnLE (bits : BitsWord) (hb : isBitsWord bits) :
    bitsWordToUInt32 bits = UInt32.ofBitVec (BitVec.ofFnLE (bitsAsBool bits)) := by
  apply UInt32.ext
  let total : ℕ := ∑ i : Fin 32, (bits i).val * 2 ^ i.val
  have hlt : total < 2 ^ 32 := by
    change (∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) < 2 ^ 32
    exact composeBits_nat_sum_lt bits hb
  have hleft' : (total.toUInt32).toNat = total % 2 ^ 32 := by
    simpa using (UInt32.toNat_ofNat (n := total))
  have hleft : (bitsWordToUInt32 bits).toNat = total := by
    change (total.toUInt32).toNat = total
    rw [hleft', Nat.mod_eq_of_lt hlt]
  have hsum : total = Nat.ofBits (bitsAsBool bits) := by
    dsimp [total]
    calc
      (∑ i : Fin 32, (bits i).val * 2 ^ i.val : ℕ) =
          ∑ i : Fin 32, (bitsAsBool bits i).toNat * 2 ^ i.val := by
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

private theorem bitvec_ofFnLE_fieldCh (f g h : Fin 32 → Bool) :
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

private theorem bitvec_ofFnLE_fieldMaj (f g h : Fin 32 → Bool) :
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

theorem fieldXor3_isBitsWord (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    isBitsWord (fun i => fieldXor (fieldXor (x i) (y i)) (z i)) := by
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _ (hx i) (hy i))
    (hz i)

private theorem bitvec_ofFnLE_xor3 (f g h : Fin 32 → Bool) :
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
      fun i => bitsAsBool x ⟨(i.val + n) % 32, Nat.mod_lt _ (by omega)⟩ := by
  funext i
  rcases hx ⟨(i.val + n) % 32, Nat.mod_lt _ (by omega)⟩ with h0 | h1
  · simp [bitsAsBool, fieldRotr, h0]
  · simp [bitsAsBool, fieldRotr, h1]

private theorem bitsAsBool_fieldShr (x : BitsWord) (n : Nat) (hx : isBitsWord x) :
    bitsAsBool (fieldShr x n) =
      fun i => if h : i.val + n < 32 then bitsAsBool x ⟨i.val + n, h⟩ else false := by
  funext i
  by_cases h : i.val + n < 32
  · rcases hx ⟨i.val + n, h⟩ with h0 | h1
    · simp [bitsAsBool, fieldShr, h, h0]
    · simp [bitsAsBool, fieldShr, h, h1]
  · simp [bitsAsBool, fieldShr, h]

private theorem bitvec_ofFnLE_fieldRotr (f : Fin 32 → Bool) (n : Nat) (hn : n < 32) :
    BitVec.ofFnLE (fun i => f ⟨(i.val + n) % 32, Nat.mod_lt _ (by omega)⟩) =
      (BitVec.ofFnLE f).rotateRight n := by
  have hn' : n % 32 = n := Nat.mod_eq_of_lt hn
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 32 - n
  · have hlt : n + i < 32 := by omega
    have hidx : (⟨(n + i) % 32, by omega⟩ : Fin 32) = ⟨n + i, hlt⟩ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hlt]
    simp [BitVec.getLsbD_ofFnLE, BitVec.rotateRight, BitVec.rotateRightAux, h, hi, hn',
      Nat.add_comm]
    simpa [hlt] using congrArg f hidx
  · have hge : ¬ n + i < 32 := by omega
    have hlt2 : i - (32 - n) < 32 := by omega
    have hm : (n + i) % 32 = i - (32 - n) := by omega
    have hidx : (⟨(n + i) % 32, by omega⟩ : Fin 32) = ⟨i - (32 - n), hlt2⟩ := by
      apply Fin.ext
      exact hm
    simp [BitVec.getLsbD_ofFnLE, BitVec.rotateRight, BitVec.rotateRightAux, h, hi, hge, hn',
      Nat.add_comm]
    simpa using congrArg f hidx

private theorem bitvec_ofFnLE_fieldShr (f : Fin 32 → Bool) (n : Nat) :
    BitVec.ofFnLE (fun i => if h : i.val + n < 32 then f ⟨i.val + n, h⟩ else false) =
      BitVec.ofFnLE f >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i + n < 32
  · simpa [BitVec.getLsbD_ofFnLE, h, hi, Nat.add_comm] using rfl
  · simpa [BitVec.getLsbD_ofFnLE, h, hi, Nat.add_comm] using rfl

theorem fieldBigSigma0_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldBigSigma0 x) := by
  simpa [fieldBigSigma0] using
    fieldXor3_isBitsWord (fieldRotr x 2) (fieldRotr x 13) (fieldRotr x 22)
      (fieldRotr_preserves_boolean x 2 hx)
      (fieldRotr_preserves_boolean x 13 hx)
      (fieldRotr_preserves_boolean x 22 hx)

theorem fieldBigSigma1_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldBigSigma1 x) := by
  simpa [fieldBigSigma1] using
    fieldXor3_isBitsWord (fieldRotr x 6) (fieldRotr x 11) (fieldRotr x 25)
      (fieldRotr_preserves_boolean x 6 hx)
      (fieldRotr_preserves_boolean x 11 hx)
      (fieldRotr_preserves_boolean x 25 hx)

private theorem fieldSmallSigma0_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldSmallSigma0 x) := by
  simpa [fieldSmallSigma0] using
    fieldXor3_isBitsWord (fieldRotr x 7) (fieldRotr x 18) (fieldShr x 3)
      (fieldRotr_preserves_boolean x 7 hx)
      (fieldRotr_preserves_boolean x 18 hx)
      (fieldShr_preserves_boolean x 3 hx)

private theorem fieldSmallSigma1_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldSmallSigma1 x) := by
  simpa [fieldSmallSigma1] using
    fieldXor3_isBitsWord (fieldRotr x 17) (fieldRotr x 19) (fieldShr x 10)
      (fieldRotr_preserves_boolean x 17 hx)
      (fieldRotr_preserves_boolean x 19 hx)
      (fieldShr_preserves_boolean x 10 hx)

private theorem bitsAsBool_fieldBigSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldBigSigma0 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩))
        (bitsAsBool x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩) := by
  calc
    bitsAsBool (fieldBigSigma0 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 2) i)
          (bitsAsBool (fieldRotr x 13) i)) (bitsAsBool (fieldRotr x 22) i) := by
            simpa [fieldBigSigma0] using
              bitsAsBool_fieldXor3 (fieldRotr x 2) (fieldRotr x 13) (fieldRotr x 22)
                (fieldRotr_preserves_boolean x 2 hx)
                (fieldRotr_preserves_boolean x 13 hx)
                (fieldRotr_preserves_boolean x 22 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 2 hx, bitsAsBool_fieldRotr x 13 hx,
        bitsAsBool_fieldRotr x 22 hx]

private theorem bitsAsBool_fieldBigSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldBigSigma1 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩))
        (bitsAsBool x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩) := by
  calc
    bitsAsBool (fieldBigSigma1 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 6) i)
          (bitsAsBool (fieldRotr x 11) i)) (bitsAsBool (fieldRotr x 25) i) := by
            simpa [fieldBigSigma1] using
              bitsAsBool_fieldXor3 (fieldRotr x 6) (fieldRotr x 11) (fieldRotr x 25)
                (fieldRotr_preserves_boolean x 6 hx)
                (fieldRotr_preserves_boolean x 11 hx)
                (fieldRotr_preserves_boolean x 25 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 6 hx, bitsAsBool_fieldRotr x 11 hx,
        bitsAsBool_fieldRotr x 25 hx]

private theorem bitsAsBool_fieldSmallSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldSmallSigma0 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 7) % 32, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 18) % 32, Nat.mod_lt _ (by omega)⟩))
        (if h : i.val + 3 < 32 then bitsAsBool x ⟨i.val + 3, h⟩ else false) := by
  calc
    bitsAsBool (fieldSmallSigma0 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 7) i)
          (bitsAsBool (fieldRotr x 18) i)) (bitsAsBool (fieldShr x 3) i) := by
            simpa [fieldSmallSigma0] using
              bitsAsBool_fieldXor3 (fieldRotr x 7) (fieldRotr x 18) (fieldShr x 3)
                (fieldRotr_preserves_boolean x 7 hx)
                (fieldRotr_preserves_boolean x 18 hx)
                (fieldShr_preserves_boolean x 3 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 7 hx, bitsAsBool_fieldRotr x 18 hx,
        bitsAsBool_fieldShr x 3 hx]

private theorem bitsAsBool_fieldSmallSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsAsBool (fieldSmallSigma1 x) =
      fun i => Bool.xor
        (Bool.xor
          (bitsAsBool x ⟨(i.val + 17) % 32, Nat.mod_lt _ (by omega)⟩)
          (bitsAsBool x ⟨(i.val + 19) % 32, Nat.mod_lt _ (by omega)⟩))
        (if h : i.val + 10 < 32 then bitsAsBool x ⟨i.val + 10, h⟩ else false) := by
  calc
    bitsAsBool (fieldSmallSigma1 x) =
        fun i => Bool.xor (Bool.xor (bitsAsBool (fieldRotr x 17) i)
          (bitsAsBool (fieldRotr x 19) i)) (bitsAsBool (fieldShr x 10) i) := by
            simpa [fieldSmallSigma1] using
              bitsAsBool_fieldXor3 (fieldRotr x 17) (fieldRotr x 19) (fieldShr x 10)
                (fieldRotr_preserves_boolean x 17 hx)
                (fieldRotr_preserves_boolean x 19 hx)
                (fieldShr_preserves_boolean x 10 hx)
    _ = _ := by
      funext i
      rw [bitsAsBool_fieldRotr x 17 hx, bitsAsBool_fieldRotr x 19 hx,
        bitsAsBool_fieldShr x 10 hx]

/-- Field-level Ch on boolean bit-words = UInt32 Ch, bit by bit. -/
theorem fieldCh_eq_ch (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsWordToUInt32 (fieldCh x y z) = ch (bitsWordToUInt32 x) (bitsWordToUInt32 y) (bitsWordToUInt32 z) := by
  rw [bitsWordToUInt32_eq_ofFnLE (fieldCh x y z) (fieldCh_isBitsWord x y z hx hy hz),
    bitsWordToUInt32_eq_ofFnLE x hx,
    bitsWordToUInt32_eq_ofFnLE y hy,
    bitsWordToUInt32_eq_ofFnLE z hz]
  congr 1
  simpa [bitsAsBool_fieldCh x y z hx hy hz] using
    bitvec_ofFnLE_fieldCh (bitsAsBool x) (bitsAsBool y) (bitsAsBool z)

/-- Field-level Maj on boolean bit-words = UInt32 Maj, bit by bit. -/
theorem fieldMaj_eq_maj (x y z : BitsWord)
    (hx : isBitsWord x) (hy : isBitsWord y) (hz : isBitsWord z) :
    bitsWordToUInt32 (fieldMaj x y z) = maj (bitsWordToUInt32 x) (bitsWordToUInt32 y) (bitsWordToUInt32 z) := by
  rw [bitsWordToUInt32_eq_ofFnLE (fieldMaj x y z) (fieldMaj_isBitsWord x y z hx hy hz),
    bitsWordToUInt32_eq_ofFnLE x hx,
    bitsWordToUInt32_eq_ofFnLE y hy,
    bitsWordToUInt32_eq_ofFnLE z hz]
  congr 1
  simpa [bitsAsBool_fieldMaj x y z hx hy hz] using
    bitvec_ofFnLE_fieldMaj (bitsAsBool x) (bitsAsBool y) (bitsAsBool z)

/-- Field-level Σ₀ on boolean bit-words = UInt32 Σ₀.
    Follows from fieldRotr_preserves_boolean + fieldXor correct + composeBits correct. -/
theorem fieldBigSigma0_eq_bigSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt32 (fieldBigSigma0 x) = bigSigma0 (bitsWordToUInt32 x) := by
  rw [bitsWordToUInt32_eq_ofFnLE (fieldBigSigma0 x) (fieldBigSigma0_isBitsWord x hx),
    bitsWordToUInt32_eq_ofFnLE x hx]
  apply UInt32.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldBigSigma0 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 2) % 32, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 13) % 32, Nat.mod_lt _ (by omega)⟩))
            (bitsAsBool x ⟨(i.val + 22) % 32, Nat.mod_lt _ (by omega)⟩)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 2 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 13 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 22 := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 2 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 13 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 22 (by decide)]
    _ = (bigSigma0 (UInt32.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [bigSigma0, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-- Field-level Σ₁ on boolean bit-words = UInt32 Σ₁. -/
theorem fieldBigSigma1_eq_bigSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt32 (fieldBigSigma1 x) = bigSigma1 (bitsWordToUInt32 x) := by
  rw [bitsWordToUInt32_eq_ofFnLE (fieldBigSigma1 x) (fieldBigSigma1_isBitsWord x hx),
    bitsWordToUInt32_eq_ofFnLE x hx]
  apply UInt32.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldBigSigma1 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 6) % 32, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 11) % 32, Nat.mod_lt _ (by omega)⟩))
            (bitsAsBool x ⟨(i.val + 25) % 32, Nat.mod_lt _ (by omega)⟩)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 6 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 11 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 25 := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 6 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 11 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 25 (by decide)]
    _ = (bigSigma1 (UInt32.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [bigSigma1, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-- Field-level σ₀ on boolean bit-words = UInt32 σ₀. -/
theorem fieldSmallSigma0_eq_smallSigma0 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt32 (fieldSmallSigma0 x) = smallSigma0 (bitsWordToUInt32 x) := by
  rw [bitsWordToUInt32_eq_ofFnLE (fieldSmallSigma0 x) (fieldSmallSigma0_isBitsWord x hx),
    bitsWordToUInt32_eq_ofFnLE x hx]
  apply UInt32.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldSmallSigma0 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 7) % 32, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 18) % 32, Nat.mod_lt _ (by omega)⟩))
            (if h : i.val + 3 < 32 then bitsAsBool x ⟨i.val + 3, h⟩ else false)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 7 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 18 ^^^
          (BitVec.ofFnLE (bitsAsBool x) >>> 3) := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 7 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 18 (by decide)]
            rw [bitvec_ofFnLE_fieldShr (bitsAsBool x) 3]
    _ = (smallSigma0 (UInt32.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [smallSigma0, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

/-- Field-level σ₁ on boolean bit-words = UInt32 σ₁. -/
theorem fieldSmallSigma1_eq_smallSigma1 (x : BitsWord) (hx : isBitsWord x) :
    bitsWordToUInt32 (fieldSmallSigma1 x) = smallSigma1 (bitsWordToUInt32 x) := by
  rw [bitsWordToUInt32_eq_ofFnLE (fieldSmallSigma1 x) (fieldSmallSigma1_isBitsWord x hx),
    bitsWordToUInt32_eq_ofFnLE x hx]
  apply UInt32.eq_of_toBitVec_eq
  rw [bitsAsBool_fieldSmallSigma1 x hx]
  calc
    BitVec.ofFnLE
        (fun i =>
          Bool.xor
            (Bool.xor
              (bitsAsBool x ⟨(i.val + 17) % 32, Nat.mod_lt _ (by omega)⟩)
              (bitsAsBool x ⟨(i.val + 19) % 32, Nat.mod_lt _ (by omega)⟩))
            (if h : i.val + 10 < 32 then bitsAsBool x ⟨i.val + 10, h⟩ else false)) =
        (BitVec.ofFnLE (bitsAsBool x)).rotateRight 17 ^^^
          (BitVec.ofFnLE (bitsAsBool x)).rotateRight 19 ^^^
          (BitVec.ofFnLE (bitsAsBool x) >>> 10) := by
            rw [bitvec_ofFnLE_xor3]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 17 (by decide)]
            rw [bitvec_ofFnLE_fieldRotr (bitsAsBool x) 19 (by decide)]
            rw [bitvec_ofFnLE_fieldShr (bitsAsBool x) 10]
    _ = (smallSigma1 (UInt32.ofBitVec (BitVec.ofFnLE (bitsAsBool x)))).toBitVec := by
      simp [smallSigma1, rotr, BitVec.rotateRight, BitVec.rotateRightAux]

theorem natCast_ne_zero_of_lt_BB_prime {n : ℕ}
    (hn_lt : n < BB_prime)
    (hn_ne : n ≠ 0) :
    (((n : ℕ) : FBB)) ≠ 0 := by
  intro hzero
  have hval := congrArg Fin.val hzero
  simp [Nat.mod_eq_of_lt hn_lt] at hval
  exact hn_ne hval

end Sha2BlockHasherVmAir_sha256.BlockSpec
