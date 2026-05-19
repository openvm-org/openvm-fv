/-
  Theta APrime interface for the KeccakfPermAir single-round correctness
  proof.

  Public theta facade: re-exports the raw xor3-linking interface from
  `ThetaXor3.lean` and adds the semantic theta-state theorem.

  Raw linking layer (re-exported from ThetaXor3.lean):
  • `xor3_recompose16_eq_value`: converts the raw `xor3_recompose16_eq`
    constraint `(sum − out) = 0` into an equality `out = xor3-weighted-sum`.
  • `theta_a_eq_xor3_recompose`: for each limb j ∈ [0, 100), the `a` column
    at index j equals the 16-bit xor3 recomposition of corresponding c_bit,
    c_prime_bit, and a_prime_bit chunks.
  • `theta_xor3_raw`: for each limb j ∈ [0, 100), the raw
    `xor3_recompose16_eq` constraint holds, as a direct projection from
    `RoundLocalConstraints`.

  Semantic layer:
  • `fbbToBool`, `fbbToBool_fieldXor`: bridge from FBB {0,1} to Bool
  • `aPrimeStateBits`, `aPrimeState`: reconstructed a_prime witness state
  • `theta_output_state`: **main export** — the a_prime witness state
    equals `θ (rowInputState air row)`

-/
import VmExtensions.Soundness.KeccakfPermAir.Round.ThetaC
import VmExtensions.Soundness.KeccakfPermAir.Round.ThetaXor3
import VmExtensions.Soundness.KeccakfPermAir.StepLimbs

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open KeccakfPermAir.StepLimbs
open Keccak

/-! ## FBB ↔ Bool bridge

`fbbToBool` converts FBB boolean values `{0, 1}` to Lean `Bool` `{false, true}`.
This bridges the field-level constraint world to the pure-math bit world
used by `StepLimbs.lean`. -/

/-- Convert an FBB boolean value to Bool. `1 ↦ true`, `0 ↦ false`. -/
noncomputable def fbbToBool (x : FBB) : Bool := decide (x = 1)

@[simp] theorem fbbToBool_zero : fbbToBool (0 : FBB) = false := by
  unfold fbbToBool; simp

@[simp] theorem fbbToBool_one : fbbToBool (1 : FBB) = true := by
  unfold fbbToBool; simp

/-- `fbbToBool` maps `fieldXor` to Bool XOR when inputs are boolean.
    Proof: 4-case split + decide. -/
theorem fbbToBool_fieldXor {a b : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    fbbToBool (fieldXor a b) = (fbbToBool a ^^ fbbToBool b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [fbbToBool, fieldXor] <;> decide

/-- `fbbToBool` maps the xor3 polynomial to 3-way Bool XOR when inputs are boolean.
    xor3(a,b,c) = a + b + c - 2ab - 2ac - 2bc + 4abc. -/
theorem fbbToBool_xor3 {a b c : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    fbbToBool (a + b + c - 2 * a * b - 2 * a * c - 2 * b * c + 4 * a * b * c)
    = Bool.xor (Bool.xor (fbbToBool a) (fbbToBool b)) (fbbToBool c) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [fbbToBool] <;> decide

-- xor3 of three boolean field elements is boolean.
private theorem xor3_is_bool {a b c : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    a + b + c - 2 * a * b - 2 * a * c - 2 * b * c + 4 * a * b * c = 0 ∨
    a + b + c - 2 * a * b - 2 * a * c - 2 * b * c + 4 * a * b * c = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp <;> decide

/-! ## aPrimeStateBits and aPrimeState

The flat index layout of `a_prime_bit` columns is:
  `a_prime_bit[320 * y + 64 * x + k]` for `x ∈ [0,5)`, `y ∈ [0,5)`, `k ∈ [0,64)`
matching `StateBits := Fin 5 → Fin 5 → Fin 64 → Bool`. -/

/-- The a_prime witness as a `StateBits` function. -/
noncomputable def aPrimeStateBits
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ) : StateBits :=
  fun x y k => fbbToBool (a_prime_bit air (320 * y.val + 64 * x.val + k.val) row)

/-- The a_prime witness reconstructed as a `State` (25 × UInt64 lanes). -/
noncomputable def aPrimeState
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ) : State :=
  bitsToState (aPrimeStateBits air row)

/-! ## Per-bit theta identity

The core per-bit identity: each `a_prime_bit` value (as Bool) equals
the corresponding theta-output bit.  The proof chains:
1. xor3(c, c', a') forms the input bits (from `theta_a_eq_xor3_recompose`)
2. c = parity of input bits over y (from `c_bit_eq_parity_xor3`)
3. c' = c XOR D (from `c_prime_bit_eq_xor`)
4. a' = input XOR D = theta output (from algebraic cancellation) -/

-- fbbToBool distributes over double fieldXor (3-way boolean XOR).
private theorem fbbToBool_fieldXor2 {a b c : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    fbbToBool (fieldXor (fieldXor a b) c) =
    Bool.xor (Bool.xor (fbbToBool a) (fbbToBool b)) (fbbToBool c) := by
  rw [fbbToBool_fieldXor (fieldXor_bool ha hb) hc, fbbToBool_fieldXor ha hb]

-- Bool XOR cancellation: (p ^^ q ^^ r) ^^ (p ^^ q) = r.
private theorem bool_xor_cancel (p q r : Bool) :
    Bool.xor (Bool.xor (Bool.xor p q) r) (Bool.xor p q) = r := by
  cases p <;> cases q <;> cases r <;> rfl

-- Bool XOR self-cancellation: p ^^ (p ^^ q ^^ r) = q ^^ r.
private theorem bool_xor_self_cancel_left (p q r : Bool) :
    Bool.xor p (Bool.xor (Bool.xor p q) r) = Bool.xor q r := by
  cases p <;> cases q <;> cases r <;> rfl

-- Bool XOR associativity.
private theorem bool_xor_assoc (p q r : Bool) :
    Bool.xor (Bool.xor p q) r = Bool.xor p (Bool.xor q r) := by
  cases p <;> cases q <;> cases r <;> rfl

-- 5-fold Bool XOR: convert left-association to right-association.
private theorem bool_xor5_left_to_right (a b c d e : Bool) :
    Bool.xor (Bool.xor (Bool.xor (Bool.xor a b) c) d) e =
    Bool.xor a (Bool.xor b (Bool.xor c (Bool.xor d e))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

-- fbbToBool distributes over 5-way nested fieldXor (all boolean),
-- yielding a LEFT-associated Bool XOR (matching theta_parity layout).
private theorem fbbToBool_fieldXor5_left {a b c d e : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1) :
    fbbToBool (fieldXor a (fieldXor b (fieldXor c (fieldXor d e)))) =
    Bool.xor (Bool.xor (Bool.xor (Bool.xor (fbbToBool a) (fbbToBool b))
                                  (fbbToBool c)) (fbbToBool d)) (fbbToBool e) := by
  have hde := fieldXor_bool hd he
  have hcde := fieldXor_bool hc hde
  have hbcde := fieldXor_bool hb hcde
  rw [fbbToBool_fieldXor ha hbcde, fbbToBool_fieldXor hb hcde,
      fbbToBool_fieldXor hc hde, fbbToBool_fieldXor hd he,
      ← bool_xor5_left_to_right]

/-! ### Bit extraction from boolean weighted sums -/

def boolNatWtSum (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ n * c n + boolNatWtSum c n

theorem boolNatWtSum_lt (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) (n : ℕ) :
    boolNatWtSum c n < 2 ^ n := by
  induction n with
  | zero => simp [boolNatWtSum]
  | succ n ih =>
    unfold boolNatWtSum
    have h1 := Nat.mul_le_mul_left (2 ^ n) (hc n)
    rw [Nat.mul_one] at h1
    rw [pow_succ]; linarith

theorem testBit_boolNatWtSum (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) (n j : ℕ) (hj : j < n) :
    (boolNatWtSum c n).testBit j = decide (c j ≠ 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold boolNatWtSum
    rw [Nat.testBit_two_pow_mul_add (c n) (boolNatWtSum_lt c hc n) j]
    by_cases hjn : j < n
    · rw [if_pos hjn]; exact ih hjn
    · have hjeq : j = n := by omega
      subst hjeq
      rw [if_neg (lt_irrefl j), Nat.sub_self, Nat.testBit_zero]
      have hcj := hc j
      interval_cases (c j) <;> simp

-- The explicit 16-term weighted sum equals boolNatWtSum c 16.
set_option maxRecDepth 1024 in
set_option maxHeartbeats 400000 in
theorem boolNatWtSum_eq_explicit (c : ℕ → ℕ) :
    c 0 + 2 * c 1 + 4 * c 2 + 8 * c 3 + 16 * c 4 + 32 * c 5 + 64 * c 6 + 128 * c 7 +
    256 * c 8 + 512 * c 9 + 1024 * c 10 + 2048 * c 11 + 4096 * c 12 + 8192 * c 13 +
    16384 * c 14 + 32768 * c 15 = boolNatWtSum c 16 := by
  simp only [boolNatWtSum]; ring

theorem fbbToBool_val_ne_zero (b : FBB) (hb : b = 0 ∨ b = 1) :
    fbbToBool b = decide (b.val ≠ 0) := by
  rcases hb with rfl | rfl <;> simp [fbbToBool] <;> decide

-- UInt16 embedded in UInt64: bits at position ≥ 16 are false.
theorem u16_toU64_getLsbD_ge (v : UInt16) (j : ℕ) (hj : 16 ≤ j) :
    v.toUInt64.toBitVec.getLsbD j = false := by
  simp only [UInt16.toBitVec_toUInt64]
  by_cases hj64 : j < 64
  · simp only [BitVec.getLsbD_setWidth, hj64, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.toBitVec.isLt
      (Nat.pow_le_pow_right (by omega) hj))
  · simp only [BitVec.getLsbD_setWidth, hj64, decide_false, Bool.false_and]

-- For a boolean FBB weighted sum, getLsbD of the fieldToU16 encoding
-- extracts the corresponding fbbToBool value.
set_option maxHeartbeats 1600000 in
theorem fieldToU16_getLsbD_fbbToBool
    (b : Fin 16 → FBB) (hb : ∀ i, b i = 0 ∨ b i = 1) (out : FBB)
    (heq : out = b ⟨0, by omega⟩ + 2 * b ⟨1, by omega⟩ + 4 * b ⟨2, by omega⟩ +
                 8 * b ⟨3, by omega⟩ + 16 * b ⟨4, by omega⟩ + 32 * b ⟨5, by omega⟩ +
                 64 * b ⟨6, by omega⟩ + 128 * b ⟨7, by omega⟩ +
                 256 * b ⟨8, by omega⟩ + 512 * b ⟨9, by omega⟩ +
                 1024 * b ⟨10, by omega⟩ + 2048 * b ⟨11, by omega⟩ +
                 4096 * b ⟨12, by omega⟩ + 8192 * b ⟨13, by omega⟩ +
                 16384 * b ⟨14, by omega⟩ + 32768 * b ⟨15, by omega⟩)
    (j : ℕ) (hj : j < 16) :
    (fieldToU16 out).toUInt64.toBitVec.getLsbD j = fbbToBool (b ⟨j, hj⟩) := by
  rw [recompose16_fieldToU16 out b hb heq]
  simp only [UInt16.toBitVec_toUInt64, BitVec.getLsbD_setWidth,
             show j < 64 from by omega, decide_true, Bool.true_and]
  dsimp only [BitVec.getLsbD, Nat.toUInt16, UInt16.ofNat]
  simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow,
             show j < 16 from hj, decide_true, Bool.true_and]
  let c : ℕ → ℕ := fun i => if h : i < 16 then (b ⟨i, h⟩).val else 0
  have hc_le : ∀ i, c i ≤ 1 := by
    intro i; dsimp only [c]; split
    · next h => rcases hb ⟨i, h⟩ with hv | hv <;> simp [hv]
    · omega
  have hc_val : ∀ (k : ℕ) (hk : k < 16), (b ⟨k, hk⟩).val = c k := by
    intro k hk; simp only [c, dif_pos hk]
  simp only [hc_val]
  rw [boolNatWtSum_eq_explicit c, testBit_boolNatWtSum c hc_le 16 j hj]
  simp only [c, dif_pos hj]
  exact (fbbToBool_val_ne_zero (b ⟨j, hj⟩) (hb ⟨j, hj⟩)).symm

-- Bit extraction from laneOfLimbs: bit k comes from limb k/16 at position k%16.
set_option maxHeartbeats 800000 in
theorem getBit_laneOfLimbs (l0 l1 l2 l3 : FBB) (k : Fin 64) :
    getBit (laneOfLimbs l0 l1 l2 l3) k =
    if k.val < 16 then (fieldToU16 l0).toBitVec.getLsbD k.val
    else if k.val < 32 then (fieldToU16 l1).toBitVec.getLsbD (k.val - 16)
    else if k.val < 48 then (fieldToU16 l2).toBitVec.getLsbD (k.val - 32)
    else (fieldToU16 l3).toBitVec.getLsbD (k.val - 48) := by
  unfold getBit laneOfLimbs limbs4ToU64
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, BitVec.getLsbD_or,
             UInt16.toBitVec_toUInt64, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft',
             show (↑k : ℕ) < 64 from by omega, decide_true, Bool.true_and,
             show (UInt64.toBitVec 16 % (64 : BitVec 64)).toNat = 16 from by decide,
             show (UInt64.toBitVec 32 % (64 : BitVec 64)).toNat = 32 from by decide,
             show (UInt64.toBitVec 48 % (64 : BitVec 64)).toNat = 48 from by decide,
             show k.val - 16 < 64 from by omega, show k.val - 32 < 64 from by omega,
             show k.val - 48 < 64 from by omega]
  by_cases h16 : k.val < 16
  · simp [h16, show k.val < 32 from by omega, show k.val < 48 from by omega]
  · by_cases h32 : k.val < 32
    · simp [h16, h32, show k.val < 48 from by omega,
            BitVec.getLsbD_of_ge _ _ (show 16 ≤ k.val from by omega)]
    · by_cases h48 : k.val < 48
      · simp [h16, h32, h48,
              BitVec.getLsbD_of_ge _ _ (show 16 ≤ k.val from by omega),
              BitVec.getLsbD_of_ge _ _ (show 16 ≤ k.val - 16 from by omega)]
      · simp [h16, h32, h48,
              BitVec.getLsbD_of_ge _ _ (show 16 ≤ k.val from by omega),
              BitVec.getLsbD_of_ge _ _ (show 16 ≤ k.val - 16 from by omega),
              BitVec.getLsbD_of_ge _ _ (show 16 ≤ k.val - 32 from by omega)]

/-! ### Bridge: stateToBits(rowInputState) = fbbToBool of xor3 witnesses -/

-- Bridge: stateToBits(rowInputState)(x,y,k) = fbbToBool(xor3(c, c', a'))
set_option maxHeartbeats 3200000 in
private theorem inputBit_bridge
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row)
    (x : Fin 5) (y : Fin 5) (k : Fin 64) :
    stateToBits (rowInputState air row) x y k =
    Bool.xor (Bool.xor (fbbToBool (c_bit air (64 * x.val + k.val) row))
                        (fbbToBool (c_prime_bit air (64 * x.val + k.val) row)))
             (fbbToBool (a_prime_bit air (320 * y.val + 64 * x.val + k.val) row)) := by
  simp only [stateToBits]
  rw [rowInputState_lane air row ⟨5 * y.val + x.val, by omega⟩, getBit_laneOfLimbs]
  suffices h : ∀ limb, limb < 4 → ∀ m, m < 16 → 16 * limb + m = k.val →
      (fieldToU16 (a air (4 * (5 * y.val + x.val) + limb) row)).toBitVec.getLsbD m =
      Bool.xor (Bool.xor (fbbToBool (c_bit air (64 * x.val + k.val) row))
                          (fbbToBool (c_prime_bit air (64 * x.val + k.val) row)))
               (fbbToBool (a_prime_bit air (320 * y.val + 64 * x.val + k.val) row)) by
    by_cases h16 : k.val < 16
    · simp only [if_pos h16]; exact h 0 (by omega) k.val (by omega) (by omega)
    · simp only [if_neg h16]; by_cases h32 : k.val < 32
      · simp only [if_pos h32]; exact h 1 (by omega) (k.val - 16) (by omega) (by omega)
      · simp only [if_neg h32]; by_cases h48 : k.val < 48
        · simp only [if_pos h48]; exact h 2 (by omega) (k.val - 32) (by omega) (by omega)
        · simp only [if_neg h48]; exact h 3 (by omega) (k.val - 48) (by omega) (by omega)
  intro limb hlimb m hm hkm
  rw [show (fieldToU16 (a air (4 * (5 * y.val + x.val) + limb) row)).toBitVec.getLsbD m =
          (fieldToU16 (a air (4 * (5 * y.val + x.val) + limb) row)).toUInt64.toBitVec.getLsbD m from by
    simp [UInt16.toBitVec_toUInt64, show m < 64 from by omega]]
  have hxor := theta_a_eq_xor3_recompose h_round (4 * (5 * y.val + x.val) + limb) (by omega)
  simp only at hxor
  have hdiv : (4 * (5 * y.val + x.val) + limb) / 4 % 5 = x.val := by omega
  have hmod4 : (4 * (5 * y.val + x.val) + limb) % 4 = limb := by omega
  simp only [hdiv, hmod4] at hxor
  let b : Fin 16 → FBB := fun i =>
    let ci := c_bit air (64 * x.val + 16 * limb + i.val) row
    let cpi := c_prime_bit air (64 * x.val + 16 * limb + i.val) row
    let api := a_prime_bit air (16 * (4 * (5 * y.val + x.val) + limb) + i.val) row
    ci + cpi + api - 2 * ci * cpi - 2 * ci * api - 2 * cpi * api + 4 * ci * cpi * api
  have hb : ∀ i, b i = 0 ∨ b i = 1 := fun i => by
    dsimp only [b]; exact xor3_is_bool
      (c_bit_is_bool h_round _ (by omega))
      (c_prime_bit_is_bool h_round _ (by omega))
      (a_prime_bit_is_bool h_round _ (by omega))
  have heq : a air (4 * (5 * y.val + x.val) + limb) row =
    b ⟨0, by omega⟩ + 2 * b ⟨1, by omega⟩ + 4 * b ⟨2, by omega⟩ + 8 * b ⟨3, by omega⟩ +
    16 * b ⟨4, by omega⟩ + 32 * b ⟨5, by omega⟩ + 64 * b ⟨6, by omega⟩ + 128 * b ⟨7, by omega⟩ +
    256 * b ⟨8, by omega⟩ + 512 * b ⟨9, by omega⟩ + 1024 * b ⟨10, by omega⟩ +
    2048 * b ⟨11, by omega⟩ + 4096 * b ⟨12, by omega⟩ + 8192 * b ⟨13, by omega⟩ +
    16384 * b ⟨14, by omega⟩ + 32768 * b ⟨15, by omega⟩ := by dsimp only [b]; exact hxor
  rw [fieldToU16_getLsbD_fbbToBool b hb _ heq m hm]
  dsimp only [b]
  rw [fbbToBool_xor3
    (c_bit_is_bool h_round _ (by omega))
    (c_prime_bit_is_bool h_round _ (by omega))
    (a_prime_bit_is_bool h_round _ (by omega))]
  have h1 : 64 * x.val + 16 * limb + m = 64 * x.val + k.val := by omega
  have h2 : 16 * (4 * (5 * y.val + x.val) + limb) + m =
            320 * y.val + 64 * x.val + k.val := by omega
  rw [h1, h2]

/-! ### Theta parity = fbbToBool(c_bit) -/

-- Theta parity of the input state = fbbToBool(c_bit)
private theorem theta_parity_eq_c_bit
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row)
    (x : Fin 5) (k : Fin 64) :
    theta_parity (stateToBits (rowInputState air row)) x k =
    fbbToBool (c_bit air (64 * x.val + k.val) row) := by
  simp only [theta_parity]
  rw [inputBit_bridge h_round x 0 k, inputBit_bridge h_round x 1 k,
      inputBit_bridge h_round x 2 k, inputBit_bridge h_round x 3 k,
      inputBit_bridge h_round x 4 k]
  have hi : 64 * x.val + k.val < 320 := by omega
  conv_rhs => rw [c_bit_eq_parity_xor3 h_round _ hi]
  have hcc' := fieldXor_bool (c_bit_is_bool h_round _ hi) (c_prime_bit_is_bool h_round _ hi)
  set i := 64 * x.val + k.val with hi_def
  have hT0 := fieldXor_bool hcc' (a_prime_bit_is_bool h_round i (by omega))
  have hT1 := fieldXor_bool hcc' (a_prime_bit_is_bool h_round (i + 320) (by omega))
  have hT2 := fieldXor_bool hcc' (a_prime_bit_is_bool h_round (i + 640) (by omega))
  have hT3 := fieldXor_bool hcc' (a_prime_bit_is_bool h_round (i + 960) (by omega))
  have hT4 := fieldXor_bool hcc' (a_prime_bit_is_bool h_round (i + 1280) (by omega))
  rw [fbbToBool_fieldXor5_left hT0 hT1 hT2 hT3 hT4]
  have hcb := c_bit_is_bool h_round i hi
  have hcpb := c_prime_bit_is_bool h_round i hi
  rw [fbbToBool_fieldXor2 hcb hcpb (a_prime_bit_is_bool h_round i (by omega)),
      fbbToBool_fieldXor2 hcb hcpb (a_prime_bit_is_bool h_round (i + 320) (by omega)),
      fbbToBool_fieldXor2 hcb hcpb (a_prime_bit_is_bool h_round (i + 640) (by omega)),
      fbbToBool_fieldXor2 hcb hcpb (a_prime_bit_is_bool h_round (i + 960) (by omega)),
      fbbToBool_fieldXor2 hcb hcpb (a_prime_bit_is_bool h_round (i + 1280) (by omega))]
  simp only [hi_def, show (0 : Fin 5).val = 0 from rfl, show (1 : Fin 5).val = 1 from rfl,
             show (2 : Fin 5).val = 2 from rfl, show (3 : Fin 5).val = 3 from rfl,
             show (4 : Fin 5).val = 4 from rfl]
  norm_num
  simp only [Nat.add_assoc, Nat.add_comm]

/-! ### Theta shift = fc ^^ fc' -/

-- Theta shift at (x, k) = fbbToBool(c_bit) ^^ fbbToBool(c_prime_bit)
private theorem theta_shift_eq_xor_c
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row)
    (x : Fin 5) (k : Fin 64) :
    theta_shift (theta_parity (stateToBits (rowInputState air row))) x k =
    Bool.xor (fbbToBool (c_bit air (64 * x.val + k.val) row))
             (fbbToBool (c_prime_bit air (64 * x.val + k.val) row)) := by
  simp only [theta_shift]
  rw [theta_parity_eq_c_bit h_round ⟨(x.val + 4) % 5, by omega⟩ k,
      theta_parity_eq_c_bit h_round ⟨(x.val + 1) % 5, by omega⟩ ⟨(k.val + 63) % 64, by omega⟩]
  have hi : 64 * x.val + k.val < 320 := by omega
  rw [c_prime_bit_eq_xor h_round (64 * x.val + k.val) hi]
  rw [fbbToBool_fieldXor2 (c_bit_is_bool h_round _ hi)
        (c_bit_is_bool h_round _ (by omega))
        (c_bit_is_bool h_round _ (by omega))]
  have hdiv : (64 * x.val + k.val) / 64 = x.val := by omega
  have hmod : (64 * x.val + k.val) % 64 = k.val := by omega
  simp only [hdiv, hmod]
  exact (bool_xor_self_cancel_left _ _ _).symm

set_option maxHeartbeats 800000 in
/-- The per-bit theta identity: `fbbToBool(a_prime_bit[320y+64x+k])` equals
    `theta_bits(stateToBits(rowInputState))[x,y,k]`. -/
theorem aPrime_bit_eq_theta_bit
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row)
    (x : Fin 5) (y : Fin 5) (k : Fin 64) :
    aPrimeStateBits air row x y k =
    theta_bits (stateToBits (rowInputState air row)) x y k := by
  unfold aPrimeStateBits
  simp only [theta_bits, theta_apply]
  rw [inputBit_bridge h_round x y k, theta_shift_eq_xor_c h_round x k]
  exact (bool_xor_cancel _ _ _).symm

/-- **Theta output identity**: the a_prime witness state equals `θ` applied
    to the row's input state.

    This theorem states that the `a_prime_bit` columns represent the
    theta-transformed input. -/
theorem theta_output_state
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) :
    aPrimeState air row = θ (rowInputState air row) := by
  rw [← theta_bits_eq_spec]
  unfold aPrimeState
  congr 1
  funext x y k
  exact aPrime_bit_eq_theta_bit h_round x y k

end KeccakfPermAir.Soundness
