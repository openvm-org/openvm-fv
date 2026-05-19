/-
  Layer C: Round Step State Bridge

  Combined module containing shared packing/carry-bound helpers and the
  word-level `a` and `e` bridge proofs for SHA-512 round steps.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.Core
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.AUpdate
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.EUpdate

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ### Shared packing and carry-bound helpers -/

def packU16x4 (l0 l1 l2 l3 : ℕ) : ℕ :=
  l0 + l1 * 2 ^ 16 + l2 * 2 ^ 32 + l3 * 2 ^ 48

theorem packU16x4_lt_u64 (l0 l1 l2 l3 : ℕ)
    (h0 : l0 < 2 ^ 16) (h1 : l1 < 2 ^ 16) (h2 : l2 < 2 ^ 16) (h3 : l3 < 2 ^ 16) :
    packU16x4 l0 l1 l2 l3 < 2 ^ 64 := by
  dsimp [packU16x4]
  omega

def packBitsWord (bits : BitsWord) : ℕ :=
  packU16x4
    (composeU16Limb bits ⟨0, by decide⟩).val
    (composeU16Limb bits ⟨1, by decide⟩).val
    (composeU16Limb bits ⟨2, by decide⟩).val
    (composeU16Limb bits ⟨3, by decide⟩).val

theorem packBitsWord_lt_u64 (bits : BitsWord) (hb : isBitsWord bits) :
    packBitsWord bits < 2 ^ 64 := by
  exact packU16x4_lt_u64 _ _ _ _
    (composeU16Limb_val_lt bits hb ⟨0, by decide⟩)
    (composeU16Limb_val_lt bits hb ⟨1, by decide⟩)
    (composeU16Limb_val_lt bits hb ⟨2, by decide⟩)
    (composeU16Limb_val_lt bits hb ⟨3, by decide⟩)

theorem packBitsWord_eq_word (bits : BitsWord) (hb : isBitsWord bits) :
    bitsWordToUInt64 bits = (packBitsWord bits).toUInt64 := by
  simpa [packBitsWord, packU16x4] using bitsWordToUInt64_eq_compose16 bits hb

theorem bitsU16Limb_val_lt (bits : BitsWord) (hb : isBitsWord bits) (limb : ℕ)
    (hlimb : limb < 4) :
    (bitsU16Limb bits limb).val < 2 ^ 16 := by
  rw [bitsU16Limb_eq_composeU16Limb bits limb hlimb]
  exact composeU16Limb_val_lt bits hb ⟨limb, hlimb⟩

theorem packBitsWord_addition_seven_uint64
    (in0 in1 in2 in3 in4 in5 r : BitsWord)
    (k0 k1 k2 k3 carry0 carry1 carry2 carry3 : FBB)
    (hin0 : isBitsWord in0) (hin1 : isBitsWord in1) (hin2 : isBitsWord in2)
    (hin3 : isBitsWord in3) (hin4 : isBitsWord in4) (hin5 : isBitsWord in5)
    (hr : isBitsWord r)
    (hk0 : k0.val < 2 ^ 16) (hk1 : k1.val < 2 ^ 16)
    (hk2 : k2.val < 2 ^ 16) (hk3 : k3.val < 2 ^ 16)
    (hcarry0 : carry0.val < 2 ^ 8) (hcarry1 : carry1.val < 2 ^ 8)
    (hcarry2 : carry2.val < 2 ^ 8) (hcarry3 : carry3.val < 2 ^ 8)
    (h0 : bitsU16Limb in0 0 + bitsU16Limb in1 0 + bitsU16Limb in2 0 + k0 +
            bitsU16Limb in3 0 + bitsU16Limb in4 0 + bitsU16Limb in5 0 =
          bitsU16Limb r 0 + carry0 * (2 ^ 16 : ℕ))
    (h1 : bitsU16Limb in0 1 + bitsU16Limb in1 1 + bitsU16Limb in2 1 + k1 +
            bitsU16Limb in3 1 + bitsU16Limb in4 1 + bitsU16Limb in5 1 + carry0 =
          bitsU16Limb r 1 + carry1 * (2 ^ 16 : ℕ))
    (h2 : bitsU16Limb in0 2 + bitsU16Limb in1 2 + bitsU16Limb in2 2 + k2 +
            bitsU16Limb in3 2 + bitsU16Limb in4 2 + bitsU16Limb in5 2 + carry1 =
          bitsU16Limb r 2 + carry2 * (2 ^ 16 : ℕ))
    (h3 : bitsU16Limb in0 3 + bitsU16Limb in1 3 + bitsU16Limb in2 3 + k3 +
            bitsU16Limb in3 3 + bitsU16Limb in4 3 + bitsU16Limb in5 3 + carry2 =
          bitsU16Limb r 3 + carry3 * (2 ^ 16 : ℕ)) :
    ((((((packBitsWord in0).toUInt64 + (packBitsWord in1).toUInt64) +
          (packBitsWord in2).toUInt64) +
          (packU16x4 k0.val k1.val k2.val k3.val).toUInt64) +
          (packBitsWord in3).toUInt64) +
          (packBitsWord in4).toUInt64) +
          (packBitsWord in5).toUInt64 =
      (packBitsWord r).toUInt64 := by
  simpa [packBitsWord, packU16x4] using
    (limbed_addition_seven_uint64
      (bitsU16Limb in0 0) (bitsU16Limb in0 1) (bitsU16Limb in0 2) (bitsU16Limb in0 3)
      (bitsU16Limb in1 0) (bitsU16Limb in1 1) (bitsU16Limb in1 2) (bitsU16Limb in1 3)
      (bitsU16Limb in2 0) (bitsU16Limb in2 1) (bitsU16Limb in2 2) (bitsU16Limb in2 3)
      k0 k1 k2 k3
      (bitsU16Limb in3 0) (bitsU16Limb in3 1) (bitsU16Limb in3 2) (bitsU16Limb in3 3)
      (bitsU16Limb in4 0) (bitsU16Limb in4 1) (bitsU16Limb in4 2) (bitsU16Limb in4 3)
      (bitsU16Limb in5 0) (bitsU16Limb in5 1) (bitsU16Limb in5 2) (bitsU16Limb in5 3)
      (bitsU16Limb r 0) (bitsU16Limb r 1) (bitsU16Limb r 2) (bitsU16Limb r 3)
      carry0 carry1 carry2 carry3
      (by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl
        · exact bitsU16Limb_val_lt _ hin0 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin0 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin0 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin0 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 3 (by decide)
        · exact hk0
        · exact hk1
        · exact hk2
        · exact hk3
        · exact bitsU16Limb_val_lt _ hin3 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin5 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin5 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin5 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin5 3 (by decide))
      (bitsU16Limb_val_lt _ hr 0 (by decide))
      (bitsU16Limb_val_lt _ hr 1 (by decide))
      (bitsU16Limb_val_lt _ hr 2 (by decide))
      (bitsU16Limb_val_lt _ hr 3 (by decide))
      hcarry0 hcarry1 hcarry2 hcarry3
      h0 h1 h2 h3)

theorem packBitsWord_addition_six_uint64
    (in0 in1 in2 in3 in4 r : BitsWord)
    (k0 k1 k2 k3 carry0 carry1 carry2 carry3 : FBB)
    (hin0 : isBitsWord in0) (hin1 : isBitsWord in1) (hin2 : isBitsWord in2)
    (hin3 : isBitsWord in3) (hin4 : isBitsWord in4) (hr : isBitsWord r)
    (hk0 : k0.val < 2 ^ 16) (hk1 : k1.val < 2 ^ 16)
    (hk2 : k2.val < 2 ^ 16) (hk3 : k3.val < 2 ^ 16)
    (hcarry0 : carry0.val < 2 ^ 8) (hcarry1 : carry1.val < 2 ^ 8)
    (hcarry2 : carry2.val < 2 ^ 8) (hcarry3 : carry3.val < 2 ^ 8)
    (h0 : bitsU16Limb in0 0 + bitsU16Limb in1 0 + bitsU16Limb in2 0 + bitsU16Limb in3 0 +
            k0 + bitsU16Limb in4 0 =
          bitsU16Limb r 0 + carry0 * (2 ^ 16 : ℕ))
    (h1 : bitsU16Limb in0 1 + bitsU16Limb in1 1 + bitsU16Limb in2 1 + bitsU16Limb in3 1 +
            k1 + bitsU16Limb in4 1 + carry0 =
          bitsU16Limb r 1 + carry1 * (2 ^ 16 : ℕ))
    (h2 : bitsU16Limb in0 2 + bitsU16Limb in1 2 + bitsU16Limb in2 2 + bitsU16Limb in3 2 +
            k2 + bitsU16Limb in4 2 + carry1 =
          bitsU16Limb r 2 + carry2 * (2 ^ 16 : ℕ))
    (h3 : bitsU16Limb in0 3 + bitsU16Limb in1 3 + bitsU16Limb in2 3 + bitsU16Limb in3 3 +
            k3 + bitsU16Limb in4 3 + carry2 =
          bitsU16Limb r 3 + carry3 * (2 ^ 16 : ℕ)) :
    (((((packBitsWord in0).toUInt64 + (packBitsWord in1).toUInt64) +
         (packBitsWord in2).toUInt64) +
         (packBitsWord in3).toUInt64) +
         (packU16x4 k0.val k1.val k2.val k3.val).toUInt64) +
         (packBitsWord in4).toUInt64 =
      (packBitsWord r).toUInt64 := by
  simpa [packBitsWord, packU16x4] using
    (limbed_addition_six_uint64
      (bitsU16Limb in0 0) (bitsU16Limb in0 1) (bitsU16Limb in0 2) (bitsU16Limb in0 3)
      (bitsU16Limb in1 0) (bitsU16Limb in1 1) (bitsU16Limb in1 2) (bitsU16Limb in1 3)
      (bitsU16Limb in2 0) (bitsU16Limb in2 1) (bitsU16Limb in2 2) (bitsU16Limb in2 3)
      (bitsU16Limb in3 0) (bitsU16Limb in3 1) (bitsU16Limb in3 2) (bitsU16Limb in3 3)
      k0 k1 k2 k3
      (bitsU16Limb in4 0) (bitsU16Limb in4 1) (bitsU16Limb in4 2) (bitsU16Limb in4 3)
      (bitsU16Limb r 0) (bitsU16Limb r 1) (bitsU16Limb r 2) (bitsU16Limb r 3)
      carry0 carry1 carry2 carry3
      (by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact bitsU16Limb_val_lt _ hin0 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin0 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin0 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin0 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin1 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin2 3 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin3 3 (by decide)
        · exact hk0
        · exact hk1
        · exact hk2
        · exact hk3
        · exact bitsU16Limb_val_lt _ hin4 0 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 1 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 2 (by decide)
        · exact bitsU16Limb_val_lt _ hin4 3 (by decide))
      (bitsU16Limb_val_lt _ hr 0 (by decide))
      (bitsU16Limb_val_lt _ hr 1 (by decide))
      (bitsU16Limb_val_lt _ hr 2 (by decide))
      (bitsU16Limb_val_lt _ hr 3 (by decide))
      hcarry0 hcarry1 hcarry2 hcarry3
      h0 h1 h2 h3)

theorem roundStepCarryInA_zero_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInA air row slot 0 + x = y) :
    x = y := by
  simpa [roundStepCarryInA] using h

theorem roundStepCarryInA_one_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInA air row slot 1 + x = y) :
    x + next_carry_a air slot 0 row = y := by
  simpa [roundStepCarryInA, add_comm] using h

theorem roundStepCarryInA_two_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInA air row slot 2 + x = y) :
    x + next_carry_a air slot 1 row = y := by
  simpa [roundStepCarryInA, add_comm] using h

theorem roundStepCarryInA_three_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInA air row slot 3 + x = y) :
    x + next_carry_a air slot 2 row = y := by
  simpa [roundStepCarryInA, add_comm] using h

theorem roundStepCarryInE_zero_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInE air row slot 0 + x = y) :
    x = y := by
  simpa [roundStepCarryInE] using h

theorem roundStepCarryInE_one_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInE air row slot 1 + x = y) :
    x + next_carry_e air slot 0 row = y := by
  simpa [roundStepCarryInE, add_comm] using h

theorem roundStepCarryInE_two_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInE air row slot 2 + x = y) :
    x + next_carry_e air slot 1 row = y := by
  simpa [roundStepCarryInE, add_comm] using h

theorem roundStepCarryInE_three_eq
    (air : C FBB ExtF) (row slot : ℕ) {x y : FBB}
    (h : roundStepCarryInE air row slot 3 + x = y) :
    x + next_carry_e air slot 2 row = y := by
  simpa [roundStepCarryInE, add_comm] using h

theorem next_carry_a_val_lt
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row)) :
    (next_carry_a air slot limb row).val < 2 ^ 8 := by
  simpa [next_carry_a_eq_nextRow air hrot slot limb row hrow] using
    (hcarry_next slot limb hslot hlimb).1

theorem next_carry_e_val_lt
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row)) :
    (next_carry_e air slot limb row).val < 2 ^ 8 := by
  simpa [next_carry_e_eq_nextRow air hrot slot limb row hrow] using
    (hcarry_next slot limb hslot hlimb).2

theorem roundStepCarryInA_val_lt
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row)) :
    (roundStepCarryInA air row slot limb).val < 2 ^ 8 := by
  by_cases hzero : limb = 0
  · simp [roundStepCarryInA, hzero]
  · have hprev : limb - 1 < 4 := by omega
    simpa [roundStepCarryInA, hzero] using
      next_carry_a_val_lt air row slot (limb - 1) hslot hprev hrow hrot hcarry_next

theorem roundStepCarryInE_val_lt
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row)) :
    (roundStepCarryInE air row slot limb).val < 2 ^ 8 := by
  by_cases hzero : limb = 0
  · simp [roundStepCarryInE, hzero]
  · have hprev : limb - 1 < 4 := by omega
    simpa [roundStepCarryInE, hzero] using
      next_carry_e_val_lt air row slot (limb - 1) hslot hprev hrow hrot hcarry_next

/-! ### Round Step A bridge -/

def roundStepA_hNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (concatEBitsWord air row slot)

def roundStepA_sigma1Nat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))

def roundStepA_chNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord
    (fieldCh (concatEBitsWord air row (slot + 3))
      (concatEBitsWord air row (slot + 2))
      (concatEBitsWord air row (slot + 1)))

def roundStepA_kNat (row_idx slot : ℕ) : ℕ :=
  packU16x4
    (k_limb_at row_idx slot 0).val
    (k_limb_at row_idx slot 1).val
    (k_limb_at row_idx slot 2).val
    (k_limb_at row_idx slot 3).val

def roundStepA_schedNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (scheduleBitsWord air (nextRow air row) slot)

def roundStepA_sigma0Nat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (fieldBigSigma0 (concatABitsWord air row (slot + 3)))

def roundStepA_majNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord
    (fieldMaj (concatABitsWord air row (slot + 3))
      (concatABitsWord air row (slot + 2))
      (concatABitsWord air row (slot + 1)))

def roundStepA_resultNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (aBitsWord air (nextRow air row) slot)

def roundStepA_sumWord (air : C FBB ExtF) (row slot row_idx : ℕ) : Word :=
  ((((((roundStepA_hNat air row slot).toUInt64 +
        (roundStepA_sigma1Nat air row slot).toUInt64) +
        (roundStepA_chNat air row slot).toUInt64) +
        (roundStepA_kNat row_idx slot).toUInt64) +
        (roundStepA_schedNat air row slot).toUInt64) +
        (roundStepA_sigma0Nat air row slot).toUInt64) +
        (roundStepA_majNat air row slot).toUInt64

theorem round_step_a_rhs_eq_sum (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hidx_bound : row_idx < 20)
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    roundStepAExpected air row slot row_idx = roundStepA_sumWord air row slot row_idx := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have ha_bits : isBitsWord (concatABitsWord air row (slot + 3)) :=
    concatABits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hb_bits : isBitsWord (concatABitsWord air row (slot + 2)) :=
    concatABits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hc_bits : isBitsWord (concatABitsWord air row (slot + 1)) :=
    concatABits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hsig0_bits :
      isBitsWord (fieldBigSigma0 (concatABitsWord air row (slot + 3))) :=
    fieldBigSigma0_isBitsWord _ ha_bits
  have hmaj_bits :
      isBitsWord (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1))) :=
    fieldMaj_isBitsWord _ _ _ ha_bits hb_bits hc_bits
  have hh_word :
      concatEWord air row slot = (roundStepA_hNat air row slot).toUInt64 := by
    rw [concatEWord_eq_bitsWordToUInt64 air row slot hslot0 hbb hbb_next]
    simpa [roundStepA_hNat] using packBitsWord_eq_word (concatEBitsWord air row slot) hh_bits
  have hsig1_word :
      bigSigma1 (concatEWord air row (slot + 3)) = (roundStepA_sigma1Nat air row slot).toUInt64 := by
    calc
      bigSigma1 (concatEWord air row (slot + 3))
          = bigSigma1 (bitsWordToUInt64 (concatEBitsWord air row (slot + 3))) := by
              rw [concatEWord_eq_bitsWordToUInt64 air row (slot + 3) hslot3 hbb hbb_next]
      _ = bitsWordToUInt64 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) := by
            rw [(fieldBigSigma1_eq_bigSigma1 (concatEBitsWord air row (slot + 3)) he_bits).symm]
      _ = (roundStepA_sigma1Nat air row slot).toUInt64 := by
            simpa [roundStepA_sigma1Nat] using
              packBitsWord_eq_word (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) hsig1_bits
  have hch_word :
      ch (concatEWord air row (slot + 3))
        (concatEWord air row (slot + 2))
        (concatEWord air row (slot + 1)) = (roundStepA_chNat air row slot).toUInt64 := by
    calc
      ch (concatEWord air row (slot + 3))
            (concatEWord air row (slot + 2))
            (concatEWord air row (slot + 1))
          = ch (bitsWordToUInt64 (concatEBitsWord air row (slot + 3)))
              (bitsWordToUInt64 (concatEBitsWord air row (slot + 2)))
              (bitsWordToUInt64 (concatEBitsWord air row (slot + 1))) := by
                rw [concatEWord_eq_bitsWordToUInt64 air row (slot + 3) hslot3 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt64 air row (slot + 2) hslot2 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt64 air row (slot + 1) hslot1 hbb hbb_next]
      _ = bitsWordToUInt64
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) := by
            symm
            exact fieldCh_eq_ch _ _ _ he_bits hf_bits hg_bits
      _ = (roundStepA_chNat air row slot).toUInt64 := by
            simpa [roundStepA_chNat] using
              packBitsWord_eq_word
                (fieldCh (concatEBitsWord air row (slot + 3))
                  (concatEBitsWord air row (slot + 2))
                  (concatEBitsWord air row (slot + 1))) hch_bits
  have hk_word :
      sha512K[row_idx * 4 + slot]! = (roundStepA_kNat row_idx slot).toUInt64 := by
    simpa [roundStepA_kNat, packU16x4] using k_word_eq_limbs row_idx slot hidx_bound hslot
  have hsched_word :
      scheduleWordAtRow air (nextRow air row) slot = (roundStepA_schedNat air row slot).toUInt64 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt64]
    simpa [roundStepA_schedNat] using
      packBitsWord_eq_word (scheduleBitsWord air (nextRow air row) slot) hsched_bits
  have hsig0_word :
      bigSigma0 (concatAWord air row (slot + 3)) = (roundStepA_sigma0Nat air row slot).toUInt64 := by
    calc
      bigSigma0 (concatAWord air row (slot + 3))
          = bigSigma0 (bitsWordToUInt64 (concatABitsWord air row (slot + 3))) := by
              rw [concatAWord_eq_bitsWordToUInt64 air row (slot + 3) hslot3 hbb hbb_next]
      _ = bitsWordToUInt64 (fieldBigSigma0 (concatABitsWord air row (slot + 3))) := by
            rw [(fieldBigSigma0_eq_bigSigma0 (concatABitsWord air row (slot + 3)) ha_bits).symm]
      _ = (roundStepA_sigma0Nat air row slot).toUInt64 := by
            simpa [roundStepA_sigma0Nat] using
              packBitsWord_eq_word (fieldBigSigma0 (concatABitsWord air row (slot + 3))) hsig0_bits
  have hmaj_word :
      maj (concatAWord air row (slot + 3))
        (concatAWord air row (slot + 2))
        (concatAWord air row (slot + 1)) = (roundStepA_majNat air row slot).toUInt64 := by
    calc
      maj (concatAWord air row (slot + 3))
            (concatAWord air row (slot + 2))
            (concatAWord air row (slot + 1))
          = maj (bitsWordToUInt64 (concatABitsWord air row (slot + 3)))
              (bitsWordToUInt64 (concatABitsWord air row (slot + 2)))
              (bitsWordToUInt64 (concatABitsWord air row (slot + 1))) := by
                rw [concatAWord_eq_bitsWordToUInt64 air row (slot + 3) hslot3 hbb hbb_next,
                  concatAWord_eq_bitsWordToUInt64 air row (slot + 2) hslot2 hbb hbb_next,
                  concatAWord_eq_bitsWordToUInt64 air row (slot + 1) hslot1 hbb hbb_next]
      _ = bitsWordToUInt64
            (fieldMaj (concatABitsWord air row (slot + 3))
              (concatABitsWord air row (slot + 2))
              (concatABitsWord air row (slot + 1))) := by
            symm
            exact fieldMaj_eq_maj _ _ _ ha_bits hb_bits hc_bits
      _ = (roundStepA_majNat air row slot).toUInt64 := by
            simpa [roundStepA_majNat] using
              packBitsWord_eq_word
                (fieldMaj (concatABitsWord air row (slot + 3))
                  (concatABitsWord air row (slot + 2))
                  (concatABitsWord air row (slot + 1))) hmaj_bits
  dsimp [roundStepAExpected, roundStepA_sumWord, roundStep, slotInputState]
  rw [hh_word, hsig1_word, hch_word, hk_word, hsched_word, hsig0_word, hmaj_word]
  simp [add_assoc]

theorem round_step_a_sum_eq_result (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    roundStepA_sumWord air row slot row_idx =
      (roundStepA_resultNat air row slot).toUInt64 := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have ha_bits : isBitsWord (concatABitsWord air row (slot + 3)) :=
    concatABits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hb_bits : isBitsWord (concatABitsWord air row (slot + 2)) :=
    concatABits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hc_bits : isBitsWord (concatABitsWord air row (slot + 1)) :=
    concatABits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hsig0_bits :
      isBitsWord (fieldBigSigma0 (concatABitsWord air row (slot + 3))) :=
    fieldBigSigma0_isBitsWord _ ha_bits
  have hmaj_bits :
      isBitsWord (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1))) :=
    fieldMaj_isBitsWord _ _ _ ha_bits hb_bits hc_bits
  have hnext_a_bits : isBitsWord (aBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.1 slot i.val hslot i.isLt
  have hk0_lt : (k_limb_at row_idx slot 0).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 0 hidx_bound hslot (by decide)
  have hk1_lt : (k_limb_at row_idx slot 1).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 1 hidx_bound hslot (by decide)
  have hk2_lt : (k_limb_at row_idx slot 2).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 2 hidx_bound hslot (by decide)
  have hk3_lt : (k_limb_at row_idx slot 3).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 3 hidx_bound hslot (by decide)
  have hcarry0_lt : (next_carry_a air slot 0 row).val < 2 ^ 8 := by
    exact next_carry_a_val_lt air row slot 0 hslot (by decide) hrow hrot hcarry_next
  have hcarry1_lt : (next_carry_a air slot 1 row).val < 2 ^ 8 := by
    exact next_carry_a_val_lt air row slot 1 hslot (by decide) hrow hrot hcarry_next
  have hcarry2_lt : (next_carry_a air slot 2 row).val < 2 ^ 8 := by
    exact next_carry_a_val_lt air row slot 2 hslot (by decide) hrow hrot hcarry_next
  have hcarry3_lt : (next_carry_a air slot 3 row).val < 2 ^ 8 := by
    exact next_carry_a_val_lt air row slot 3 hslot (by decide) hrow hrot hcarry_next
  have hlimb0 :
      bitsU16Limb (concatEBitsWord air row slot) 0 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 0 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 0 +
          k_limb_at row_idx slot 0 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 0 +
          bitsU16Limb (fieldBigSigma0 (concatABitsWord air row (slot + 3))) 0 +
          bitsU16Limb
            (fieldMaj (concatABitsWord air row (slot + 3))
              (concatABitsWord air row (slot + 2))
              (concatABitsWord air row (slot + 1))) 0 =
        bitsU16Limb (aBitsWord air (nextRow air row) slot) 0 +
          next_carry_a air slot 0 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInA] using
      round_step_a_limb_eq air row slot 0 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  have hlimb1 :
      bitsU16Limb (concatEBitsWord air row slot) 1 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 1 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 1 +
          k_limb_at row_idx slot 1 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 1 +
          bitsU16Limb (fieldBigSigma0 (concatABitsWord air row (slot + 3))) 1 +
          bitsU16Limb
            (fieldMaj (concatABitsWord air row (slot + 3))
              (concatABitsWord air row (slot + 2))
              (concatABitsWord air row (slot + 1))) 1 +
          next_carry_a air slot 0 row =
        bitsU16Limb (aBitsWord air (nextRow air row) slot) 1 +
          next_carry_a air slot 1 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInA] using
      round_step_a_limb_eq air row slot 1 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  have hlimb2 :
      bitsU16Limb (concatEBitsWord air row slot) 2 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 2 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 2 +
          k_limb_at row_idx slot 2 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 2 +
          bitsU16Limb (fieldBigSigma0 (concatABitsWord air row (slot + 3))) 2 +
          bitsU16Limb
            (fieldMaj (concatABitsWord air row (slot + 3))
              (concatABitsWord air row (slot + 2))
              (concatABitsWord air row (slot + 1))) 2 +
          next_carry_a air slot 1 row =
        bitsU16Limb (aBitsWord air (nextRow air row) slot) 2 +
          next_carry_a air slot 2 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInA] using
      round_step_a_limb_eq air row slot 2 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  have hlimb3 :
      bitsU16Limb (concatEBitsWord air row slot) 3 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 3 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 3 +
          k_limb_at row_idx slot 3 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 3 +
          bitsU16Limb (fieldBigSigma0 (concatABitsWord air row (slot + 3))) 3 +
          bitsU16Limb
            (fieldMaj (concatABitsWord air row (slot + 3))
              (concatABitsWord air row (slot + 2))
              (concatABitsWord air row (slot + 1))) 3 +
          next_carry_a air slot 2 row =
        bitsU16Limb (aBitsWord air (nextRow air row) slot) 3 +
          next_carry_a air slot 3 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInA] using
      round_step_a_limb_eq air row slot 3 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  change ((((((packBitsWord (concatEBitsWord air row slot)).toUInt64 +
        (packBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).toUInt64) +
        (packBitsWord
          (fieldCh (concatEBitsWord air row (slot + 3))
            (concatEBitsWord air row (slot + 2))
            (concatEBitsWord air row (slot + 1)))).toUInt64) +
        (packU16x4
          (k_limb_at row_idx slot 0).val
          (k_limb_at row_idx slot 1).val
          (k_limb_at row_idx slot 2).val
          (k_limb_at row_idx slot 3).val).toUInt64) +
        (packBitsWord (scheduleBitsWord air (nextRow air row) slot)).toUInt64) +
        (packBitsWord (fieldBigSigma0 (concatABitsWord air row (slot + 3)))).toUInt64) +
        (packBitsWord
          (fieldMaj (concatABitsWord air row (slot + 3))
            (concatABitsWord air row (slot + 2))
            (concatABitsWord air row (slot + 1)))).toUInt64 =
      (packBitsWord (aBitsWord air (nextRow air row) slot)).toUInt64
  exact
    packBitsWord_addition_seven_uint64
      (concatEBitsWord air row slot)
      (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))
      (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1)))
      (scheduleBitsWord air (nextRow air row) slot)
      (fieldBigSigma0 (concatABitsWord air row (slot + 3)))
      (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1)))
      (aBitsWord air (nextRow air row) slot)
      (k_limb_at row_idx slot 0)
      (k_limb_at row_idx slot 1)
      (k_limb_at row_idx slot 2)
      (k_limb_at row_idx slot 3)
      (next_carry_a air slot 0 row)
      (next_carry_a air slot 1 row)
      (next_carry_a air slot 2 row)
      (next_carry_a air slot 3 row)
      hh_bits hsig1_bits hch_bits hsched_bits hsig0_bits hmaj_bits hnext_a_bits
      hk0_lt hk1_lt hk2_lt hk3_lt
      hcarry0_lt hcarry1_lt hcarry2_lt hcarry3_lt
      hlimb0 hlimb1 hlimb2 hlimb3

/-- A single round step: the new a-word matches `roundStep.a`. -/
theorem single_round_a_correct (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (row_idx : ℕ)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    aWord air (nextRow air row) slot = roundStepAExpected air row slot row_idx := by
  have hnext_a_bits : isBitsWord (aBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.1 slot i.val hslot i.isLt
  have hres_word :
      aWord air (nextRow air row) slot =
        (roundStepA_resultNat air row slot).toUInt64 := by
    rw [aWord_eq_bitsWordToUInt64]
    simpa [roundStepA_resultNat] using
      packBitsWord_eq_word (aBitsWord air (nextRow air row) slot) hnext_a_bits
  calc
    aWord air (nextRow air row) slot = (roundStepA_resultNat air row slot).toUInt64 := hres_word
    _ = roundStepA_sumWord air row slot row_idx := by
          symm
          exact round_step_a_sum_eq_result air row slot row_idx hslot hrow hrot hrs hbb hbb_next
            hround_next hflags_next hidx hidx_bound hcarry_next hsched_bits
    _ = roundStepAExpected air row slot row_idx := by
          symm
          exact round_step_a_rhs_eq_sum air row slot row_idx hslot hbb hbb_next
            hidx_bound hsched_bits

/-! ### Round Step E bridge -/

def roundStepE_dNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (concatABitsWord air row slot)

def roundStepE_hNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (concatEBitsWord air row slot)

def roundStepE_sigma1Nat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))

def roundStepE_chNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord
    (fieldCh (concatEBitsWord air row (slot + 3))
      (concatEBitsWord air row (slot + 2))
      (concatEBitsWord air row (slot + 1)))

def roundStepE_kNat (row_idx slot : ℕ) : ℕ :=
  packU16x4
    (k_limb_at row_idx slot 0).val
    (k_limb_at row_idx slot 1).val
    (k_limb_at row_idx slot 2).val
    (k_limb_at row_idx slot 3).val

def roundStepE_schedNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (scheduleBitsWord air (nextRow air row) slot)

def roundStepE_resultNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  packBitsWord (eBitsWord air (nextRow air row) slot)

def roundStepE_sumWord (air : C FBB ExtF) (row slot row_idx : ℕ) : Word :=
  (((((roundStepE_dNat air row slot).toUInt64 +
      (roundStepE_hNat air row slot).toUInt64) +
      (roundStepE_sigma1Nat air row slot).toUInt64) +
      (roundStepE_chNat air row slot).toUInt64) +
      (roundStepE_kNat row_idx slot).toUInt64) +
      (roundStepE_schedNat air row slot).toUInt64

theorem round_step_e_rhs_eq_sum (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hidx_bound : row_idx < 20)
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    roundStepEExpected air row slot row_idx = roundStepE_sumWord air row slot row_idx := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hd_bits : isBitsWord (concatABitsWord air row slot) :=
    concatABits_boolean air row slot hslot0 hbb hbb_next
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hd_word :
      concatAWord air row slot = (roundStepE_dNat air row slot).toUInt64 := by
    rw [concatAWord_eq_bitsWordToUInt64 air row slot hslot0 hbb hbb_next]
    simpa [roundStepE_dNat] using packBitsWord_eq_word (concatABitsWord air row slot) hd_bits
  have hh_word :
      concatEWord air row slot = (roundStepE_hNat air row slot).toUInt64 := by
    rw [concatEWord_eq_bitsWordToUInt64 air row slot hslot0 hbb hbb_next]
    simpa [roundStepE_hNat] using packBitsWord_eq_word (concatEBitsWord air row slot) hh_bits
  have hsig1_word :
      bigSigma1 (concatEWord air row (slot + 3)) = (roundStepE_sigma1Nat air row slot).toUInt64 := by
    calc
      bigSigma1 (concatEWord air row (slot + 3))
          = bigSigma1 (bitsWordToUInt64 (concatEBitsWord air row (slot + 3))) := by
              rw [concatEWord_eq_bitsWordToUInt64 air row (slot + 3) hslot3 hbb hbb_next]
      _ = bitsWordToUInt64 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) := by
            rw [(fieldBigSigma1_eq_bigSigma1 (concatEBitsWord air row (slot + 3)) he_bits).symm]
      _ = (roundStepE_sigma1Nat air row slot).toUInt64 := by
            simpa [roundStepE_sigma1Nat] using
              packBitsWord_eq_word (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) hsig1_bits
  have hch_word :
      ch (concatEWord air row (slot + 3))
        (concatEWord air row (slot + 2))
        (concatEWord air row (slot + 1)) = (roundStepE_chNat air row slot).toUInt64 := by
    calc
      ch (concatEWord air row (slot + 3))
            (concatEWord air row (slot + 2))
            (concatEWord air row (slot + 1))
          = ch (bitsWordToUInt64 (concatEBitsWord air row (slot + 3)))
              (bitsWordToUInt64 (concatEBitsWord air row (slot + 2)))
              (bitsWordToUInt64 (concatEBitsWord air row (slot + 1))) := by
                rw [concatEWord_eq_bitsWordToUInt64 air row (slot + 3) hslot3 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt64 air row (slot + 2) hslot2 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt64 air row (slot + 1) hslot1 hbb hbb_next]
      _ = bitsWordToUInt64
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) := by
            symm
            exact fieldCh_eq_ch _ _ _ he_bits hf_bits hg_bits
      _ = (roundStepE_chNat air row slot).toUInt64 := by
            simpa [roundStepE_chNat] using
              packBitsWord_eq_word
                (fieldCh (concatEBitsWord air row (slot + 3))
                  (concatEBitsWord air row (slot + 2))
                  (concatEBitsWord air row (slot + 1))) hch_bits
  have hk_word :
      sha512K[row_idx * 4 + slot]! = (roundStepE_kNat row_idx slot).toUInt64 := by
    simpa [roundStepE_kNat, packU16x4] using k_word_eq_limbs row_idx slot hidx_bound hslot
  have hsched_word :
      scheduleWordAtRow air (nextRow air row) slot = (roundStepE_schedNat air row slot).toUInt64 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt64]
    simpa [roundStepE_schedNat] using
      packBitsWord_eq_word (scheduleBitsWord air (nextRow air row) slot) hsched_bits
  dsimp [roundStepEExpected, roundStepE_sumWord, roundStep, slotInputState]
  rw [hd_word, hh_word, hsig1_word, hch_word, hk_word, hsched_word]
  simp [add_assoc]

theorem round_step_e_sum_eq_result (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (_hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    roundStepE_sumWord air row slot row_idx =
      (roundStepE_resultNat air row slot).toUInt64 := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hd_bits : isBitsWord (concatABitsWord air row slot) :=
    concatABits_boolean air row slot hslot0 hbb hbb_next
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hnext_e_bits : isBitsWord (eBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.2 slot i.val hslot i.isLt
  have hk0_lt : (k_limb_at row_idx slot 0).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 0 hidx_bound hslot (by decide)
  have hk1_lt : (k_limb_at row_idx slot 1).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 1 hidx_bound hslot (by decide)
  have hk2_lt : (k_limb_at row_idx slot 2).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 2 hidx_bound hslot (by decide)
  have hk3_lt : (k_limb_at row_idx slot 3).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 3 hidx_bound hslot (by decide)
  have hcarry0_lt : (next_carry_e air slot 0 row).val < 2 ^ 8 := by
    exact next_carry_e_val_lt air row slot 0 hslot (by decide) hrow hrot hcarry_next
  have hcarry1_lt : (next_carry_e air slot 1 row).val < 2 ^ 8 := by
    exact next_carry_e_val_lt air row slot 1 hslot (by decide) hrow hrot hcarry_next
  have hcarry2_lt : (next_carry_e air slot 2 row).val < 2 ^ 8 := by
    exact next_carry_e_val_lt air row slot 2 hslot (by decide) hrow hrot hcarry_next
  have hcarry3_lt : (next_carry_e air slot 3 row).val < 2 ^ 8 := by
    exact next_carry_e_val_lt air row slot 3 hslot (by decide) hrow hrot hcarry_next
  have hlimb0 :
      bitsU16Limb (concatABitsWord air row slot) 0 +
          bitsU16Limb (concatEBitsWord air row slot) 0 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 0 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 0 +
      k_limb_at row_idx slot 0 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 0 =
        bitsU16Limb (eBitsWord air (nextRow air row) slot) 0 +
          next_carry_e air slot 0 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInE] using
      round_step_e_limb_eq air row slot 0 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  have hlimb1 :
      bitsU16Limb (concatABitsWord air row slot) 1 +
          bitsU16Limb (concatEBitsWord air row slot) 1 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 1 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 1 +
          k_limb_at row_idx slot 1 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 1 +
          next_carry_e air slot 0 row =
        bitsU16Limb (eBitsWord air (nextRow air row) slot) 1 +
          next_carry_e air slot 1 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInE] using
      round_step_e_limb_eq air row slot 1 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  have hlimb2 :
      bitsU16Limb (concatABitsWord air row slot) 2 +
          bitsU16Limb (concatEBitsWord air row slot) 2 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 2 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 2 +
          k_limb_at row_idx slot 2 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 2 +
          next_carry_e air slot 1 row =
        bitsU16Limb (eBitsWord air (nextRow air row) slot) 2 +
          next_carry_e air slot 2 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInE] using
      round_step_e_limb_eq air row slot 2 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  have hlimb3 :
      bitsU16Limb (concatABitsWord air row slot) 3 +
          bitsU16Limb (concatEBitsWord air row slot) 3 +
          bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 3 +
          bitsU16Limb
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) 3 +
          k_limb_at row_idx slot 3 +
          bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 3 +
          next_carry_e air slot 2 row =
        bitsU16Limb (eBitsWord air (nextRow air row) slot) 3 +
          next_carry_e air slot 3 row * (2 ^ 16 : ℕ) := by
    simpa [roundStepCarryInE] using
      round_step_e_limb_eq air row slot 3 row_idx hslot (by decide) hrow hrot hrs
        hround_next hidx hidx_bound
  change (((((packBitsWord (concatABitsWord air row slot)).toUInt64 +
        (packBitsWord (concatEBitsWord air row slot)).toUInt64) +
        (packBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).toUInt64) +
        (packBitsWord
          (fieldCh (concatEBitsWord air row (slot + 3))
            (concatEBitsWord air row (slot + 2))
            (concatEBitsWord air row (slot + 1)))).toUInt64) +
        (packU16x4
          (k_limb_at row_idx slot 0).val
          (k_limb_at row_idx slot 1).val
          (k_limb_at row_idx slot 2).val
          (k_limb_at row_idx slot 3).val).toUInt64) +
        (packBitsWord (scheduleBitsWord air (nextRow air row) slot)).toUInt64 =
      (packBitsWord (eBitsWord air (nextRow air row) slot)).toUInt64
  exact
    packBitsWord_addition_six_uint64
      (concatABitsWord air row slot)
      (concatEBitsWord air row slot)
      (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))
      (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1)))
      (scheduleBitsWord air (nextRow air row) slot)
      (eBitsWord air (nextRow air row) slot)
      (k_limb_at row_idx slot 0)
      (k_limb_at row_idx slot 1)
      (k_limb_at row_idx slot 2)
      (k_limb_at row_idx slot 3)
      (next_carry_e air slot 0 row)
      (next_carry_e air slot 1 row)
      (next_carry_e air slot 2 row)
      (next_carry_e air slot 3 row)
      hd_bits hh_bits hsig1_bits hch_bits hsched_bits hnext_e_bits
      hk0_lt hk1_lt hk2_lt hk3_lt
      hcarry0_lt hcarry1_lt hcarry2_lt hcarry3_lt
      hlimb0 hlimb1 hlimb2 hlimb3

/-- A single round step: the new e-word matches `roundStep.e`. -/
theorem single_round_e_correct (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (row_idx : ℕ)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    eWord air (nextRow air row) slot = roundStepEExpected air row slot row_idx := by
  have hnext_e_bits : isBitsWord (eBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.2 slot i.val hslot i.isLt
  have hres_word :
      eWord air (nextRow air row) slot =
        (roundStepE_resultNat air row slot).toUInt64 := by
    rw [eWord_eq_bitsWordToUInt64]
    simpa [roundStepE_resultNat] using
      packBitsWord_eq_word (eBitsWord air (nextRow air row) slot) hnext_e_bits
  calc
    eWord air (nextRow air row) slot = (roundStepE_resultNat air row slot).toUInt64 := hres_word
    _ = roundStepE_sumWord air row slot row_idx := by
          symm
          exact round_step_e_sum_eq_result air row slot row_idx hslot hrow hrot hrs hbb hbb_next
            hround_next hflags_next hidx hidx_bound hcarry_next hsched_bits
    _ = roundStepEExpected air row slot row_idx := by
          symm
          exact round_step_e_rhs_eq_sum air row slot row_idx hslot hbb hbb_next
            hidx_bound hsched_bits

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
