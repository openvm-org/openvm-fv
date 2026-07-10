/-
  Layer C: Round Step Block-Constraint Bridge

  Repackages the extracted SHA-512 round-step slice inside
  `blockHasherConstraints` into the proof-side `round_step_constraints` record
  expected by the single-round bridge.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.BitsFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.StateBridge

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

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

theorem composeLimb0_explicit (bits : BitsWord) :
    composeU16Limb bits ⟨0, by decide⟩ =
      bits ⟨0, by omega⟩ + bits ⟨1, by omega⟩ * 2 +
      bits ⟨2, by omega⟩ * 4 + bits ⟨3, by omega⟩ * 8 +
      bits ⟨4, by omega⟩ * 16 + bits ⟨5, by omega⟩ * 32 +
      bits ⟨6, by omega⟩ * 64 + bits ⟨7, by omega⟩ * 128 +
      bits ⟨8, by omega⟩ * 256 + bits ⟨9, by omega⟩ * 512 +
      bits ⟨10, by omega⟩ * 1024 + bits ⟨11, by omega⟩ * 2048 +
      bits ⟨12, by omega⟩ * 4096 + bits ⟨13, by omega⟩ * 8192 +
      bits ⟨14, by omega⟩ * 16384 + bits ⟨15, by omega⟩ * 32768 := by
  simpa [composeLo16] using composeLo16_explicit bits

theorem composeLimb1_explicit (bits : BitsWord) :
    composeU16Limb bits ⟨1, by decide⟩ =
      bits ⟨16, by omega⟩ + bits ⟨17, by omega⟩ * 2 +
      bits ⟨18, by omega⟩ * 4 + bits ⟨19, by omega⟩ * 8 +
      bits ⟨20, by omega⟩ * 16 + bits ⟨21, by omega⟩ * 32 +
      bits ⟨22, by omega⟩ * 64 + bits ⟨23, by omega⟩ * 128 +
      bits ⟨24, by omega⟩ * 256 + bits ⟨25, by omega⟩ * 512 +
      bits ⟨26, by omega⟩ * 1024 + bits ⟨27, by omega⟩ * 2048 +
      bits ⟨28, by omega⟩ * 4096 + bits ⟨29, by omega⟩ * 8192 +
      bits ⟨30, by omega⟩ * 16384 + bits ⟨31, by omega⟩ * 32768 := by
  rw [composeU16Limb_range_eq]
  norm_num [Finset.sum_range_succ]

theorem composeLimb2_explicit (bits : BitsWord) :
    composeU16Limb bits ⟨2, by decide⟩ =
      bits ⟨32, by omega⟩ + bits ⟨33, by omega⟩ * 2 +
      bits ⟨34, by omega⟩ * 4 + bits ⟨35, by omega⟩ * 8 +
      bits ⟨36, by omega⟩ * 16 + bits ⟨37, by omega⟩ * 32 +
      bits ⟨38, by omega⟩ * 64 + bits ⟨39, by omega⟩ * 128 +
      bits ⟨40, by omega⟩ * 256 + bits ⟨41, by omega⟩ * 512 +
      bits ⟨42, by omega⟩ * 1024 + bits ⟨43, by omega⟩ * 2048 +
      bits ⟨44, by omega⟩ * 4096 + bits ⟨45, by omega⟩ * 8192 +
      bits ⟨46, by omega⟩ * 16384 + bits ⟨47, by omega⟩ * 32768 := by
  rw [composeU16Limb_range_eq]
  norm_num [Finset.sum_range_succ]

theorem composeLimb3_explicit (bits : BitsWord) :
    composeU16Limb bits ⟨3, by decide⟩ =
      bits ⟨48, by omega⟩ + bits ⟨49, by omega⟩ * 2 +
      bits ⟨50, by omega⟩ * 4 + bits ⟨51, by omega⟩ * 8 +
      bits ⟨52, by omega⟩ * 16 + bits ⟨53, by omega⟩ * 32 +
      bits ⟨54, by omega⟩ * 64 + bits ⟨55, by omega⟩ * 128 +
      bits ⟨56, by omega⟩ * 256 + bits ⟨57, by omega⟩ * 512 +
      bits ⟨58, by omega⟩ * 1024 + bits ⟨59, by omega⟩ * 2048 +
      bits ⟨60, by omega⟩ * 4096 + bits ⟨61, by omega⟩ * 8192 +
      bits ⟨62, by omega⟩ * 16384 + bits ⟨63, by omega⟩ * 32768 := by
  rw [composeU16Limb_range_eq]
  norm_num [Finset.sum_range_succ]

theorem fieldCh_bit_poly_of_boolean (x y z : FBB) (hx : x = 0 ∨ x = 1) :
    fieldXor (fieldAnd x y) (fieldAnd (fieldNot x) z) =
      x * y + (1 - x) * z := by
  rcases hx with rfl | rfl <;> simp [fieldXor, fieldAnd, fieldNot]

theorem fieldMaj_apply_poly (x y z : BitsWord) (i : Fin 64)
    (hx : x i = 0 ∨ x i = 1)
    (hy : y i = 0 ∨ y i = 1)
    (hz : z i = 0 ∨ z i = 1) :
    fieldMaj x y z i =
      x i * y i + x i * z i + y i * z i - 2 * x i * y i * z i := by
  rcases hx with hx0 | hx1
  · rcases hy with hy0 | hy1
    · rcases hz with hz0 | hz1
      · simp [fieldMaj, fieldXor, fieldAnd, hx0, hy0, hz0]
      · simp [fieldMaj, fieldXor, fieldAnd, hx0, hy0, hz1]
    · rcases hz with hz0 | hz1
      · simp [fieldMaj, fieldXor, fieldAnd, hx0, hy1, hz0]
      · simp [fieldMaj, fieldXor, fieldAnd, hx0, hy1, hz1]
  · rcases hy with hy0 | hy1
    · rcases hz with hz0 | hz1
      · simp [fieldMaj, fieldXor, fieldAnd, hx1, hy0, hz0]
      · simp [fieldMaj, fieldXor, fieldAnd, hx1, hy0, hz1]
    · rcases hz with hz0 | hz1
      · simp [fieldMaj, fieldXor, fieldAnd, hx1, hy1, hz0]
      · simp [fieldMaj, fieldXor, fieldAnd, hx1, hy1, hz1]

theorem fieldBigSigma0_apply_poly (x : BitsWord) (i : Fin 64) :
    fieldBigSigma0 x i =
      x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩ *
          x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩ *
          x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩ +
        x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩ *
            (1 - x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩) *
            (1 - x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩ *
              (1 - x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) +
            (1 - x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩) *
                (1 - x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩) *
                x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩ := by
  simp [fieldBigSigma0, fieldRotr]
  rw [fieldXor3_poly]

theorem fieldBigSigma1_apply_poly (x : BitsWord) (i : Fin 64) :
    fieldBigSigma1 x i =
      x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩ *
          x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩ *
          x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩ +
        x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩ *
            (1 - x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩) *
            (1 - x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩ *
              (1 - x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) +
            (1 - x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩) *
                (1 - x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩) *
                x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩ := by
  simp [fieldBigSigma1, fieldRotr]
  rw [fieldXor3_poly]

def fieldBigSigma0PolyWord (x : BitsWord) : BitsWord :=
  fun i =>
    x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩ *
        x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩ *
        x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩ +
      x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩ *
          (1 - x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩) *
          (1 - x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) +
        (1 - x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩) *
            x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩ *
            (1 - x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩) *
              (1 - x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩

def fieldBigSigma1PolyWord (x : BitsWord) : BitsWord :=
  fun i =>
    x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩ *
        x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩ *
        x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩ +
      x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩ *
          (1 - x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩) *
          (1 - x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) +
        (1 - x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩) *
            x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩ *
            (1 - x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) +
          (1 - x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩) *
              (1 - x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩) *
              x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩

def fieldChPolyWord (x y z : BitsWord) : BitsWord :=
  fun i => x i * y i + (1 - x i) * z i

def fieldMajPolyWord (x y z : BitsWord) : BitsWord :=
  fun i => x i * y i + x i * z i + y i * z i - 2 * x i * y i * z i

theorem fieldBigSigma0_eq_polyWord (x : BitsWord) :
    fieldBigSigma0 x = fieldBigSigma0PolyWord x := by
  funext i
  exact fieldBigSigma0_apply_poly x i

theorem fieldBigSigma1_eq_polyWord (x : BitsWord) :
    fieldBigSigma1 x = fieldBigSigma1PolyWord x := by
  funext i
  exact fieldBigSigma1_apply_poly x i

theorem fieldCh_eq_polyWord (x y z : BitsWord) (hx : isBitsWord x) :
    fieldCh x y z = fieldChPolyWord x y z := by
  funext i
  exact fieldCh_bit_poly_of_boolean _ _ _ (hx i)

theorem fieldMaj_eq_polyWord
    (x y z : BitsWord)
    (hx : isBitsWord x)
    (hy : isBitsWord y)
    (hz : isBitsWord z) :
    fieldMaj x y z = fieldMajPolyWord x y z := by
  funext i
  exact fieldMaj_apply_poly _ _ _ i (hx i) (hy i) (hz i)

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

theorem bitsU16Limb_zero_eq_lo16Expr (bits : BitsWord) :
    bitsU16Limb bits 0 = lo16Expr bits := by
  simpa [bitsU16Limb, lo16Expr] using composeLimb0_explicit bits

abbrev lo16FieldBigSigma0Bit (x : BitsWord) (i : Fin 16) : FBB :=
  x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩ *
      x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩ *
      x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩ +
    x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩ *
        (1 - x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩) *
        (1 - x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) +
      (1 - x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩) *
          x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩ *
          (1 - x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩) +
        (1 - x ⟨(i.val + 28) % 64, Nat.mod_lt _ (by omega)⟩) *
            (1 - x ⟨(i.val + 34) % 64, Nat.mod_lt _ (by omega)⟩) *
            x ⟨(i.val + 39) % 64, Nat.mod_lt _ (by omega)⟩

abbrev lo16FieldBigSigma1Bit (x : BitsWord) (i : Fin 16) : FBB :=
  x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩ *
      x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩ *
      x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩ +
    x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩ *
        (1 - x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩) *
        (1 - x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) +
      (1 - x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩) *
          x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩ *
          (1 - x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩) +
        (1 - x ⟨(i.val + 14) % 64, Nat.mod_lt _ (by omega)⟩) *
            (1 - x ⟨(i.val + 18) % 64, Nat.mod_lt _ (by omega)⟩) *
            x ⟨(i.val + 41) % 64, Nat.mod_lt _ (by omega)⟩

abbrev lo16FieldChBit (x y z : BitsWord) (i : Fin 16) : FBB :=
  x ⟨i.val, by omega⟩ * y ⟨i.val, by omega⟩ +
    (1 - x ⟨i.val, by omega⟩) * z ⟨i.val, by omega⟩

abbrev lo16FieldMajBit (x y z : BitsWord) (i : Fin 16) : FBB :=
  x ⟨i.val, by omega⟩ * y ⟨i.val, by omega⟩ +
    x ⟨i.val, by omega⟩ * z ⟨i.val, by omega⟩ +
    y ⟨i.val, by omega⟩ * z ⟨i.val, by omega⟩ -
    2 * x ⟨i.val, by omega⟩ * y ⟨i.val, by omega⟩ * z ⟨i.val, by omega⟩

abbrev lo16FieldBigSigma0PolyWord (x : BitsWord) : FBB :=
  lo16FieldBigSigma0Bit x ⟨0, by decide⟩ +
    lo16FieldBigSigma0Bit x ⟨1, by decide⟩ * 2 +
    lo16FieldBigSigma0Bit x ⟨2, by decide⟩ * 4 +
    lo16FieldBigSigma0Bit x ⟨3, by decide⟩ * 8 +
    lo16FieldBigSigma0Bit x ⟨4, by decide⟩ * 16 +
    lo16FieldBigSigma0Bit x ⟨5, by decide⟩ * 32 +
    lo16FieldBigSigma0Bit x ⟨6, by decide⟩ * 64 +
    lo16FieldBigSigma0Bit x ⟨7, by decide⟩ * 128 +
    lo16FieldBigSigma0Bit x ⟨8, by decide⟩ * 256 +
    lo16FieldBigSigma0Bit x ⟨9, by decide⟩ * 512 +
    lo16FieldBigSigma0Bit x ⟨10, by decide⟩ * 1024 +
    lo16FieldBigSigma0Bit x ⟨11, by decide⟩ * 2048 +
    lo16FieldBigSigma0Bit x ⟨12, by decide⟩ * 4096 +
    lo16FieldBigSigma0Bit x ⟨13, by decide⟩ * 8192 +
    lo16FieldBigSigma0Bit x ⟨14, by decide⟩ * 16384 +
    lo16FieldBigSigma0Bit x ⟨15, by decide⟩ * 32768

abbrev lo16FieldBigSigma1PolyWord (x : BitsWord) : FBB :=
  lo16FieldBigSigma1Bit x ⟨0, by decide⟩ +
    lo16FieldBigSigma1Bit x ⟨1, by decide⟩ * 2 +
    lo16FieldBigSigma1Bit x ⟨2, by decide⟩ * 4 +
    lo16FieldBigSigma1Bit x ⟨3, by decide⟩ * 8 +
    lo16FieldBigSigma1Bit x ⟨4, by decide⟩ * 16 +
    lo16FieldBigSigma1Bit x ⟨5, by decide⟩ * 32 +
    lo16FieldBigSigma1Bit x ⟨6, by decide⟩ * 64 +
    lo16FieldBigSigma1Bit x ⟨7, by decide⟩ * 128 +
    lo16FieldBigSigma1Bit x ⟨8, by decide⟩ * 256 +
    lo16FieldBigSigma1Bit x ⟨9, by decide⟩ * 512 +
    lo16FieldBigSigma1Bit x ⟨10, by decide⟩ * 1024 +
    lo16FieldBigSigma1Bit x ⟨11, by decide⟩ * 2048 +
    lo16FieldBigSigma1Bit x ⟨12, by decide⟩ * 4096 +
    lo16FieldBigSigma1Bit x ⟨13, by decide⟩ * 8192 +
    lo16FieldBigSigma1Bit x ⟨14, by decide⟩ * 16384 +
    lo16FieldBigSigma1Bit x ⟨15, by decide⟩ * 32768

abbrev lo16FieldChPolyWord (x y z : BitsWord) : FBB :=
  lo16FieldChBit x y z ⟨0, by decide⟩ +
    lo16FieldChBit x y z ⟨1, by decide⟩ * 2 +
    lo16FieldChBit x y z ⟨2, by decide⟩ * 4 +
    lo16FieldChBit x y z ⟨3, by decide⟩ * 8 +
    lo16FieldChBit x y z ⟨4, by decide⟩ * 16 +
    lo16FieldChBit x y z ⟨5, by decide⟩ * 32 +
    lo16FieldChBit x y z ⟨6, by decide⟩ * 64 +
    lo16FieldChBit x y z ⟨7, by decide⟩ * 128 +
    lo16FieldChBit x y z ⟨8, by decide⟩ * 256 +
    lo16FieldChBit x y z ⟨9, by decide⟩ * 512 +
    lo16FieldChBit x y z ⟨10, by decide⟩ * 1024 +
    lo16FieldChBit x y z ⟨11, by decide⟩ * 2048 +
    lo16FieldChBit x y z ⟨12, by decide⟩ * 4096 +
    lo16FieldChBit x y z ⟨13, by decide⟩ * 8192 +
    lo16FieldChBit x y z ⟨14, by decide⟩ * 16384 +
    lo16FieldChBit x y z ⟨15, by decide⟩ * 32768

abbrev lo16FieldMajPolyWord (x y z : BitsWord) : FBB :=
  lo16FieldMajBit x y z ⟨0, by decide⟩ +
    lo16FieldMajBit x y z ⟨1, by decide⟩ * 2 +
    lo16FieldMajBit x y z ⟨2, by decide⟩ * 4 +
    lo16FieldMajBit x y z ⟨3, by decide⟩ * 8 +
    lo16FieldMajBit x y z ⟨4, by decide⟩ * 16 +
    lo16FieldMajBit x y z ⟨5, by decide⟩ * 32 +
    lo16FieldMajBit x y z ⟨6, by decide⟩ * 64 +
    lo16FieldMajBit x y z ⟨7, by decide⟩ * 128 +
    lo16FieldMajBit x y z ⟨8, by decide⟩ * 256 +
    lo16FieldMajBit x y z ⟨9, by decide⟩ * 512 +
    lo16FieldMajBit x y z ⟨10, by decide⟩ * 1024 +
    lo16FieldMajBit x y z ⟨11, by decide⟩ * 2048 +
    lo16FieldMajBit x y z ⟨12, by decide⟩ * 4096 +
    lo16FieldMajBit x y z ⟨13, by decide⟩ * 8192 +
    lo16FieldMajBit x y z ⟨14, by decide⟩ * 16384 +
    lo16FieldMajBit x y z ⟨15, by decide⟩ * 32768

theorem bitsU16Limb_fieldBigSigma0PolyWord_zero (x : BitsWord) :
    bitsU16Limb (fieldBigSigma0PolyWord x) 0 = lo16FieldBigSigma0PolyWord x := by
  rw [bitsU16Limb_zero_eq_lo16Expr]
  simp [lo16Expr, fieldBigSigma0PolyWord, lo16FieldBigSigma0PolyWord, lo16FieldBigSigma0Bit]

theorem bitsU16Limb_fieldBigSigma1PolyWord_zero (x : BitsWord) :
    bitsU16Limb (fieldBigSigma1PolyWord x) 0 = lo16FieldBigSigma1PolyWord x := by
  rw [bitsU16Limb_zero_eq_lo16Expr]
  simp [lo16Expr, fieldBigSigma1PolyWord, lo16FieldBigSigma1PolyWord, lo16FieldBigSigma1Bit]

theorem bitsU16Limb_fieldChPolyWord_zero (x y z : BitsWord) :
    bitsU16Limb (fieldChPolyWord x y z) 0 = lo16FieldChPolyWord x y z := by
  rw [bitsU16Limb_zero_eq_lo16Expr]
  simp [lo16Expr, fieldChPolyWord, lo16FieldChPolyWord, lo16FieldChBit]

theorem bitsU16Limb_fieldMajPolyWord_zero (x y z : BitsWord) :
    bitsU16Limb (fieldMajPolyWord x y z) 0 = lo16FieldMajPolyWord x y z := by
  rw [bitsU16Limb_zero_eq_lo16Expr]
  simp [lo16Expr, fieldMajPolyWord, lo16FieldMajPolyWord, lo16FieldMajBit]

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

theorem bitsU16Limb_one_eq_hi16Expr (bits : BitsWord) :
    bitsU16Limb bits 1 = hi16Expr bits := by
  simpa [bitsU16Limb, hi16Expr] using composeLimb1_explicit bits

abbrev hi16FieldBigSigma0PolyWord (x : BitsWord) : FBB :=
  hi16Expr (fieldBigSigma0PolyWord x)

abbrev hi16FieldBigSigma1PolyWord (x : BitsWord) : FBB :=
  hi16Expr (fieldBigSigma1PolyWord x)

abbrev hi16FieldChPolyWord (x y z : BitsWord) : FBB :=
  hi16Expr (fieldChPolyWord x y z)

abbrev hi16FieldMajPolyWord (x y z : BitsWord) : FBB :=
  hi16Expr (fieldMajPolyWord x y z)

theorem bitsU16Limb_fieldBigSigma0PolyWord_one (x : BitsWord) :
    bitsU16Limb (fieldBigSigma0PolyWord x) 1 = hi16FieldBigSigma0PolyWord x := by
  rw [bitsU16Limb_one_eq_hi16Expr]

theorem bitsU16Limb_fieldBigSigma1PolyWord_one (x : BitsWord) :
    bitsU16Limb (fieldBigSigma1PolyWord x) 1 = hi16FieldBigSigma1PolyWord x := by
  rw [bitsU16Limb_one_eq_hi16Expr]

theorem bitsU16Limb_fieldChPolyWord_one (x y z : BitsWord) :
    bitsU16Limb (fieldChPolyWord x y z) 1 = hi16FieldChPolyWord x y z := by
  rw [bitsU16Limb_one_eq_hi16Expr]

theorem bitsU16Limb_fieldMajPolyWord_one (x y z : BitsWord) :
    bitsU16Limb (fieldMajPolyWord x y z) 1 = hi16FieldMajPolyWord x y z := by
  rw [bitsU16Limb_one_eq_hi16Expr]

abbrev limb2Expr (bits : BitsWord) : FBB :=
  bits ⟨32, by decide⟩ +
    bits ⟨33, by decide⟩ * 2 +
    bits ⟨34, by decide⟩ * 4 +
    bits ⟨35, by decide⟩ * 8 +
    bits ⟨36, by decide⟩ * 16 +
    bits ⟨37, by decide⟩ * 32 +
    bits ⟨38, by decide⟩ * 64 +
    bits ⟨39, by decide⟩ * 128 +
    bits ⟨40, by decide⟩ * 256 +
    bits ⟨41, by decide⟩ * 512 +
    bits ⟨42, by decide⟩ * 1024 +
    bits ⟨43, by decide⟩ * 2048 +
    bits ⟨44, by decide⟩ * 4096 +
    bits ⟨45, by decide⟩ * 8192 +
    bits ⟨46, by decide⟩ * 16384 +
    bits ⟨47, by decide⟩ * 32768

theorem bitsU16Limb_two_eq_limb2Expr (bits : BitsWord) :
    bitsU16Limb bits 2 = limb2Expr bits := by
  simpa [bitsU16Limb, limb2Expr] using composeLimb2_explicit bits

abbrev limb2FieldBigSigma0PolyWord (x : BitsWord) : FBB :=
  limb2Expr (fieldBigSigma0PolyWord x)

abbrev limb2FieldBigSigma1PolyWord (x : BitsWord) : FBB :=
  limb2Expr (fieldBigSigma1PolyWord x)

abbrev limb2FieldChPolyWord (x y z : BitsWord) : FBB :=
  limb2Expr (fieldChPolyWord x y z)

abbrev limb2FieldMajPolyWord (x y z : BitsWord) : FBB :=
  limb2Expr (fieldMajPolyWord x y z)

theorem bitsU16Limb_fieldBigSigma0PolyWord_two (x : BitsWord) :
    bitsU16Limb (fieldBigSigma0PolyWord x) 2 = limb2FieldBigSigma0PolyWord x := by
  rw [bitsU16Limb_two_eq_limb2Expr]

theorem bitsU16Limb_fieldBigSigma1PolyWord_two (x : BitsWord) :
    bitsU16Limb (fieldBigSigma1PolyWord x) 2 = limb2FieldBigSigma1PolyWord x := by
  rw [bitsU16Limb_two_eq_limb2Expr]

theorem bitsU16Limb_fieldChPolyWord_two (x y z : BitsWord) :
    bitsU16Limb (fieldChPolyWord x y z) 2 = limb2FieldChPolyWord x y z := by
  rw [bitsU16Limb_two_eq_limb2Expr]

theorem bitsU16Limb_fieldMajPolyWord_two (x y z : BitsWord) :
    bitsU16Limb (fieldMajPolyWord x y z) 2 = limb2FieldMajPolyWord x y z := by
  rw [bitsU16Limb_two_eq_limb2Expr]

abbrev limb3Expr (bits : BitsWord) : FBB :=
  bits ⟨48, by decide⟩ +
    bits ⟨49, by decide⟩ * 2 +
    bits ⟨50, by decide⟩ * 4 +
    bits ⟨51, by decide⟩ * 8 +
    bits ⟨52, by decide⟩ * 16 +
    bits ⟨53, by decide⟩ * 32 +
    bits ⟨54, by decide⟩ * 64 +
    bits ⟨55, by decide⟩ * 128 +
    bits ⟨56, by decide⟩ * 256 +
    bits ⟨57, by decide⟩ * 512 +
    bits ⟨58, by decide⟩ * 1024 +
    bits ⟨59, by decide⟩ * 2048 +
    bits ⟨60, by decide⟩ * 4096 +
    bits ⟨61, by decide⟩ * 8192 +
    bits ⟨62, by decide⟩ * 16384 +
    bits ⟨63, by decide⟩ * 32768

theorem bitsU16Limb_three_eq_limb3Expr (bits : BitsWord) :
    bitsU16Limb bits 3 = limb3Expr bits := by
  simpa [bitsU16Limb, limb3Expr] using composeLimb3_explicit bits

abbrev limb3FieldBigSigma0PolyWord (x : BitsWord) : FBB :=
  limb3Expr (fieldBigSigma0PolyWord x)

abbrev limb3FieldBigSigma1PolyWord (x : BitsWord) : FBB :=
  limb3Expr (fieldBigSigma1PolyWord x)

abbrev limb3FieldChPolyWord (x y z : BitsWord) : FBB :=
  limb3Expr (fieldChPolyWord x y z)

abbrev limb3FieldMajPolyWord (x y z : BitsWord) : FBB :=
  limb3Expr (fieldMajPolyWord x y z)

theorem bitsU16Limb_fieldBigSigma0PolyWord_three (x : BitsWord) :
    bitsU16Limb (fieldBigSigma0PolyWord x) 3 = limb3FieldBigSigma0PolyWord x := by
  rw [bitsU16Limb_three_eq_limb3Expr]

theorem bitsU16Limb_fieldBigSigma1PolyWord_three (x : BitsWord) :
    bitsU16Limb (fieldBigSigma1PolyWord x) 3 = limb3FieldBigSigma1PolyWord x := by
  rw [bitsU16Limb_three_eq_limb3Expr]

theorem bitsU16Limb_fieldChPolyWord_three (x y z : BitsWord) :
    bitsU16Limb (fieldChPolyWord x y z) 3 = limb3FieldChPolyWord x y z := by
  rw [bitsU16Limb_three_eq_limb3Expr]

theorem bitsU16Limb_fieldMajPolyWord_three (x y z : BitsWord) :
    bitsU16Limb (fieldMajPolyWord x y z) 3 = limb3FieldMajPolyWord x y z := by
  rw [bitsU16Limb_three_eq_limb3Expr]

theorem rawConcatABits_boolean
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    isBitsWord (rawConcatABitsWord air row j) := by
  rw [rawConcatABitsWord_eq_concatABitsWord air row j hrot hrow]
  exact concatABits_boolean air row j hj8 hbb hbb_next

theorem rawConcatEBits_boolean
    (air : C FBB ExtF) (row j : ℕ)
    (hj8 : j < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    isBitsWord (rawConcatEBitsWord air row j) := by
  rw [rawConcatEBitsWord_eq_concatEBitsWord air row j hrot hrow]
  exact concatEBits_boolean air row j hj8 hbb hbb_next

theorem raw_a_update_constraint_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4) :
    raw_a_update_constraint air row slot limb := by
  have hrs_raw :=
    Sha2BlockHasherVmAir_sha512.constraints.round_step_constraints_of_blockHasherConstraints
      air hc row
  have h1416_1425 := hrs_raw.1
  have h1426_1435 := hrs_raw.2.1
  have h1436_1445 := hrs_raw.2.2.1
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  have hl : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl | rfl
  · simpa [raw_a_update_constraint] using h1416_1425.1
  · simpa [raw_a_update_constraint] using h1416_1425.2.1
  · simpa [raw_a_update_constraint] using h1416_1425.2.2.1
  · simpa [raw_a_update_constraint] using h1416_1425.2.2.2.1
  · simpa [raw_a_update_constraint] using h1416_1425.2.2.2.2.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1416_1425.2.2.2.2.2.2.2.2.2
  · simpa [raw_a_update_constraint] using h1426_1435.1
  · simpa [raw_a_update_constraint] using h1426_1435.2.1
  · simpa [raw_a_update_constraint] using h1426_1435.2.2.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1426_1435.2.2.2.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1426_1435.2.2.2.2.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1426_1435.2.2.2.2.2.2.2.2.2
  · simpa [raw_a_update_constraint] using h1436_1445.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1436_1445.2.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1436_1445.2.2.2.2.2.2.1
  · simpa [raw_a_update_constraint] using h1436_1445.2.2.2.2.2.2.2.1

theorem raw_e_update_constraint_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4) :
    raw_e_update_constraint air row slot limb := by
  have hrs_raw :=
    Sha2BlockHasherVmAir_sha512.constraints.round_step_constraints_of_blockHasherConstraints
      air hc row
  have h1416_1425 := hrs_raw.1
  have h1426_1435 := hrs_raw.2.1
  have h1436_1445 := hrs_raw.2.2.1
  have h1446_1447 := hrs_raw.2.2.2
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  have hl : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl | rfl
  · simpa [raw_e_update_constraint] using h1416_1425.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1416_1425.2.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1416_1425.2.2.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1416_1425.2.2.2.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1426_1435.2.2.1
  · simpa [raw_e_update_constraint] using h1426_1435.2.2.2.1
  · simpa [raw_e_update_constraint] using h1426_1435.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1426_1435.2.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1436_1445.1
  · simpa [raw_e_update_constraint] using h1436_1445.2.1
  · simpa [raw_e_update_constraint] using h1436_1445.2.2.1
  · simpa [raw_e_update_constraint] using h1436_1445.2.2.2.1
  · simpa [raw_e_update_constraint] using h1436_1445.2.2.2.2.2.2.2.2.1
  · simpa [raw_e_update_constraint] using h1436_1445.2.2.2.2.2.2.2.2.2
  · simpa [raw_e_update_constraint] using h1446_1447.1
  · simpa [raw_e_update_constraint] using h1446_1447.2

theorem a_update_slot0_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 =
      lo16Expr (nextABitsWord air row 0) +
        next_carry_a air 0 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 0 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 -
          (lo16Expr (nextABitsWord air row 0) +
            next_carry_a air 0 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot1_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 =
      lo16Expr (nextABitsWord air row 1) +
        next_carry_a air 1 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 1 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 -
          (lo16Expr (nextABitsWord air row 1) +
            next_carry_a air 1 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot2_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 =
      lo16Expr (nextABitsWord air row 2) +
        next_carry_a air 2 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 2 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 -
          (lo16Expr (nextABitsWord air row 2) +
            next_carry_a air 2 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot3_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 =
      lo16Expr (nextABitsWord air row 3) +
        next_carry_a air 3 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 3 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 -
          (lo16Expr (nextABitsWord air row 3) +
            next_carry_a air 3 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot0_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 0 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 0 +
      roundConstantPolyAtNext air row 0 0 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 0 =
    lo16Expr (rawConcatEBitsWord air row 0) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
      lo16FieldMajPolyWord
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2)
        (rawConcatABitsWord air row 1) +
      lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 0 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 1) :=
    rawConcatABits_boolean air row 1 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 3) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 3) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_fieldBigSigma0PolyWord_zero, bitsU16Limb_fieldMajPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInA air row 0 0 +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 0 +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)
        =
      lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 0 +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) := by
            simp [roundStepCarryInA]
    _ =
      lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 := by
          ac_rfl

theorem a_update_slot0_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 0 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 0 +
      roundConstantPolyAtNext air row 0 0 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 0 =
    bitsU16Limb (nextABitsWord air row 0) 0 +
      next_carry_a air 0 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 0 0 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 0 +
        roundConstantPolyAtNext air row 0 0 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 0 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 0 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)
            (rawConcatABitsWord air row 1)) 0
        =
      lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 :=
      a_update_slot0_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextABitsWord air row 0) +
        next_carry_a air 0 0 row * (2 ^ 16 : ℕ) :=
      a_update_slot0_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 0) 0 +
        next_carry_a air 0 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextABitsWord air row 0)]

theorem a_update_slot1_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 0 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 0 +
      roundConstantPolyAtNext air row 1 0 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 0 =
    lo16Expr (rawConcatEBitsWord air row 1) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
      lo16FieldMajPolyWord
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2) +
      lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 0 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 4) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 4) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_fieldBigSigma0PolyWord_zero, bitsU16Limb_fieldMajPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInA air row 1 0 +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 0 +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
        =
      lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 0 +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) := by
            simp [roundStepCarryInA]
    _ =
      lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 := by
          ac_rfl

theorem a_update_slot1_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 0 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 0 +
      roundConstantPolyAtNext air row 1 0 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 0 =
    bitsU16Limb (nextABitsWord air row 1) 0 +
      next_carry_a air 1 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 1 0 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 0 +
        roundConstantPolyAtNext air row 1 0 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 0 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 0 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)) 0
        =
      lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 :=
      a_update_slot1_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextABitsWord air row 1) +
        next_carry_a air 1 0 row * (2 ^ 16 : ℕ) :=
      a_update_slot1_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 1) 0 +
        next_carry_a air 1 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextABitsWord air row 1)]

theorem a_update_slot2_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 0 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 0 +
      roundConstantPolyAtNext air row 2 0 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 0 =
    lo16Expr (rawConcatEBitsWord air row 2) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
      lo16FieldMajPolyWord
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3) +
      lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 0 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 5) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 5) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_fieldBigSigma0PolyWord_zero, bitsU16Limb_fieldMajPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInA air row 2 0 +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 0 +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
        =
      lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 0 +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) := by
            simp [roundStepCarryInA]
    _ =
      lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 := by
          ac_rfl

theorem a_update_slot2_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 0 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 0 +
      roundConstantPolyAtNext air row 2 0 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 0 =
    bitsU16Limb (nextABitsWord air row 2) 0 +
      next_carry_a air 2 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 2 0 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 0 +
        roundConstantPolyAtNext air row 2 0 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 0 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 0 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)) 0
        =
      lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 :=
      a_update_slot2_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextABitsWord air row 2) +
        next_carry_a air 2 0 row * (2 ^ 16 : ℕ) :=
      a_update_slot2_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 2) 0 +
        next_carry_a air 2 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextABitsWord air row 2)]

theorem a_update_slot3_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 0 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 0 +
      roundConstantPolyAtNext air row 3 0 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 0 =
    lo16Expr (rawConcatEBitsWord air row 3) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
      lo16FieldMajPolyWord
        (rawConcatABitsWord air row 6)
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4) +
      lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 0 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 6) :=
    rawConcatABits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 6) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 6) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_fieldBigSigma0PolyWord_zero, bitsU16Limb_fieldMajPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInA air row 3 0 +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 0 +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
        =
      lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 0 +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) := by
            simp [roundStepCarryInA]
    _ =
      lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 := by
          ac_rfl

theorem a_update_slot3_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 0 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 0 +
      roundConstantPolyAtNext air row 3 0 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 0 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 0 =
    bitsU16Limb (nextABitsWord air row 3) 0 +
      next_carry_a air 3 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 3 0 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 0 +
        roundConstantPolyAtNext air row 3 0 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 0 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 0 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 6)
            (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)) 0
        =
      lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        lo16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 :=
      a_update_slot3_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextABitsWord air row 3) +
        next_carry_a air 3 0 row * (2 ^ 16 : ℕ) :=
      a_update_slot3_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 3) 0 +
        next_carry_a air 3 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextABitsWord air row 3)]

theorem a_update_slot0_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 0 0 row +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 =
      hi16Expr (nextABitsWord air row 0) +
        next_carry_a air 0 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 0 1 (by decide) (by decide)
  change
    next_carry_a air 0 0 row +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 -
          (hi16Expr (nextABitsWord air row 0) +
            next_carry_a air 0 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot1_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 1 0 row +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 =
      hi16Expr (nextABitsWord air row 1) +
        next_carry_a air 1 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 1 1 (by decide) (by decide)
  change
    next_carry_a air 1 0 row +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 -
          (hi16Expr (nextABitsWord air row 1) +
            next_carry_a air 1 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot2_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 2 0 row +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 =
      hi16Expr (nextABitsWord air row 2) +
        next_carry_a air 2 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 2 1 (by decide) (by decide)
  change
    next_carry_a air 2 0 row +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 -
          (hi16Expr (nextABitsWord air row 2) +
            next_carry_a air 2 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot3_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 3 0 row +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 =
      hi16Expr (nextABitsWord air row 3) +
        next_carry_a air 3 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 3 1 (by decide) (by decide)
  change
    next_carry_a air 3 0 row +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 -
          (hi16Expr (nextABitsWord air row 3) +
            next_carry_a air 3 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot0_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 1 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 1 +
      roundConstantPolyAtNext air row 0 1 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 1 =
    next_carry_a air 0 0 row +
      hi16Expr (rawConcatEBitsWord air row 0) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
      hi16FieldMajPolyWord
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2)
        (rawConcatABitsWord air row 1) +
      hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 1 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 1) :=
    rawConcatABits_boolean air row 1 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 3) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 3) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_fieldBigSigma0PolyWord_one, bitsU16Limb_fieldMajPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInA air row 0 1 +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 1 +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)
        =
      next_carry_a air 0 0 row +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 1 +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 0 0 row +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 := by
          ac_rfl

theorem a_update_slot0_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 1 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 1 +
      roundConstantPolyAtNext air row 0 1 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 1 =
    bitsU16Limb (nextABitsWord air row 0) 1 +
      next_carry_a air 0 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 0 1 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 1 +
        roundConstantPolyAtNext air row 0 1 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 1 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 1 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)
            (rawConcatABitsWord air row 1)) 1
        =
      next_carry_a air 0 0 row +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 :=
      a_update_slot0_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextABitsWord air row 0) +
        next_carry_a air 0 1 row * (2 ^ 16 : ℕ) :=
      a_update_slot0_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 0) 1 +
        next_carry_a air 0 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextABitsWord air row 0)]

theorem a_update_slot1_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 1 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 1 +
      roundConstantPolyAtNext air row 1 1 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 1 =
    next_carry_a air 1 0 row +
      hi16Expr (rawConcatEBitsWord air row 1) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
      hi16FieldMajPolyWord
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2) +
      hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 1 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 4) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 4) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_fieldBigSigma0PolyWord_one, bitsU16Limb_fieldMajPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInA air row 1 1 +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 1 +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
        =
      next_carry_a air 1 0 row +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 1 +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 1 0 row +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 := by
          ac_rfl

theorem a_update_slot1_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 1 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 1 +
      roundConstantPolyAtNext air row 1 1 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 1 =
    bitsU16Limb (nextABitsWord air row 1) 1 +
      next_carry_a air 1 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 1 1 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 1 +
        roundConstantPolyAtNext air row 1 1 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 1 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 1 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)) 1
        =
      next_carry_a air 1 0 row +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 :=
      a_update_slot1_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextABitsWord air row 1) +
        next_carry_a air 1 1 row * (2 ^ 16 : ℕ) :=
      a_update_slot1_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 1) 1 +
        next_carry_a air 1 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextABitsWord air row 1)]

theorem a_update_slot2_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 1 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 1 +
      roundConstantPolyAtNext air row 2 1 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 1 =
    next_carry_a air 2 0 row +
      hi16Expr (rawConcatEBitsWord air row 2) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
      hi16FieldMajPolyWord
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3) +
      hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 1 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 5) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 5) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_fieldBigSigma0PolyWord_one, bitsU16Limb_fieldMajPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInA air row 2 1 +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 1 +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
        =
      next_carry_a air 2 0 row +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 1 +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 2 0 row +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 := by
          ac_rfl

theorem a_update_slot2_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 1 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 1 +
      roundConstantPolyAtNext air row 2 1 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 1 =
    bitsU16Limb (nextABitsWord air row 2) 1 +
      next_carry_a air 2 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 2 1 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 1 +
        roundConstantPolyAtNext air row 2 1 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 1 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 1 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)) 1
        =
      next_carry_a air 2 0 row +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 :=
      a_update_slot2_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextABitsWord air row 2) +
        next_carry_a air 2 1 row * (2 ^ 16 : ℕ) :=
      a_update_slot2_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 2) 1 +
        next_carry_a air 2 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextABitsWord air row 2)]

theorem a_update_slot3_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 1 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 1 +
      roundConstantPolyAtNext air row 3 1 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 1 =
    next_carry_a air 3 0 row +
      hi16Expr (rawConcatEBitsWord air row 3) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
      hi16FieldMajPolyWord
        (rawConcatABitsWord air row 6)
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4) +
      hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 1 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 6) :=
    rawConcatABits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 6) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 6) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_fieldBigSigma0PolyWord_one, bitsU16Limb_fieldMajPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInA air row 3 1 +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 1 +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
        =
      next_carry_a air 3 0 row +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 1 +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 3 0 row +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 := by
          ac_rfl

theorem a_update_slot3_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 1 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 1 +
      roundConstantPolyAtNext air row 3 1 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 1 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 1 =
    bitsU16Limb (nextABitsWord air row 3) 1 +
      next_carry_a air 3 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 3 1 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 1 +
        roundConstantPolyAtNext air row 3 1 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 1 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 1 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 6)
            (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)) 1
        =
      next_carry_a air 3 0 row +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        hi16FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 :=
      a_update_slot3_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextABitsWord air row 3) +
        next_carry_a air 3 1 row * (2 ^ 16 : ℕ) :=
      a_update_slot3_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 3) 1 +
        next_carry_a air 3 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextABitsWord air row 3)]

theorem a_update_slot0_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 0 1 row +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 =
      limb2Expr (nextABitsWord air row 0) +
        next_carry_a air 0 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 0 2 (by decide) (by decide)
  change
    next_carry_a air 0 1 row +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 -
          (limb2Expr (nextABitsWord air row 0) +
            next_carry_a air 0 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot1_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 1 1 row +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 =
      limb2Expr (nextABitsWord air row 1) +
        next_carry_a air 1 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 1 2 (by decide) (by decide)
  change
    next_carry_a air 1 1 row +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 -
          (limb2Expr (nextABitsWord air row 1) +
            next_carry_a air 1 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot2_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 2 1 row +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 =
      limb2Expr (nextABitsWord air row 2) +
        next_carry_a air 2 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 2 2 (by decide) (by decide)
  change
    next_carry_a air 2 1 row +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 -
          (limb2Expr (nextABitsWord air row 2) +
            next_carry_a air 2 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot3_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 3 1 row +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 =
      limb2Expr (nextABitsWord air row 3) +
        next_carry_a air 3 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 3 2 (by decide) (by decide)
  change
    next_carry_a air 3 1 row +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 -
          (limb2Expr (nextABitsWord air row 3) +
            next_carry_a air 3 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot0_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 2 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 2 +
      roundConstantPolyAtNext air row 0 2 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 2 =
    next_carry_a air 0 1 row +
      limb2Expr (rawConcatEBitsWord air row 0) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
      limb2FieldMajPolyWord
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2)
        (rawConcatABitsWord air row 1) +
      limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 2 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 1) :=
    rawConcatABits_boolean air row 1 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 3) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 3) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_fieldBigSigma0PolyWord_two, bitsU16Limb_fieldMajPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInA air row 0 2 +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 2 +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)
        =
      next_carry_a air 0 1 row +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 2 +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 0 1 row +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 := by
          ac_rfl

theorem a_update_slot0_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 2 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 2 +
      roundConstantPolyAtNext air row 0 2 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 2 =
    bitsU16Limb (nextABitsWord air row 0) 2 +
      next_carry_a air 0 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 0 2 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 2 +
        roundConstantPolyAtNext air row 0 2 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 2 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 2 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)
            (rawConcatABitsWord air row 1)) 2
        =
      next_carry_a air 0 1 row +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 :=
      a_update_slot0_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextABitsWord air row 0) +
        next_carry_a air 0 2 row * (2 ^ 16 : ℕ) :=
      a_update_slot0_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 0) 2 +
        next_carry_a air 0 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextABitsWord air row 0)]

theorem a_update_slot1_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 2 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 2 +
      roundConstantPolyAtNext air row 1 2 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 2 =
    next_carry_a air 1 1 row +
      limb2Expr (rawConcatEBitsWord air row 1) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
      limb2FieldMajPolyWord
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2) +
      limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 2 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 4) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 4) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_fieldBigSigma0PolyWord_two, bitsU16Limb_fieldMajPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInA air row 1 2 +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 2 +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
        =
      next_carry_a air 1 1 row +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 2 +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 1 1 row +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 := by
          ac_rfl

theorem a_update_slot1_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 2 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 2 +
      roundConstantPolyAtNext air row 1 2 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 2 =
    bitsU16Limb (nextABitsWord air row 1) 2 +
      next_carry_a air 1 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 1 2 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 2 +
        roundConstantPolyAtNext air row 1 2 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 2 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 2 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)) 2
        =
      next_carry_a air 1 1 row +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 :=
      a_update_slot1_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextABitsWord air row 1) +
        next_carry_a air 1 2 row * (2 ^ 16 : ℕ) :=
      a_update_slot1_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 1) 2 +
        next_carry_a air 1 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextABitsWord air row 1)]

theorem a_update_slot2_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 2 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 2 +
      roundConstantPolyAtNext air row 2 2 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 2 =
    next_carry_a air 2 1 row +
      limb2Expr (rawConcatEBitsWord air row 2) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
      limb2FieldMajPolyWord
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3) +
      limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 2 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 5) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 5) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_fieldBigSigma0PolyWord_two, bitsU16Limb_fieldMajPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInA air row 2 2 +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 2 +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
        =
      next_carry_a air 2 1 row +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 2 +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 2 1 row +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 := by
          ac_rfl

theorem a_update_slot2_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 2 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 2 +
      roundConstantPolyAtNext air row 2 2 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 2 =
    bitsU16Limb (nextABitsWord air row 2) 2 +
      next_carry_a air 2 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 2 2 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 2 +
        roundConstantPolyAtNext air row 2 2 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 2 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 2 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)) 2
        =
      next_carry_a air 2 1 row +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 :=
      a_update_slot2_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextABitsWord air row 2) +
        next_carry_a air 2 2 row * (2 ^ 16 : ℕ) :=
      a_update_slot2_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 2) 2 +
        next_carry_a air 2 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextABitsWord air row 2)]

theorem a_update_slot3_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 2 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 2 +
      roundConstantPolyAtNext air row 3 2 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 2 =
    next_carry_a air 3 1 row +
      limb2Expr (rawConcatEBitsWord air row 3) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
      limb2FieldMajPolyWord
        (rawConcatABitsWord air row 6)
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4) +
      limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 2 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 6) :=
    rawConcatABits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 6) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 6) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_fieldBigSigma0PolyWord_two, bitsU16Limb_fieldMajPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInA air row 3 2 +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 2 +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
        =
      next_carry_a air 3 1 row +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 2 +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 3 1 row +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 := by
          ac_rfl

theorem a_update_slot3_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 2 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 2 +
      roundConstantPolyAtNext air row 3 2 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 2 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 2 =
    bitsU16Limb (nextABitsWord air row 3) 2 +
      next_carry_a air 3 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 3 2 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 2 +
        roundConstantPolyAtNext air row 3 2 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 2 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 2 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 6)
            (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)) 2
        =
      next_carry_a air 3 1 row +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb2FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 :=
      a_update_slot3_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextABitsWord air row 3) +
        next_carry_a air 3 2 row * (2 ^ 16 : ℕ) :=
      a_update_slot3_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 3) 2 +
        next_carry_a air 3 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextABitsWord air row 3)]

theorem a_update_slot0_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 0 2 row +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 =
      limb3Expr (nextABitsWord air row 0) +
        next_carry_a air 0 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 0 3 (by decide) (by decide)
  change
    next_carry_a air 0 2 row +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 -
          (limb3Expr (nextABitsWord air row 0) +
            next_carry_a air 0 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot1_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 1 2 row +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 =
      limb3Expr (nextABitsWord air row 1) +
        next_carry_a air 1 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 1 3 (by decide) (by decide)
  change
    next_carry_a air 1 2 row +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 -
          (limb3Expr (nextABitsWord air row 1) +
            next_carry_a air 1 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot2_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 2 2 row +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 =
      limb3Expr (nextABitsWord air row 2) +
        next_carry_a air 2 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 2 3 (by decide) (by decide)
  change
    next_carry_a air 2 2 row +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 -
          (limb3Expr (nextABitsWord air row 2) +
            next_carry_a air 2 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot3_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_a air 3 2 row +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 =
      limb3Expr (nextABitsWord air row 3) +
        next_carry_a air 3 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_a_update_constraint_of_blockHasherConstraints air hc row 3 3 (by decide) (by decide)
  change
    next_carry_a air 3 2 row +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 -
          (limb3Expr (nextABitsWord air row 3) +
            next_carry_a air 3 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem a_update_slot0_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 3 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 3 +
      roundConstantPolyAtNext air row 0 3 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 3 =
    next_carry_a air 0 2 row +
      limb3Expr (rawConcatEBitsWord air row 0) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
      limb3FieldMajPolyWord
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2)
        (rawConcatABitsWord air row 1) +
      limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 3 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 1) :=
    rawConcatABits_boolean air row 1 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 3) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 3) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_fieldBigSigma0PolyWord_three, bitsU16Limb_fieldMajPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInA air row 0 3 +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 3 +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)
        =
      next_carry_a air 0 2 row +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 3 +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 0 2 row +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 := by
          ac_rfl

theorem a_update_slot0_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 0 3 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 3 +
      roundConstantPolyAtNext air row 0 3 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1)) 3 =
    bitsU16Limb (nextABitsWord air row 0) 3 +
      next_carry_a air 0 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 0 3 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 3 +
        roundConstantPolyAtNext air row 0 3 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 3 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 3)) 3 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)
            (rawConcatABitsWord air row 1)) 3
        =
      next_carry_a air 0 2 row +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 3) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
          (rawConcatABitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 :=
      a_update_slot0_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextABitsWord air row 0) +
        next_carry_a air 0 3 row * (2 ^ 16 : ℕ) :=
      a_update_slot0_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 0) 3 +
        next_carry_a air 0 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextABitsWord air row 0)]

theorem a_update_slot1_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 3 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 3 +
      roundConstantPolyAtNext air row 1 3 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 3 =
    next_carry_a air 1 2 row +
      limb3Expr (rawConcatEBitsWord air row 1) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
      limb3FieldMajPolyWord
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3)
        (rawConcatABitsWord air row 2) +
      limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 3 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 2) :=
    rawConcatABits_boolean air row 2 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 4) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 4) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_fieldBigSigma0PolyWord_three, bitsU16Limb_fieldMajPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInA air row 1 3 +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 3 +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)
        =
      next_carry_a air 1 2 row +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 3 +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 1 2 row +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 := by
          ac_rfl

theorem a_update_slot1_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 1 3 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 3 +
      roundConstantPolyAtNext air row 1 3 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2)) 3 =
    bitsU16Limb (nextABitsWord air row 1) 3 +
      next_carry_a air 1 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 1 3 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 3 +
        roundConstantPolyAtNext air row 1 3 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 3 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 4)) 3 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)
            (rawConcatABitsWord air row 2)) 3
        =
      next_carry_a air 1 2 row +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 4) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
          (rawConcatABitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 :=
      a_update_slot1_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextABitsWord air row 1) +
        next_carry_a air 1 3 row * (2 ^ 16 : ℕ) :=
      a_update_slot1_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 1) 3 +
        next_carry_a air 1 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextABitsWord air row 1)]

theorem a_update_slot2_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 3 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 3 +
      roundConstantPolyAtNext air row 2 3 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 3 =
    next_carry_a air 2 2 row +
      limb3Expr (rawConcatEBitsWord air row 2) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
      limb3FieldMajPolyWord
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4)
        (rawConcatABitsWord air row 3) +
      limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 3 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 3) :=
    rawConcatABits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 5) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 5) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_fieldBigSigma0PolyWord_three, bitsU16Limb_fieldMajPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInA air row 2 3 +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 3 +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)
        =
      next_carry_a air 2 2 row +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 3 +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 2 2 row +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 := by
          ac_rfl

theorem a_update_slot2_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 2 3 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 3 +
      roundConstantPolyAtNext air row 2 3 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3)) 3 =
    bitsU16Limb (nextABitsWord air row 2) 3 +
      next_carry_a air 2 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 2 3 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 3 +
        roundConstantPolyAtNext air row 2 3 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 3 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 5)) 3 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)
            (rawConcatABitsWord air row 3)) 3
        =
      next_carry_a air 2 2 row +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 5) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
          (rawConcatABitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 :=
      a_update_slot2_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextABitsWord air row 2) +
        next_carry_a air 2 3 row * (2 ^ 16 : ℕ) :=
      a_update_slot2_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 2) 3 +
        next_carry_a air 2 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextABitsWord air row 2)]

theorem a_update_slot3_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 3 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 3 +
      roundConstantPolyAtNext air row 3 3 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 3 =
    next_carry_a air 3 2 row +
      limb3Expr (rawConcatEBitsWord air row 3) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
      limb3FieldMajPolyWord
        (rawConcatABitsWord air row 6)
        (rawConcatABitsWord air row 5)
        (rawConcatABitsWord air row 4) +
      limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 3 := by
  have ha_bits : isBitsWord (rawConcatABitsWord air row 6) :=
    rawConcatABits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hb_bits : isBitsWord (rawConcatABitsWord air row 5) :=
    rawConcatABits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hc_bits : isBitsWord (rawConcatABitsWord air row 4) :=
    rawConcatABits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hsig0_poly :
      fieldBigSigma0 (rawConcatABitsWord air row 6) =
        fieldBigSigma0PolyWord (rawConcatABitsWord air row 6) :=
    fieldBigSigma0_eq_polyWord _
  have hmaj_poly_word :
      fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) =
        fieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) :=
    fieldMaj_eq_polyWord _ _ _ ha_bits hb_bits hc_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word, hsig0_poly, hmaj_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_fieldBigSigma0PolyWord_three, bitsU16Limb_fieldMajPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInA air row 3 3 +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 3 +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)
        =
      next_carry_a air 3 2 row +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 3 +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) := by
            simp [roundStepCarryInA]
    _ =
      next_carry_a air 3 2 row +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 := by
          ac_rfl

theorem a_update_slot3_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInA air row 3 3 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 3 +
      roundConstantPolyAtNext air row 3 3 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 3 +
      bitsU16Limb
        (fieldMaj (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4)) 3 =
    bitsU16Limb (nextABitsWord air row 3) 3 +
      next_carry_a air 3 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInA air row 3 3 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 3 +
        roundConstantPolyAtNext air row 3 3 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 3 * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row 6)) 3 +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row 6)
            (rawConcatABitsWord air row 5)
            (rawConcatABitsWord air row 4)) 3
        =
      next_carry_a air 3 2 row +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3FieldBigSigma0PolyWord (rawConcatABitsWord air row 6) +
        limb3FieldMajPolyWord
          (rawConcatABitsWord air row 6)
          (rawConcatABitsWord air row 5)
          (rawConcatABitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 :=
      a_update_slot3_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextABitsWord air row 3) +
        next_carry_a air 3 3 row * (2 ^ 16 : ℕ) :=
      a_update_slot3_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextABitsWord air row 3) 3 +
        next_carry_a air 3 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextABitsWord air row 3)]

theorem e_update_slot0_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatABitsWord air row 0) +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 =
      lo16Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 0 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatABitsWord air row 0) +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 -
          (lo16Expr (nextEBitsWord air row 0) +
            next_carry_e air 0 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot1_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatABitsWord air row 1) +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 =
      lo16Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 1 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatABitsWord air row 1) +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 -
          (lo16Expr (nextEBitsWord air row 1) +
            next_carry_e air 1 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot2_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatABitsWord air row 2) +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 =
      lo16Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 2 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatABitsWord air row 2) +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 -
          (lo16Expr (nextEBitsWord air row 2) +
            next_carry_e air 2 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot3_limb0_lo16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    lo16Expr (rawConcatABitsWord air row 3) +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 =
      lo16Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 0 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 3 0 (by decide) (by decide)
  change
    lo16Expr (rawConcatABitsWord air row 3) +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 -
          (lo16Expr (nextEBitsWord air row 3) +
            next_carry_e air 3 0 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot0_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 0 +
      bitsU16Limb (rawConcatABitsWord air row 0) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 0 +
      roundConstantPolyAtNext air row 0 0 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 0 * next_is_round_row air row =
    lo16Expr (rawConcatABitsWord air row 0) +
      lo16Expr (rawConcatEBitsWord air row 0) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 0 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatABitsWord air row 0),
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInE air row 0 0 +
        lo16Expr (rawConcatABitsWord air row 0) +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 0 +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 0) +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 0 +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      lo16Expr (rawConcatABitsWord air row 0) +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 := by
          ac_rfl

theorem e_update_slot0_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 0 +
      bitsU16Limb (rawConcatABitsWord air row 0) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 0 +
      roundConstantPolyAtNext air row 0 0 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 0 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 0) 0 +
      next_carry_e air 0 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 0 0 +
        bitsU16Limb (rawConcatABitsWord air row 0) 0 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 0 +
        roundConstantPolyAtNext air row 0 0 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 0 * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 0) +
        lo16Expr (rawConcatEBitsWord air row 0) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        lo16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 0 :=
      e_update_slot0_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 0 row * (2 ^ 16 : ℕ) :=
      e_update_slot0_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 0) 0 +
        next_carry_e air 0 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextEBitsWord air row 0)]

theorem e_update_slot1_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 0 +
      bitsU16Limb (rawConcatABitsWord air row 1) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 0 +
      roundConstantPolyAtNext air row 1 0 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 0 * next_is_round_row air row =
    lo16Expr (rawConcatABitsWord air row 1) +
      lo16Expr (rawConcatEBitsWord air row 1) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 0 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatABitsWord air row 1),
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInE air row 1 0 +
        lo16Expr (rawConcatABitsWord air row 1) +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 0 +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 1) +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 0 +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      lo16Expr (rawConcatABitsWord air row 1) +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 := by
          ac_rfl

theorem e_update_slot1_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 0 +
      bitsU16Limb (rawConcatABitsWord air row 1) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 0 +
      roundConstantPolyAtNext air row 1 0 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 0 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 1) 0 +
      next_carry_e air 1 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 1 0 +
        bitsU16Limb (rawConcatABitsWord air row 1) 0 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 0 +
        roundConstantPolyAtNext air row 1 0 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 0 * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 1) +
        lo16Expr (rawConcatEBitsWord air row 1) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        lo16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 0 :=
      e_update_slot1_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 0 row * (2 ^ 16 : ℕ) :=
      e_update_slot1_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 1) 0 +
        next_carry_e air 1 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextEBitsWord air row 1)]

theorem e_update_slot2_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 0 +
      bitsU16Limb (rawConcatABitsWord air row 2) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 0 +
      roundConstantPolyAtNext air row 2 0 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 0 * next_is_round_row air row =
    lo16Expr (rawConcatABitsWord air row 2) +
      lo16Expr (rawConcatEBitsWord air row 2) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 0 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatABitsWord air row 2),
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInE air row 2 0 +
        lo16Expr (rawConcatABitsWord air row 2) +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 0 +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 2) +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 0 +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      lo16Expr (rawConcatABitsWord air row 2) +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 := by
          ac_rfl

theorem e_update_slot2_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 0 +
      bitsU16Limb (rawConcatABitsWord air row 2) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 0 +
      roundConstantPolyAtNext air row 2 0 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 0 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 2) 0 +
      next_carry_e air 2 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 2 0 +
        bitsU16Limb (rawConcatABitsWord air row 2) 0 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 0 +
        roundConstantPolyAtNext air row 2 0 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 0 * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 2) +
        lo16Expr (rawConcatEBitsWord air row 2) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        lo16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 0 :=
      e_update_slot2_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 0 row * (2 ^ 16 : ℕ) :=
      e_update_slot2_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 2) 0 +
        next_carry_e air 2 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextEBitsWord air row 2)]

theorem e_update_slot3_limb0_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 0 +
      bitsU16Limb (rawConcatABitsWord air row 3) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 0 +
      roundConstantPolyAtNext air row 3 0 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 0 * next_is_round_row air row =
    lo16Expr (rawConcatABitsWord air row 3) +
      lo16Expr (rawConcatEBitsWord air row 3) +
      lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      lo16FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 0 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 0 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_zero, bitsU16Limb_fieldChPolyWord_zero,
    bitsU16Limb_zero_eq_lo16Expr (rawConcatABitsWord air row 3),
    bitsU16Limb_zero_eq_lo16Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_zero_eq_lo16Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInE air row 3 0 +
        lo16Expr (rawConcatABitsWord air row 3) +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 0 +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 3) +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 0 +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      lo16Expr (rawConcatABitsWord air row 3) +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 := by
          ac_rfl

theorem e_update_slot3_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 0 +
      bitsU16Limb (rawConcatABitsWord air row 3) 0 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 0 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 0 +
      roundConstantPolyAtNext air row 3 0 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 0 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 3) 0 +
      next_carry_e air 3 0 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 3 0 +
        bitsU16Limb (rawConcatABitsWord air row 3) 0 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 0 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 0 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 0 +
        roundConstantPolyAtNext air row 3 0 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 0 * next_is_round_row air row
        =
      lo16Expr (rawConcatABitsWord air row 3) +
        lo16Expr (rawConcatEBitsWord air row 3) +
        lo16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        lo16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        lo16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 0 :=
      e_update_slot3_limb0_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = lo16Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 0 row * (2 ^ 16 : ℕ) :=
      e_update_slot3_limb0_lo16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 3) 0 +
        next_carry_e air 3 0 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_zero_eq_lo16Expr (nextEBitsWord air row 3)]

theorem e_update_slot0_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 0 0 row +
        hi16Expr (rawConcatABitsWord air row 0) +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 =
      hi16Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 0 1 (by decide) (by decide)
  change
    next_carry_e air 0 0 row +
        hi16Expr (rawConcatABitsWord air row 0) +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 -
          (hi16Expr (nextEBitsWord air row 0) +
            next_carry_e air 0 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot1_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 1 0 row +
        hi16Expr (rawConcatABitsWord air row 1) +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 =
      hi16Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 1 1 (by decide) (by decide)
  change
    next_carry_e air 1 0 row +
        hi16Expr (rawConcatABitsWord air row 1) +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 -
          (hi16Expr (nextEBitsWord air row 1) +
            next_carry_e air 1 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot2_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 2 0 row +
        hi16Expr (rawConcatABitsWord air row 2) +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 =
      hi16Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 2 1 (by decide) (by decide)
  change
    next_carry_e air 2 0 row +
        hi16Expr (rawConcatABitsWord air row 2) +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 -
          (hi16Expr (nextEBitsWord air row 2) +
            next_carry_e air 2 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot3_limb1_hi16_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 3 0 row +
        hi16Expr (rawConcatABitsWord air row 3) +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 =
      hi16Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 1 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 3 1 (by decide) (by decide)
  change
    next_carry_e air 3 0 row +
        hi16Expr (rawConcatABitsWord air row 3) +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 -
          (hi16Expr (nextEBitsWord air row 3) +
            next_carry_e air 3 1 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot0_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 1 +
      bitsU16Limb (rawConcatABitsWord air row 0) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 1 +
      roundConstantPolyAtNext air row 0 1 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 1 * next_is_round_row air row =
    next_carry_e air 0 0 row +
      hi16Expr (rawConcatABitsWord air row 0) +
      hi16Expr (rawConcatEBitsWord air row 0) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 1 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatABitsWord air row 0),
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInE air row 0 1 +
        hi16Expr (rawConcatABitsWord air row 0) +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 1 +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row
        =
      next_carry_e air 0 0 row +
        hi16Expr (rawConcatABitsWord air row 0) +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 1 +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 0 0 row +
        hi16Expr (rawConcatABitsWord air row 0) +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 := by
          ac_rfl

theorem e_update_slot0_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 1 +
      bitsU16Limb (rawConcatABitsWord air row 0) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 1 +
      roundConstantPolyAtNext air row 0 1 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 1 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 0) 1 +
      next_carry_e air 0 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 0 1 +
        bitsU16Limb (rawConcatABitsWord air row 0) 1 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 1 +
        roundConstantPolyAtNext air row 0 1 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 1 * next_is_round_row air row
        =
      next_carry_e air 0 0 row +
        hi16Expr (rawConcatABitsWord air row 0) +
        hi16Expr (rawConcatEBitsWord air row 0) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 1 :=
      e_update_slot0_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 1 row * (2 ^ 16 : ℕ) :=
      e_update_slot0_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 0) 1 +
        next_carry_e air 0 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextEBitsWord air row 0)]

theorem e_update_slot1_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 1 +
      bitsU16Limb (rawConcatABitsWord air row 1) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 1 +
      roundConstantPolyAtNext air row 1 1 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 1 * next_is_round_row air row =
    next_carry_e air 1 0 row +
      hi16Expr (rawConcatABitsWord air row 1) +
      hi16Expr (rawConcatEBitsWord air row 1) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 1 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatABitsWord air row 1),
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInE air row 1 1 +
        hi16Expr (rawConcatABitsWord air row 1) +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 1 +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row
        =
      next_carry_e air 1 0 row +
        hi16Expr (rawConcatABitsWord air row 1) +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 1 +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 1 0 row +
        hi16Expr (rawConcatABitsWord air row 1) +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 := by
          ac_rfl

theorem e_update_slot1_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 1 +
      bitsU16Limb (rawConcatABitsWord air row 1) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 1 +
      roundConstantPolyAtNext air row 1 1 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 1 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 1) 1 +
      next_carry_e air 1 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 1 1 +
        bitsU16Limb (rawConcatABitsWord air row 1) 1 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 1 +
        roundConstantPolyAtNext air row 1 1 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 1 * next_is_round_row air row
        =
      next_carry_e air 1 0 row +
        hi16Expr (rawConcatABitsWord air row 1) +
        hi16Expr (rawConcatEBitsWord air row 1) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 1 :=
      e_update_slot1_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 1 row * (2 ^ 16 : ℕ) :=
      e_update_slot1_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 1) 1 +
        next_carry_e air 1 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextEBitsWord air row 1)]

theorem e_update_slot2_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 1 +
      bitsU16Limb (rawConcatABitsWord air row 2) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 1 +
      roundConstantPolyAtNext air row 2 1 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 1 * next_is_round_row air row =
    next_carry_e air 2 0 row +
      hi16Expr (rawConcatABitsWord air row 2) +
      hi16Expr (rawConcatEBitsWord air row 2) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 1 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatABitsWord air row 2),
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInE air row 2 1 +
        hi16Expr (rawConcatABitsWord air row 2) +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 1 +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row
        =
      next_carry_e air 2 0 row +
        hi16Expr (rawConcatABitsWord air row 2) +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 1 +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 2 0 row +
        hi16Expr (rawConcatABitsWord air row 2) +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 := by
          ac_rfl

theorem e_update_slot2_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 1 +
      bitsU16Limb (rawConcatABitsWord air row 2) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 1 +
      roundConstantPolyAtNext air row 2 1 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 1 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 2) 1 +
      next_carry_e air 2 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 2 1 +
        bitsU16Limb (rawConcatABitsWord air row 2) 1 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 1 +
        roundConstantPolyAtNext air row 2 1 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 1 * next_is_round_row air row
        =
      next_carry_e air 2 0 row +
        hi16Expr (rawConcatABitsWord air row 2) +
        hi16Expr (rawConcatEBitsWord air row 2) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 1 :=
      e_update_slot2_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 1 row * (2 ^ 16 : ℕ) :=
      e_update_slot2_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 2) 1 +
        next_carry_e air 2 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextEBitsWord air row 2)]

theorem e_update_slot3_limb1_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 1 +
      bitsU16Limb (rawConcatABitsWord air row 3) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 1 +
      roundConstantPolyAtNext air row 3 1 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 1 * next_is_round_row air row =
    next_carry_e air 3 0 row +
      hi16Expr (rawConcatABitsWord air row 3) +
      hi16Expr (rawConcatEBitsWord air row 3) +
      hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      hi16FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 1 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 1 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_one, bitsU16Limb_fieldChPolyWord_one,
    bitsU16Limb_one_eq_hi16Expr (rawConcatABitsWord air row 3),
    bitsU16Limb_one_eq_hi16Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_one_eq_hi16Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInE air row 3 1 +
        hi16Expr (rawConcatABitsWord air row 3) +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 1 +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row
        =
      next_carry_e air 3 0 row +
        hi16Expr (rawConcatABitsWord air row 3) +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 1 +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 3 0 row +
        hi16Expr (rawConcatABitsWord air row 3) +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 := by
          ac_rfl

theorem e_update_slot3_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 1 +
      bitsU16Limb (rawConcatABitsWord air row 3) 1 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 1 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 1 +
      roundConstantPolyAtNext air row 3 1 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 1 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 3) 1 +
      next_carry_e air 3 1 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 3 1 +
        bitsU16Limb (rawConcatABitsWord air row 3) 1 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 1 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 1 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 1 +
        roundConstantPolyAtNext air row 3 1 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 1 * next_is_round_row air row
        =
      next_carry_e air 3 0 row +
        hi16Expr (rawConcatABitsWord air row 3) +
        hi16Expr (rawConcatEBitsWord air row 3) +
        hi16FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        hi16FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 1 :=
      e_update_slot3_limb1_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = hi16Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 1 row * (2 ^ 16 : ℕ) :=
      e_update_slot3_limb1_hi16_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 3) 1 +
        next_carry_e air 3 1 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_one_eq_hi16Expr (nextEBitsWord air row 3)]

theorem e_update_slot0_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 0 1 row +
        limb2Expr (rawConcatABitsWord air row 0) +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 =
      limb2Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 0 2 (by decide) (by decide)
  change
    next_carry_e air 0 1 row +
        limb2Expr (rawConcatABitsWord air row 0) +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 -
          (limb2Expr (nextEBitsWord air row 0) +
            next_carry_e air 0 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot1_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 1 1 row +
        limb2Expr (rawConcatABitsWord air row 1) +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 =
      limb2Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 1 2 (by decide) (by decide)
  change
    next_carry_e air 1 1 row +
        limb2Expr (rawConcatABitsWord air row 1) +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 -
          (limb2Expr (nextEBitsWord air row 1) +
            next_carry_e air 1 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot2_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 2 1 row +
        limb2Expr (rawConcatABitsWord air row 2) +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 =
      limb2Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 2 2 (by decide) (by decide)
  change
    next_carry_e air 2 1 row +
        limb2Expr (rawConcatABitsWord air row 2) +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 -
          (limb2Expr (nextEBitsWord air row 2) +
            next_carry_e air 2 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot3_limb2_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 3 1 row +
        limb2Expr (rawConcatABitsWord air row 3) +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 =
      limb2Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 2 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 3 2 (by decide) (by decide)
  change
    next_carry_e air 3 1 row +
        limb2Expr (rawConcatABitsWord air row 3) +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 -
          (limb2Expr (nextEBitsWord air row 3) +
            next_carry_e air 3 2 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot0_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 2 +
      bitsU16Limb (rawConcatABitsWord air row 0) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 2 +
      roundConstantPolyAtNext air row 0 2 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 2 * next_is_round_row air row =
    next_carry_e air 0 1 row +
      limb2Expr (rawConcatABitsWord air row 0) +
      limb2Expr (rawConcatEBitsWord air row 0) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 2 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatABitsWord air row 0),
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInE air row 0 2 +
        limb2Expr (rawConcatABitsWord air row 0) +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 2 +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row
        =
      next_carry_e air 0 1 row +
        limb2Expr (rawConcatABitsWord air row 0) +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 2 +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 0 1 row +
        limb2Expr (rawConcatABitsWord air row 0) +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 := by
          ac_rfl

theorem e_update_slot0_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 2 +
      bitsU16Limb (rawConcatABitsWord air row 0) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 2 +
      roundConstantPolyAtNext air row 0 2 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 2 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 0) 2 +
      next_carry_e air 0 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 0 2 +
        bitsU16Limb (rawConcatABitsWord air row 0) 2 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 2 +
        roundConstantPolyAtNext air row 0 2 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 2 * next_is_round_row air row
        =
      next_carry_e air 0 1 row +
        limb2Expr (rawConcatABitsWord air row 0) +
        limb2Expr (rawConcatEBitsWord air row 0) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb2Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 2 :=
      e_update_slot0_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 2 row * (2 ^ 16 : ℕ) :=
      e_update_slot0_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 0) 2 +
        next_carry_e air 0 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextEBitsWord air row 0)]

theorem e_update_slot1_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 2 +
      bitsU16Limb (rawConcatABitsWord air row 1) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 2 +
      roundConstantPolyAtNext air row 1 2 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 2 * next_is_round_row air row =
    next_carry_e air 1 1 row +
      limb2Expr (rawConcatABitsWord air row 1) +
      limb2Expr (rawConcatEBitsWord air row 1) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 2 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatABitsWord air row 1),
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInE air row 1 2 +
        limb2Expr (rawConcatABitsWord air row 1) +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 2 +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row
        =
      next_carry_e air 1 1 row +
        limb2Expr (rawConcatABitsWord air row 1) +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 2 +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 1 1 row +
        limb2Expr (rawConcatABitsWord air row 1) +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 := by
          ac_rfl

theorem e_update_slot1_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 2 +
      bitsU16Limb (rawConcatABitsWord air row 1) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 2 +
      roundConstantPolyAtNext air row 1 2 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 2 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 1) 2 +
      next_carry_e air 1 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 1 2 +
        bitsU16Limb (rawConcatABitsWord air row 1) 2 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 2 +
        roundConstantPolyAtNext air row 1 2 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 2 * next_is_round_row air row
        =
      next_carry_e air 1 1 row +
        limb2Expr (rawConcatABitsWord air row 1) +
        limb2Expr (rawConcatEBitsWord air row 1) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb2Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 2 :=
      e_update_slot1_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 2 row * (2 ^ 16 : ℕ) :=
      e_update_slot1_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 1) 2 +
        next_carry_e air 1 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextEBitsWord air row 1)]

theorem e_update_slot2_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 2 +
      bitsU16Limb (rawConcatABitsWord air row 2) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 2 +
      roundConstantPolyAtNext air row 2 2 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 2 * next_is_round_row air row =
    next_carry_e air 2 1 row +
      limb2Expr (rawConcatABitsWord air row 2) +
      limb2Expr (rawConcatEBitsWord air row 2) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 2 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatABitsWord air row 2),
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInE air row 2 2 +
        limb2Expr (rawConcatABitsWord air row 2) +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 2 +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row
        =
      next_carry_e air 2 1 row +
        limb2Expr (rawConcatABitsWord air row 2) +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 2 +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 2 1 row +
        limb2Expr (rawConcatABitsWord air row 2) +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 := by
          ac_rfl

theorem e_update_slot2_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 2 +
      bitsU16Limb (rawConcatABitsWord air row 2) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 2 +
      roundConstantPolyAtNext air row 2 2 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 2 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 2) 2 +
      next_carry_e air 2 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 2 2 +
        bitsU16Limb (rawConcatABitsWord air row 2) 2 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 2 +
        roundConstantPolyAtNext air row 2 2 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 2 * next_is_round_row air row
        =
      next_carry_e air 2 1 row +
        limb2Expr (rawConcatABitsWord air row 2) +
        limb2Expr (rawConcatEBitsWord air row 2) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb2Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 2 :=
      e_update_slot2_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 2 row * (2 ^ 16 : ℕ) :=
      e_update_slot2_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 2) 2 +
        next_carry_e air 2 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextEBitsWord air row 2)]

theorem e_update_slot3_limb2_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 2 +
      bitsU16Limb (rawConcatABitsWord air row 3) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 2 +
      roundConstantPolyAtNext air row 3 2 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 2 * next_is_round_row air row =
    next_carry_e air 3 1 row +
      limb2Expr (rawConcatABitsWord air row 3) +
      limb2Expr (rawConcatEBitsWord air row 3) +
      limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      limb2FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 2 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 2 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_two, bitsU16Limb_fieldChPolyWord_two,
    bitsU16Limb_two_eq_limb2Expr (rawConcatABitsWord air row 3),
    bitsU16Limb_two_eq_limb2Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_two_eq_limb2Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInE air row 3 2 +
        limb2Expr (rawConcatABitsWord air row 3) +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 2 +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row
        =
      next_carry_e air 3 1 row +
        limb2Expr (rawConcatABitsWord air row 3) +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 2 +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 3 1 row +
        limb2Expr (rawConcatABitsWord air row 3) +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 := by
          ac_rfl

theorem e_update_slot3_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 2 +
      bitsU16Limb (rawConcatABitsWord air row 3) 2 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 2 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 2 +
      roundConstantPolyAtNext air row 3 2 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 2 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 3) 2 +
      next_carry_e air 3 2 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 3 2 +
        bitsU16Limb (rawConcatABitsWord air row 3) 2 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 2 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 2 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 2 +
        roundConstantPolyAtNext air row 3 2 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 2 * next_is_round_row air row
        =
      next_carry_e air 3 1 row +
        limb2Expr (rawConcatABitsWord air row 3) +
        limb2Expr (rawConcatEBitsWord air row 3) +
        limb2FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb2FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb2Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 2 :=
      e_update_slot3_limb2_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb2Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 2 row * (2 ^ 16 : ℕ) :=
      e_update_slot3_limb2_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 3) 2 +
        next_carry_e air 3 2 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_two_eq_limb2Expr (nextEBitsWord air row 3)]

theorem e_update_slot0_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 0 2 row +
        limb3Expr (rawConcatABitsWord air row 0) +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 =
      limb3Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 0 3 (by decide) (by decide)
  change
    next_carry_e air 0 2 row +
        limb3Expr (rawConcatABitsWord air row 0) +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 -
          (limb3Expr (nextEBitsWord air row 0) +
            next_carry_e air 0 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot1_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 1 2 row +
        limb3Expr (rawConcatABitsWord air row 1) +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 =
      limb3Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 1 3 (by decide) (by decide)
  change
    next_carry_e air 1 2 row +
        limb3Expr (rawConcatABitsWord air row 1) +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 -
          (limb3Expr (nextEBitsWord air row 1) +
            next_carry_e air 1 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot2_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 2 2 row +
        limb3Expr (rawConcatABitsWord air row 2) +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 =
      limb3Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 2 3 (by decide) (by decide)
  change
    next_carry_e air 2 2 row +
        limb3Expr (rawConcatABitsWord air row 2) +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 -
          (limb3Expr (nextEBitsWord air row 2) +
            next_carry_e air 2 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot3_limb3_exact_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    next_carry_e air 3 2 row +
        limb3Expr (rawConcatABitsWord air row 3) +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 =
      limb3Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 3 row * (2 ^ 16 : ℕ) := by
  have hraw :=
    raw_e_update_constraint_of_blockHasherConstraints air hc row 3 3 (by decide) (by decide)
  change
    next_carry_e air 3 2 row +
        limb3Expr (rawConcatABitsWord air row 3) +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 -
          (limb3Expr (nextEBitsWord air row 3) +
            next_carry_e air 3 3 row * (2 ^ 16 : ℕ)) = 0 at hraw
  exact sub_eq_zero.mp hraw

theorem e_update_slot0_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 3 +
      bitsU16Limb (rawConcatABitsWord air row 0) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 3 +
      roundConstantPolyAtNext air row 0 3 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 3 * next_is_round_row air row =
    next_carry_e air 0 2 row +
      limb3Expr (rawConcatABitsWord air row 0) +
      limb3Expr (rawConcatEBitsWord air row 0) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2)
        (rawConcatEBitsWord air row 1) +
      limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 0 3 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 3) :=
    rawConcatEBits_boolean air row 3 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 3) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 0 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatABitsWord air row 0),
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 0),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 0)]
  calc
    roundStepCarryInE air row 0 3 +
        limb3Expr (rawConcatABitsWord air row 0) +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 3 +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row
        =
      next_carry_e air 0 2 row +
        limb3Expr (rawConcatABitsWord air row 0) +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        roundConstantAirPolyAtNext air row 0 3 +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 0 2 row +
        limb3Expr (rawConcatABitsWord air row 0) +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 := by
          ac_rfl

theorem e_update_slot0_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 0 3 +
      bitsU16Limb (rawConcatABitsWord air row 0) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 0) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1)) 3 +
      roundConstantPolyAtNext air row 0 3 +
      bitsU16Limb (nextScheduleBitsWord air row 0) 3 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 0) 3 +
      next_carry_e air 0 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 0 3 +
        bitsU16Limb (rawConcatABitsWord air row 0) 3 +
        bitsU16Limb (rawConcatEBitsWord air row 0) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 3)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)
            (rawConcatEBitsWord air row 1)) 3 +
        roundConstantPolyAtNext air row 0 3 +
        bitsU16Limb (nextScheduleBitsWord air row 0) 3 * next_is_round_row air row
        =
      next_carry_e air 0 2 row +
        limb3Expr (rawConcatABitsWord air row 0) +
        limb3Expr (rawConcatEBitsWord air row 0) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 3) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)
          (rawConcatEBitsWord air row 1) +
        limb3Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 0 3 :=
      e_update_slot0_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextEBitsWord air row 0) +
        next_carry_e air 0 3 row * (2 ^ 16 : ℕ) :=
      e_update_slot0_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 0) 3 +
        next_carry_e air 0 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextEBitsWord air row 0)]

theorem e_update_slot1_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 3 +
      bitsU16Limb (rawConcatABitsWord air row 1) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 3 +
      roundConstantPolyAtNext air row 1 3 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 3 * next_is_round_row air row =
    next_carry_e air 1 2 row +
      limb3Expr (rawConcatABitsWord air row 1) +
      limb3Expr (rawConcatEBitsWord air row 1) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) +
      limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 1 3 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 4) :=
    rawConcatEBits_boolean air row 4 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 4) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 1 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatABitsWord air row 1),
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 1),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 1)]
  calc
    roundStepCarryInE air row 1 3 +
        limb3Expr (rawConcatABitsWord air row 1) +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 3 +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row
        =
      next_carry_e air 1 2 row +
        limb3Expr (rawConcatABitsWord air row 1) +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        roundConstantAirPolyAtNext air row 1 3 +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 1 2 row +
        limb3Expr (rawConcatABitsWord air row 1) +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 := by
          ac_rfl

theorem e_update_slot1_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 1 3 +
      bitsU16Limb (rawConcatABitsWord air row 1) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 1) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2)) 3 +
      roundConstantPolyAtNext air row 1 3 +
      bitsU16Limb (nextScheduleBitsWord air row 1) 3 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 1) 3 +
      next_carry_e air 1 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 1 3 +
        bitsU16Limb (rawConcatABitsWord air row 1) 3 +
        bitsU16Limb (rawConcatEBitsWord air row 1) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 4)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2)) 3 +
        roundConstantPolyAtNext air row 1 3 +
        bitsU16Limb (nextScheduleBitsWord air row 1) 3 * next_is_round_row air row
        =
      next_carry_e air 1 2 row +
        limb3Expr (rawConcatABitsWord air row 1) +
        limb3Expr (rawConcatEBitsWord air row 1) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 4) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)
          (rawConcatEBitsWord air row 2) +
        limb3Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 1 3 :=
      e_update_slot1_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextEBitsWord air row 1) +
        next_carry_e air 1 3 row * (2 ^ 16 : ℕ) :=
      e_update_slot1_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 1) 3 +
        next_carry_e air 1 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextEBitsWord air row 1)]

theorem e_update_slot2_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 3 +
      bitsU16Limb (rawConcatABitsWord air row 2) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 3 +
      roundConstantPolyAtNext air row 2 3 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 3 * next_is_round_row air row =
    next_carry_e air 2 2 row +
      limb3Expr (rawConcatABitsWord air row 2) +
      limb3Expr (rawConcatEBitsWord air row 2) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) +
      limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 2 3 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 5) :=
    rawConcatEBits_boolean air row 5 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 5) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 2 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatABitsWord air row 2),
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 2),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 2)]
  calc
    roundStepCarryInE air row 2 3 +
        limb3Expr (rawConcatABitsWord air row 2) +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 3 +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row
        =
      next_carry_e air 2 2 row +
        limb3Expr (rawConcatABitsWord air row 2) +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        roundConstantAirPolyAtNext air row 2 3 +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 2 2 row +
        limb3Expr (rawConcatABitsWord air row 2) +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 := by
          ac_rfl

theorem e_update_slot2_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 2 3 +
      bitsU16Limb (rawConcatABitsWord air row 2) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 2) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3)) 3 +
      roundConstantPolyAtNext air row 2 3 +
      bitsU16Limb (nextScheduleBitsWord air row 2) 3 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 2) 3 +
      next_carry_e air 2 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 2 3 +
        bitsU16Limb (rawConcatABitsWord air row 2) 3 +
        bitsU16Limb (rawConcatEBitsWord air row 2) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 5)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3)) 3 +
        roundConstantPolyAtNext air row 2 3 +
        bitsU16Limb (nextScheduleBitsWord air row 2) 3 * next_is_round_row air row
        =
      next_carry_e air 2 2 row +
        limb3Expr (rawConcatABitsWord air row 2) +
        limb3Expr (rawConcatEBitsWord air row 2) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 5) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)
          (rawConcatEBitsWord air row 3) +
        limb3Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 2 3 :=
      e_update_slot2_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextEBitsWord air row 2) +
        next_carry_e air 2 3 row * (2 ^ 16 : ℕ) :=
      e_update_slot2_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 2) 3 +
        next_carry_e air 2 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextEBitsWord air row 2)]

theorem e_update_slot3_limb3_lhs_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 3 +
      bitsU16Limb (rawConcatABitsWord air row 3) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 3 +
      roundConstantPolyAtNext air row 3 3 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 3 * next_is_round_row air row =
    next_carry_e air 3 2 row +
      limb3Expr (rawConcatABitsWord air row 3) +
      limb3Expr (rawConcatEBitsWord air row 3) +
      limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
      limb3FieldChPolyWord
        (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) +
      limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
      roundConstantAirPolyAtNext air row 3 3 := by
  have he_bits : isBitsWord (rawConcatEBitsWord air row 6) :=
    rawConcatEBits_boolean air row 6 (by decide) hrow hrot hbb hbb_next
  have hsig1_poly :
      fieldBigSigma1 (rawConcatEBitsWord air row 6) =
        fieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) :=
    fieldBigSigma1_eq_polyWord _
  have hch_poly_word :
      fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) =
        fieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) :=
    fieldCh_eq_polyWord _ _ _ he_bits
  have hflags_next : flag_constraints air (nextRow air row) :=
    (hc (nextRow air row)).1
  rw [roundConstantPolyAtNext_eq_airPolyAtNext air row 3 3 (by decide) (by decide)
      hrow hrot hflags_next]
  rw [hsig1_poly, hch_poly_word]
  rw [bitsU16Limb_fieldBigSigma1PolyWord_three, bitsU16Limb_fieldChPolyWord_three,
    bitsU16Limb_three_eq_limb3Expr (rawConcatABitsWord air row 3),
    bitsU16Limb_three_eq_limb3Expr (rawConcatEBitsWord air row 3),
    bitsU16Limb_three_eq_limb3Expr (nextScheduleBitsWord air row 3)]
  calc
    roundStepCarryInE air row 3 3 +
        limb3Expr (rawConcatABitsWord air row 3) +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 3 +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row
        =
      next_carry_e air 3 2 row +
        limb3Expr (rawConcatABitsWord air row 3) +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        roundConstantAirPolyAtNext air row 3 3 +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row := by
          simp [roundStepCarryInE]
    _ =
      next_carry_e air 3 2 row +
        limb3Expr (rawConcatABitsWord air row 3) +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 := by
          ac_rfl

theorem e_update_slot3_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    roundStepCarryInE air row 3 3 +
      bitsU16Limb (rawConcatABitsWord air row 3) 3 +
      bitsU16Limb (rawConcatEBitsWord air row 3) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 3 +
      bitsU16Limb
        (fieldCh (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4)) 3 +
      roundConstantPolyAtNext air row 3 3 +
      bitsU16Limb (nextScheduleBitsWord air row 3) 3 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row 3) 3 +
      next_carry_e air 3 3 row * (2 ^ 16 : ℕ) := by
  calc
    roundStepCarryInE air row 3 3 +
        bitsU16Limb (rawConcatABitsWord air row 3) 3 +
        bitsU16Limb (rawConcatEBitsWord air row 3) 3 +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row 6)) 3 +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4)) 3 +
        roundConstantPolyAtNext air row 3 3 +
        bitsU16Limb (nextScheduleBitsWord air row 3) 3 * next_is_round_row air row
        =
      next_carry_e air 3 2 row +
        limb3Expr (rawConcatABitsWord air row 3) +
        limb3Expr (rawConcatEBitsWord air row 3) +
        limb3FieldBigSigma1PolyWord (rawConcatEBitsWord air row 6) +
        limb3FieldChPolyWord
          (rawConcatEBitsWord air row 6)
          (rawConcatEBitsWord air row 5)
          (rawConcatEBitsWord air row 4) +
        limb3Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
        roundConstantAirPolyAtNext air row 3 3 :=
      e_update_slot3_limb3_lhs_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
    _ = limb3Expr (nextEBitsWord air row 3) +
        next_carry_e air 3 3 row * (2 ^ 16 : ℕ) :=
      e_update_slot3_limb3_exact_eq_of_blockHasherConstraints air hc row
    _ = bitsU16Limb (nextEBitsWord air row 3) 3 +
        next_carry_e air 3 3 row * (2 ^ 16 : ℕ) := by
          rw [← bitsU16Limb_three_eq_limb3Expr (nextEBitsWord air row 3)]

private theorem a_update_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInA air row slot 0 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 0 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 0 +
      roundConstantPolyAtNext air row slot 0 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 0 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) 0 +
      bitsU16Limb (fieldMaj (rawConcatABitsWord air row (slot + 3))
          (rawConcatABitsWord air row (slot + 2))
          (rawConcatABitsWord air row (slot + 1))) 0 =
    bitsU16Limb (nextABitsWord air row slot) 0 +
      next_carry_a air slot 0 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact a_update_slot0_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot1_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot2_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot3_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

private theorem a_update_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInA air row slot 1 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 1 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 1 +
      roundConstantPolyAtNext air row slot 1 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 1 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) 1 +
      bitsU16Limb (fieldMaj (rawConcatABitsWord air row (slot + 3))
          (rawConcatABitsWord air row (slot + 2))
          (rawConcatABitsWord air row (slot + 1))) 1 =
    bitsU16Limb (nextABitsWord air row slot) 1 +
      next_carry_a air slot 1 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact a_update_slot0_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot1_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot2_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot3_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

private theorem a_update_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInA air row slot 2 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 2 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 2 +
      roundConstantPolyAtNext air row slot 2 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 2 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) 2 +
      bitsU16Limb (fieldMaj (rawConcatABitsWord air row (slot + 3))
          (rawConcatABitsWord air row (slot + 2))
          (rawConcatABitsWord air row (slot + 1))) 2 =
    bitsU16Limb (nextABitsWord air row slot) 2 +
      next_carry_a air slot 2 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact a_update_slot0_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot1_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot2_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot3_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

private theorem a_update_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInA air row slot 3 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 3 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 3 +
      roundConstantPolyAtNext air row slot 3 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 3 * next_is_round_row air row +
      bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) 3 +
      bitsU16Limb (fieldMaj (rawConcatABitsWord air row (slot + 3))
          (rawConcatABitsWord air row (slot + 2))
          (rawConcatABitsWord air row (slot + 1))) 3 =
    bitsU16Limb (nextABitsWord air row slot) 3 +
      next_carry_a air slot 3 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact a_update_slot0_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot1_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot2_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact a_update_slot3_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

theorem a_update_limb_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    ∀ (slot limb : ℕ) (hslot : slot < 4) (hlimb : limb < 4),
      roundStepCarryInA air row slot limb +
        bitsU16Limb (rawConcatEBitsWord air row slot) limb +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) limb +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row (slot + 3))
            (rawConcatEBitsWord air row (slot + 2))
            (rawConcatEBitsWord air row (slot + 1))) limb +
        roundConstantPolyAtNext air row slot limb +
        bitsU16Limb (nextScheduleBitsWord air row slot) limb * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) limb +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row (slot + 3))
            (rawConcatABitsWord air row (slot + 2))
            (rawConcatABitsWord air row (slot + 1))) limb =
      bitsU16Limb (nextABitsWord air row slot) limb +
        next_carry_a air slot limb row * (2 ^ 16 : ℕ) := by
  intro slot limb hslot hlimb
  have hl : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hl with rfl | rfl | rfl | rfl
  · exact a_update_limb0_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot
  · exact a_update_limb1_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot
  · exact a_update_limb2_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot
  · exact a_update_limb3_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot

private theorem e_update_limb0_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInE air row slot 0 +
      bitsU16Limb (rawConcatABitsWord air row slot) 0 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 0 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 0 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 0 +
      roundConstantPolyAtNext air row slot 0 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 0 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row slot) 0 +
      next_carry_e air slot 0 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact e_update_slot0_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot1_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot2_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot3_limb0_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

private theorem e_update_limb1_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInE air row slot 1 +
      bitsU16Limb (rawConcatABitsWord air row slot) 1 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 1 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 1 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 1 +
      roundConstantPolyAtNext air row slot 1 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 1 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row slot) 1 +
      next_carry_e air slot 1 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact e_update_slot0_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot1_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot2_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot3_limb1_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

private theorem e_update_limb2_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInE air row slot 2 +
      bitsU16Limb (rawConcatABitsWord air row slot) 2 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 2 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 2 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 2 +
      roundConstantPolyAtNext air row slot 2 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 2 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row slot) 2 +
      next_carry_e air slot 2 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact e_update_slot0_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot1_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot2_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot3_limb2_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

private theorem e_update_limb3_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row slot : ℕ)
    (hrow : row ≤ Circuit.last_row air) (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hslot : slot < 4) :
    roundStepCarryInE air row slot 3 +
      bitsU16Limb (rawConcatABitsWord air row slot) 3 +
      bitsU16Limb (rawConcatEBitsWord air row slot) 3 +
      bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) 3 +
      bitsU16Limb (fieldCh (rawConcatEBitsWord air row (slot + 3))
          (rawConcatEBitsWord air row (slot + 2))
          (rawConcatEBitsWord air row (slot + 1))) 3 +
      roundConstantPolyAtNext air row slot 3 +
      bitsU16Limb (nextScheduleBitsWord air row slot) 3 * next_is_round_row air row =
    bitsU16Limb (nextEBitsWord air row slot) 3 +
      next_carry_e air slot 3 row * (2 ^ 16 : ℕ) := by
  have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl
  · exact e_update_slot0_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot1_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot2_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_slot3_limb3_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

theorem e_update_limb_eq_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    ∀ (slot limb : ℕ) (hslot : slot < 4) (hlimb : limb < 4),
      roundStepCarryInE air row slot limb +
        bitsU16Limb (rawConcatABitsWord air row slot) limb +
        bitsU16Limb (rawConcatEBitsWord air row slot) limb +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) limb +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row (slot + 3))
            (rawConcatEBitsWord air row (slot + 2))
            (rawConcatEBitsWord air row (slot + 1))) limb +
      roundConstantPolyAtNext air row slot limb +
      bitsU16Limb (nextScheduleBitsWord air row slot) limb * next_is_round_row air row =
      bitsU16Limb (nextEBitsWord air row slot) limb +
        next_carry_e air slot limb row * (2 ^ 16 : ℕ) := by
  intro slot limb hslot hlimb
  have hl : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hl with rfl | rfl | rfl | rfl
  · exact e_update_limb0_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot
  · exact e_update_limb1_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot
  · exact e_update_limb2_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot
  · exact e_update_limb3_eq_of_blockHasherConstraints air hc row slot hrow hrot hbb hbb_next hslot

theorem round_step_constraints_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    round_step_constraints air row := by
  refine { a_update_limb_eq := ?_, e_update_limb_eq := ?_ }
  · exact a_update_limb_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next
  · exact e_update_limb_eq_of_blockHasherConstraints air hc row hrow hrot hbb hbb_next

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
