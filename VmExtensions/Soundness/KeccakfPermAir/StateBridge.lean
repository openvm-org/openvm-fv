/-
  State representation bridge: connects lane-level State views
  (rowInputState, rowOutputState) to byte-level SpongeState views
  (decodeBusState) via the intermediate UInt16 limb representation.

  Pre-state and post-state decode equality.
  These lemmas are purely representation-level — no constraint or step-flag
  dependencies.
-/
import VmExtensions.Soundness.KeccakfPermAir.LimbRepr
import VmExtensions.Soundness.Keccakf.Interface
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface
import VmExtensions.Airs.KeccakfPermAirViews
import VmExtensions.Keccak.Spec.Permutation
import Std.Tactic.BVDecide

set_option autoImplicit false

namespace KeccakfPermAir.Soundness.StateBridge

open KeccakfPermAir.constraints
open KeccakfPermAir.Soundness
open Keccakf.Interface
open Keccak
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## Core bitvector identity

Byte extraction from a lane built by `limbs4ToU64` matches per-limb
lo/hi byte extraction. The lane packs 4 little-endian u16 limbs into u64.
Byte `2m` of the lane is the low byte of limb `m`; byte `2m+1` is the high byte.
-/

-- Out-of-range getLsbD is false (kernel-checked, no bv_decide).
private theorem bitVec_getLsbD_ge {w : Nat} (b : BitVec w) {i : Nat} (h : w ≤ i) :
    b.getLsbD i = false := by
  unfold BitVec.getLsbD
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) h))

-- Specialized: for BitVec 16, positions ≥ 16 give false.
-- simp can discharge the `16 ≤ i` condition via omega when i is concrete or bounded.
private theorem bv16_getLsbD_ge (b : BitVec 16) (i : Nat) (h : 16 ≤ i) :
    b.getLsbD i = false := bitVec_getLsbD_ge b h

-- Bridge: UInt64.ofNat to BitVec (UInt64.toBitVec_ofNat only matches OfNat.ofNat).
private theorem UInt64_ofNat_toBitVec (n : Nat) :
    (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := rfl
-- Bridge: UInt16 literal to BitVec for shift amounts on RHS.
private theorem UInt16_ofNat_toBitVec (n : Nat) :
    (UInt16.ofNat n).toBitVec = BitVec.ofNat 16 n := rfl

-- Byte b of limbs4ToU64 l0 l1 l2 l3 matches lo/hi byte of the appropriate limb.
-- Kernel-checked proof: per-bit equality via getLsbD + omega on index arithmetic.
-- No bv_decide — avoids Lean.ofReduceBool/Lean.trustCompiler axioms.
set_option maxHeartbeats 3200000 in
private theorem laneGetByte_limbs4ToU64 (l0 l1 l2 l3 : UInt16) (b : Fin 8) :
    laneGetByte (limbs4ToU64 l0 l1 l2 l3) b =
      (let limb := if b.val < 2 then l0
                   else if b.val < 4 then l1
                   else if b.val < 6 then l2
                   else l3
       if b.val % 2 = 0 then UInt16.loByte limb else UInt16.hiByte limb) := by
  fin_cases b <;>
    simp only [laneGetByte, limbs4ToU64, UInt16.loByte, UInt16.hiByte,
               Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, ↓reduceIte,
               Nat.toUInt64, show (1 : Nat) ≠ 0 from by omega] <;>
    (apply UInt8.eq_of_toBitVec_eq
     -- Step A: Normalize UInt operations to BitVec
     simp only [UInt64.toBitVec_toUInt8, UInt16.toBitVec_toUInt8,
                UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
                UInt64.toBitVec_shiftLeft, UInt16.toBitVec_toUInt64,
                UInt16.toBitVec_shiftRight,
                UInt64_ofNat_toBitVec,
                BitVec.ofNat_eq_ofNat, BitVec.reduceMod]
     -- Step B: Reduce remaining UInt64/16.toBitVec literals + convert BitVec shifts to Nat shifts
     simp only [UInt64.toBitVec_ofNat, UInt16.toBitVec_ofNat,
                BitVec.reduceMod,
                show ∀ (x y : BitVec 64), x >>> y = x >>> y.toNat from fun _ _ => rfl,
                show ∀ (x y : BitVec 64), x <<< y = x <<< y.toNat from fun _ _ => rfl,
                show ∀ (x y : BitVec 16), x >>> y = x >>> y.toNat from fun _ _ => rfl,
                BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
     -- Step C: Per-bit equality
     apply BitVec.eq_of_getLsbD_eq; intro i hi
     simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
                BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
     -- Reduce decide comparisons and out-of-range getLsbD.
     -- For BitVec 16, getLsbD at positions ≥ 16 is false.
     -- Provide explicit instances for all out-of-range positions that appear.
     have oor := fun (b : BitVec 16) (k : Nat) (h : 16 ≤ k) => bitVec_getLsbD_ge b h
     simp only [oor _ _ (by omega : 16 ≤ 16 + i), oor _ _ (by omega : 16 ≤ 24 + i),
       oor _ _ (by omega : 16 ≤ 32 + i), oor _ _ (by omega : 16 ≤ 40 + i),
       oor _ _ (by omega : 16 ≤ 48 + i), oor _ _ (by omega : 16 ≤ 56 + i),
       oor _ _ (by omega : 16 ≤ 32 + i - 16), oor _ _ (by omega : 16 ≤ 40 + i - 16),
       oor _ _ (by omega : 16 ≤ 48 + i - 16), oor _ _ (by omega : 16 ≤ 56 + i - 16),
       oor _ _ (by omega : 16 ≤ 48 + i - 32), oor _ _ (by omega : 16 ≤ 56 + i - 32),
       show i < 16 from by omega, show i < 32 from by omega,
       show i < 48 from by omega, show i < 64 from by omega,
       show 8 + i < 16 from by omega, show 8 + i < 32 from by omega,
       show 8 + i < 48 from by omega, show 8 + i < 64 from by omega,
       show ¬(16 + i < 16) from by omega, show 16 + i < 32 from by omega,
       show 16 + i < 48 from by omega, show 16 + i < 64 from by omega,
       show ¬(24 + i < 16) from by omega, show 24 + i < 32 from by omega,
       show 24 + i < 48 from by omega, show 24 + i < 64 from by omega,
       show ¬(32 + i < 16) from by omega, show ¬(32 + i < 32) from by omega,
       show 32 + i < 48 from by omega, show 32 + i < 64 from by omega,
       show ¬(40 + i < 16) from by omega, show ¬(40 + i < 32) from by omega,
       show 40 + i < 48 from by omega, show 40 + i < 64 from by omega,
       show ¬(48 + i < 16) from by omega, show ¬(48 + i < 32) from by omega,
       show ¬(48 + i < 48) from by omega, show 48 + i < 64 from by omega,
       show ¬(56 + i < 16) from by omega, show ¬(56 + i < 32) from by omega,
       show ¬(56 + i < 48) from by omega, show 56 + i < 64 from by omega,
       show 0 + i = i from by omega, show 16 + i - 16 = i from by omega,
       show 32 + i - 32 = i from by omega, show 48 + i - 48 = i from by omega,
       show 24 + i - 16 = 8 + i from by omega,
       show 40 + i - 32 = 8 + i from by omega, show 56 + i - 48 = 8 + i from by omega,
       hi, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false,
       Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or])

/-! ## Main representation bridge

The two byte-level decoding paths agree: extracting lo/hi bytes from each u16
limb (decodeBusState) equals packing 4 limbs into u64 lanes then extracting
bytes (stateToSponge).
-/

-- The canonical bridge: decodeBusState of a limb vector equals stateToSponge
-- of the State built from those same limbs via limbs4ToU64.
set_option maxHeartbeats 1600000 in
theorem decodeBusState_eq_stateToSponge_ofLimbs (f : Fin 100 → UInt16) :
    decodeBusState (Vector.ofFn f) =
    stateToSponge ⟨Array.ofFn (fun (i : Fin 25) =>
      limbs4ToU64 (f ⟨4 * i.val, by omega⟩) (f ⟨4 * i.val + 1, by omega⟩)
                  (f ⟨4 * i.val + 2, by omega⟩) (f ⟨4 * i.val + 3, by omega⟩)),
      by simp⟩ := by
  apply Subtype.ext
  simp only [decodeBusState, stateToSponge, ByteArray.mk.injEq]
  apply Array.ext
  · simp
  · intro j h₁ h₂
    simp only [Array.size_ofFn] at h₁
    simp only [Array.getElem_ofFn, Vector.getElem_ofFn]
    -- Reduce the Arr25 subscript: State.getElem unfolds via .val subscript
    show _ = laneGetByte ((Array.ofFn _)[j / 8]'(by simp; omega)) ⟨j % 8, by omega⟩
    simp only [Array.getElem_ofFn]
    -- Apply the core BV identity to the RHS
    rw [laneGetByte_limbs4ToU64]
    simp only [Fin.val_mk]
    -- The selected limb equals f[j/2], and (j%8)%2 = j%2
    suffices h_limb :
        (if j % 8 < 2 then f ⟨4 * (j / 8), by omega⟩
         else if j % 8 < 4 then f ⟨4 * (j / 8) + 1, by omega⟩
         else if j % 8 < 6 then f ⟨4 * (j / 8) + 2, by omega⟩
         else f ⟨4 * (j / 8) + 3, by omega⟩) = f ⟨j / 2, by omega⟩ by
      rw [h_limb, show j % 8 % 2 = j % 2 from by omega]
    split_ifs <;> (apply congrArg f; apply Fin.ext; simp only [Fin.val_mk]; omega)

/-! ## Pre-state bridge

Under preimage persistence, the bus pre-state payload decodes to the same
SpongeState as stateToSponge of the row's input state.
-/

-- fieldToU16 is definitionally UInt16.ofNat ∘ ZMod.val
private theorem fieldToU16_eq_ofNat (x : FBB) :
    fieldToU16 x = UInt16.ofNat x.val := rfl

/-! ## Row-Indexed State Bridges -/

-- Row-indexed pre-state bridge: decodeBusState(rowPreMsg.state) = stateToSponge(rowInputState startRow)
-- under preimage persistence (preimage columns at exportRow = a columns at startRow).
set_option maxHeartbeats 800000 in
theorem pre_state_bridge_row
    (air : Valid_KeccakfPermAir FBB ExtF) {startRow exportRow : ℕ}
    (h_persist : ∀ i, i < 100 →
      preimage air i exportRow = a air i startRow) :
    decodeBusState (rowPreMsg air exportRow).state =
      stateToSponge (rowInputState air startRow) := by
  have h_state : (rowPreMsg air exportRow).state =
      Vector.ofFn (fun k : Fin 100 => fieldToU16 (a air k.val startRow)) := by
    refine Vector.ext (fun i hi => ?_)
    simp only [rowPreMsg, Vector.getElem_ofFn, fieldToU16_eq_ofNat]
    rw [h_persist i (by omega)]
  rw [h_state, decodeBusState_eq_stateToSponge_ofLimbs]
  rfl

-- Row-indexed post-state bridge: decodeBusState(rowPostMsg.state) = stateToSponge(rowOutputState row)
-- No extra hypotheses needed: both sides use the same output columns at the same row.
set_option maxHeartbeats 800000 in
theorem post_state_bridge_row
    (air : Valid_KeccakfPermAir FBB ExtF) {row : ℕ} :
    decodeBusState (rowPostMsg air row).state =
      stateToSponge (rowOutputState air row) := by
  set g : Fin 100 → UInt16 := fun k =>
    fieldToU16 (if k.val < 4
      then a_ppp_00_limb air k.val row
      else a_prime_prime air k.val row)
  have h_state : (rowPostMsg air row).state = Vector.ofFn g := by
    refine Vector.ext (fun i hi => ?_)
    simp only [rowPostMsg, Vector.getElem_ofFn, g, fieldToU16_eq_ofNat]
    split_ifs <;> rfl
  rw [h_state, decodeBusState_eq_stateToSponge_ofLimbs]
  congr 1

/-! ## Block-Indexed Wrappers -/

-- Block-indexed pre-state bridge: thin wrapper over pre_state_bridge_row.
set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem pre_state_bridge
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ)
    (h_persist : ∀ i, i < 100 →
      preimage air i (air.blockExportRow block) = a air i (air.blockStartRow block)) :
    decodeBusState (blockPreMsg air block).state =
      stateToSponge (rowInputState air (air.blockStartRow block)) :=
  pre_state_bridge_row air h_persist

-- Block-indexed post-state bridge: thin wrapper over post_state_bridge_row.
-- Uses explicit rw to avoid expensive term-mode definitional unification.
set_option maxHeartbeats 800000 in
theorem post_state_bridge
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
    decodeBusState (blockPostMsg air block).state =
      stateToSponge (rowOutputState air (air.blockExportRow block)) := by
  rw [blockPostMsg_eq_rowPostMsg]
  exact post_state_bridge_row air

end KeccakfPermAir.Soundness.StateBridge
