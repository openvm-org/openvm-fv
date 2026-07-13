/-
  Chi helpers: field↔bool bridges, column mapping, roundtrip lemmas,
  and per-bit extraction infrastructure for the chi-preiota proof.

  The public façade is `ChiFacts.lean`; this file provides the building blocks.
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.ThetaAPrime
import VmExtensions.Soundness.KeccakfPermAir.Round.ChiIdx
import VmExtensions.Soundness.KeccakfPermAir.StepLimbs

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open KeccakfPermAir.StepLimbs
open Keccak

/-! ## Field↔Bool bridge for the chi polynomial

The chi field polynomial is `ch(a,b,d) = a + d - b*d - 2*a*d + 2*a*b*d`.
For boolean inputs this equals `a XOR ((NOT b) AND d)`. -/

-- The chi polynomial of three boolean field elements is boolean.
theorem chi_field_is_bool {a b d : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hd : d = 0 ∨ d = 1) :
    a + d - b * d - 2 * a * d + 2 * a * b * d = 0 ∨
    a + d - b * d - 2 * a * d + 2 * a * b * d = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp <;> decide

/-- `fbbToBool` maps the chi polynomial to `a XOR ((NOT b) AND d)` when
    inputs are boolean (8-case split + decide). -/
theorem fbbToBool_chi {a b d : FBB}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hd : d = 0 ∨ d = 1) :
    fbbToBool (a + d - b * d - 2 * a * d + 2 * a * b * d) =
    (fbbToBool a ^^ (!(fbbToBool b) && fbbToBool d)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp [fbbToBool] <;> decide

/-! ## ρπ column mapping

`chiAPrimeIdx n j inp` computes the a_prime_bit index for chi constraint `n`
(0–99), bit position `j` (0–15), and chi input `inp` (0=a, 1=b, 2=d).
The formula encodes the ρπ permutation baked into the AIR's column wiring. -/

-- Rotation values as a match-based function (reduces cleanly via decide).
@[reducible] def rotNat : Nat → Nat
  | 0 => 0 | 1 => 63 | 2 => 2 | 3 => 36 | 4 => 37
  | 5 => 28 | 6 => 20 | 7 => 58 | 8 => 9 | 9 => 44
  | 10 => 61 | 11 => 54 | 12 => 21 | 13 => 39 | 14 => 25
  | 15 => 23 | 16 => 19 | 17 => 49 | 18 => 43 | 19 => 56
  | 20 => 46 | 21 => 62 | 22 => 3 | 23 => 8 | 24 => 50
  | _ => 0

abbrev chiAPrimeIdx (n j inp : Nat) : Nat :=
  let lane := n / 4
  let limb := n % 4
  let x_out := lane % 5
  let y_out := lane / 5
  let x_in := (x_out + inp) % 5
  let sx := (x_in + 3 * y_out) % 5
  let sy := x_in
  let flat := 5 * sy + sx
  let rot := rotNat flat
  let k := 16 * limb + j
  320 * sy + 64 * sx + (k + rot) % 64

/-! ## Canonical chi constraint using chiIdx (kernel-reducible) -/

abbrev chiCanonicalK
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (n : Nat) (row : Nat) : Prop :=
  let ab (j : Nat) := a_prime_bit air (chiIdx n j 0) row
  let bb (j : Nat) := a_prime_bit air (chiIdx n j 1) row
  let db (j : Nat) := a_prime_bit air (chiIdx n j 2) row
  let ch (a b d : FBB) := a + d - b * d - 2 * a * d + 2 * a * b * d
  (ch (ab 0) (bb 0) (db 0) + 2 * ch (ab 1) (bb 1) (db 1) +
   4 * ch (ab 2) (bb 2) (db 2) + 8 * ch (ab 3) (bb 3) (db 3) +
   16 * ch (ab 4) (bb 4) (db 4) + 32 * ch (ab 5) (bb 5) (db 5) +
   64 * ch (ab 6) (bb 6) (db 6) + 128 * ch (ab 7) (bb 7) (db 7) +
   256 * ch (ab 8) (bb 8) (db 8) + 512 * ch (ab 9) (bb 9) (db 9) +
   1024 * ch (ab 10) (bb 10) (db 10) + 2048 * ch (ab 11) (bb 11) (db 11) +
   4096 * ch (ab 12) (bb 12) (db 12) + 8192 * ch (ab 13) (bb 13) (db 13) +
   16384 * ch (ab 14) (bb 14) (db 14) + 32768 * ch (ab 15) (bb 15) (db 15) -
   a_prime_prime air n row) = 0

-- Bridge: verified for both contiguous (2910) and wrapped (2912) constraints.
-- The full 100-constraint bridge is split into per-group lemmas to avoid timeout.

-- Verify chiIdx matches chiAPrimeIdx (computational verification).
theorem chiIdx_eq_chiAPrimeIdx :
    ∀ n : Fin 100, ∀ j : Fin 16, ∀ inp : Fin 3,
    chiIdx n.val j.val inp.val = chiAPrimeIdx n.val j.val inp.val := by
  decide

/-! ## Chi output state -/

/-- The chi output state: all 25 lanes from a_prime_prime columns. -/
noncomputable def chiOutputState
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ) : State :=
  ⟨Array.ofFn fun (i : Fin 25) =>
    let base := 4 * i.val
    laneOfLimbs (a_prime_prime air base row) (a_prime_prime air (base + 1) row)
                (a_prime_prime air (base + 2) row) (a_prime_prime air (base + 3) row),
   by simp⟩

theorem chiOutputState_lane
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ) (i : Fin 25) :
    (chiOutputState air row)[i.val]'(by omega) =
    laneOfLimbs (a_prime_prime air (4 * i.val) row) (a_prime_prime air (4 * i.val + 1) row)
                (a_prime_prime air (4 * i.val + 2) row) (a_prime_prime air (4 * i.val + 3) row) := by
  simp [chiOutputState]

/-! ## Roundtrip lemmas -/

-- stateToBits ∘ bitsToState = id (pointwise).
-- Uses arr25_getElem_mk from Surface.lean for subtype array access.
theorem stateToBits_bitsToState (B : StateBits) (x : Fin 5) (y : Fin 5) (k : Fin 64) :
    stateToBits (bitsToState B) x y k = B x y k := by
  -- Unfold stateToBits to getBit, then convert Arr25 access to raw Array access
  show getBit ((bitsToState B)[5 * y.val + x.val]'(by omega)) k = B x y k
  -- Arr25 getElem goes through .val
  change getBit ((bitsToState B).1[5 * y.val + x.val]'(by
    have := (bitsToState B).2; omega)) k = B x y k
  simp only [bitsToState, Array.getElem_ofFn]
  rw [getBit_bitsToU64]
  congr 1 <;> ext <;> simp <;> omega

-- Spec-level: χ(ρπ(aPrimeState)) via bits
set_option maxHeartbeats 1600000 in
theorem chi_rho_pi_aPrime
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
    χ (ρπ (aPrimeState air row)) =
    bitsToState (chi_bits (rho_pi_bits (aPrimeStateBits air row))) := by
  -- aPrimeState = bitsToState(aPrimeStateBits) by definition
  change χ (ρπ (bitsToState (aPrimeStateBits air row))) = _
  -- Use rho_pi_bits_eq_spec: ρπ(st) = bitsToState(rho_pi_bits(stateToBits(st)))
  rw [← rho_pi_bits_eq_spec (bitsToState (aPrimeStateBits air row))]
  -- Now LHS: χ(bitsToState(rho_pi_bits(stateToBits(bitsToState(aPrimeStateBits)))))
  -- Use chi_bits_eq_spec: χ(st) = bitsToState(chi_bits(stateToBits(st)))
  rw [← chi_bits_eq_spec]
  -- Both sides are bitsToState(...); need the StateBits arguments to match.
  -- Goal: bitsToState(chi_bits(stateToBits(bitsToState(rho_pi_bits(stateToBits(bitsToState(S)))))))
  --     = bitsToState(chi_bits(rho_pi_bits(S)))
  -- Suffices: the two StateBits functions are equal pointwise.
  congr 1; funext x y k
  -- chi_bits is pointwise, so suffices if its input matches
  show chi_bits (stateToBits (bitsToState (rho_pi_bits (stateToBits (bitsToState (aPrimeStateBits air row)))))) x y k =
       chi_bits (rho_pi_bits (aPrimeStateBits air row)) x y k
  -- chi_bits(A)(x,y,k) depends on A at (x,y,k), ((x+1)%5,y,k), ((x+2)%5,y,k)
  -- It suffices to show the argument StateBits are equal
  suffices h : stateToBits (bitsToState (rho_pi_bits (stateToBits (bitsToState (aPrimeStateBits air row))))) =
               rho_pi_bits (aPrimeStateBits air row) by
    simp only [chi_bits]; rw [h]
  funext x' y' k'
  rw [stateToBits_bitsToState]
  congr 1; funext x'' y'' k''
  exact stateToBits_bitsToState _ x'' y'' k''

/-! ## Per-bit chi extraction

From chiCanonicalK, extract the per-bit identity: each bit of the
a_prime_prime limb equals the corresponding chi_bits value. -/

-- chiCanonicalK implies a_prime_prime = recompose of chi values.
theorem chi_limb_recompose
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row n : ℕ}
    (hc : chiCanonicalK air n row) :
    a_prime_prime air n row =
    let ab (j : Nat) := a_prime_bit air (chiIdx n j 0) row
    let bb (j : Nat) := a_prime_bit air (chiIdx n j 1) row
    let db (j : Nat) := a_prime_bit air (chiIdx n j 2) row
    let ch (a b d : FBB) := a + d - b * d - 2 * a * d + 2 * a * b * d
    ch (ab 0) (bb 0) (db 0) + 2 * ch (ab 1) (bb 1) (db 1) +
    4 * ch (ab 2) (bb 2) (db 2) + 8 * ch (ab 3) (bb 3) (db 3) +
    16 * ch (ab 4) (bb 4) (db 4) + 32 * ch (ab 5) (bb 5) (db 5) +
    64 * ch (ab 6) (bb 6) (db 6) + 128 * ch (ab 7) (bb 7) (db 7) +
    256 * ch (ab 8) (bb 8) (db 8) + 512 * ch (ab 9) (bb 9) (db 9) +
    1024 * ch (ab 10) (bb 10) (db 10) + 2048 * ch (ab 11) (bb 11) (db 11) +
    4096 * ch (ab 12) (bb 12) (db 12) + 8192 * ch (ab 13) (bb 13) (db 13) +
    16384 * ch (ab 14) (bb 14) (db 14) + 32768 * ch (ab 15) (bb 15) (db 15) := by
  exact (sub_eq_zero.mp hc).symm

-- UInt16 bit access: .toBitVec.getLsbD = .toUInt64.toBitVec.getLsbD for j < 16.
-- This bridges getBit_laneOfLimbs (which uses .toBitVec) with
-- fieldToU16_getLsbD_fbbToBool (which uses .toUInt64.toBitVec).
theorem u16_toBitVec_eq_toU64_toBitVec (v : UInt16) (j : Nat) (hj : j < 16) :
    v.toBitVec.getLsbD j = v.toUInt64.toBitVec.getLsbD j := by
  simp [UInt16.toBitVec_toUInt64, show j < 64 from by omega]

-- Per-bit extraction: from chiCanonicalK, extract that bit j of a_prime_prime[n]
-- equals fbbToBool(chi_field(a_prime_bit inputs)).
-- Uses fieldToU16_getLsbD_fbbToBool from ThetaAPrime.
set_option maxHeartbeats 3200000 in
theorem chi_bit_extraction
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row n : ℕ}
    (hc : chiCanonicalK air n row)
    (hbool : ∀ idx, idx < 1600 → a_prime_bit air idx row = 0 ∨ a_prime_bit air idx row = 1)
    (j : ℕ) (hj : j < 16)
    (hab : ∀ jj, jj < 16 → chiIdx n jj 0 < 1600)
    (hbb : ∀ jj, jj < 16 → chiIdx n jj 1 < 1600)
    (hdb : ∀ jj, jj < 16 → chiIdx n jj 2 < 1600) :
    (fieldToU16 (a_prime_prime air n row)).toUInt64.toBitVec.getLsbD j =
    fbbToBool (a_prime_bit air (chiIdx n j 0) row +
               a_prime_bit air (chiIdx n j 2) row -
               a_prime_bit air (chiIdx n j 1) row * a_prime_bit air (chiIdx n j 2) row -
               2 * a_prime_bit air (chiIdx n j 0) row * a_prime_bit air (chiIdx n j 2) row +
               2 * a_prime_bit air (chiIdx n j 0) row * a_prime_bit air (chiIdx n j 1) row *
                 a_prime_bit air (chiIdx n j 2) row) := by
  have hrecomp := chi_limb_recompose hc
  -- Define b : Fin 16 → FBB as the chi field polynomial at each bit
  let b : Fin 16 → FBB := fun jj =>
    let a := a_prime_bit air (chiIdx n jj.val 0) row
    let bv := a_prime_bit air (chiIdx n jj.val 1) row
    let d := a_prime_bit air (chiIdx n jj.val 2) row
    a + d - bv * d - 2 * a * d + 2 * a * bv * d
  have hb_bool : ∀ i, b i = 0 ∨ b i = 1 := fun i =>
    chi_field_is_bool (hbool _ (hab i.val i.isLt)) (hbool _ (hbb i.val i.isLt)) (hbool _ (hdb i.val i.isLt))
  rw [fieldToU16_getLsbD_fbbToBool b hb_bool _ hrecomp j hj]

-- Key connecting lemma: fbbToBool(a_prime_bit[chiAPrimeIdx(n,j,inp)]) equals
-- the corresponding rho_pi_bits(aPrimeStateBits) value.
-- This follows by definition since chiAPrimeIdx IS the ρπ index formula.
theorem a_prime_bit_chiAPrimeIdx_eq_rho_pi
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
    (n j inp : Nat) :
    fbbToBool (a_prime_bit air (chiAPrimeIdx n j inp) row) =
    let lane := n / 4; let limb := n % 4; let x_out := lane % 5; let y_out := lane / 5
    let x_in := (x_out + inp) % 5; let sx := (x_in + 3 * y_out) % 5; let sy := x_in
    let rot := rotNat (5 * sy + sx)
    fbbToBool (a_prime_bit air (320 * sy + 64 * sx + (16 * limb + j + rot) % 64) row) := by
  rfl

-- Key per-bit connection: fbbToBool(a_prime_bit[chiIdx n j inp]) equals the
-- corresponding rho_pi_bits(aPrimeStateBits) value, for the limb case where
-- n = 4*lane + limb and j is the bit within the limb.
-- This combines chiIdx_eq_chiAPrimeIdx + definitional unfolding.
-- The proof rewrites chiIdx to chiAPrimeIdx (via decide), then
-- both sides are definitionally equal.
theorem chi_col_eq_rho_pi_bit
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
    (n : Fin 100) (j : Fin 16) (inp : Fin 3) :
    fbbToBool (a_prime_bit air (chiIdx n.val j.val inp.val) row) =
    fbbToBool (a_prime_bit air (chiAPrimeIdx n.val j.val inp.val) row) := by
  rw [chiIdx_eq_chiAPrimeIdx]

-- chiAPrimeIdx gives the same index as rho_pi_bits ∘ aPrimeStateBits,
-- expressed as: the a_prime_bit at chiAPrimeIdx position equals aPrimeStateBits
-- at the rho_pi_src position with rotation.
-- This is true by rfl since chiAPrimeIdx IS the formula for 320*sy + 64*sx + (k+rot)%64.
theorem chiAPrimeIdx_eq_aPrimeStateBits_idx
    (n j inp : Nat) (hn : n < 100) (hj : j < 16) :
    chiAPrimeIdx n j inp =
    let lane := n / 4; let limb := n % 4; let x_out := lane % 5; let y_out := lane / 5
    let x_in := (x_out + inp) % 5; let sx := (x_in + 3 * y_out) % 5; let sy := x_in
    320 * sy + 64 * sx + (16 * limb + j + rotNat (5 * sy + sx)) % 64 := rfl

-- rotNat (match-based) agrees with rotOffset (UInt64 array-based).
theorem rotNat_eq_rotOffset : ∀ flat : Fin 25,
    rotNat flat.val = rotOffset flat := by decide

-- The full per-bit column matching: fbbToBool(a_prime_bit[chiIdx(4*lane+limb, j, inp)])
-- equals rho_pi_bits(aPrimeStateBits)(x_in, y_out, 16*limb+j), where
-- x_in = (lane%5 + inp) % 5 and y_out = lane / 5.
-- Proof: rewrite chiIdx → chiAPrimeIdx → unfold chiAPrimeIdx → match aPrimeStateBits
-- → match rho_pi_bits (using rotNat_eq_rotOffset for the rotation value).
theorem fbbToBool_a_prime_bit_chiIdx_eq_rho_pi_bits
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
    (lane : ℕ) (hlane : lane < 25) (limb : Fin 4) (j : Fin 16) (inp : Fin 3)
    (hn : 4 * lane + limb.val < 100) :
    fbbToBool (a_prime_bit air (chiIdx (4 * lane + limb.val) j.val inp.val) row) =
    rho_pi_bits (aPrimeStateBits air row)
      ⟨(lane % 5 + inp.val) % 5, by omega⟩
      ⟨lane / 5, by omega⟩
      ⟨16 * limb.val + j.val, by omega⟩ := by
  -- Step 1: chiIdx → chiAPrimeIdx
  rw [chiIdx_eq_chiAPrimeIdx ⟨4 * lane + limb.val, hn⟩ j inp]
  -- Step 2: unfold both sides
  simp only [rho_pi_bits, aPrimeStateBits, rho_pi_src, rotOffset, chiAPrimeIdx, fbbToBool]
  -- Simplify: (4*lane+limb)/4 = lane, (4*lane+limb)%4 = limb
  -- Use simp (not rw) to handle Decidable instance dependency
  simp only [show (4 * lane + limb.val) / 4 = lane from by omega,
             show (4 * lane + limb.val) % 4 = limb.val from by omega]
  -- Now both sides match except rotNat vs rotationValues[...].toNat
  -- Convert rotNat to rotOffset via decide
  have hflat : 5 * ((lane % 5 + inp.val) % 5) +
    ((lane % 5 + inp.val) % 5 + 3 * (lane / 5)) % 5 < 25 := by
    have : (lane % 5 + inp.val) % 5 < 5 := Nat.mod_lt _ (by omega)
    have : ((lane % 5 + inp.val) % 5 + 3 * (lane / 5)) % 5 < 5 := Nat.mod_lt _ (by omega)
    omega
  simp only [rotNat_eq_rotOffset ⟨_, hflat⟩, rotOffset]

-- Main theorems (chi_output_state_eq, chi_preiota_lane_zero, chi_nonzero_lanes)
-- are in ChiState.lean, which imports both ChiFacts and ChiBridge to avoid
-- circular dependencies.

end KeccakfPermAir.Soundness
