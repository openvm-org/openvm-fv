/-
  Keccak steps at bit/limb level, plus equivalence to the u64 spec.

  Defines pure-math bit-level versions of θ, ρπ, χ, ι and proves them
  equivalent to the lane-level spec in `Keccak.Spec.Basic`.
-/
import VmExtensions.Keccak.Spec.Basic
import VmExtensions.Keccak.Spec.Permutation
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

open Keccak

namespace KeccakfPermAir.StepLimbs

/-! ## Core types and bit extraction -/

/-- Extract bit `k` from a UInt64 value using BitVec.getLsbD. -/
def getBit (v : UInt64) (k : Fin 64) : Bool :=
  v.toBitVec.getLsbD k.val

/-- 5×5×64 bit array (state at bit level). -/
abbrev StateBits := Fin 5 → Fin 5 → Fin 64 → Bool

/-- 5×64 parity bit array. -/
abbrev ParityBits := Fin 5 → Fin 64 → Bool

/-- Convert a lane-level state to bit-level. -/
def stateToBits (st : State) : StateBits := fun x y k =>
  getBit (st[5 * y.val + x.val]'(by omega)) k

/-- Convert 64 bits back to a UInt64 via fold over bit positions. -/
def bitsToU64 (bits : Fin 64 → Bool) : UInt64 :=
  let bv := Fin.foldl 64 (init := (0 : BitVec 64)) fun acc k =>
    if bits ⟨k.val, k.isLt⟩ then acc ||| (BitVec.ofNat 64 1 <<< k.val) else acc
  ⟨bv⟩

/-- Convert a bit-level state back to lane-level. -/
def bitsToState (A : StateBits) : State :=
  ⟨Array.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val % 5, by omega⟩
    let y : Fin 5 := ⟨i.val / 5, by omega⟩
    bitsToU64 (A x y),
   by simp⟩

/-! ## Fundamental getBit lemmas -/

theorem getBit_xor (a b : UInt64) (k : Fin 64) :
    getBit (a ^^^ b) k = (getBit a k ^^ getBit b k) := by
  simp [getBit]

theorem getBit_and (a b : UInt64) (k : Fin 64) :
    getBit (a &&& b) k = (getBit a k && getBit b k) := by
  simp [getBit]

theorem getBit_or (a b : UInt64) (k : Fin 64) :
    getBit (a ||| b) k = (getBit a k || getBit b k) := by
  simp [getBit]

theorem getBit_complement (a : UInt64) (k : Fin 64) :
    getBit (a ^^^ 0xFFFFFFFFFFFFFFFF) k = !(getBit a k) := by
  simp only [getBit]
  show (a ^^^ 0xFFFFFFFFFFFFFFFF).toBitVec.getLsbD k.val = !a.toBitVec.getLsbD k.val
  rw [show (a ^^^ (0xFFFFFFFFFFFFFFFF : UInt64)).toBitVec =
    a.toBitVec ^^^ (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec from rfl]
  rw [BitVec.getLsbD_xor]
  rw [show (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 from rfl]
  rw [BitVec.getLsbD_allOnes]
  simp [k.isLt]

theorem getBit_rotateBy (v : UInt64) (n : UInt64) (k : Fin 64) :
    getBit (rotateBy v n) k = getBit v ⟨(k.val + n.toNat) % 64, by omega⟩ := by
  simp only [getBit, rotateBy]
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_sub]
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec]
  have h64 : BitVec.toNat (64 : BitVec 64) = 64 := by rfl
  simp only [h64]
  have hsub : (UInt64.toBitVec 64 - n.toBitVec).toNat % 64 = (64 - n.toNat % 64) % 64 := by
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec]
    have h1 : (UInt64.toBitVec 64).toNat = 64 := by rfl
    rw [h1]; have : n.toNat < 2 ^ 64 := n.toBitVec.isLt; omega
  simp only [hsub]
  by_cases hr : n.toNat % 64 = 0
  · simp only [hr, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
    simp only [k.isLt, decide_true, Bool.true_and, Nat.not_lt_zero, decide_false,
      Bool.not_false, Bool.or_self]
    congr 1; omega
  · have hs : (64 - n.toNat % 64) % 64 = 64 - n.toNat % 64 := Nat.mod_eq_of_lt (by omega)
    simp only [hs]
    by_cases hk : n.toNat % 64 + k.val < 64
    · have hlt : k.val < 64 - n.toNat % 64 := by omega
      simp only [hlt, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]
      congr 1; omega
    · have hge : ¬(k.val < 64 - n.toNat % 64) := by omega
      have h_over : v.toBitVec.getLsbD (n.toNat % 64 + k.val) = false :=
        BitVec.getLsbD_of_ge v.toBitVec _ (by omega)
      rw [h_over]
      simp only [Bool.false_or, k.isLt, decide_true, Bool.true_and, hge, decide_false,
        Bool.not_false, Bool.true_and]
      congr 1; omega

/-! ## Bit-level step definitions -/

/-- θ parity: XOR of 5 rows in each column. -/
def theta_parity (A : StateBits) : ParityBits := fun x k =>
  A x 0 k ^^ A x 1 k ^^ A x 2 k ^^ A x 3 k ^^ A x 4 k

/-- θ shift: combines parity of adjacent columns with rotation. -/
def theta_shift (C : ParityBits) : ParityBits := fun x k =>
  C ⟨(x.val + 4) % 5, by omega⟩ k ^^
  C ⟨(x.val + 1) % 5, by omega⟩ ⟨(k.val + 63) % 64, by omega⟩

/-- θ apply: XOR each bit with the theta shift. -/
def theta_apply (A : StateBits) (Cp : ParityBits) : StateBits := fun x y k =>
  A x y k ^^ Cp x k

/-- Full θ at bit level. -/
def theta_bits (A : StateBits) : StateBits :=
  theta_apply A (theta_shift (theta_parity A))

/-- χ at bit level: the non-linear step. -/
def chi_bits (A : StateBits) : StateBits := fun x y k =>
  A x y k ^^ (!(A ⟨(x.val + 1) % 5, by omega⟩ y k) && A ⟨(x.val + 2) % 5, by omega⟩ y k)

/-- ι at bit level: XOR lane (0,0) with round constant. -/
def iota_bits (A : StateBits) (rc : UInt64) : StateBits := fun x y k =>
  if x.val = 0 ∧ y.val = 0 then A x y k ^^ getBit rc k else A x y k

/-! ## ρπ rotation offsets

The ρπ step permutes lanes and rotates them. The rotation offsets
are stored in `rotationValues` from the spec. -/

/-- ρπ source mapping: destination (x, y) reads from source ((x+3y)%5, x).
This is the inverse of the standard π permutation (x,y) → (y, (2x+3y)%5). -/
def rho_pi_src (x y : Fin 5) : Fin 5 × Fin 5 :=
  (⟨(x.val + 3 * y.val) % 5, by omega⟩, x)

/-- Get the rotation offset for lane at flat index. -/
def rotOffset (flat : Fin 25) : Nat :=
  (rotationValues[flat.val]'(by omega)).toNat

/-- ρπ at bit level: permute and rotate. -/
def rho_pi_bits (A : StateBits) : StateBits := fun x y k =>
  let (sx, sy) := rho_pi_src x y
  let flat : Fin 25 := ⟨5 * sy.val + sx.val, by omega⟩
  let rot := rotOffset flat
  A sx sy ⟨(k.val + rot) % 64, by omega⟩

/-! ## Roundtrip: getBit ∘ bitsToU64 = id -/

private theorem testBit_one_ge_one (k : Nat) (hk : k ≥ 1) :
    Nat.testBit 1 k = false := by
  cases k with
  | zero => omega
  | succ n => simp [Nat.testBit_succ]

set_option maxRecDepth 2048 in
private theorem foldl_or_getLsbD (n : Nat) (hn : n ≤ 64) (bits : Fin 64 → Bool)
    (init : BitVec 64) (j : Nat) (hj : j < 64) :
    (Fin.foldl n (fun acc (k : Fin n) =>
      if bits ⟨k.val, by omega⟩ then acc ||| (BitVec.ofNat 64 1 <<< k.val)
      else acc) init).getLsbD j
    = (init.getLsbD j || (decide (j < n) && bits ⟨j, hj⟩)) := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last, Fin.coe_castSucc]
    split
    · -- bits n = true
      rename_i hb
      rw [BitVec.getLsbD_or, ih (by omega) init, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_ofNat]
      by_cases hjn : j = n
      · subst hjn; simp [hb, hj]
      · by_cases hjn2 : j < n
        · simp [hjn2, show j < n + 1 from by omega]
        · simp only [show ¬ (j < n) from hjn2, show ¬ (j < n + 1) from by omega,
            decide_false, Bool.false_and, Bool.or_false, Bool.not_false, Bool.true_and,
            show j < 64 from hj, decide_true, Bool.and_true,
            show j - n < 64 from by omega,
            testBit_one_ge_one _ (show j - n ≥ 1 from by omega)]
    · -- bits n = false
      rename_i hb
      have hb' : bits ⟨n, by omega⟩ = false := Bool.eq_false_iff.mpr hb
      simp only [ih (by omega)]
      by_cases hjn : j < n
      · simp [hjn, show j < n + 1 from by omega]
      · by_cases hjn2 : j = n
        · subst hjn2; simp [hb']
        · simp [hjn, show ¬ (j < n + 1) from by omega]

theorem getBit_bitsToU64 (bits : Fin 64 → Bool) (k : Fin 64) :
    getBit (bitsToU64 bits) k = bits k := by
  simp only [getBit, bitsToU64, foldl_or_getLsbD 64 (by omega) bits 0 k.val k.isLt]
  simp [k.isLt]

/-- Roundtrip: bitsToU64 ∘ getBit = id. -/
theorem bitsToU64_getBit (v : UInt64) : bitsToU64 (getBit v) = v := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := getBit_bitsToU64 (getBit v) ⟨i, hi⟩
  simp only [getBit] at this
  exact this

theorem bitsToU64_congr {f g : Fin 64 → Bool} (h : f = g) : bitsToU64 f = bitsToU64 g :=
  congrArg _ h

theorem stateToBits_val (st : State) (x y : Fin 5) (k : Fin 64) :
    stateToBits st x y k = getBit (st[5 * y.val + x.val]'(by omega)) k := rfl

theorem iota_bits_zero (A : StateBits) (rc : UInt64) (k : Fin 64) :
    iota_bits A rc ⟨0, by omega⟩ ⟨0, by omega⟩ k =
    (A ⟨0, by omega⟩ ⟨0, by omega⟩ k ^^ getBit rc k) := by
  unfold iota_bits; rw [if_pos ⟨rfl, rfl⟩]

theorem iota_bits_nonzero (A : StateBits) (rc : UInt64) (x y : Fin 5)
    (h : ¬(x.val = 0 ∧ y.val = 0)) (k : Fin 64) :
    iota_bits A rc x y k = A x y k := by
  unfold iota_bits; rw [if_neg h]

/-! ## Subtype-level modify chain resolution

These lemmas resolve `subtypeModify` chains at the `Arr25` and `Arr5` level,
avoiding raw `Array.getElem_modify` which generates huge proof terms. -/

private theorem subtypeModify_getElem_ne (a : Arr25) (j : Nat) (v : UInt64)
    (i : Nat) (hi : i < 25) (hne : j ≠ i) :
    (subtypeModify a j v)[i]'hi = a[i]'hi := by
  show (subtypeModify a j v).val[i]'_ = a.val[i]'_
  simp [subtypeModify, Array.getElem_modify, hne]

private theorem subtypeModify_getElem_eq (a : Arr25) (i : Nat) (v : UInt64) (hi : i < 25) :
    (subtypeModify a i v)[i]'hi = v := by
  show (subtypeModify a i v).val[i]'_ = v
  simp [subtypeModify, Array.getElem_modify]

private theorem subtypeModify5_getElem_ne (a : Arr5) (j : Nat) (v : UInt64)
    (i : Nat) (hi : i < 5) (hne : j ≠ i) :
    (subtypeModify a j v)[i]'hi = a[i]'hi := by
  show (subtypeModify a j v).val[i]'_ = a.val[i]'_
  simp [subtypeModify, Array.getElem_modify, hne]

private theorem subtypeModify5_getElem_eq (a : Arr5) (i : Nat) (v : UInt64) (hi : i < 5) :
    (subtypeModify a i v)[i]'hi = v := by
  show (subtypeModify a i v).val[i]'_ = v
  simp [subtypeModify, Array.getElem_modify]

/-! ## Spec loop unrolling helpers

These lemmas characterize what each spec function computes at each lane index.
The proof strategy avoids unfolding `subtypeModify` in the loop-unrolling step
(which generates huge proof terms) and instead uses the chain-resolution lemmas
in this section with `simp (discharger := decide)`. -/

set_option maxHeartbeats 8000000 in
private theorem chi_getElem (A' : State) (i : Nat) (hi : i < 25) :
    (χ A')[i]'hi = A'[i]'hi ^^^
      ((A'[(i % 5 + 1) % 5 + 5 * (i / 5)]'(by omega) ^^^
        (0xffffffffffffffff : UInt64)) &&&
       A'[(i % 5 + 2) % 5 + 5 * (i / 5)]'(by omega)) := by
  simp only [χ, Id.run, bind_pure_comp, map_pure, Std.Range.forIn'_eq_forIn'_range',
    Std.Range.size, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Nat.add_one_sub_one, Nat.div_one,
    List.forIn'_pure_yield_eq_foldl, pure_bind,
    List.range', List.attach, List.attachWith, List.pmap, List.foldl_cons, List.foldl_nil]
  interval_cases i <;>
    simp (discharger := decide) only [subtypeModify_getElem_ne, subtypeModify_getElem_eq]

/-- Column parity for θ characterization. -/
private def thetaC (A : State) (x : Nat) (_ : x < 5) : UInt64 :=
  A[x]'(by omega) ^^^ A[x+5]'(by omega) ^^^ A[x+10]'(by omega) ^^^
  A[x+15]'(by omega) ^^^ A[x+20]'(by omega)

/-- D value for θ characterization. -/
private def thetaD (A : State) (x : Nat) (_ : x < 5) : UInt64 :=
  thetaC A ((x+4)%5) (by omega) ^^^
  (thetaC A ((x+1)%5) (by omega) <<< 1 ||| thetaC A ((x+1)%5) (by omega) >>> 63)

/-- Common tactic for θ per-index proofs: loop unrolling then chain resolution. -/
macro "theta_resolve" : tactic => `(tactic| (
  simp only [θ, Id.run, bind_pure_comp, map_pure, Std.Range.forIn'_eq_forIn'_range',
    Std.Range.size, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Nat.add_one_sub_one, Nat.div_one,
    List.forIn'_pure_yield_eq_foldl, pure_bind,
    List.range', List.attach, List.attachWith, List.pmap, List.foldl_cons, List.foldl_nil]
  simp (discharger := decide) only [
    subtypeModify_getElem_ne, subtypeModify_getElem_eq,
    subtypeModify5_getElem_ne, subtypeModify5_getElem_eq,
    thetaC, thetaD, Nat.reduceAdd, Nat.reduceMod]))

set_option maxHeartbeats 64000000 in
private theorem theta_getElem_x0 (A : State) (y : Nat) (hy : y < 5) :
    (θ A)[5 * y + 0]'(by omega) = A[5 * y + 0]'(by omega) ^^^ thetaD A 0 (by omega) := by
  interval_cases y <;> theta_resolve

set_option maxHeartbeats 64000000 in
private theorem theta_getElem_x1 (A : State) (y : Nat) (hy : y < 5) :
    (θ A)[5 * y + 1]'(by omega) = A[5 * y + 1]'(by omega) ^^^ thetaD A 1 (by omega) := by
  interval_cases y <;> theta_resolve

set_option maxHeartbeats 64000000 in
private theorem theta_getElem_x2 (A : State) (y : Nat) (hy : y < 5) :
    (θ A)[5 * y + 2]'(by omega) = A[5 * y + 2]'(by omega) ^^^ thetaD A 2 (by omega) := by
  interval_cases y <;> theta_resolve

set_option maxHeartbeats 64000000 in
private theorem theta_getElem_x3 (A : State) (y : Nat) (hy : y < 5) :
    (θ A)[5 * y + 3]'(by omega) = A[5 * y + 3]'(by omega) ^^^ thetaD A 3 (by omega) := by
  interval_cases y <;> theta_resolve

set_option maxHeartbeats 64000000 in
private theorem theta_getElem_x4 (A : State) (y : Nat) (hy : y < 5) :
    (θ A)[5 * y + 4]'(by omega) = A[5 * y + 4]'(by omega) ^^^ thetaD A 4 (by omega) := by
  interval_cases y <;> theta_resolve

private theorem theta_getElem (A : State) (i : Nat) (hi : i < 25) :
    (θ A)[i]'hi = A[i]'hi ^^^ thetaD A (i % 5) (by omega) := by
  interval_cases i <;> first
  | exact theta_getElem_x0 A 0 (by omega) | exact theta_getElem_x1 A 0 (by omega)
  | exact theta_getElem_x2 A 0 (by omega) | exact theta_getElem_x3 A 0 (by omega)
  | exact theta_getElem_x4 A 0 (by omega) | exact theta_getElem_x0 A 1 (by omega)
  | exact theta_getElem_x1 A 1 (by omega) | exact theta_getElem_x2 A 1 (by omega)
  | exact theta_getElem_x3 A 1 (by omega) | exact theta_getElem_x4 A 1 (by omega)
  | exact theta_getElem_x0 A 2 (by omega) | exact theta_getElem_x1 A 2 (by omega)
  | exact theta_getElem_x2 A 2 (by omega) | exact theta_getElem_x3 A 2 (by omega)
  | exact theta_getElem_x4 A 2 (by omega) | exact theta_getElem_x0 A 3 (by omega)
  | exact theta_getElem_x1 A 3 (by omega) | exact theta_getElem_x2 A 3 (by omega)
  | exact theta_getElem_x3 A 3 (by omega) | exact theta_getElem_x4 A 3 (by omega)
  | exact theta_getElem_x0 A 4 (by omega) | exact theta_getElem_x1 A 4 (by omega)
  | exact theta_getElem_x2 A 4 (by omega) | exact theta_getElem_x3 A 4 (by omega)
  | exact theta_getElem_x4 A 4 (by omega)

set_option maxHeartbeats 16000000 in
private theorem rho_pi_getElem (A : State) (i : Nat) (hi : i < 25) :
    (ρπ A)[i]'hi = rotateBy
      (A[((i%5) + 3*(i/5))%5 + 5*(i%5)]'(by omega))
      (rotationValues[((i%5) + 3*(i/5))%5 + 5*(i%5)]'(by omega)) := by
  simp only [ρπ, Id.run, bind_pure_comp, map_pure, Std.Range.forIn'_eq_forIn'_range',
    Std.Range.size, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    Nat.add_one_sub_one, Nat.div_one,
    List.forIn'_pure_yield_eq_foldl, pure_bind,
    mkState, List.range', List.attach, List.attachWith, List.pmap,
    List.foldl_cons, List.foldl_nil]
  interval_cases i <;>
    simp (discharger := decide) only [subtypeModify_getElem_ne, subtypeModify_getElem_eq,
      rotationValues]

/-! ## Step equivalence theorems

These theorems connect the bit-level step definitions to the u64-level
spec definitions from `Keccak.Spec.Basic`. The proofs use the `_getElem`
helper lemmas in this file to avoid brute-force loop unrolling in the main
theorems. -/

private theorem allOnes64_getLsbD (j : Nat) (hj : j < 64) :
    (18446744073709551615#64).getLsbD j = true := by
  change (BitVec.allOnes 64).getLsbD j = true
  rw [BitVec.getLsbD_allOnes]; simp [hj]

/-- χ equivalence: bit-level χ matches the spec's χ. -/
theorem chi_bits_eq_spec (st : State) :
    bitsToState (chi_bits (stateToBits st)) = χ st := by
  apply Subtype.ext
  apply Array.ext
  · rw [show (bitsToState _).val.size = 25 from by simp [bitsToState]]
    exact (χ st).property.symm
  · intro i h1 h2
    simp only [bitsToState, Array.getElem_ofFn]
    have hi : i < 25 := by simp [bitsToState] at h1; exact h1
    change _ = (χ st)[i]'hi
    rw [chi_getElem]
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro j hj
    have lhs := getBit_bitsToU64
      (chi_bits (stateToBits st) ⟨i % 5, by omega⟩ ⟨i / 5, by omega⟩) ⟨j, hj⟩
    simp only [getBit] at lhs ⊢; rw [lhs]
    simp only [chi_bits, stateToBits, getBit, UInt64.toBitVec_xor, UInt64.toBitVec_and,
      BitVec.getLsbD_xor, BitVec.getLsbD_and]
    have h_ones : (UInt64.toBitVec (18446744073709551615 : UInt64)).getLsbD j = true := by
      change (BitVec.allOnes 64).getLsbD j = true; rw [BitVec.getLsbD_allOnes]; simp [hj]
    rw [h_ones, Bool.xor_true]
    have heq : 5 * (i / 5) + i % 5 = i := by omega
    have hcomm : ∀ a, 5 * (i / 5) + a = a + 5 * (i / 5) := fun a => by omega
    simp only [heq, hcomm]

/-- θ equivalence: bit-level θ matches the spec's θ. -/
theorem theta_bits_eq_spec (st : State) :
    bitsToState (theta_bits (stateToBits st)) = θ st := by
  apply Subtype.ext
  apply Array.ext
  · rw [show (bitsToState _).val.size = 25 from by simp [bitsToState]]
    exact (θ st).property.symm
  · intro i h1 h2
    simp only [bitsToState, Array.getElem_ofFn]
    have hi : i < 25 := by simp [bitsToState] at h1; exact h1
    change _ = (θ st)[i]'hi
    rw [theta_getElem]
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro j hj
    have lhs := getBit_bitsToU64
      (theta_bits (stateToBits st) ⟨i % 5, by omega⟩ ⟨i / 5, by omega⟩) ⟨j, hj⟩
    simp only [getBit] at lhs ⊢; rw [lhs]
    simp only [theta_bits, theta_apply, theta_shift, theta_parity, stateToBits, thetaD, thetaC,
      getBit]
    -- Handle rotation: LHS uses (j+63)%64, RHS has shift decomposition
    have idx_eq : 5 * (i / 5) + i % 5 = i := by omega
    have idx_comm : ∀ n x, n + (i + x) % 5 = (i + x) % 5 + n := fun n x => by omega
    by_cases hj0 : j = 0
    · subst hj0; simp
      simp only [idx_eq, idx_comm]
    · -- j > 0: (j+63)%64 = j-1, and shift_right_63 terms vanish
      have hge : ∀ (x : BitVec 64), x.getLsbD (63 + j) = false :=
        fun x => BitVec.getLsbD_of_ge x _ (by omega)
      simp [hj0, hge, show (j + 63) % 64 = j - 1 from by omega]
      simp only [idx_eq, decide_eq_true_eq.mpr hj, Bool.true_and, idx_comm]

set_option maxHeartbeats 800000 in
/-- ι equivalence: bit-level ι matches the spec's ι. -/
theorem iota_bits_eq_spec (st : State) (round : Fin 24) :
    bitsToState (iota_bits (stateToBits st)
      (roundConstants[round.val]'(by simp [roundConstants])))
    = ι st round (by simp [roundConstants]) := by
  apply Subtype.ext
  simp only [bitsToState, ι, Id.run, subtypeModify]
  apply Array.ext
  · simp [st.property]
  · intro i h1 h2
    simp only [Array.getElem_ofFn, Array.getElem_modify]
    by_cases hi0 : i = 0
    · subst hi0; rw [if_pos rfl]
      apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro j hj
      have hlhs := getBit_bitsToU64
        (iota_bits (stateToBits st) (roundConstants[round.val]'(by simp [roundConstants]))
          ⟨0 % 5, by omega⟩ ⟨0 / 5, by omega⟩) ⟨j, hj⟩
      simp only [getBit] at hlhs ⊢
      rw [hlhs]; clear hlhs
      simp [iota_bits, stateToBits, getBit]
    · have h0i : ¬(0 = i) := fun h => hi0 h.symm
      rw [if_neg h0i]
      have hne : ¬(i % 5 = 0 ∧ i / 5 = 0) := by omega
      change bitsToU64 (fun k =>
        iota_bits (stateToBits st) _ ⟨i % 5, _⟩ ⟨i / 5, _⟩ k) = _
      simp only [iota_bits, hne, ite_false, stateToBits]
      rw [bitsToU64_getBit]; congr 1; omega

/-- ρπ equivalence: bit-level ρπ matches the spec's ρπ. -/
theorem rho_pi_bits_eq_spec (st : State) :
    bitsToState (rho_pi_bits (stateToBits st)) = ρπ st := by
  apply Subtype.ext
  apply Array.ext
  · rw [show (bitsToState _).val.size = 25 from by simp [bitsToState]]
    exact (ρπ st).property.symm
  · intro i h1 h2
    simp only [bitsToState, Array.getElem_ofFn]
    have hi : i < 25 := by simp [bitsToState] at h1; exact h1
    change _ = (ρπ st)[i]'hi
    rw [rho_pi_getElem]
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro j hj
    have lhs := getBit_bitsToU64
      (rho_pi_bits (stateToBits st) ⟨i % 5, by omega⟩ ⟨i / 5, by omega⟩) ⟨j, hj⟩
    simp only [getBit] at lhs; rw [lhs]
    -- LHS: rho_pi_bits (stateToBits st) ... ⟨j, hj⟩
    -- RHS: (rotateBy (st[...]) rotVal).toBitVec.getLsbD j
    -- Unfold LHS, then use getBit_rotateBy on RHS
    simp only [rho_pi_bits, rho_pi_src, rotOffset, stateToBits, getBit]
    -- Now LHS = (st[...]).toBitVec.getLsbD ((j + rot) % 64)
    -- RHS = (rotateBy (st[...]) rotVal).toBitVec.getLsbD j
    -- Apply getBit_rotateBy to convert RHS
    conv_rhs =>
      rw [show (rotateBy _ _).toBitVec.getLsbD j =
        getBit (rotateBy _ _) ⟨j, hj⟩ from rfl, getBit_rotateBy, getBit]
    -- Normalize indices
    have idx_rp : ∀ a, 5 * (i % 5) + a = a + 5 * (i % 5) := fun a => by omega
    simp only [idx_rp]

end KeccakfPermAir.StepLimbs
