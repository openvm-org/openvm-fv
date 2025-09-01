import Mathlib

@[simp] notation "LIMB_BITS" => 8
@[simp] notation "NUM_LIMBS" => 4

@[reducible] def U32 := Vector (BitVec LIMB_BITS) NUM_LIMBS

namespace BitVec

/-- `BitVec` extensionality as an iff -/
lemma ext_iff {n : ℕ} {x y : BitVec n} : x = y ↔ ∀ i : Fin n, x[i] = y[i] := by
  constructor <;> [ simp_all; intro heq ]
  . ext j lt_j
    exact heq ⟨ j, lt_j ⟩

/-- Equality of `BitVec` concatenation, equal lengths -/
@[simp, grind =]
lemma append_eq_append_eql {m n : ℕ} {x1 y1: BitVec m} {x2 y2 : BitVec n} :
  (x1 ++ x2) = (y1 ++ y2) ↔ x1 = y1 ∧ x2 = y2 := by
  constructor <;> [ intro h_eq_bv; simp_all ]
  split_ands <;> rw [ext_iff] at h_eq_bv ⊢ <;> intro i
  . specialize h_eq_bv ⟨i + n, by omega⟩; simp_all
    iterate 2 rw [BitVec.getElem_append (by omega)] at h_eq_bv
    simp_all
  . specialize h_eq_bv ⟨i, by omega⟩; simp_all
    iterate 2 rw [BitVec.getElem_append (by omega)] at h_eq_bv
    simp_all

end BitVec

namespace U32

/-- `U32` as a vector of its constituents -/
lemma destruct (x : U32) : x = #v[x[0], x[1], x[2], x[3]] :=
  Vector.ext fun | 0, _ | 1, _ | 2, _ | 3, _ => by simp | n + 4, _ => by omega

section toBV

/-- From `U32` to `BitVec 32` -/
@[grind →]
def toBV (x : U32) : BitVec 32 := x[3] ++ x[2] ++ x[1] ++ x[0]

/-- Injectivity of `toBV` -/
@[simp, grind →]
lemma toBV_inj {x y : U32} : x.toBV = y.toBV → x = y := by
  intro h_eq_bv
  . simp [toBV] at h_eq_bv
    rw [destruct x, destruct y]
    grind

end toBV

section toNat_fromNat

/-- From `U32` to `ℕ` -/
def toNat (x : U32) : ℕ := x[0].toNat + x[1].toNat * 256 + x[2].toNat * 65536 + x[3].toNat * 16777216

/-- `toNat` compatibility with `toBV` -/
@[simp]
lemma toBV_toNat {x : U32} : x.toBV.toNat = x.toNat := by
  simp [toNat, toBV]
  iterate 3 rw [BitVec.toNat_append,
                ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                Nat.shiftLeft_eq]
  omega

/-- Upper bound of `toNat` -/
lemma toNat_ub (x : U32) : x.toNat < 4294967296 := by simp [toNat]; omega

grind_pattern toBV_toNat => x.toBV.toNat
grind_pattern toNat_ub => x.toNat

/-- Injectivity of `toNat` -/
@[simp, grind →]
lemma toNat_inj {x y : U32} : x.toNat = y.toNat → x = y := by
  rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
  exact toBV_inj

/-- Reconstructing a `U32` from a `ℕ` -/
def fromNat (n : ℕ) : U32 :=
  #v[⟨n % 256, by omega⟩, ⟨ n / 256 % 256, by omega ⟩, ⟨ n / 65536 % 256, by omega ⟩, ⟨ n / 16777216 % 256, by omega ⟩ ]

/-- `fromNat`-`toNat` invertibility -/
lemma fromNat_toNat {x : U32} : fromNat x.toNat = x := by
  rw [destruct x]; simp [fromNat, toNat]
  iterate 4 rw [← BitVec.toNat_inj]
  split_ands
  all_goals
    rw [BitVec.toNat_ofFin]; simp; omega

/-- `toNat`-`fromNat` invertibility -/
lemma toNat_fromNat {n : ℕ} (_ : n < 4294967296) : (fromNat n).toNat = n := by
  simp [fromNat, toNat]; grind

end toNat_fromNat

section negative

grind_pattern BitVec.msb_eq_decide => x.msb

/-- Negativity -/
@[grind →]
def negative (x : U32) := ¬ (2 * x.toNat < 4294967296)
instance : Decidable (negative x) := by unfold negative; infer_instance

/-- `msb` is `negative` -/
@[simp]
lemma toBV_msb_negative {x : U32} : x.toBV.msb = x.negative := by grind

/-- `msb` of top byte is the same as `negative` -/
@[simp] lemma msb_3_negative {x : U32} : x[3].msb = x.negative := by
  simp [← toBV_msb_negative]; grind

grind_pattern toBV_msb_negative => x.toBV.msb
grind_pattern msb_3_negative => x[3].msb

end negative

section toInt_fromInt

attribute [local grind →] BitVec.toInt

/-- From `U32` to `ℤ` -/
@[grind →]
def toInt (x : U32) : ℤ := x.toNat - (if x.negative then 4294967296 else 0)

/-- `toBV` compatibility with `toInt` -/
@[simp]
lemma toBV_toInt {x : U32} : x.toBV.toInt = x.toInt := by
  simp [toInt]; split_ifs <;> grind

/-- Range of `toInt` -/
lemma toInt_range {x : U32} : -2147483648 ≤ x.toInt ∧ x.toInt < 2147483648 := by
  simp [toInt]; split_ifs <;> grind

grind_pattern toBV_toInt => x.toBV.toInt
grind_pattern toInt_range => x.toInt

/-- Injectivity of `toInt` -/
@[simp, grind →]
lemma toInt_inj {x y : U32} : x.toInt = y.toInt → x = y := by
  rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
  exact toBV_inj

/-- `negative` in terms of `toInt` -/
lemma negative_toInt {x : U32} : negative x ↔ ¬ 0 ≤ x.toInt := by
  simp [toInt]; split_ifs <;> grind

/-- Reconstructing a `U32` from an `ℤ` -/
def fromInt (z : ℤ) : U32 :=
  let y := (z + if z < 0 then 4294967296 else 0).toNat
  #v[⟨y % 256, by omega⟩, ⟨ y / 256 % 256, by omega ⟩, ⟨ y / 65536 % 256, by omega ⟩, ⟨ y / 16777216 % 256, by omega ⟩ ]

/-- `fromInt`-`toInt` invertibility -/
@[simp]
lemma fromInt_toInt {x : U32} : fromInt x.toInt = x := by
  rw [toInt]; simp [negative]; split_ifs with neg_x
  all_goals
    simp [fromInt]; simp [toNat] at *
    split_ifs with neg <;> try omega
    . conv => rhs; rw [destruct x]
      simp; iterate 4 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

/-- `toInt`-`fromInt` invertibility -/
lemma toInt_fromInt {z : ℤ} (_ : -2147483648 ≤ z) (_ : z < 2147483647) : (fromInt z).toInt = z := by
  simp [fromInt, toInt, toNat]; split_ifs with neg_z
  . rw [if_pos] <;> [ skip; simp [negative, toNat] ] <;> grind
  . rw [if_neg] <;> [ skip; simp [negative, toNat] ] <;> grind

end toInt_fromInt

end U32
