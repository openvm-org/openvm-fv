import Mathlib

/-- A prime finite field has no zero divisors -/
instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

namespace BitVec

/-- `BitVec` extensionality as an iff -/
lemma ext_iff {n : ℕ} {x y : BitVec n} : x = y ↔ ∀ i : Fin n, x[i] = y[i] := by
  constructor <;> [ simp_all; intro heq ]
  . ext j lt_j
    exact heq ⟨ j, lt_j ⟩

/-- `BitVec` extension, signed and unsigned -/
def extend {m : ℕ} (bv : BitVec m) (n : ℕ) (sgn : Prop) [Decidable sgn] :=
  (if sgn then signExtend else setWidth) n bv

/-- Equality of `BitVec` concatenation, equal lengths -/
@[simp, grind =]
lemma append_eq_append_eql {m n : ℕ} {x1 y1 : BitVec m} {x2 y2 : BitVec n} :
  (x1 ++ x2) = (y1 ++ y2) ↔ x1 = y1 ∧ x2 = y2 := by
  constructor <;> [ intro h_eq_bv; simp_all ]
  split_ands <;> rw [ext_iff] at h_eq_bv ⊢ <;> intro i
  . specialize h_eq_bv ⟨i + n, by omega⟩; simp_all
    iterate 2 rw [BitVec.getElem_append (by omega)] at h_eq_bv
    simp_all
  . specialize h_eq_bv ⟨i, by omega⟩; simp_all
    iterate 2 rw [BitVec.getElem_append (by omega)] at h_eq_bv
    simp_all

/-- Reformulation of `sshiftRight` -/
lemma sshiftright_eq {n : ℕ} {bv : BitVec n} {shift : ℕ} :
  bv.sshiftRight shift =
    BitVec.setWidth n
      (BitVec.extractLsb ((n - 1) + shift) shift (BitVec.signExtend (n + shift) bv))
    := by grind

end BitVec

namespace Int

/-- Case analysis on `abs` -/
lemma abs_cases {a : ℤ} : abs a = if 0 ≤ a then a else -a := by
  unfold abs; rw [Int.max_def]; omega

/-- Case analysis of `Int.sign` -/
lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  by_cases a = 0
  . simp_all
  . by_cases 0 < a
    . rw [Int.sign_eq_one_of_pos (by omega)]; omega
    . rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

/-- Case analysis on negative-zero-positive -/
lemma split_nzp (a : ℤ) (P : Prop) :
  (a < 0 → P) → (a = 0 → P) → (0 < a → P) → P := by
  intro an az ap
  by_cases a = 0
  . apply az (by assumption)
  . by_cases 0 < a
    . apply ap (by omega)
    . apply an (by omega)

end Int

section auxiliaries

/-- Helper for reasoning about `execute_MUL` -/
lemma toInt_toInt_as_toNat_64 {r1 r2 : BitVec 32} :
  (r1.toInt * r2.toInt % 18446744073709551616).toNat =
    (BitVec.signExtend 64 r1 * BitVec.signExtend 64 r2).toNat
    := by
  rw [← BitVec.toInt_signExtend_of_le (v := 64) (x := r1) (by simp)]
  rw [← BitVec.toInt_signExtend_of_le (v := 64) (x := r2) (by simp)]

  have h_max : forall (x : ℤ), max (x % 18446744073709551616) 0 = x % 18446744073709551616 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 18446744073709551616) 0 = (r2.toNat : ℤ) % 18446744073709551616 := by omega
  have rr1 : (r1.toNat : ℤ) % 18446744073709551616 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 18446744073709551616 = r2.toNat := by omega

  simp [BitVec.toInt, BitVec.signExtend]; split_ifs

  all_goals
    simp_all
    try omega

  on_goal 1 => have : ((r1.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r1.toNat := by omega
  on_goal 2 => have : ((r2.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r2.toNat := by omega
  on_goal 3 => have : ((r1.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r1.toNat := by omega

  all_goals
    zify; simp_all [Int.toNat_add]
    ring_nf
    omega

/-- Helper for reasoning about `execute_MUL` -/
lemma toInt_toNat_as_toNat_64 {r1 r2 : BitVec 32} :
  (r1.toInt * r2.toNat % 18446744073709551616).toNat =
    (BitVec.signExtend 64 r1 * BitVec.setWidth 64 r2).toNat
    := by
  simp [← BitVec.toInt_signExtend_of_le (v := 64) (x := r1) (by simp)]

  have h_max : forall (x : ℤ), max (x % 18446744073709551616) 0 = x % 18446744073709551616 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 18446744073709551616) 0 = (r2.toNat : ℤ) % 18446744073709551616 := by omega
  have rr1 : (r1.toNat : ℤ) % 18446744073709551616 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 18446744073709551616 = r2.toNat := by omega

  simp [BitVec.toInt, BitVec.signExtend]; split_ifs

  all_goals
    simp_all
    try omega

  . have : ((r1.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r1.toNat := by omega
    zify; simp_all [Int.toNat_add]
    ring_nf
    omega

/-- Helper for reasoning about `execute_MUL` -/
lemma toNat_toInt_as_toNat_64 {r1 r2 : BitVec 32} :
  ((r1.toNat : ℤ) * r2.toInt % 18446744073709551616).toNat =
    (BitVec.setWidth 64 r1 * BitVec.signExtend 64 r2).toNat
    := by
  simp [← BitVec.toInt_signExtend_of_le (v := 64) (x := r2) (by simp)]

  have h_max : forall (x : ℤ), max (x % 18446744073709551616) 0 = x % 18446744073709551616 := by omega
  have mr1 : max ((r1.toNat : ℤ) % 18446744073709551616) 0 = (r1.toNat : ℤ) % 18446744073709551616 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 18446744073709551616) 0 = (r2.toNat : ℤ) % 18446744073709551616 := by omega
  have rr1 : (r1.toNat : ℤ) % 18446744073709551616 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 18446744073709551616 = r2.toNat := by omega

  simp [BitVec.toInt, BitVec.signExtend]; split_ifs

  all_goals
    simp_all
    try omega

  . have : ((r2.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r2.toNat := by omega
    zify; simp_all [Int.toNat_add]
    ring_nf
    omega

/-- Helper for reasoning about `execute_DIV` -/
lemma div_overflow {x y : ℤ} :
  -2147483648 ≤ x ∧ x < 2147483648 →
    -2147483648 ≤ y ∧ y < 2147483648 →
      (2147483648 ≤ x.tdiv y ↔ x = -2147483648 ∧ y = -1) := by
  intro hx hy
  constructor <;> intro hc
  have : (x.tdiv y).sign = 1 := by rw [Int.sign_cases, if_neg (by omega), if_neg (by omega)]
  rw [Int.sign_tdiv] at this
  split_ifs at this with hyp <;> [ simp_all; clear hyp ]
  . simp [Int.sign_cases] at this
    split_ifs at this <;> simp_all
    . suffices : -x = 2147483648 ∧ -y = 1
      . omega
      . have eq : x.tdiv y = (-x).tdiv (-y) := by simp
        rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
        by_cases yone : -y = 1
        . simp_all; omega
        . have := @Int.ediv_lt_self_of_pos_of_ne_one (-x) (-y) (by omega) (by omega)
          omega
    . rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
      by_cases yone : y = 1
      . simp_all; omega
      . have := @Int.ediv_lt_self_of_pos_of_ne_one x y (by omega) (by omega)
        omega
  . simp_all

lemma List.forall_in_range
  {n : ℕ}
  {P : ℕ → Prop}
  (m : ℕ)
  (in_range : m < n)
:
  List.Forall (fun n => P n) (List.range n) → P m
:= by
  induction n generalizing m
  case zero => simp_all
  case succ n ih => simp [List.range_add]; grind

end auxiliaries
