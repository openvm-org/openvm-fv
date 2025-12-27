import Mathlib

set_option maxHeartbeats 1_000_000_000

namespace Fin

  /-- A prime finite field has no zero divisors -/
  instance noZeroDivisors_of_prime (p : ℕ)
      [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
    refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

end Fin

namespace List

  lemma append_eq_append_split
    {T : Type}
    {a b c d : List T}
    (h_eq : a ++ b = c ++ d)
    (h_len_ab : a.length = c.length)
  :
    a = c ∧ b = d
  := by
    induction a generalizing b c d
    case nil => symm at h_len_ab; simp_all
    case cons a₀ a ih =>
      cases c
      case nil => grind
      case cons c₀ c =>
        simp_all
        apply ih <;> grind

  lemma flatMap_eq_flatMap
    {A B C : Type}
    {f : A → List C}
    {g : B → List C}
    {lf : List A}
    {lg : List B}
    (h_eq_fmap : flatMap f lf = flatMap g lg)
    (h_eq_len : lf.length = lg.length)
    (h_eq_len_fg : forall a b, (f a).length = (g b).length)
    (idx : ℕ)
    (h_idx : idx < lf.length)
  :
    f lf[idx] = g lg[idx]
  := by
    induction lf generalizing idx lg
    case nil => grind
    case cons f₀ lf ih =>
      cases lg
      case nil => grind
      case cons g₀ lg =>
        simp_all
        have h_eq'
        :
          flatMap f lf = flatMap g lg
        := by
          apply append_eq_append_split (h_len_ab := h_eq_len_fg f₀ g₀) at h_eq_fmap
          tauto
        cases idx
        case zero => simp_all
        case succ idx =>
          specialize @ih lg h_eq' (by grind)
          grind

  lemma forall_in_range
    {n : ℕ}
    {P : ℕ → Prop}
    (m : ℕ)
    (in_range : m < n)
  :
    Forall (fun n => P n) (range n) → P m
  := by
    induction n generalizing m
    case zero => simp_all
    case succ n ih => simp [range_add]; grind

end List

namespace BitVec

/-- `BitVec` extensionality as an iff -/
lemma ext_iff {n : ℕ} {x y : BitVec n} : x = y ↔ ∀ i : Fin n, x[i] = y[i] := by
  constructor <;> [ simp_all; intro heq ]
  . ext j lt_j
    exact heq ⟨ j, lt_j ⟩

/-- `BitVec` extension, signed and unsigned -/
def extend {m : ℕ} (bv : BitVec m) (n : ℕ) (sgn : Bool) :=
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

/-- Characterisation of `toInt` invertibility -/
lemma toInt_ofInt_eq_self_iff
  {w : Nat} (hw : 0 < w) {n : Int}
:
  (BitVec.ofInt w n).toInt = n ↔ -2 ^ (w - 1) ≤ n ∧ n < 2 ^ (w - 1)
:= by
  constructor <;> intro h
  . simp [BitVec.ofInt, BitVec.toInt] at h
    rw [Int.max_eq_left (by omega)] at h
    split_ifs at h with h'
    . replace h' : (n % 2 ^ w).toNat < 2 ^ (w - 1) := by
        rw [← Nat.mul_lt_mul_left (a := 2 ^ 1) (by omega)]
        apply lt_of_lt_of_le
        . exact h'
        . rw [← pow_add]
          apply pow_le_pow <;> omega
      have ⟨ lb_n, ub_n ⟩ : 0 ≤ n ∧ n < 2 ^ w := by omega
      rw [h] at *; clear h
      simp_all
      omega
    . replace h' : 2 ^ (w - 1) ≤ (n % 2 ^ w).toNat := by
        simp at h'
        suffices : 2 ^ 1 * 2 ^ (w - 1) ≤ 2 ^ 1 * (n % 2 ^ w).toNat
        . omega
        . rw [← pow_add]
          trans 2 ^ w
          . apply pow_le_pow <;> omega
          . simpa
      have ub_n : n < 0 := by omega
      split_ands <;> [ skip; grind ]
      replace h : n % 2 ^ w = n + 2 ^ w := by omega
      rw [h] at h'
      suffices : -2 ^ (w - 1) + 2 ^ w ≤ n + 2 ^ w
      . omega
      . trans 2 ^ (w - 1)
        . simp [← Int.two_mul]
          rw [mul_comm]
          simp [← pow_succ]
          have : (w - 1) + 1 = w := by omega
          simp [this]
        . zify at *; simp_all
          omega
  . apply BitVec.toInt_ofInt_eq_self <;> omega

/-- Reformulation of `sshiftRight` -/
lemma sshiftright_eq {n : ℕ} {bv : BitVec n} {shift : ℕ} :
  bv.sshiftRight shift =
    BitVec.setWidth n
      (BitVec.extractLsb ((n - 1) + shift) shift (BitVec.signExtend (n + shift) bv))
    := by grind

lemma xor_as_and
  {a b : ℕ}
  (ub_a : a < 256)
  (ub_b : b < 256)
:
  a ^^^ b = (a + b) - 2 * (a &&& b)
:= by
  have lt_b_and_c := @Nat.and_le_left a b
  have bv_xor_as_and : forall (a b : BitVec 9), a ^^^ b = (a + b) - 2 * (a &&& b) := by bv_decide
  specialize bv_xor_as_and { toFin := ⟨ a, by omega⟩ } { toFin := ⟨ b, by omega⟩ }
  simp [← BitVec.toNat_inj, Fin.add_def] at bv_xor_as_and
  rw [Nat.mod_eq_of_lt (a := 2 * (a &&& b)) (by omega)] at bv_xor_as_and
  have : (512 - 2 * (a &&& b) + (a + b)) % 512 < 256 := by rw [← bv_xor_as_and]; exact Nat.xor_lt_two_pow (n := 8) ub_a ub_b
  have : (512 - 2 * (a &&& b) + (a + b)) % 512 = (a + b) - 2 * (a &&& b) := by omega
  rw [this] at bv_xor_as_and
  exact bv_xor_as_and

lemma xor_as_or
  {a b : ℕ}
  (ub_a : a < 256)
  (ub_b : b < 256)
:
  a ^^^ b = 2 * (a ||| b) - (a + b)
:= by
  have := @Nat.left_le_or a b
  have := @Nat.or_lt_two_pow a b 8 ub_a ub_b
  have bv_xor_as_or : forall (a b : BitVec 9), a ^^^ b = 2 * (a ||| b) - (a + b) := by bv_decide
  specialize bv_xor_as_or { toFin := ⟨ a, by omega⟩ } { toFin := ⟨ b, by omega⟩ }
  simp [← BitVec.toNat_inj, Fin.add_def] at bv_xor_as_or
  rw [Nat.mod_eq_of_lt (a := a + b) (by omega)] at bv_xor_as_or
  have : (512 - (a + b) + 2 * (a ||| b)) % 512 < 256 := by rw [← bv_xor_as_or]; exact Nat.xor_lt_two_pow (n := 8) ub_a ub_b
  have : (512 - (a + b) + 2 * (a ||| b)) % 512 = 2 * (a ||| b) - (a + b) := by omega
  rw [this] at bv_xor_as_or
  exact bv_xor_as_or

lemma toInt_mod_eq_zero_of_bitvec_mod_eq_zero (bv: BitVec 13) (h: bv % 4 = 0):
  bv.toInt % 4 = 0
:= by
  simp at h ⊢
  have : (4: Int) = (4#13).toInt := rfl
  rewrite [this]
  apply BitVec.toInt_dvd_toInt_iff.mpr
  bv_decide

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

lemma tdiv_tmod_unique_full {b c q r : ℤ} (hcnz : c ≠ 0) :
  q = b.tdiv c ∧ r = b.tmod c ↔
  b = q * c + r ∧
  |r| < |c| ∧
  (r = 0 ∨ r.sign = b.sign) := by
  have hmod1 := @Int.tdiv_tmod_unique b c r q
  have hmod2 := @Int.tdiv_tmod_unique' b c r q
  rw [@eq_comm (a := q), @eq_comm (a := r), @eq_comm (a := b), add_comm, mul_comm]
  repeat rw [Int.natCast_natAbs] at *; repeat rw [Int.abs_cases] at *
  by_cases hb_split : 0 ≤ b
  . simp_all; intro heq; clear hmod1 hmod2
    constructor <;> intro ⟨ h0, h1 ⟩
    . simp_all
      by_cases hr_split : r = 0 <;> [ simp_all; right ]
      rw [Int.sign_eq_one_of_pos (by omega)]
      rw [Int.sign_eq_one_of_pos]
      suffices : ¬ b = 0
      . omega
      . intro bz; simp_all
        apply Int.split_nzp q <;> intro hq <;> [ skip; simp_all; skip ]
        all_goals
          have : c * q > r := by split_ifs at * <;> nlinarith
          omega
    . rcases h1 with rz | h_sign <;> [ omega; skip ]
      split_ifs with hc_split <;> split_ifs at h0 with hr_split <;> simp_all
      all_goals
        rw [Int.sign_eq_neg_one_of_neg (by assumption)] at h_sign
        symm at h_sign; rw [Int.sign_eq_neg_one_iff_neg] at h_sign
        omega
  . rw [hmod2 (by omega) hcnz]; simp_all; intro heq; clear hmod2
    constructor <;> intro ⟨ h0, h1 ⟩
    . constructor
      . by_cases hr_split : r = 0 <;> [ simp_all; skip ]
        rw [if_neg (by omega)]
        omega
      . by_cases hr_split : r = 0 <;> [ simp_all; right ]
        rw [Int.sign_eq_neg_one_of_neg (by omega)]
        rw [Int.sign_eq_neg_one_of_neg hb_split]
    . rcases h1 with rz | h_sign <;> [ omega; skip ]
      rw [Int.sign_eq_neg_one_of_neg hb_split] at h_sign
      rw [Int.sign_eq_neg_one_iff_neg] at h_sign
      rw [if_neg (by omega)] at h0
      omega

lemma tmod_range_32
  {b c : ℤ}
  (range_b : -2147483648 ≤ b ∧ b < 2147483648)
  (range_c : -2147483648 ≤ c ∧ c < 2147483648)
:
  -2147483648 ≤ b.tmod c ∧ b.tmod c < 2147483648
:= by
  apply Int.split_nzp b <;> intro hb
  rotate_left
  . simp_all
  rotate_right
  . have h_sgn := Int.sign_tmod b c
    split_ifs at h_sgn with h_dvd
    . simp [Int.sign_cases] at h_sgn
      grind
    . simp [Int.sign_cases] at h_sgn
      split_ifs at h_sgn with h_tmod; simp_all
      split_ands <;> [ skip; omega ]
      rw [b.tmod_eq_emod]
      split_ifs
      . omega
      . apply Int.split_nzp c <;> intro hc <;> simp_all
        . have h_abs : |c| = -c := by exact abs_of_neg hc
          simp [h_abs]; clear h_abs
          omega
        . have h_abs : |c| = c := by exact abs_of_pos hc
          simp [h_abs]; clear h_abs
          omega
  . have h_sgn := Int.sign_tmod b c
    split_ifs at h_sgn with h_dvd
    . simp [Int.sign_cases] at h_sgn
      grind
    . simp [Int.sign_cases] at h_sgn
      split_ifs at h_sgn with h_tmod <;> simp_all
      . omega
      . split_ands <;> [ omega; skip ]
        rw [b.tmod_eq_emod]
        split_ifs <;> simp_all
        next h0 h1 h2 =>
          replace tmod : 0 < b.tmod c := by omega
          clear h0 h1 h2 h_tmod
          apply Int.split_nzp c <;> intro hc
          . have := @Int.emod_lt_of_neg b c hc
            omega
          . simp_all
          . have := @Int.emod_lt_of_pos b c hc
            omega

lemma tdiv_overflow_32
  {b c : ℤ}
  (range_b : -2147483648 ≤ b ∧ b < 2147483648)
:
  (2147483648 ≤ b.tdiv c ↔ b = -2147483648 ∧ c = -1)
:= by
  constructor <;> intro hc
  have : (b.tdiv c).sign = 1 := by rw [Int.sign_cases, if_neg (by omega), if_neg (by omega)]
  rw [Int.sign_tdiv] at this
  split_ifs at this with hyp <;> [ simp_all; clear hyp ]
  . simp [Int.sign_cases] at this
    split_ifs at this <;> simp_all
    . suffices : -b = 2147483648 ∧ -c = 1
      . omega
      . have eq : b.tdiv c = (-b).tdiv (-c) := by simp
        rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
        by_cases yone : -c = 1
        . simp_all; omega
        . have := @Int.ediv_lt_self_of_pos_of_ne_one (-b) (-c) (by omega) (by omega)
          omega
    . rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
      by_cases yone : c = 1
      . simp_all; omega
      . have := @Int.ediv_lt_self_of_pos_of_ne_one b c (by omega) (by omega)
        omega
  . simp_all

lemma tdiv_range_32
  {b c : ℤ}
  (nzc : ¬(c = 0))
  (nof : ¬(b = -2147483648 ∧ c = -1))
  (range_b : -2147483648 ≤ b ∧ b < 2147483648)
  (range_c : -2147483648 ≤ c ∧ c < 2147483648)
:
  -2147483648 ≤ b.tdiv c ∧ b.tdiv c < 2147483648
:= by
  have sgn := Int.sign_tdiv b c
  split_ifs at sgn with h_sgn <;> zify at h_sgn
  . grind [sign_cases]
  . apply Int.split_nzp b <;> intro hb
    rotate_left
    . simp_all
    . apply Int.split_nzp c <;> intro hc
      . have : b.sign = 1 := by rw [← Int.sign_eq_one_iff_pos] at hb; assumption
        have : c.sign = -1 := by rw [← Int.sign_eq_neg_one_iff_neg] at hc; assumption
        split_ands <;> [ skip; (simp_all; omega) ]
        rw [Int.tdiv_eq_ediv]
        split_ifs with h_div <;> simp_all
        . trans -b
          . omega
          . trans b / (-1)
            . omega
            . suffices : -(-(b / (-c))) ≤ -(b / -1)
              . simp at this; omega
              . simp; rw [← Int.ediv_neg]
                apply Int.ediv_le_self
                omega
        . omega
      . simp_all
      . have : b.sign = 1 := by rw [← Int.sign_eq_one_iff_pos] at hb; assumption
        have : c.sign = 1 := by rw [← Int.sign_eq_one_iff_pos] at hc; assumption
        split_ands <;> [ (simp_all; omega); skip ]
        rw [Int.tdiv_eq_ediv]
        split_ifs with h_div <;> simp_all
        . apply lt_of_le_of_lt (b := b)
          . apply Int.ediv_le_self
            omega
          . omega
        . omega
    . apply Int.split_nzp c <;> intro hc
      . have : b.sign = -1 := by rw [← Int.sign_eq_neg_one_iff_neg] at hb; assumption
        have : c.sign = -1 := by rw [← Int.sign_eq_neg_one_iff_neg] at hc; assumption
        simp_all
        split_ands <;> [ omega; skip ]
        . by_contra h_div; simp at h_div
          rw [tdiv_overflow_32 range_b] at h_div
          omega
      . simp_all
      . have : b.sign = -1 := by rw [← sign_eq_neg_one_iff_neg] at hb; assumption
        have : c.sign = 1 := by rw [← Int.sign_eq_one_iff_pos] at hc; assumption
        split_ands <;> [ skip; (simp_all; omega) ]
        have eq : b.tdiv c = (-b).tdiv (-c) := by simp
        rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)]
        clear eq; simp
        trans (-b)
        . apply Int.ediv_le_self; omega
        . omega

end Int

namespace Nat.DivMod

lemma div_8 (a b : ℕ) :
  (a / 256 + b) / 256 = (a + b * 256) / 65536
    := by grind

lemma div_16 (a b : ℕ) :
  (a / 65536 + b) / 256 = (a + b * 65536) / 16777216
    := by grind

lemma div_24 (a b : ℕ) :
  (a / 16777216 + b) / 256 = (a + b * 16777216) / 4294967296
    := by grind

lemma div_32 (a b : ℕ) :
  (a / 4294967296 + b) / 256 = (a + b * 4294967296) / 1099511627776
    := by grind

lemma div_40 (a b : ℕ) :
  (a / 1099511627776 + b) / 256 = (a + b * 1099511627776) / 281474976710656
    := by grind

lemma div_48 (a b : ℕ) :
  (a / 281474976710656 + b) / 256 = (a + b * 281474976710656) / 72057594037927936
    := by grind

lemma div_56 (a b : ℕ) :
  (a / 72057594037927936 + b) / 256 = (a + b * 72057594037927936) / 18446744073709551616
    := by grind

lemma join_8 (a b : ℕ) :
  a % 256 + (a / 256 + b) % 256 * 256 = (a + b * 256) % 65536
    := by grind

lemma join_16 (a b : ℕ) :
  a % 65536 + (a / 65536 + b) % 256 * 65536 = (a + b * 65536) % 16777216
    := by grind

lemma join_24 (a b : ℕ) :
  a % 16777216 + (a / 16777216 + b) % 256 * 16777216 = (a + b * 16777216) % 4294967296
    := by grind

lemma join_24' (a : ℕ) :
  a % 16777216 + (a / 16777216) % 256 * 16777216 = a % 4294967296
    := by grind

lemma join_32 (a b : ℕ) :
  a % 4294967296 + (a / 4294967296 + b) % 256 * 4294967296 = (a + b * 4294967296) % 1099511627776
    := by grind

lemma join_40 (a b : ℕ) :
  a % 1099511627776 + (a / 1099511627776 + b) % 256 * 1099511627776 = (a + b * 1099511627776) % 281474976710656
    := by grind

lemma join_48 (a b : ℕ) :
  a % 281474976710656 + (a / 281474976710656 + b) % 256 * 281474976710656 = (a + b * 281474976710656) % 72057594037927936
    := by grind

lemma join_56 (a b : ℕ) :
  a % 72057594037927936 + (a / 72057594037927936 + b) % 256 * 72057594037927936 = (a + b * 72057594037927936) % 18446744073709551616
    := by grind

lemma join_56' (a : ℕ) :
  a % 72057594037927936 + (a / 72057594037927936) % 256 * 72057594037927936 = a % 18446744073709551616
    := by grind

end Nat.DivMod

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

lemma ite_neg_cond (a : Prop) (b c : T) [Decidable a] : (if a then b else c) = (if !a then c else b) := by grind

@[simp low] lemma to_the_right_nat_0 : 0 = a ↔ a = 0 := by omega
@[simp low] lemma to_the_right_nat_1 : 1 = a ↔ a = 1 := by omega
@[simp low] lemma to_the_right_nat_255 : 255 = a ↔ a = 255 := by omega
@[simp low] lemma to_the_right_nat_256 : 256 = a ↔ a = 256 := by omega

end auxiliaries
