import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32BaseAluAdapterAir_LessThanCoreAir_4_8_air_simplification
register_simp_attr VmAirWrapper_Rv32BaseAluAdapterAir_LessThanCoreAir_4_8_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32BaseAluAdapterAir_LessThanCoreAir_4_8.extraction

-----Constraints for VmAirWrapper<Rv32BaseAluAdapterAir, LessThanCoreAir<4, 8>-----

-----Used Columns-------------------
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 3) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 4) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 5) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 6) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 7) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 8) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 9) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 10) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 11) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 12) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 13) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 14) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 15) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 16) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 17) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 18) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 19) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 20) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 21) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 22) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 23) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 24) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 25) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 26) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 27) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 28) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 29) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 30) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 31) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 32) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 33) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 34) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 35) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 36) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t5 := (t4 - 1)
    t5

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t19 := (2 * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t20 := (t19 - 1)
    t20

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t18 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t21 := (t18 * inter_1 c row)
    t21

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t33 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t36 := (t33 * inter_1 c row)
    t36

  @[simp]
  def inter_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t46 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t47 := (t46 + (Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)))
    t47

  @[simp]
  def inter_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t49 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
    let t52 := (t49 * inter_1 c row)
    t52

  @[simp]
  def inter_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t64 := (inter_4 c row + (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    t64

  @[simp]
  def inter_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t65 := (1 - inter_6 c row)
    t65

  @[simp]
  def inter_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t66 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    let t69 := (t66 * inter_1 c row)
    t69

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t6 := (t4 * inter_0 c row)
    t6 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t7 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t8 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t7)
    t8 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t9 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t10 := (256 - t9)
    let t11 := (t9 * t10)
    t11 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t12 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
    let t13 := (256 - t12)
    let t14 := (t12 * t13)
    t14 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t15 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) - 1)
    let t16 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t15)
    t16 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t17 := (1 - (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    let t22 := (t17 * inter_2 c row)
    t22 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t27 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) - inter_2 c row)
    let t28 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t27)
    t28 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t29 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) - 1)
    let t30 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t29)
    t30 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t31 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t32 := (1 - t31)
    let t37 := (t32 * inter_3 c row)
    t37 = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t42 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) - inter_3 c row)
    let t43 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t42)
    t43 = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t44 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) - 1)
    let t45 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * t44)
    t45 = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t48 := (1 - inter_4 c row)
    let t53 := (t48 * inter_5 c row)
    t53 = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t58 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) - inter_5 c row)
    let t59 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * t58)
    t59 = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t60 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) - 1)
    let t61 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t60)
    t61 = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t70 := (inter_7 c row * inter_8 c row)
    t70 = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t75 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) - inter_8 c row)
    let t76 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t75)
    t76 = 0

  @[simp]
  def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t80 := (inter_6 c row - 1)
    let t81 := (inter_6 c row * t80)
    t81 = 0

  @[simp]
  def constraint_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t86 := (inter_7 c row * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    t86 = 0

  @[simp]
  def constraint_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t87 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) - 1)
    let t88 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * t87)
    t88 = 0

  @[simp]
  def constraint_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t89 := (1 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t90 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * 256)
    let t91 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + t90)
    let t92 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * 65536)
    let t93 := (t91 + t92)
    let t94 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) - t93)
    let t95 := (t89 * t94)
    t95 = 0

  @[simp]
  def constraint_22 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t96 := (1 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t97 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t98 := (t96 * t97)
    t98 = 0

  @[simp]
  def constraint_23 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t99 := (1 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t100 := (255 - (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t101 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * t100)
    let t102 := (t99 * t101)
    t102 = 0

  @[simp]
  def constraint_24 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t103 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t104 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)))
    let t105 := (t104 - 1)
    let t106 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) * 131072)
    let t107 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) + t106)
    let t108 := (t105 - t107)
    let t109 := (t103 * t108)
    t109 = 0

  @[simp]
  def constraint_25 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t112 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * inter_0 c row)
    t112 = 0

  @[simp]
  def constraint_26 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t113 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t114 := (t113 - (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)))
    let t115 := (t114 - 1)
    let t116 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 131072)
    let t117 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) + t116)
    let t118 := (t115 - t117)
    let t119 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * t118)
    t119 = 0

  @[simp]
  def constraint_27 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t120 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t121 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
    let t122 := (t121 - (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
    let t123 := (t122 - 1)
    let t124 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 131072)
    let t125 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) + t124)
    let t126 := (t123 - t125)
    let t127 := (t120 * t126)
    t127 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t128 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t129 := -(t128)
          let t130 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t131 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t132 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 3)
          [(t129, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t130, [t131, t132])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t133 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t134 := (2013265920 * t133)
          let t135 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t136 := (2013265920 * (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
          let t137 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          let t138 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t139 := (2013265920 * t138)
          let t140 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t141 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t134, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0))]), (t135, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t136, [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), t137]), (t139, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0))]), (t140, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), 0, 0, 0, t141])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t142 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t143 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) + 520)
          [(t142, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t143, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 1, (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t144 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t145 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t146 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t147 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          [(t144, [(Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)), 17]), (t145, [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), 12]), (t146, [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 17]), (t147, [(Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t148 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t149 := (128 * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t150 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) + t149)
          let t151 := (128 * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t152 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) + t151)
          let t155 := (inter_4 c row + (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
          let t156 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) - 1)
          let t157 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t158 := (t157 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
          [(t148, [t150, t152, 0, 0]), (t155, [t156, 0, 0, 0]), (t158, [(Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), 0, 0])])
    else []

end VmAirWrapper_Rv32BaseAluAdapterAir_LessThanCoreAir_4_8.extraction
------
