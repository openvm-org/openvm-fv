import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32BaseAluAdapterAir_BaseAluCoreAir_4_8_air_simplification
register_simp_attr VmAirWrapper_Rv32BaseAluAdapterAir_BaseAluCoreAir_4_8_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32BaseAluAdapterAir_BaseAluCoreAir_4_8.extraction

-----Constraints for VmAirWrapper<Rv32BaseAluAdapterAir, BaseAluCoreAir<4, 8>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    let t11 := (t10 + (Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)))
    let t12 := (t11 + (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    t12

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t13 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    t13

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t14 := (inter_1 c row - 1)
    t14

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t16 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t17 := (t16 - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    let t18 := (2005401601 * t17)
    t18

  @[simp]
  def inter_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t22 := ((Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t23 := (t22 - (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
    let t24 := (2005401601 * t23)
    t24

  @[simp]
  def inter_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t28 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t29 := (t28 - (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
    let t33 := (t29 + inter_3 c row)
    let t34 := (2005401601 * t33)
    t34

  @[simp]
  def inter_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t38 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t39 := (t38 - (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t43 := (t39 + inter_4 c row)
    let t44 := (2005401601 * t43)
    t44

  @[simp]
  def inter_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t48 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t49 := (t48 - (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t57 := (t49 + inter_5 c row)
    let t58 := (2005401601 * t57)
    t58

  @[simp]
  def inter_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t62 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t63 := (t62 - (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t71 := (t63 + inter_6 c row)
    let t72 := (2005401601 * t71)
    t72

  @[simp]
  def inter_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t76 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t77 := (t76 - (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    let t89 := (t77 + inter_7 c row)
    let t90 := (2005401601 * t89)
    t90

  @[simp]
  def inter_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t94 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t95 := (t94 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t107 := (t95 + inter_8 c row)
    let t108 := (2005401601 * t107)
    t108

  @[simp]
  def inter_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t225 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t226 := (t225 + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    t226

  @[simp]
  def inter_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t227 := (1 - inter_11 c row)
    t227

  @[simp]
  def inter_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t228 := (inter_12 c row * (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    t228

  @[simp]
  def inter_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t254 := (inter_12 c row * (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
    t254

  @[simp]
  def inter_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t280 := (inter_12 c row * (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    t280

  @[simp]
  def inter_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t306 := (inter_12 c row * (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    t306

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) - 1)
    let t5 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) - 1)
    let t7 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t6)
    t7 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) - 1)
    let t9 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t8)
    t9 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t15 := (inter_1 c row * inter_2 c row)
    t15 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t19 := (inter_3 c row - 1)
    let t20 := (inter_3 c row * t19)
    let t21 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) * t20)
    t21 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t25 := (inter_4 c row - 1)
    let t26 := (inter_4 c row * t25)
    let t27 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t26)
    t27 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t35 := (inter_5 c row - 1)
    let t36 := (inter_5 c row * t35)
    let t37 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) * t36)
    t37 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t45 := (inter_6 c row - 1)
    let t46 := (inter_6 c row * t45)
    let t47 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t46)
    t47 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t59 := (inter_7 c row - 1)
    let t60 := (inter_7 c row * t59)
    let t61 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) * t60)
    t61 = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t73 := (inter_8 c row - 1)
    let t74 := (inter_8 c row * t73)
    let t75 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t74)
    t75 = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t91 := (inter_9 c row - 1)
    let t92 := (inter_9 c row * t91)
    let t93 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) * t92)
    t93 = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t109 := (inter_10 c row - 1)
    let t110 := (inter_10 c row * t109)
    let t111 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) * t110)
    t111 = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t112 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) - 1)
    let t113 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * t112)
    t113 = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t114 := (1 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t115 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * 256)
    let t116 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) + t115)
    let t117 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * 65536)
    let t118 := (t116 + t117)
    let t119 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) - t118)
    let t120 := (t114 * t119)
    t120 = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t121 := (1 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t122 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t123 := (t121 * t122)
    t123 = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t124 := (1 - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t125 := (255 - (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t126 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * t125)
    let t127 := (t124 * t126)
    t127 = 0

  @[simp]
  def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t132 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)))
    let t133 := (t132 - 1)
    let t134 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) * 131072)
    let t135 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) + t134)
    let t136 := (t133 - t135)
    let t137 := (inter_1 c row * t136)
    t137 = 0

  @[simp]
  def constraint_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t143 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * inter_2 c row)
    t143 = 0

  @[simp]
  def constraint_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t144 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t145 := (t144 - (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)))
    let t146 := (t145 - 1)
    let t147 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 131072)
    let t148 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) + t147)
    let t149 := (t146 - t148)
    let t150 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * t149)
    t150 = 0

  @[simp]
  def constraint_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t155 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
    let t156 := (t155 - (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
    let t157 := (t156 - 1)
    let t158 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 131072)
    let t159 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) + t158)
    let t160 := (t157 - t159)
    let t161 := (inter_1 c row * t160)
    t161 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t166 := -(inter_1 c row)
          let t170 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t171 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t172 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 3)
          [(t166, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t170, [t171, t172])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t177 := (2013265920 * inter_1 c row)
          let t181 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t182 := (2013265920 * (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
          let t183 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          let t188 := (2013265920 * inter_1 c row)
          let t192 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t193 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t177, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0))]), (t181, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t182, [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), t183]), (t188, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0))]), (t192, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), t193])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t197 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t198 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * 2)
          let t199 := ((Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)) + t198)
          let t200 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * 3)
          let t201 := (t199 + t200)
          let t202 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * 4)
          let t203 := (t201 + t202)
          let t204 := (512 + t203)
          [(t197, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t204, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 1, (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t208 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t212 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t216 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t220 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          [(t208, [(Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)), 17]), (t212, [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), 12]), (t216, [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 17]), (t220, [(Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t224 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t229 := (inter_11 c row * (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t230 := (inter_13 c row + t229)
          let t235 := (inter_11 c row * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t236 := (inter_13 c row + t235)
          let t237 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
          let t238 := (2 * (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
          let t239 := (t238 - (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t240 := (t239 - (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t241 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t240)
          let t242 := (t237 + t241)
          let t243 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t244 := (t243 - t238)
          let t245 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t244)
          let t246 := (t242 + t245)
          let t250 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t255 := (inter_11 c row * (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t256 := (inter_14 c row + t255)
          let t261 := (inter_11 c row * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t262 := (inter_14 c row + t261)
          let t263 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
          let t264 := (2 * (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
          let t265 := (t264 - (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
          let t266 := (t265 - (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t267 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t266)
          let t268 := (t263 + t267)
          let t269 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t270 := (t269 - t264)
          let t271 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t270)
          let t272 := (t268 + t271)
          let t276 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t281 := (inter_11 c row * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t282 := (inter_15 c row + t281)
          let t287 := (inter_11 c row * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t288 := (inter_15 c row + t287)
          let t289 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t290 := (2 * (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t291 := (t290 - (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
          let t292 := (t291 - (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t293 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t292)
          let t294 := (t289 + t293)
          let t295 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t296 := (t295 - t290)
          let t297 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t296)
          let t298 := (t294 + t297)
          let t302 := (inter_0 c row + (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t307 := (inter_11 c row * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
          let t308 := (inter_16 c row + t307)
          let t313 := (inter_11 c row * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t314 := (inter_16 c row + t313)
          let t315 := ((Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
          let t316 := (2 * (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
          let t317 := (t316 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
          let t318 := (t317 - (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t319 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * t318)
          let t320 := (t315 + t319)
          let t321 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t322 := (t321 - t316)
          let t323 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * t322)
          let t324 := (t320 + t323)
          let t329 := (inter_1 c row - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
          [(t224, [t230, t236, t246, 1]), (t250, [t256, t262, t272, 1]), (t276, [t282, t288, t298, 1]), (t302, [t308, t314, t324, 1]), (t329, [(Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), 0, 0])])
    else []

end VmAirWrapper_Rv32BaseAluAdapterAir_BaseAluCoreAir_4_8.extraction
------
