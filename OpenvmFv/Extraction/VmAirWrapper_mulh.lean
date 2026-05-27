import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32MultAdapterAir_MulHCoreAir_4_8_air_simplification
register_simp_attr VmAirWrapper_Rv32MultAdapterAir_MulHCoreAir_4_8_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32MultAdapterAir_MulHCoreAir_4_8.extraction

-----Constraints for VmAirWrapper<Rv32MultAdapterAir, MulHCoreAir<4, 8>-----

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
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 37) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 38) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
    let t7 := (t6 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
    t7

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t100 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t101 := (t100 - (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    t101

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t107 := (2005401601 * inter_1 c row)
    let t108 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t109 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t110 := (t108 + t109)
    let t111 := (t107 + t110)
    let t112 := (t111 - (Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)))
    t112

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t124 := (2005401601 * inter_2 c row)
    let t125 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t126 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t127 := (t125 + t126)
    let t128 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t129 := (t127 + t128)
    let t130 := (t124 + t129)
    let t131 := (t130 - (Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)))
    t131

  @[simp]
  def inter_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t151 := (2005401601 * inter_3 c row)
    let t152 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t153 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t154 := (t152 + t153)
    let t155 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t156 := (t154 + t155)
    let t157 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t158 := (t156 + t157)
    let t159 := (t151 + t158)
    let t160 := (t159 - (Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)))
    t160

  @[simp]
  def inter_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t197 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    let t198 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t199 := (t197 + t198)
    t199

  @[simp]
  def inter_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t190 := (2005401601 * inter_4 c row)
    let t191 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t192 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t193 := (t191 + t192)
    let t194 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t195 := (t193 + t194)
    let t196 := (t190 + t195)
    let t200 := (t196 + inter_5 c row)
    let t201 := (t200 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t201

  @[simp]
  def inter_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t248 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    let t249 := (inter_5 c row + t248)
    let t250 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t251 := (t249 + t250)
    t251

  @[simp]
  def inter_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t243 := (2005401601 * inter_6 c row)
    let t244 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t245 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t246 := (t244 + t245)
    let t247 := (t243 + t246)
    let t252 := (t247 + inter_7 c row)
    let t253 := (t252 - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    t253

  @[simp]
  def inter_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t309 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
    let t310 := (inter_7 c row + t309)
    let t311 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
    let t312 := (t310 + t311)
    t312

  @[simp]
  def inter_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t306 := (2005401601 * inter_8 c row)
    let t307 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t308 := (t306 + t307)
    let t313 := (t308 + inter_9 c row)
    let t314 := (t313 - (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
    t314

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)) - 1)
    let t5 := ((Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := (inter_0 c row - 1)
    let t9 := (inter_0 c row * t8)
    t9 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * 465814468)
    let t11 := (t10 - 1)
    let t12 := (t10 * t11)
    t12 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t13 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * 465814468)
    let t14 := (t13 - 1)
    let t15 := (t13 * t14)
    t15 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t16 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * 465814468)
    let t17 := ((Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)) * t16)
    t17 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t18 := ((Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
    let t19 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * 465814468)
    let t20 := (t18 * t19)
    t20 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t23 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t24 := (t23 - 1)
    let t25 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 131072)
    let t26 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) + t25)
    let t27 := (t24 - t26)
    let t28 := (inter_0 c row * t27)
    t28 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t31 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t32 := (t31 - (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)))
    let t33 := (t32 - 1)
    let t34 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 131072)
    let t35 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) + t34)
    let t36 := (t33 - t35)
    let t37 := (inter_0 c row * t36)
    t37 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t40 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
    let t41 := (t40 - (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
    let t42 := (t41 - 1)
    let t43 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 131072)
    let t44 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) + t43)
    let t45 := (t42 - t44)
    let t46 := (inter_0 c row * t45)
    t46 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t49 := -(inter_0 c row)
          let t50 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t51 := (t50 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t52 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t53 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 3)
          [(t49, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t51, [t52, t53])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t56 := (2013265920 * inter_0 c row)
          let t57 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t58 := (t57 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t61 := (2013265920 * inter_0 c row)
          let t62 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t63 := (t62 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t64 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          let t67 := (2013265920 * inter_0 c row)
          let t68 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t69 := (t68 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t70 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t56, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0))]), (t58, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t61, [1, (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0))]), (t63, [1, (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), t64]), (t67, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0))]), (t69, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), t70])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t71 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t72 := (t71 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t73 := ((Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)) * 2)
          let t74 := ((Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)) + t73)
          let t75 := (593 + t74)
          [(t72, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t75, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 1, 0, 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t76 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t77 := (t76 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t78 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t79 := (t78 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t80 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t81 := (t80 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t82 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t83 := (t82 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t84 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t85 := (t84 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t86 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t87 := (t86 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          [(t77, [(Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), 17]), (t79, [(Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)), 12]), (t81, [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 17]), (t83, [(Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), 12]), (t85, [(Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), 17]), (t87, [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t88 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t89 := ((Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)) * 465814468)
          let t90 := (t89 * 128)
          let t91 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - t90)
          let t92 := (2 * t91)
          let t93 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + 1)
          let t94 := ((Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)) * 465814468)
          let t95 := (t94 * 128)
          let t96 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) - t95)
          let t97 := (t93 * t96)
          [(t88, [t92, t97, 0, 0])])
      else if index = 10 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t98 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t99 := (t98 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t102 := (2005401601 * inter_1 c row)
          let t103 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t104 := (t103 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t113 := (2005401601 * inter_2 c row)
          let t114 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t115 := (t114 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t132 := (2005401601 * inter_3 c row)
          let t133 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t134 := (t133 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t161 := (2005401601 * inter_4 c row)
          let t162 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t163 := (t162 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t202 := (2005401601 * inter_6 c row)
          let t203 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t204 := (t203 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t254 := (2005401601 * inter_8 c row)
          let t255 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t256 := (t255 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t315 := (2005401601 * inter_10 c row)
          let t316 := ((Circuit.main c (id := 0) (column := 36) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 37) (row := row) (rotation := 0)))
          let t317 := (t316 + (Circuit.main c (id := 0) (column := 38) (row := row) (rotation := 0)))
          let t376 := (2005401601 * inter_10 c row)
          let t377 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 35) (row := row) (rotation := 0)))
          let t378 := (inter_9 c row + t377)
          let t379 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 34) (row := row) (rotation := 0)))
          let t380 := (t378 + t379)
          let t381 := (t376 + t380)
          let t382 := (t381 - (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t383 := (2005401601 * t382)
          [(t99, [(Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), t102]), (t104, [(Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)), t113]), (t115, [(Circuit.main c (id := 0) (column := 32) (row := row) (rotation := 0)), t132]), (t134, [(Circuit.main c (id := 0) (column := 33) (row := row) (rotation := 0)), t161]), (t163, [(Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), t202]), (t204, [(Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), t254]), (t256, [(Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), t315]), (t317, [(Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), t383])])
    else []

end VmAirWrapper_Rv32MultAdapterAir_MulHCoreAir_4_8.extraction
------
