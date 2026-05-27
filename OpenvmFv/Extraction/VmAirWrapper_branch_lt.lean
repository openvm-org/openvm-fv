import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32BranchAdapterAir_BranchLessThanCoreAir_4_8_air_simplification
register_simp_attr VmAirWrapper_Rv32BranchAdapterAir_BranchLessThanCoreAir_4_8_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32BranchAdapterAir_BranchLessThanCoreAir_4_8.extraction

-----Constraints for VmAirWrapper<Rv32BranchAdapterAir, BranchLessThanCoreAir<4, 8>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t9 := (t8 + (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    t9

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
    t10

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t32 := (2 * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t33 := (t32 - 1)
    t33

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t31 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t34 := (t31 * inter_2 c row)
    t34

  @[simp]
  def inter_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t46 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
    let t49 := (t46 * inter_2 c row)
    t49

  @[simp]
  def inter_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t59 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t60 := (t59 + (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    t60

  @[simp]
  def inter_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t62 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
    let t65 := (t62 * inter_2 c row)
    t65

  @[simp]
  def inter_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t77 := (inter_5 c row + (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    t77

  @[simp]
  def inter_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t78 := (1 - inter_7 c row)
    t78

  @[simp]
  def inter_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t79 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    let t82 := (t79 * inter_2 c row)
    t82

  @[simp]
  def inter_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t170 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    let t171 := (128 * t170)
    t171

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) - 1)
    let t5 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - 1)
    let t7 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t6)
    t7 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t11 := (inter_1 c row - 1)
    let t12 := (inter_1 c row * t11)
    t12 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t13 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) - 1)
    let t14 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) * t13)
    t14 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t15 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t16 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) * t15)
    let t17 := (1 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    let t18 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
    let t19 := (t17 * t18)
    let t20 := (t16 + t19)
    let t21 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) - t20)
    t21 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t22 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t23 := (256 - t22)
    let t24 := (t22 * t23)
    t24 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t25 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t26 := (256 - t25)
    let t27 := (t25 * t26)
    t27 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t28 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) - 1)
    let t29 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) * t28)
    t29 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t30 := (1 - (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
    let t35 := (t30 * inter_3 c row)
    t35 = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t40 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - inter_3 c row)
    let t41 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) * t40)
    t41 = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t42 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) - 1)
    let t43 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * t42)
    t43 = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t44 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
    let t45 := (1 - t44)
    let t50 := (t45 * inter_4 c row)
    t50 = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t55 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - inter_4 c row)
    let t56 := ((Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)) * t55)
    t56 = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t57 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) - 1)
    let t58 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * t57)
    t58 = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t61 := (1 - inter_5 c row)
    let t66 := (t61 * inter_6 c row)
    t66 = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t71 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - inter_6 c row)
    let t72 := ((Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)) * t71)
    t72 = 0

  @[simp]
  def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t73 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t74 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t73)
    t74 = 0

  @[simp]
  def constraint_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t83 := (inter_8 c row * inter_9 c row)
    t83 = 0

  @[simp]
  def constraint_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t88 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - inter_9 c row)
    let t89 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t88)
    t89 = 0

  @[simp]
  def constraint_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t93 := (inter_7 c row - 1)
    let t94 := (inter_7 c row * t93)
    t94 = 0

  @[simp]
  def constraint_22 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t99 := (inter_8 c row * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    t99 = 0

  @[simp]
  def constraint_23 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t103 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)))
    let t104 := (t103 - 1)
    let t105 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 131072)
    let t106 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) + t105)
    let t107 := (t104 - t106)
    let t108 := (inter_1 c row * t107)
    t108 = 0

  @[simp]
  def constraint_24 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t112 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t113 := (t112 - (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)))
    let t114 := (t113 - 1)
    let t115 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 131072)
    let t116 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + t115)
    let t117 := (t114 - t116)
    let t118 := (inter_1 c row * t117)
    t118 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t122 := -(inter_1 c row)
          let t125 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t126 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
          let t127 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + t126)
          let t128 := (1 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
          let t129 := (t128 * 4)
          let t130 := (t127 + t129)
          let t131 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t122, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t125, [t130, t131])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t135 := (2013265920 * inter_1 c row)
          let t138 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t142 := (2013265920 * inter_1 c row)
          let t145 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t146 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          [(t135, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0))]), (t138, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t142, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0))]), (t145, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), t146])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t149 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t150 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * 2)
          let t151 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) + t150)
          let t152 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * 3)
          let t153 := (t151 + t152)
          let t154 := (t153 + 549)
          [(t149, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t154, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), 1, 1, 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t157 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t160 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t163 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t166 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          [(t157, [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 17]), (t160, [(Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), 12]), (t163, [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 17]), (t166, [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t169 := (inter_0 c row + (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t172 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) + inter_10 c row)
          let t175 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) + inter_10 c row)
          let t178 := (inter_5 c row + (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t179 := ((Circuit.main c (id := 0) (column := 31) (row := row) (rotation := 0)) - 1)
          [(t169, [t172, t175, 0, 0]), (t178, [t179, 0, 0, 0])])
    else []

end VmAirWrapper_Rv32BranchAdapterAir_BranchLessThanCoreAir_4_8.extraction
------
