import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32MultAdapterAir_MultiplicationCoreAir_4_8_air_simplification
register_simp_attr VmAirWrapper_Rv32MultAdapterAir_MultiplicationCoreAir_4_8_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32MultAdapterAir_MultiplicationCoreAir_4_8.extraction

-----Constraints for VmAirWrapper<Rv32MultAdapterAir, MultiplicationCoreAir<4, 8>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t30 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t31 := (t30 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    t31

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t35 := (2005401601 * inter_0 c row)
    let t36 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t37 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t38 := (t36 + t37)
    let t39 := (t35 + t38)
    let t40 := (t39 - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    t40

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t50 := (2005401601 * inter_1 c row)
    let t51 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
    let t52 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
    let t53 := (t51 + t52)
    let t54 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t55 := (t53 + t54)
    let t56 := (t50 + t55)
    let t57 := (t56 - (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
    t57

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
    let t3 := (t2 - 1)
    let t4 := ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 131072)
    let t5 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) + t4)
    let t6 := (t3 - t5)
    let t7 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) * t6)
    t7 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t9 := (t8 - (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)))
    let t10 := (t9 - 1)
    let t11 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 131072)
    let t12 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) + t11)
    let t13 := (t10 - t12)
    let t14 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) * t13)
    t14 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t15 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
    let t16 := (t15 - (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
    let t17 := (t16 - 1)
    let t18 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 131072)
    let t19 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) + t18)
    let t20 := (t17 - t19)
    let t21 := ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)) * t20)
    t21 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t22 := -((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t23 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t24 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 3)
          [(t22, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [t23, t24])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t25 := (2013265920 * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t26 := (2013265920 * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t27 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          let t28 := (2013265920 * (Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)))
          let t29 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t25, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t26, [1, (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)), t27]), (t28, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), t29])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), 592, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 1, 0, 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 12])])
      else if index = 10 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t32 := (2005401601 * inter_0 c row)
          let t41 := (2005401601 * inter_1 c row)
          let t58 := (2005401601 * inter_2 c row)
          let t75 := (2005401601 * inter_2 c row)
          let t76 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 29) (row := row) (rotation := 0)))
          let t77 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 28) (row := row) (rotation := 0)))
          let t78 := (t76 + t77)
          let t79 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)))
          let t80 := (t78 + t79)
          let t81 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
          let t82 := (t80 + t81)
          let t83 := (t75 + t82)
          let t84 := (t83 - (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t85 := (2005401601 * t84)
          [((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), t32]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), t41]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), t58]), ((Circuit.main c (id := 0) (column := 30) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), t85])])
    else []

end VmAirWrapper_Rv32MultAdapterAir_MultiplicationCoreAir_4_8.extraction
------
