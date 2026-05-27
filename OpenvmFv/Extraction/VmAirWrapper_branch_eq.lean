import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32BranchAdapterAir_BranchEqualCoreAir_4_air_simplification
register_simp_attr VmAirWrapper_Rv32BranchAdapterAir_BranchEqualCoreAir_4_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32BranchAdapterAir_BranchEqualCoreAir_4.extraction

-----Constraints for VmAirWrapper<Rv32BranchAdapterAir, BranchEqualCoreAir<4>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t9 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)))
    let t10 := (1 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    let t11 := (t10 * (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t12 := (t9 + t11)
    t12

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
    let t4 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t5 := (t4 - 1)
    let t6 := (t4 * t5)
    t6 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t7 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) - 1)
    let t8 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) * t7)
    t8 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t13 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
    let t14 := (inter_0 c row * t13)
    t14 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t19 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)))
    let t20 := (inter_0 c row * t19)
    t20 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t25 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
    let t26 := (inter_0 c row * t25)
    t26 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t31 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
    let t32 := (inter_0 c row * t31)
    t32 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t33 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t38 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
    let t39 := (t38 * (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)))
    let t40 := (inter_0 c row + t39)
    let t41 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)))
    let t42 := (t41 * (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
    let t43 := (t40 + t42)
    let t44 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
    let t45 := (t44 * (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t46 := (t43 + t45)
    let t47 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
    let t48 := (t47 * (Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)))
    let t49 := (t46 + t48)
    let t50 := (t49 - 1)
    let t51 := (t33 * t50)
    t51 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t52 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t53 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)))
    let t54 := (t53 - 1)
    let t55 := ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 131072)
    let t56 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) + t55)
    let t57 := (t54 - t56)
    let t58 := (t52 * t57)
    t58 = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t59 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
    let t60 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t61 := (t60 - (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)))
    let t62 := (t61 - 1)
    let t63 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 131072)
    let t64 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + t63)
    let t65 := (t62 - t64)
    let t66 := (t59 * t65)
    t66 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t67 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t68 := -(t67)
          let t69 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t70 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
          let t71 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + t70)
          let t72 := (1 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
          let t73 := (t72 * 4)
          let t74 := (t71 + t73)
          let t75 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t68, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t69, [t74, t75])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t76 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t77 := (2013265920 * t76)
          let t78 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t79 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t80 := (2013265920 * t79)
          let t81 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t82 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          [(t77, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0))]), (t78, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t80, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0))]), (t81, [1, (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), t82])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t83 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t84 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) + 544)
          [(t83, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t84, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), 1, 1, 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t85 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t86 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t87 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          let t88 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)))
          [(t85, [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 17]), (t86, [(Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), 12]), (t87, [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 17]), (t88, [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 12])])
    else []

end VmAirWrapper_Rv32BranchAdapterAir_BranchEqualCoreAir_4.extraction
------
