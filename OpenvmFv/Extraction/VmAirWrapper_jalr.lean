import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32JalrAdapterAir_Rv32JalrCoreAir_air_simplification
register_simp_attr VmAirWrapper_Rv32JalrAdapterAir_Rv32JalrCoreAir_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32JalrAdapterAir_Rv32JalrCoreAir.extraction

-----Constraints for VmAirWrapper<Rv32JalrAdapterAir, Rv32JalrCoreAir>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * 256)
    let t7 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) + t6)
    let t8 := (t7 + (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)))
    let t9 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * 2)
    let t10 := (t8 - t9)
    let t11 := (t10 - (Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)))
    let t12 := (t11 * 2013235201)
    t12

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t16 := ((Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)) * 256)
    let t17 := ((Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)) + t16)
    let t18 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * 65535)
    let t19 := (t17 + t18)
    let t27 := (t19 + inter_0 c row)
    let t28 := (t27 - (Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)))
    let t29 := (t28 * 2013235201)
    t29

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t58 := ((Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)) * 256)
    let t59 := ((Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)) * 65536)
    let t60 := (t58 + t59)
    let t61 := ((Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)) * 16777216)
    let t62 := (t60 + t61)
    t62

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) - 1)
    let t5 := ((Circuit.main c (id := 0) (column := 24) (row := row) (rotation := 0)) * t4)
    t5 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t13 := (inter_0 c row - 1)
    let t14 := (inter_0 c row * t13)
    let t15 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t14)
    t15 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t30 := (inter_1 c row - 1)
    let t31 := (inter_1 c row * t30)
    let t32 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t31)
    t32 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t33 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) - 1)
    let t34 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * t33)
    t34 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t35 := (1 - (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
    let t36 := (t35 * (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
    t36 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t37 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))
    let t38 := (t37 - 1)
    let t39 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 131072)
    let t40 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) + t39)
    let t41 := (t38 - t40)
    let t42 := ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)) * t41)
    t42 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t43 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
    let t44 := (t43 - (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)))
    let t45 := (t44 - 1)
    let t46 := ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 131072)
    let t47 := ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + t46)
    let t48 := (t45 - t47)
    let t49 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * t48)
    t49 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t50 := -((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t51 := ((Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)) * 2)
          let t52 := ((Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)) * 65536)
          let t53 := (t51 + t52)
          let t54 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 2)
          [(t50, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [t53, t54])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t55 := (2013265920 * (Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)))
          let t56 := (2013265920 * (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))
          let t57 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t63 := (t57 - inter_2 c row)
          let t64 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          [(t55, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t56, [1, (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), t63, (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), t64])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), 565, (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), 1, 0, (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 27) (row := row) (rotation := 0))])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 21) (row := row) (rotation := 0)), 8]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 22) (row := row) (rotation := 0)), 6]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 26) (row := row) (rotation := 0)), 14]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 25) (row := row) (rotation := 0)), 15]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 12]), ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t65 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t71 := (t65 - inter_2 c row)
          [((Circuit.main c (id := 0) (column := 23) (row := row) (rotation := 0)), [t71, (Circuit.main c (id := 0) (column := 20) (row := row) (rotation := 0)), 0, 0])])
    else []

end VmAirWrapper_Rv32JalrAdapterAir_Rv32JalrCoreAir.extraction
------
