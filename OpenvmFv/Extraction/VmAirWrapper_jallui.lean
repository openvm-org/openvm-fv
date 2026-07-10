import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32CondRdWriteAdapterAir_Rv32JalLuiCoreAir_air_simplification
register_simp_attr VmAirWrapper_Rv32CondRdWriteAdapterAir_Rv32JalLuiCoreAir_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32CondRdWriteAdapterAir_Rv32JalLuiCoreAir.extraction

-----Constraints for VmAirWrapper<Rv32CondRdWriteAdapterAir, Rv32JalLuiCoreAir>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 256)
    let t9 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) + t8)
    let t10 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 65536)
    let t11 := (t9 + t10)
    t11

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) * t2)
    t3 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
    let t5 := (t4 - 1)
    let t6 := (t4 * t5)
    t6 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t7 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
    t7 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t12 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 16)
    let t13 := (inter_0 c row - t12)
    let t14 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * t13)
    t14 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t19 := (inter_0 c row * 256)
    let t20 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) + t19)
    let t21 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
    let t22 := (t20 - t21)
    let t23 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) * t22)
    t23 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t24 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) - 1)
    let t25 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t24)
    t25 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t26 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
    let t27 := (1 - t26)
    let t28 := (t27 * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
    t28 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t29 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))
    let t30 := (t29 - 1)
    let t31 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 131072)
    let t32 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) + t31)
    let t33 := (t30 - t32)
    let t34 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t33)
    t34 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t35 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
          let t36 := -(t35)
          let t37 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
          let t38 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) * 4)
          let t39 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + t38)
          let t40 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) * (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
          let t41 := (t39 + t40)
          let t42 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          [(t36, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), (t37, [t41, t42])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t43 := (2013265920 * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
          [(t43, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t44 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
          let t45 := (560 + (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
          [(t44, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), t45, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), 0, (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), 1, 0, (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t46 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
          let t47 := ((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)))
          let t48 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) + 192)
          [(t46, [(Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), 0, 0]), (t47, [(Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), 0, 0]), ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), 192, t48, 1])])
    else []

end VmAirWrapper_Rv32CondRdWriteAdapterAir_Rv32JalLuiCoreAir.extraction
------
