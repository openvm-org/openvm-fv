import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VmAirWrapper_Rv32RdWriteAdapterAir_Rv32AuipcCoreAir_air_simplification
register_simp_attr VmAirWrapper_Rv32RdWriteAdapterAir_Rv32AuipcCoreAir_constraint_and_interaction_simplification

namespace VmAirWrapper_Rv32RdWriteAdapterAir_Rv32AuipcCoreAir.extraction

-----Constraints for VmAirWrapper<Rv32RdWriteAdapterAir, Rv32AuipcCoreAir>-----

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

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))
    let t3 := (t2 - (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)))
    let t4 := (2005401601 * t3)
    t4

  @[simp]
  def inter_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))
    let t9 := (t8 - (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)))
    let t13 := (t9 + inter_0 c row)
    let t14 := (2005401601 * t13)
    t14

  @[simp]
  def inter_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t18 := ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 256)
    let t19 := ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 65536)
    let t20 := (t18 + t19)
    let t21 := ((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)) + t20)
    let t22 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) - t21)
    let t23 := (t22 * 2013265801)
    t23

  @[simp]
  def inter_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t24 := (inter_2 c row + (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)))
    let t25 := (t24 - (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)))
    let t33 := (t25 + inter_1 c row)
    let t34 := (2005401601 * t33)
    t34

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t0)
    t1 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t5 := (inter_0 c row - 1)
    let t6 := (inter_0 c row * t5)
    let t7 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t6)
    t7 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t15 := (inter_1 c row - 1)
    let t16 := (inter_1 c row * t15)
    let t17 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t16)
    t17 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t35 := (inter_3 c row - 1)
    let t36 := (inter_3 c row * t35)
    let t37 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t36)
    t37 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t38 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))
    let t39 := (t38 - 1)
    let t40 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 131072)
    let t41 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) + t40)
    let t42 := (t39 - t41)
    let t43 := ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * t42)
    t43 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t44 := -((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
          let t45 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t46 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + 1)
          [(t44, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [t45, t46])])
      else if index = 1 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t47 := (2013265920 * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))
          [(t47, [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [1, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t48 := ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 256)
          let t49 := ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) + t48)
          let t50 := ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 65536)
          let t51 := (t49 + t50)
          [((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), 576, (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), 0, t51, 1, 0, 0, 0])])
      else if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)), 17]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), 12])])
      else if index = 6 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t58 := (inter_2 c row * 4)
          [((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0)), 0, 0]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 18) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 19) (row := row) (rotation := 0)), 0, 0]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)), 0, 0]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)), 0, 0]), ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)), t58, 0, 0])])
    else []

end VmAirWrapper_Rv32RdWriteAdapterAir_Rv32AuipcCoreAir.extraction
------
