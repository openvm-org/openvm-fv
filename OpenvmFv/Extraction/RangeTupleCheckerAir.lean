import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr RangeTupleCheckerAir_2_air_simplification
register_simp_attr RangeTupleCheckerAir_2_constraint_and_interaction_simplification

namespace RangeTupleCheckerAir_2.extraction

-----Constraints for RangeTupleCheckerAir<2>-----

-----Used Columns-------------------
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def inter_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t10 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
    let t11 := (t10 - 1)
    t11

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.isFirstRow c row) * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))
    t0 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t1 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) - 255)
    let t2 := ((Circuit.isLastRow c row) * t1)
    t2 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t3 := ((Circuit.isFirstRow c row) * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
    t3 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - 8191)
    let t5 := ((Circuit.isLastRow c row) * t4)
    t5 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t6 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))
    let t7 := (t6 - 1)
    let t8 := (t6 * t7)
    let t9 := ((Circuit.isTransitionRow c row) * t8)
    t9 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t12 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - 8191)
    let t13 := (inter_0 c row * t12)
    t13 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t16 := (inter_0 c row * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)))
    t16 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t17 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
    let t19 := (t17 * inter_0 c row)
    let t20 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))
    let t21 := -(t20)
    let t22 := (t21 * 2013265667)
    let t23 := (t22 + 2013265666)
    let t24 := (t19 * t23)
    let t25 := (t20 * t20)
    let t26 := (t17 * 2013249538)
    let t27 := (t26 - 67092481)
    let t28 := (t25 * t27)
    let t29 := (t24 + t28)
    t29 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 10 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t30 := -((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)))
          [(t30, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))])])
    else []

end RangeTupleCheckerAir_2.extraction
------
