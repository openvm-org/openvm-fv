import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VariableRangeCheckerAir_air_simplification
register_simp_attr VariableRangeCheckerAir_constraint_and_interaction_simplification

namespace VariableRangeCheckerAir.extraction

-----Constraints for VariableRangeCheckerAir-----

-----Used Columns-------------------
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 1)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 3) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.isFirstRow c row) * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))
    t0 = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t1 := ((Circuit.isFirstRow c row) * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
    t1 = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t2 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) - 1)
    let t3 := ((Circuit.isFirstRow c row) * t2)
    t3 = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t4 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
    let t5 := (t4 - 1)
    let t6 := (t4 * t5)
    let t7 := ((Circuit.isTransitionRow c row) * t6)
    t7 = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t8 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 1)
    let t9 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) - t8)
    let t10 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) * t9)
    let t11 := ((Circuit.isTransitionRow c row) * t10)
    t11 = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t12 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))
    let t13 := (1 + t12)
    let t14 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * t13)
    let t15 := ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 1)) - t14)
    let t16 := ((Circuit.isTransitionRow c row) * t15)
    t16 = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t17 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)))
    let t18 := (t17 + 1)
    let t19 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) + (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 1)))
    let t20 := (t18 - t19)
    let t21 := ((Circuit.isTransitionRow c row) * t20)
    t21 = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t22 := ((Circuit.isLastRow c row) * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))
    t22 = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t23 := ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - 18)
    let t24 := ((Circuit.isLastRow c row) * t23)
    t24 = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t25 := ((Circuit.isLastRow c row) * (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))
    t25 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 3 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t26 := -((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))
          [(t26, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))])])
    else []

end VariableRangeCheckerAir.extraction
------
