import Mathlib.Algebra.Field.Basic

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr PhantomAir_air_simplification
register_simp_attr PhantomAir_constraint_and_interaction_simplification

namespace PhantomAir.extraction

-----Constraints for PhantomAir-----

-----Used Columns-------------------
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 0) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 1) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 2) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 3) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 4) (row := row) (rotation := 0)
--def Circuit._ (c: Circuit F ExtF) (row: N) := c.main (id := 0) (column := 5) (row := row) (rotation := 0)

-----Extracted constraints----------
  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    let t0 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) - 1)
    let t1 := ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * t0)
    t1 = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 0 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          let t2 := -((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)))
          let t3 := ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 4)
          let t4 := ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) + 1)
          [(t2, [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0))]), ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [t3, t4])])
      else if index = 2 then
        (List.range (Circuit.last_row c + 1)).flatMap (λ row =>
          [((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)), [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), 1, (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)), 0, 0, 0, 0])])
    else []

end PhantomAir.extraction
------
