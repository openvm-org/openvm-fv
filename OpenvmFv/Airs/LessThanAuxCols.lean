import LeanZKCircuit.OpenVM.Circuit

import OpenvmFv.Tactic.AssignColumn
import OpenvmFv.Tactic.RewriteColumnOfIsValid

#assign_columns "LessThanAuxCols_2"
  Column["lower_decomp_0"]
  Column["lower_decomp_1"]

-- structure LessThanAuxCols_2 (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ

--   lower_decomp_0 (row : ℕ) (rotation : ℕ) : F
--   lower_decomp_1 (row : ℕ) (rotation : ℕ) : F

-- instance [Field F] [Field ExtF] : Circuit F ExtF LessThanAuxCols_2 where
--   buses := LessThanAuxCols_2.buses
--   challenge := LessThanAuxCols_2.challenge
--   exposed := LessThanAuxCols_2.exposed
--   main := LessThanAuxCols_2.main
--   permutation := LessThanAuxCols_2.permutation
--   preprocessed := LessThanAuxCols_2.preprocessed
--   public_values := LessThanAuxCols_2.public_values
--   last_row := LessThanAuxCols_2.last_row

-- #assign_column "LessThanAuxCols_2" 0 "lower_decomp_0"
-- #assign_column "LessThanAuxCols_2" 1 "lower_decomp_1"

-- def LessThanAuxCols_2.isValid
--   (c : LessThanAuxCols_2 F ExtF) : Prop :=
--     (
--       true
--     ) ∧
--     ∀ row rotation,
--       c.col_0 row rotation ∧
--       c.col_1 row rotation ∧
--       true

-- #rewrite_column_of_isValid "LessThanAuxCols_2" 0 "lower_decomp_0"
-- #rewrite_column_of_isValid "LessThanAuxCols_2" 1 "lower_decomp_1"

-- abbrev Valid_LessThanAuxCols_2 (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: LessThanAuxCols_2 F ExtF // c.isValid }
-- abbrev Valid_LessThanAuxCols_2.main [Field F] [Field ExtF] (c: Valid_LessThanAuxCols_2 F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
