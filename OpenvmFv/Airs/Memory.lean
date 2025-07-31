import LeanZKCircuit.OpenVM.Circuit

import OpenvmFv.Tactic.AssignColumn
import OpenvmFv.Tactic.RewriteColumnOfIsValid
import OpenvmFv.Tactic.SubcircuitIsValidOfIsValid

import OpenvmFv.Airs.LessThanAuxCols

#assign_columns "MemoryBaseAuxCols"
  Column["prev_timestamp"]
  SubAir["timestamp_lt_aux": "LessThanAuxCols_2" width := 2]

#assign_columns "MemoryReadAuxCols"
  SubAir["base": "MemoryBaseAuxCols" width := 3]

#assign_columns "MemoryWriteAuxCols_4"
  SubAir["base": "MemoryBaseAuxCols" width := 3]
  Column["prev_data_0"]
  Column["prev_data_1"]
  Column["prev_data_2"]
  Column["prev_data_3"]

-- AUX_LEN = 2
-- width 3
-- structure MemoryBaseAuxCols (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ
--   prev_timestamp (row : ℕ) (rotation : ℕ) : F
--   timestamp_lt_aux : LessThanAuxCols_2 F ExtF

-- instance [Field F] [Field ExtF] : Circuit F ExtF MemoryBaseAuxCols where
--   buses := MemoryBaseAuxCols.buses
--   challenge := MemoryBaseAuxCols.challenge
--   exposed := MemoryBaseAuxCols.exposed
--   main := MemoryBaseAuxCols.main
--   permutation := MemoryBaseAuxCols.permutation
--   preprocessed := MemoryBaseAuxCols.preprocessed
--   public_values := MemoryBaseAuxCols.public_values
--   last_row := MemoryBaseAuxCols.last_row

-- #assign_column "MemoryBaseAuxCols" 0 "prev_timestamp"
-- #assign_column "MemoryBaseAuxCols" 1 "timestamp_lt_aux.main (id := 0) (column := 0)"
-- #assign_column "MemoryBaseAuxCols" 2 "timestamp_lt_aux.main (id := 0) (column := 1)"

-- def MemoryBaseAuxCols.isValid
--   (c : MemoryBaseAuxCols F ExtF) : Prop :=
--     (
--       c.timestamp_lt_aux.isValid ∧
--       true
--     ) ∧
--     ∀ row rotation,
--       c.col_0 row rotation ∧
--       c.col_1 row rotation ∧
--       c.col_2 row rotation ∧
--       true

-- #subcircuit_isValid_of_isValid "MemoryBaseAuxCols" 0 "timestamp_lt_aux"

-- #rewrite_column_of_isValid "MemoryBaseAuxCols" 0 "prev_timestamp"
-- #rewrite_column_of_isValid "MemoryBaseAuxCols" 1 "timestamp_lt_aux.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "MemoryBaseAuxCols" 2 "timestamp_lt_aux.main (id := 0) (column := 1)"

-- abbrev Valid_MemoryBaseAuxCols (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: MemoryBaseAuxCols F ExtF // c.isValid }
-- abbrev ValidMemoryReadAuxCols.main [Field F] [Field ExtF] (c: Valid_MemoryBaseAuxCols F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
-- def Valid_MemoryBaseAuxCols.timestamp_lt_aux [Field F] [Field ExtF] (c: Valid_MemoryBaseAuxCols F ExtF) : Valid_LessThanAuxCols_2 F ExtF := ⟨
--   c.1.timestamp_lt_aux,
--   c.1.subcircuit_timestamp_lt_aux_isValid_of_isValid c.2
-- ⟩

-- -- width 3
-- structure MemoryReadAuxCols (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ
--   base : MemoryBaseAuxCols F ExtF

-- instance [Field F] [Field ExtF] : Circuit F ExtF MemoryReadAuxCols where
--   buses := MemoryReadAuxCols.buses
--   challenge := MemoryReadAuxCols.challenge
--   exposed := MemoryReadAuxCols.exposed
--   main := MemoryReadAuxCols.main
--   permutation := MemoryReadAuxCols.permutation
--   preprocessed := MemoryReadAuxCols.preprocessed
--   public_values := MemoryReadAuxCols.public_values
--   last_row := MemoryReadAuxCols.last_row

-- #assign_column "MemoryReadAuxCols" 0 "base.main (id := 0) (column := 0)"
-- #assign_column "MemoryReadAuxCols" 1 "base.main (id := 0) (column := 1)"
-- #assign_column "MemoryReadAuxCols" 2 "base.main (id := 0) (column := 2)"

-- def MemoryReadAuxCols.isValid
--   (c : MemoryReadAuxCols F ExtF) : Prop :=
--     (
--       c.base.isValid ∧
--       true
--     ) ∧
--     ∀ row rotation,
--       c.col_0 row rotation ∧
--       c.col_1 row rotation ∧
--       c.col_2 row rotation ∧
--       true

-- #subcircuit_isValid_of_isValid "MemoryReadAuxCols" 0 "base"

-- #rewrite_column_of_isValid "MemoryReadAuxCols" 0 "base.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "MemoryReadAuxCols" 1 "base.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "MemoryReadAuxCols" 2 "base.main (id := 0) (column := 2)"

-- abbrev Valid_MemoryReadAuxCols (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: MemoryReadAuxCols F ExtF // c.isValid }
-- abbrev Valid_MemoryReadAuxCols.main [Field F] [Field ExtF] (c: Valid_MemoryReadAuxCols F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
-- def Valid_MemoryReadAuxCols.base [Field F] [Field ExtF] (c: Valid_MemoryReadAuxCols F ExtF) : Valid_MemoryBaseAuxCols F ExtF := ⟨
--   c.1.base,
--   c.1.subcircuit_base_isValid_of_isValid c.2
-- ⟩

-- -- width 7
-- structure MemoryWriteAuxCols_4 (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ
--   base : MemoryBaseAuxCols F ExtF
--   prev_data_0 (row : ℕ) (rotation : ℕ) : F
--   prev_data_1 (row : ℕ) (rotation : ℕ) : F
--   prev_data_2 (row : ℕ) (rotation : ℕ) : F
--   prev_data_3 (row : ℕ) (rotation : ℕ) : F

-- instance [Field F] [Field ExtF] : Circuit F ExtF MemoryWriteAuxCols_4 where
--   buses := MemoryWriteAuxCols_4.buses
--   challenge := MemoryWriteAuxCols_4.challenge
--   exposed := MemoryWriteAuxCols_4.exposed
--   main := MemoryWriteAuxCols_4.main
--   permutation := MemoryWriteAuxCols_4.permutation
--   preprocessed := MemoryWriteAuxCols_4.preprocessed
--   public_values := MemoryWriteAuxCols_4.public_values
--   last_row := MemoryWriteAuxCols_4.last_row

-- #assign_column "MemoryWriteAuxCols_4" 0 "base.main (id := 0) (column := 0)"
-- #assign_column "MemoryWriteAuxCols_4" 1 "base.main (id := 0) (column := 1)"
-- #assign_column "MemoryWriteAuxCols_4" 2 "base.main (id := 0) (column := 2)"
-- #assign_column "MemoryWriteAuxCols_4" 3 "prev_data_0"
-- #assign_column "MemoryWriteAuxCols_4" 4 "prev_data_1"
-- #assign_column "MemoryWriteAuxCols_4" 5 "prev_data_2"
-- #assign_column "MemoryWriteAuxCols_4" 6 "prev_data_3"

-- def MemoryWriteAuxCols_4.isValid
--   (c : MemoryWriteAuxCols_4 F ExtF) : Prop :=
--     (
--       c.base.isValid ∧
--       true
--     ) ∧
--     ∀ row rotation,
--       c.col_0 row rotation ∧
--       c.col_1 row rotation ∧
--       c.col_2 row rotation ∧
--       c.col_3 row rotation ∧
--       c.col_4 row rotation ∧
--       c.col_5 row rotation ∧
--       c.col_6 row rotation ∧
--       true

-- #subcircuit_isValid_of_isValid "MemoryWriteAuxCols_4" 0 "base"

-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 0 "base.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 1 "base.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 2 "base.main (id := 0) (column := 2)"
-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 3 "prev_data_0"
-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 4 "prev_data_1"
-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 5 "prev_data_2"
-- #rewrite_column_of_isValid "MemoryWriteAuxCols_4" 6 "prev_data_3"

-- abbrev Valid_MemoryWriteAuxCols_4 (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: MemoryWriteAuxCols_4 F ExtF // c.isValid }
-- abbrev Valid_MemoryWriteAuxCols_4.main [Field F] [Field ExtF] (c: Valid_MemoryWriteAuxCols_4 F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
-- def Valid_MemoryWriteAuxCols_4.base [Field F] [Field ExtF] (c: Valid_MemoryWriteAuxCols_4 F ExtF) : Valid_MemoryBaseAuxCols F ExtF := ⟨
--   c.1.base,
--   c.1.subcircuit_base_isValid_of_isValid c.2
-- ⟩
