import LeanZKCircuit.OpenVM.Circuit

import OpenvmFv.Tactic.AssignColumn
import OpenvmFv.Tactic.RewriteColumnOfIsValid
import OpenvmFv.Tactic.SubcircuitIsValidOfIsValid
import OpenvmFv.Airs.ExecutionState
import OpenvmFv.Airs.Memory

-- width 17
-- structure Rv32BaseAluAdapterAir (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ

--   from_state : ExecutionState F ExtF
--   rd_ptr (row: ℕ) (rotation: ℕ) : F
--   rs1_ptr (row: ℕ) (rotation: ℕ) : F
--   rs2 (row: ℕ) (rotation: ℕ) : F
--   rs2_as (row: ℕ) (rotation: ℕ) : F
--   reads_aux_0 : MemoryReadAuxCols F ExtF
--   reads_aux_1 : MemoryReadAuxCols F ExtF
--   writes_aux : MemoryWriteAuxCols_4 F ExtF

-- instance [Field F] [Field ExtF] : Circuit F ExtF Rv32BaseAluAdapterAir where
--   buses := Rv32BaseAluAdapterAir.buses
--   challenge := Rv32BaseAluAdapterAir.challenge
--   exposed := Rv32BaseAluAdapterAir.exposed
--   main := Rv32BaseAluAdapterAir.main
--   permutation := Rv32BaseAluAdapterAir.permutation
--   preprocessed := Rv32BaseAluAdapterAir.preprocessed
--   public_values := Rv32BaseAluAdapterAir.public_values
--   last_row := Rv32BaseAluAdapterAir.last_row
#assign_columns "Rv32BaseAluAdapterAir"
  SubAir["from_state": "ExecutionState" width := 2]
  Column["rd_ptr"]
  Column["rs1_ptr"]
  Column["rs2"]
  Column["rs2_as"]
  SubAir["reads_aux_0": "MemoryReadAuxCols" width := 3]
  SubAir["reads_aux_1": "MemoryReadAuxCols" width := 3]
  SubAir["writes_aux": "MemoryWriteAuxCols_4" width := 7]

-- #assign_column "Rv32BaseAluAdapterAir" 0 "from_state.main (id := 0) (column := 0)"
-- #assign_column "Rv32BaseAluAdapterAir" 1 "from_state.main (id := 0) (column := 1)"
-- #assign_column "Rv32BaseAluAdapterAir" 2 "rd_ptr"
-- #assign_column "Rv32BaseAluAdapterAir" 3 "rs1_ptr"
-- #assign_column "Rv32BaseAluAdapterAir" 4 "rs2"
-- #assign_column "Rv32BaseAluAdapterAir" 5 "rs2_as"
-- #assign_column "Rv32BaseAluAdapterAir" 6 "reads_aux_0.main (id := 0) (column := 0)"
-- #assign_column "Rv32BaseAluAdapterAir" 7 "reads_aux_0.main (id := 0) (column := 1)"
-- #assign_column "Rv32BaseAluAdapterAir" 8 "reads_aux_1.main (id := 0) (column := 0)"
-- #assign_column "Rv32BaseAluAdapterAir" 9 "reads_aux_1.main (id := 0) (column := 1)"
-- #assign_column "Rv32BaseAluAdapterAir" 10 "writes_aux.main (id := 0) (column := 0)"
-- #assign_column "Rv32BaseAluAdapterAir" 11 "writes_aux.main (id := 0) (column := 1)"
-- #assign_column "Rv32BaseAluAdapterAir" 12 "writes_aux.main (id := 0) (column := 2)"
-- #assign_column "Rv32BaseAluAdapterAir" 13 "writes_aux.main (id := 0) (column := 3)"
-- #assign_column "Rv32BaseAluAdapterAir" 14 "writes_aux.main (id := 0) (column := 4)"
-- #assign_column "Rv32BaseAluAdapterAir" 15 "writes_aux.main (id := 0) (column := 5)"
-- #assign_column "Rv32BaseAluAdapterAir" 16 "writes_aux.main (id := 0) (column := 6)"

-- def Rv32BaseAluAdapterAir.isValid
--   (c : Rv32BaseAluAdapterAir F ExtF) : Prop :=
--     (
--       c.from_state.isValid ∧
--       c.reads_aux_0.isValid ∧
--       c.reads_aux_1.isValid ∧
--       c.writes_aux.isValid ∧
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
--       c.col_7 row rotation ∧
--       c.col_8 row rotation ∧
--       c.col_9 row rotation ∧
--       c.col_10 row rotation ∧
--       c.col_11 row rotation ∧
--       c.col_12 row rotation ∧
--       c.col_13 row rotation ∧
--       c.col_14 row rotation ∧
--       c.col_15 row rotation ∧
--       c.col_16 row rotation ∧
--       true

-- #subcircuit_isValid_of_isValid "Rv32BaseAluAdapterAir" 0 "from_state"
-- #subcircuit_isValid_of_isValid "Rv32BaseAluAdapterAir" 1 "reads_aux_0"
-- #subcircuit_isValid_of_isValid "Rv32BaseAluAdapterAir" 2 "reads_aux_1"
-- #subcircuit_isValid_of_isValid "Rv32BaseAluAdapterAir" 3 "writes_aux"

-- -- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 0 "from_state.main (id := 0) (column := 0)"

-- -- #print Rv32BaseAluAdapterAir.col_0_of_isValid

-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 1 "from_state.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 2 "rd_ptr"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 3 "rs1_ptr"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 4 "rs2"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 5 "rs2_as"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 6 "reads_aux_0.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 7 "reads_aux_0.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 8 "reads_aux_1.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 9 "reads_aux_1.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 10 "writes_aux.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 11 "writes_aux.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 12 "writes_aux.main (id := 0) (column := 2)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 13 "writes_aux.main (id := 0) (column := 3)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 14 "writes_aux.main (id := 0) (column := 4)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 15 "writes_aux.main (id := 0) (column := 5)"
-- #rewrite_column_of_isValid "Rv32BaseAluAdapterAir" 16 "writes_aux.main (id := 0) (column := 6)"

-- abbrev Valid_Rv32BaseAluAdapterAir (F : Type) (ExtF : Type) := { c: Rv32BaseAluAdapterAir F ExtF // c.isValid }
-- abbrev Valid_Rv32BaseAluAdapterAir.main [Field F] [Field ExtF] (c: Valid_Rv32BaseAluAdapterAir F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
-- def Valid_Rv32BaseAluAdapterAir.from_state [Field F] [Field ExtF] (c: Valid_Rv32BaseAluAdapterAir F ExtF) : Valid_ExecutionState F ExtF := ⟨
--   c.1.from_state,
--   c.1.subcircuit_from_state_isValid_of_isValid c.2
-- ⟩
-- def Valid_Rv32BaseAluAdapterAir.reads_aux_0 [Field F] [Field ExtF] (c: Valid_Rv32BaseAluAdapterAir F ExtF) : Valid_MemoryReadAuxCols F ExtF := ⟨
--   c.1.reads_aux_0,
--   c.1.subcircuit_reads_aux_0_isValid_of_isValid c.2
-- ⟩
-- def Valid_Rv32BaseAluAdapterAir.reads_aux_1 [Field F] [Field ExtF] (c: Valid_Rv32BaseAluAdapterAir F ExtF) : Valid_MemoryReadAuxCols F ExtF := ⟨
--   c.1.reads_aux_1,
--   c.1.subcircuit_reads_aux_1_isValid_of_isValid c.2
-- ⟩
-- def Valid_Rv32BaseAluAdapterAir.writes_aux [Field F] [Field ExtF] (c: Valid_Rv32BaseAluAdapterAir F ExtF) : Valid_MemoryWriteAuxCols_4 F ExtF := ⟨
--   c.1.writes_aux,
--   c.1.subcircuit_writes_aux_isValid_of_isValid c.2
-- ⟩

-- @[openvm_encapsulation]
-- theorem Rv32BaseAluAdapterAir.col_0_of_isValid {F ExtF : Type} [inst : Field F] [inst_1 : Field ExtF]
--   (c : Valid_Rv32BaseAluAdapterAir F ExtF) (row rotation : ℕ) :
--   c.main 0 0 row rotation = c.from_state.main 0 0 row rotation := (c.2.2 row rotation).1

-- @[openvm_encapsulation]
-- theorem Rv32BaseAluAdapterAir.push_cast {F ExtF : Type} [inst : Field F] [inst_1 : Field ExtF]
--   (c : Valid_Rv32BaseAluAdapterAir F ExtF) :
--   c.1.from_state = c.from_state.1 := by
--     obtain ⟨c, h_c⟩ := c
--     unfold Valid_Rv32BaseAluAdapterAir.from_state
--     simp
