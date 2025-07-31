import LeanZKCircuit.OpenVM.Circuit

import OpenvmFv.Tactic.AssignColumn
import OpenvmFv.Tactic.RewriteColumnOfIsValid

#assign_columns "ExecutionState"
  Column["pc"]
  Column["timestamp"]

-- width 2
-- structure ExecutionState (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ
--   pc (row : ℕ) (rotation : ℕ) : F
--   timestamp (row : ℕ) (rotation : ℕ) : F

-- instance [Field F] [Field ExtF] : Circuit F ExtF ExecutionState where
--   buses := ExecutionState.buses
--   challenge := ExecutionState.challenge
--   exposed := ExecutionState.exposed
--   main := ExecutionState.main
--   permutation := ExecutionState.permutation
--   preprocessed := ExecutionState.preprocessed
--   public_values := ExecutionState.public_values
--   last_row := ExecutionState.last_row

-- #assign_column "ExecutionState" 0 "pc"
-- #assign_column "ExecutionState" 1 "timestamp"

-- def ExecutionState.isValid
--   (c : ExecutionState F ExtF) : Prop :=
--     (
--       true
--     ) ∧
--     ∀ row rotation,
--       c.col_0 row rotation ∧
--       c.col_1 row rotation ∧
--       true

-- -- #rewrite_column_of_isValid "ExecutionState" 0 "pc"

-- -- #print ExecutionState.col_0_of_isValid

-- #rewrite_column_of_isValid "ExecutionState" 1 "timestamp"

-- abbrev Valid_ExecutionState (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: ExecutionState F ExtF // c.isValid }
-- abbrev Valid_ExecutionState.main [Field F] [Field ExtF] (c: Valid_ExecutionState F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
-- abbrev Valid_ExecutionState.pc [Field F] [Field ExtF] (c: Valid_ExecutionState F ExtF) (row rotation : ℕ) := c.1.pc row rotation

-- @[openvm_encapsulation]
-- theorem ExecutionState.col_0_of_isValid {F ExtF : Type} [inst : Field F] [inst_1 : Field ExtF]
--   (c : Valid_ExecutionState F ExtF) (row rotation : ℕ) : c.main 0 0 row rotation = c.pc row rotation := (c.2.2 row rotation).1
