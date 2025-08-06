import LeanZKCircuit.OpenVM.Circuit

/-
REVIEW: This doesn't built.
        `Circuit` is parameterised by three types (in the `Dom` revision of the dependency).
-/

-- structure ExecutionDummyAir (F: Type) [Field F] (ExtF: Type) [Field ExtF]
-- extends Circuit F ExtF

-- def ExecutionDummyAir.main0 [Field F] [Field ExtF] (c : ExecutionDummyAir F ExtF) (row : ℕ) : F :=
--   c.main (id := 0) (column := 0) (row := row) (rotation := 0)
-- def ExecutionDummyAir.main1 [Field F] [Field ExtF] (c : ExecutionDummyAir F ExtF) (row : ℕ) : F :=
--   c.main (id := 0) (column := 1) (row := row) (rotation := 0)
-- def ExecutionDummyAir.main2 [Field F] [Field ExtF] (c : ExecutionDummyAir F ExtF) (row : ℕ) : F :=
--   c.main (id := 0) (column := 2) (row := row) (rotation := 0)
-- def ExecutionDummyAir.main3 [Field F] [Field ExtF] (c : ExecutionDummyAir F ExtF) (row : ℕ) : F :=
--   c.main (id := 0) (column := 3) (row := row) (rotation := 0)
-- def ExecutionDummyAir.main4 [Field F] [Field ExtF] (c : ExecutionDummyAir F ExtF) (row : ℕ) : F :=
--   c.main (id := 0) (column := 4) (row := row) (rotation := 0)

-- def ExecutionDummyAir.executionBus [Field F] [Field ExtF] (c : ExecutionDummyAir F ExtF) : List F :=
--   c.buses (index := 0)

-- #min_imports
