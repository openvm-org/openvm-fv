import LeanZKCircuit.OpenVM.Circuit

import OpenvmFv.Airs.Alu.BaseAluCoreAir
import OpenvmFv.Airs.Alu.Rv32BaseAluAdapterAir

-- structure VmAirWrapper_alu (F : Type) (ExtF : Type) where
--   buses: (index: ℕ) -> List (F × List F)
--   challenge: (index: ℕ) -> ExtF
--   exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
--   main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
--   preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
--   public_values: (index: ℕ) -> F
--   last_row: ℕ

--   adapter : Rv32BaseAluAdapterAir F ExtF
--   core : BaseAluCoreAir F ExtF

-- instance [Field F] [Field ExtF] : Circuit F ExtF VmAirWrapper_alu where
--   buses := VmAirWrapper_alu.buses
--   challenge := VmAirWrapper_alu.challenge
--   exposed := VmAirWrapper_alu.exposed
--   main := VmAirWrapper_alu.main
--   permutation := VmAirWrapper_alu.permutation
--   preprocessed := VmAirWrapper_alu.preprocessed
--   public_values := VmAirWrapper_alu.public_values
--   last_row := VmAirWrapper_alu.last_row

#assign_columns "VmAirWrapper_alu"
  SubAir["adapter": "Rv32BaseAluAdapterAir"]
  SubAir["core": "BaseAluCoreAir"]
  [0, "adapter.main (id := 0) (column := 0)"]
  [1, "adapter.main (id := 0) (column := 1)"]
  [2, "adapter.main (id := 0) (column := 2)"]
  [3, "adapter.main (id := 0) (column := 3)"]
  [4, "adapter.main (id := 0) (column := 4)"]
  [5, "adapter.main (id := 0) (column := 5)"]
  [6, "adapter.main (id := 0) (column := 6)"]
  [7, "adapter.main (id := 0) (column := 7)"]
  [8, "adapter.main (id := 0) (column := 8)"]
  [9, "adapter.main (id := 0) (column := 9)"]
  [10, "adapter.main (id := 0) (column := 10)"]
  [11, "adapter.main (id := 0) (column := 11)"]
  [12, "adapter.main (id := 0) (column := 12)"]
  [13, "adapter.main (id := 0) (column := 13)"]
  [14, "adapter.main (id := 0) (column := 14)"]
  [15, "adapter.main (id := 0) (column := 15)"]
  [16, "adapter.main (id := 0) (column := 16)"]
  [17, "adapter.main (id := 0) (column := 17)"]
  [18, "adapter.main (id := 0) (column := 18)"]
  [19, "core.main (id := 0) (column := 0)"]
  [20, "core.main (id := 0) (column := 1)"]
  [21, "core.main (id := 0) (column := 2)"]
  [22, "core.main (id := 0) (column := 3)"]
  [23, "core.main (id := 0) (column := 4)"]
  [24, "core.main (id := 0) (column := 5)"]
  [25, "core.main (id := 0) (column := 6)"]
  [26, "core.main (id := 0) (column := 7)"]
  [27, "core.main (id := 0) (column := 8)"]
  [28, "core.main (id := 0) (column := 9)"]
  [29, "core.main (id := 0) (column := 10)"]
  [30, "core.main (id := 0) (column := 11)"]
  [31, "core.main (id := 0) (column := 12)"]
  [32, "core.main (id := 0) (column := 13)"]
  [33, "core.main (id := 0) (column := 14)"]
  [34, "core.main (id := 0) (column := 15)"]
  [35, "core.main (id := 0) (column := 16)"]

#print VmAirWrapper_alu.isValid

#print VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid

#print VmAirWrapper_alu.col_1_of_isValid



-- #print VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid

-- @[openvm_encapsulation]
-- theorem VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid : ∀ {F ExtF : Type} [inst : Field F]
--   [inst_1 : Field ExtF] (c : VmAirWrapper_alu F ExtF), c.isValid → c.adapter.isValid :=
-- fun {F ExtF} [Field F] [Field ExtF] c h ↦ h.left.left

-- #subcircuit_isValid_of_isValid "VmAirWrapper_alu" 1 "core"

-- abbrev Valid_VmAirWrapper_alu (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: VmAirWrapper_alu F ExtF // c.isValid }
-- abbrev Valid_VmAirWrapper_alu.main [Field F] [Field ExtF] (c: Valid_VmAirWrapper_alu F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
-- def Valid_VmAirWrapper_alu.adapter [Field F] [Field ExtF] (c: Valid_VmAirWrapper_alu F ExtF) : Valid_Rv32BaseAluAdapterAir F ExtF := ⟨
--   c.1.adapter,
--   c.1.subcircuit_adapter_isValid_of_isValid c.2
-- ⟩
-- def Valid_VmAirWrapper_alu.core [Field F] [Field ExtF] (c: Valid_VmAirWrapper_alu F ExtF) : Valid_BaseAluCoreAir F ExtF := ⟨
--   c.1.core,
--   c.1.subcircuit_core_isValid_of_isValid c.2
-- ⟩

-- #rewrite_column_of_isValid "VmAirWrapper_alu" 0 "adapter.main (id := 0) (column := 0)"

-- #print VmAirWrapper_alu.col_0_of_isValid

-- @[openvm_encapsulation]
-- theorem VmAirWrapper_alu.col_0_of_isValid {F ExtF : Type} [inst : Field F] [inst_1 : Field ExtF]
--   (c : Valid_VmAirWrapper_alu F ExtF) (row rotation : ℕ) :
--   c.main 0 0 row rotation = c.adapter.main 0 0 row rotation := (c.2.2 row rotation).1

-- @[openvm_encapsulation]
-- theorem VmAirWrapper_alu.push_cast {F ExtF : Type} [inst : Field F] [inst_1 : Field ExtF]
--   (c : Valid_VmAirWrapper_alu F ExtF) :
--   c.1.adapter = c.adapter.1 := by
--     obtain ⟨c, h_c⟩ := c
--     unfold Valid_VmAirWrapper_alu.adapter
--     simp

-- #rewrite_column_of_isValid "VmAirWrapper_alu" 1 "adapter.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 2 "adapter.main (id := 0) (column := 2)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 3 "adapter.main (id := 0) (column := 3)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 4 "adapter.main (id := 0) (column := 4)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 5 "adapter.main (id := 0) (column := 5)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 6 "adapter.main (id := 0) (column := 6)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 7 "adapter.main (id := 0) (column := 7)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 8 "adapter.main (id := 0) (column := 8)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 9 "adapter.main (id := 0) (column := 9)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 10 "adapter.main (id := 0) (column := 10)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 11 "adapter.main (id := 0) (column := 11)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 12 "adapter.main (id := 0) (column := 12)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 13 "adapter.main (id := 0) (column := 13)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 14 "adapter.main (id := 0) (column := 14)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 15 "adapter.main (id := 0) (column := 15)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 16 "adapter.main (id := 0) (column := 16)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 17 "adapter.main (id := 0) (column := 17)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 18 "adapter.main (id := 0) (column := 18)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 19 "core.main (id := 0) (column := 0)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 20 "core.main (id := 0) (column := 1)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 21 "core.main (id := 0) (column := 2)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 22 "core.main (id := 0) (column := 3)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 23 "core.main (id := 0) (column := 4)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 24 "core.main (id := 0) (column := 5)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 25 "core.main (id := 0) (column := 6)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 26 "core.main (id := 0) (column := 7)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 27 "core.main (id := 0) (column := 8)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 28 "core.main (id := 0) (column := 9)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 29 "core.main (id := 0) (column := 10)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 30 "core.main (id := 0) (column := 11)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 31 "core.main (id := 0) (column := 12)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 32 "core.main (id := 0) (column := 13)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 33 "core.main (id := 0) (column := 14)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 34 "core.main (id := 0) (column := 15)"
-- #rewrite_column_of_isValid "VmAirWrapper_alu" 35 "core.main (id := 0) (column := 16)"
