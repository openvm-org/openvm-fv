import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Tactics.Air.define_air

set_option linter.unusedVariables false


-- structure Raw_LessThanAuxCols_2 (F: Type) (ExtF : Type) where
--   buses (index: ℕ) : List (F × List F)
--   challenge (index: ℕ) : ExtF
--   exposed (index: ℕ) : ExtF
--   main (id: ℕ) (column: ℕ) (row: ℕ) (rotation: ℕ) : F
--   permutation (column: ℕ) (row: ℕ) (rotation: ℕ) : ExtF
--   preprocessed (column: ℕ) (row: ℕ) (rotation: ℕ) : F
--   public_values (index: ℕ) : F
--   last_row: ℕ
--   lower_decomp_0 (row : ℕ) (rotation : ℕ) : F
--   lower_decomp_1 (row : ℕ) (rotation : ℕ) : F

-- instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Raw_LessThanAuxCols_2 where
--   buses := Raw_LessThanAuxCols_2.buses
--   challenge := Raw_LessThanAuxCols_2.challenge
--   exposed := Raw_LessThanAuxCols_2.exposed
--   main := Raw_LessThanAuxCols_2.main
--   permutation := Raw_LessThanAuxCols_2.permutation
--   preprocessed := Raw_LessThanAuxCols_2.preprocessed
--   public_values := Raw_LessThanAuxCols_2.public_values
--   last_row := Raw_LessThanAuxCols_2.last_row


-- @[openvm_encapsulation]
-- def Raw_LessThanAuxCols_2.col_0 {F ExtF}
--   (c: Raw_LessThanAuxCols_2 F ExtF) (row: ℕ) (rotation: ℕ)
-- : Prop :=
--   c.main (id := 0) (column := 0) (row := row) (rotation := rotation) =
--   c.lower_decomp_0 (row := row) (rotation := rotation)

-- @[openvm_encapsulation]
-- def Raw_LessThanAuxCols_2.col_1 {F ExtF}
--   (c: Raw_LessThanAuxCols_2 F ExtF) (row: ℕ) (rotation: ℕ)
-- : Prop :=
--   c.main (id := 0) (column := 1) (row := row) (rotation := rotation) =
--   c.lower_decomp_1 (row := row) (rotation := rotation)

-- def Raw_LessThanAuxCols_2.isValid {F ExtF}
--   (c: Raw_LessThanAuxCols_2 F ExtF)
-- : Prop :=
--   (true) ∧
--   (∀ row rotation, c.col_0 row rotation ∧ c.col_1 row rotation ∧ true)

-- abbrev Valid_LessThanAuxCols_2
--   (F: Type) (ExtF: Type)
-- :=
--   { c : Raw_LessThanAuxCols_2 F ExtF // c.isValid }

-- abbrev Valid_LessThanAuxCols_2.buses {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.buses

-- abbrev Valid_LessThanAuxCols_2.challenge {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.challenge

-- abbrev Valid_LessThanAuxCols_2.exposed {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.exposed

-- abbrev Valid_LessThanAuxCols_2.main {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.main

-- abbrev Valid_LessThanAuxCols_2.permutation {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.permutation

-- abbrev Valid_LessThanAuxCols_2.preprocessed {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.preprocessed

-- abbrev Valid_LessThanAuxCols_2.public_values {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.public_values

-- abbrev Valid_LessThanAuxCols_2.last_row {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF)
-- :=
--   c.1.last_row

-- def Valid_LessThanAuxCols_2.lower_decomp_0 {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF) (row rotation : ℕ)
-- : F :=
--   c.1.lower_decomp_0 row rotation

-- def Valid_LessThanAuxCols_2.lower_decomp_1 {F ExtF}
--   (c : Valid_LessThanAuxCols_2 F ExtF) (row rotation : ℕ)
-- : F :=
--   c.1.lower_decomp_1 row rotation

-- instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Valid_LessThanAuxCols_2 where
--   buses := Valid_LessThanAuxCols_2.buses
--   challenge := Valid_LessThanAuxCols_2.challenge
--   exposed := Valid_LessThanAuxCols_2.exposed
--   main := Valid_LessThanAuxCols_2.main
--   permutation := Valid_LessThanAuxCols_2.permutation
--   preprocessed := Valid_LessThanAuxCols_2.preprocessed
--   public_values := Valid_LessThanAuxCols_2.public_values
--   last_row := Valid_LessThanAuxCols_2.last_row

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_buses_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.buses F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.buses :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_challenge_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.challenge F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.challenge :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_exposed_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.exposed F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.exposed :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_main_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.main F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.main :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_permutation_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.permutation F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.permutation :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_preprocessed_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.preprocessed F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.preprocessed :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_public_values_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.public_values F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.public_values :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2_last_row_project {F ExtF}
--   (c: Valid_LessThanAuxCols_2 F ExtF) [Field F] [Field ExtF] :
-- @Circuit.last_row F (by assumption) ExtF (by assumption) Valid_LessThanAuxCols_2 _ c = c.last_row :=
--   rfl

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2.col_0 {F ExtF} [Field F] [Field ExtF]
--   (c : Valid_LessThanAuxCols_2 F ExtF) (row rotation: ℕ) :
-- c.main 0 0 row rotation = c.lower_decomp_0 row rotation :=
--   (c.2.2 row rotation).1

-- @[openvm_encapsulation]
-- lemma Valid_LessThanAuxCols_2.col_1 {F ExtF} [Field F] [Field ExtF]
--   (c : Valid_LessThanAuxCols_2 F ExtF) (row rotation: ℕ) :
-- c.main 0 1 row rotation = c.lower_decomp_1 row rotation :=
--   (c.2.2 row rotation).2.1

#define_air "LessThanAuxCols_2" using "openvm_encapsulation" where
  Column["lower_decomp_0"]
  Column["lower_decomp_1"]
