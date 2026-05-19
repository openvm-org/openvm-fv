import VmExtensions.Airs.XorinVmAir
import VmExtensions.Extraction.XorinVmAir

set_option linter.unusedVariables false
set_option maxHeartbeats 1_000_000_000

namespace XorinVmAir.constraints

/-! ## Column Abbreviations

Named accessors for the 914 main-trace columns of XorinVmAir.
Each abbreviation is definitionally equal to the corresponding `Circuit.main` call.
Uses generic circuit variables matching the extraction signature.
-/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  /-- Column 442: Program counter -/
  abbrev pc (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 442) (row := row) (rotation := 0)

  /-- Column 443: Row is active -/
  abbrev is_enabled (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 443) (row := row) (rotation := 0)

  /-- Column 444: Register pointer for buffer -/
  abbrev buffer_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 444) (row := row) (rotation := 0)

  /-- Column 445: Register pointer for input -/
  abbrev input_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 445) (row := row) (rotation := 0)

  /-- Column 446: Register pointer for length -/
  abbrev len_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 446) (row := row) (rotation := 0)

  /-- Column 447: Memory pointer for buffer -/
  abbrev buffer_ptr (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 447) (row := row) (rotation := 0)

  /-- Column 452: Memory pointer for input -/
  abbrev input_ptr (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 452) (row := row) (rotation := 0)

  /-- Column 457: Number of non-padding bytes times 4 -/
  abbrev xorin_len (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 457) (row := row) (rotation := 0)

  /-- Column 462: Starting timestamp for memory ops -/
  abbrev start_timestamp (c : C F ExtF) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 462) (row := row) (rotation := 0)

  /-- Padding flags (cols 0-33) -/
  abbrev is_padding_byte (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := i) (row := row) (rotation := 0)

  /-- Preimage buffer bytes (cols 34-169) -/
  abbrev preimage_buffer_byte (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 34 + i) (row := row) (rotation := 0)

  /-- Input bytes (cols 170-305) -/
  abbrev input_byte (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 170 + i) (row := row) (rotation := 0)

  /-- Postimage buffer bytes (cols 306-441) -/
  abbrev postimage_buffer_byte (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 306 + i) (row := row) (rotation := 0)

  /-- Buffer pointer limbs (cols 448-451) -/
  abbrev buffer_ptr_limb (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 448 + i) (row := row) (rotation := 0)

  /-- Input pointer limbs (cols 453-456) -/
  abbrev input_ptr_limb (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 453 + i) (row := row) (rotation := 0)

  /-- Length limbs (cols 458-461) -/
  abbrev len_limb (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 458 + i) (row := row) (rotation := 0)

  /-- Memory auxiliary columns (cols 463-913) -/
  abbrev mem_aux_col (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
    Circuit.main c (id := 0) (column := 463 + i) (row := row) (rotation := 0)

  /-! ## Simplified Row Constraints

  Each constraint is definitionally equal to its extraction counterpart,
  with `Circuit.main` column references replaced by named abbreviations.
  -/

  section row_constraints

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_0 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * ((is_enabled c row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_0_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_0 c row ↔ constraint_0 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_1 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 0 row) * ((is_padding_byte c 0 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_1_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_1 c row ↔ constraint_1 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_2 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 1 row) * ((is_padding_byte c 1 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_2_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_2 c row ↔ constraint_2 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_3 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 2 row) * ((is_padding_byte c 2 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_3_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_3 c row ↔ constraint_3 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_4 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 3 row) * ((is_padding_byte c 3 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_4_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_4 c row ↔ constraint_4 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_5 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 4 row) * ((is_padding_byte c 4 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_5_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_5 c row ↔ constraint_5 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_6 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 5 row) * ((is_padding_byte c 5 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_6_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_6 c row ↔ constraint_6 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_7 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 6 row) * ((is_padding_byte c 6 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_7_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_7 c row ↔ constraint_7 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_8 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 7 row) * ((is_padding_byte c 7 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_8_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_8 c row ↔ constraint_8 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_9 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 8 row) * ((is_padding_byte c 8 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_9_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_9 c row ↔ constraint_9 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_10 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 9 row) * ((is_padding_byte c 9 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_10_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_10 c row ↔ constraint_10 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_11 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 10 row) * ((is_padding_byte c 10 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_11_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_11 c row ↔ constraint_11 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_12 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 11 row) * ((is_padding_byte c 11 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_12_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_12 c row ↔ constraint_12 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_13 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 12 row) * ((is_padding_byte c 12 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_13_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_13 c row ↔ constraint_13 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_14 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 13 row) * ((is_padding_byte c 13 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_14_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_14 c row ↔ constraint_14 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_15 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 14 row) * ((is_padding_byte c 14 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_15_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_15 c row ↔ constraint_15 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_16 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 15 row) * ((is_padding_byte c 15 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_16_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_16 c row ↔ constraint_16 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_17 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 16 row) * ((is_padding_byte c 16 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_17_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_17 c row ↔ constraint_17 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_18 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 17 row) * ((is_padding_byte c 17 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_18_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_18 c row ↔ constraint_18 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_19 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 18 row) * ((is_padding_byte c 18 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_19_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_19 c row ↔ constraint_19 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_20 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 19 row) * ((is_padding_byte c 19 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_20_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_20 c row ↔ constraint_20 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_21 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 20 row) * ((is_padding_byte c 20 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_21_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_21 c row ↔ constraint_21 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_22 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 21 row) * ((is_padding_byte c 21 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_22_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_22 c row ↔ constraint_22 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_23 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 22 row) * ((is_padding_byte c 22 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_23_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_23 c row ↔ constraint_23 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_24 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 23 row) * ((is_padding_byte c 23 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_24_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_24 c row ↔ constraint_24 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_25 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 24 row) * ((is_padding_byte c 24 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_25_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_25 c row ↔ constraint_25 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_26 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 25 row) * ((is_padding_byte c 25 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_26_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_26 c row ↔ constraint_26 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_27 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 26 row) * ((is_padding_byte c 26 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_27_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_27 c row ↔ constraint_27 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_28 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 27 row) * ((is_padding_byte c 27 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_28_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_28 c row ↔ constraint_28 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_29 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 28 row) * ((is_padding_byte c 28 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_29_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_29 c row ↔ constraint_29 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_30 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 29 row) * ((is_padding_byte c 29 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_30_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_30 c row ↔ constraint_30 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_31 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 30 row) * ((is_padding_byte c 30 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_31_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_31 c row ↔ constraint_31 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_32 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 31 row) * ((is_padding_byte c 31 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_32_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_32 c row ↔ constraint_32 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_33 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 32 row) * ((is_padding_byte c 32 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_33_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_33 c row ↔ constraint_33 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_34 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_padding_byte c 33 row) * ((is_padding_byte c 33 row) - 1)) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_34_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_34 c row ↔ constraint_34 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_35 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * ((((((((((((((((((((((((((((((((((((1 - (is_padding_byte c 0 row)) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) * 4) - (xorin_len c row))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_35_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_35 c row ↔ constraint_35 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_36 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 1 row) - (is_padding_byte c 0 row)) * (((is_padding_byte c 1 row) - (is_padding_byte c 0 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_36_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_36 c row ↔ constraint_36 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_37 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 2 row) - (is_padding_byte c 1 row)) * (((is_padding_byte c 2 row) - (is_padding_byte c 1 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_37_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_37 c row ↔ constraint_37 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_38 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 3 row) - (is_padding_byte c 2 row)) * (((is_padding_byte c 3 row) - (is_padding_byte c 2 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_38_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_38 c row ↔ constraint_38 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_39 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 4 row) - (is_padding_byte c 3 row)) * (((is_padding_byte c 4 row) - (is_padding_byte c 3 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_39_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_39 c row ↔ constraint_39 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_40 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 5 row) - (is_padding_byte c 4 row)) * (((is_padding_byte c 5 row) - (is_padding_byte c 4 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_40_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_40 c row ↔ constraint_40 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_41 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 6 row) - (is_padding_byte c 5 row)) * (((is_padding_byte c 6 row) - (is_padding_byte c 5 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_41_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_41 c row ↔ constraint_41 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_42 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 7 row) - (is_padding_byte c 6 row)) * (((is_padding_byte c 7 row) - (is_padding_byte c 6 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_42_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_42 c row ↔ constraint_42 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_43 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 8 row) - (is_padding_byte c 7 row)) * (((is_padding_byte c 8 row) - (is_padding_byte c 7 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_43_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_43 c row ↔ constraint_43 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_44 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 9 row) - (is_padding_byte c 8 row)) * (((is_padding_byte c 9 row) - (is_padding_byte c 8 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_44_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_44 c row ↔ constraint_44 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_45 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 10 row) - (is_padding_byte c 9 row)) * (((is_padding_byte c 10 row) - (is_padding_byte c 9 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_45_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_45 c row ↔ constraint_45 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_46 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 11 row) - (is_padding_byte c 10 row)) * (((is_padding_byte c 11 row) - (is_padding_byte c 10 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_46_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_46 c row ↔ constraint_46 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_47 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 12 row) - (is_padding_byte c 11 row)) * (((is_padding_byte c 12 row) - (is_padding_byte c 11 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_47_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_47 c row ↔ constraint_47 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_48 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 13 row) - (is_padding_byte c 12 row)) * (((is_padding_byte c 13 row) - (is_padding_byte c 12 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_48_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_48 c row ↔ constraint_48 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_49 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 14 row) - (is_padding_byte c 13 row)) * (((is_padding_byte c 14 row) - (is_padding_byte c 13 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_49_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_49 c row ↔ constraint_49 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_50 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 15 row) - (is_padding_byte c 14 row)) * (((is_padding_byte c 15 row) - (is_padding_byte c 14 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_50_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_50 c row ↔ constraint_50 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_51 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 16 row) - (is_padding_byte c 15 row)) * (((is_padding_byte c 16 row) - (is_padding_byte c 15 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_51_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_51 c row ↔ constraint_51 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_52 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 17 row) - (is_padding_byte c 16 row)) * (((is_padding_byte c 17 row) - (is_padding_byte c 16 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_52_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_52 c row ↔ constraint_52 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_53 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 18 row) - (is_padding_byte c 17 row)) * (((is_padding_byte c 18 row) - (is_padding_byte c 17 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_53_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_53 c row ↔ constraint_53 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_54 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 19 row) - (is_padding_byte c 18 row)) * (((is_padding_byte c 19 row) - (is_padding_byte c 18 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_54_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_54 c row ↔ constraint_54 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_55 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 20 row) - (is_padding_byte c 19 row)) * (((is_padding_byte c 20 row) - (is_padding_byte c 19 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_55_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_55 c row ↔ constraint_55 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_56 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 21 row) - (is_padding_byte c 20 row)) * (((is_padding_byte c 21 row) - (is_padding_byte c 20 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_56_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_56 c row ↔ constraint_56 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_57 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 22 row) - (is_padding_byte c 21 row)) * (((is_padding_byte c 22 row) - (is_padding_byte c 21 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_57_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_57 c row ↔ constraint_57 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_58 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 23 row) - (is_padding_byte c 22 row)) * (((is_padding_byte c 23 row) - (is_padding_byte c 22 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_58_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_58 c row ↔ constraint_58 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_59 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 24 row) - (is_padding_byte c 23 row)) * (((is_padding_byte c 24 row) - (is_padding_byte c 23 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_59_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_59 c row ↔ constraint_59 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_60 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 25 row) - (is_padding_byte c 24 row)) * (((is_padding_byte c 25 row) - (is_padding_byte c 24 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_60_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_60 c row ↔ constraint_60 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_61 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 26 row) - (is_padding_byte c 25 row)) * (((is_padding_byte c 26 row) - (is_padding_byte c 25 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_61_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_61 c row ↔ constraint_61 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_62 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 27 row) - (is_padding_byte c 26 row)) * (((is_padding_byte c 27 row) - (is_padding_byte c 26 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_62_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_62 c row ↔ constraint_62 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_63 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 28 row) - (is_padding_byte c 27 row)) * (((is_padding_byte c 28 row) - (is_padding_byte c 27 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_63_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_63 c row ↔ constraint_63 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_64 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 29 row) - (is_padding_byte c 28 row)) * (((is_padding_byte c 29 row) - (is_padding_byte c 28 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_64_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_64 c row ↔ constraint_64 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_65 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 30 row) - (is_padding_byte c 29 row)) * (((is_padding_byte c 30 row) - (is_padding_byte c 29 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_65_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_65 c row ↔ constraint_65 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_66 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 31 row) - (is_padding_byte c 30 row)) * (((is_padding_byte c 31 row) - (is_padding_byte c 30 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_66_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_66 c row ↔ constraint_66 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_67 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 32 row) - (is_padding_byte c 31 row)) * (((is_padding_byte c 32 row) - (is_padding_byte c 31 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_67_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_67 c row ↔ constraint_67 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_68 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((is_padding_byte c 33 row) - (is_padding_byte c 32 row)) * (((is_padding_byte c 33 row) - (is_padding_byte c 32 row)) - 1))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_68_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_68 c row ↔ constraint_68 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_69 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * ((((start_timestamp c row) - (mem_aux_col c 0 row)) - 1) - ((mem_aux_col c 1 row) + ((mem_aux_col c 2 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_69_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_69 c row ↔ constraint_69 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_70 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * (((((start_timestamp c row) + 1) - (mem_aux_col c 3 row)) - 1) - ((mem_aux_col c 4 row) + ((mem_aux_col c 5 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_70_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_70 c row ↔ constraint_70 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_71 (c : C F ExtF) (row : ℕ) : Prop :=
    ((is_enabled c row) * ((((((start_timestamp c row) + 1) + 1) - (mem_aux_col c 6 row)) - 1) - ((mem_aux_col c 7 row) + ((mem_aux_col c 8 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_71_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_71 c row ↔ constraint_71 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_72 (c : C F ExtF) (row : ℕ) : Prop :=
    ((buffer_ptr c row) - ((((buffer_ptr_limb c 0 row) + ((buffer_ptr_limb c 1 row) * 256)) + ((buffer_ptr_limb c 2 row) * 65536)) + ((buffer_ptr_limb c 3 row) * 16777216))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_72_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_72 c row ↔ constraint_72 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_73 (c : C F ExtF) (row : ℕ) : Prop :=
    ((input_ptr c row) - ((((input_ptr_limb c 0 row) + ((input_ptr_limb c 1 row) * 256)) + ((input_ptr_limb c 2 row) * 65536)) + ((input_ptr_limb c 3 row) * 16777216))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_73_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_73 c row ↔ constraint_73 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_74 (c : C F ExtF) (row : ℕ) : Prop :=
    ((xorin_len c row) - ((((len_limb c 0 row) + ((len_limb c 1 row) * 256)) + ((len_limb c 2 row) * 65536)) + ((len_limb c 3 row) * 16777216))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_74_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_74 c row ↔ constraint_74 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_75 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 0 row))) * (((((((start_timestamp c row) + 1) + 1) + 1) - (mem_aux_col c 111 row)) - 1) - ((mem_aux_col c 112 row) + ((mem_aux_col c 113 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_75_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_75 c row ↔ constraint_75 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_76 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 1 row))) * ((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) - (mem_aux_col c 114 row)) - 1) - ((mem_aux_col c 115 row) + ((mem_aux_col c 116 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_76_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_76 c row ↔ constraint_76 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_77 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 2 row))) * (((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) - (mem_aux_col c 117 row)) - 1) - ((mem_aux_col c 118 row) + ((mem_aux_col c 119 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_77_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_77 c row ↔ constraint_77 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_78 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 3 row))) * ((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) - (mem_aux_col c 120 row)) - 1) - ((mem_aux_col c 121 row) + ((mem_aux_col c 122 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_78_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_78 c row ↔ constraint_78 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_79 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 4 row))) * (((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) - (mem_aux_col c 123 row)) - 1) - ((mem_aux_col c 124 row) + ((mem_aux_col c 125 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_79_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_79 c row ↔ constraint_79 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_80 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 5 row))) * ((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) - (mem_aux_col c 126 row)) - 1) - ((mem_aux_col c 127 row) + ((mem_aux_col c 128 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_80_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_80 c row ↔ constraint_80 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_81 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 6 row))) * (((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) - (mem_aux_col c 129 row)) - 1) - ((mem_aux_col c 130 row) + ((mem_aux_col c 131 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_81_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_81 c row ↔ constraint_81 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_82 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 7 row))) * ((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) - (mem_aux_col c 132 row)) - 1) - ((mem_aux_col c 133 row) + ((mem_aux_col c 134 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_82_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_82 c row ↔ constraint_82 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_83 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 8 row))) * (((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) - (mem_aux_col c 135 row)) - 1) - ((mem_aux_col c 136 row) + ((mem_aux_col c 137 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_83_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_83 c row ↔ constraint_83 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_84 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 9 row))) * ((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) - (mem_aux_col c 138 row)) - 1) - ((mem_aux_col c 139 row) + ((mem_aux_col c 140 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_84_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_84 c row ↔ constraint_84 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_85 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 10 row))) * (((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) - (mem_aux_col c 141 row)) - 1) - ((mem_aux_col c 142 row) + ((mem_aux_col c 143 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_85_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_85 c row ↔ constraint_85 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_86 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 11 row))) * ((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) - (mem_aux_col c 144 row)) - 1) - ((mem_aux_col c 145 row) + ((mem_aux_col c 146 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_86_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_86 c row ↔ constraint_86 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_87 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 12 row))) * (((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) - (mem_aux_col c 147 row)) - 1) - ((mem_aux_col c 148 row) + ((mem_aux_col c 149 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_87_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_87 c row ↔ constraint_87 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_88 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 13 row))) * ((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) - (mem_aux_col c 150 row)) - 1) - ((mem_aux_col c 151 row) + ((mem_aux_col c 152 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_88_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_88 c row ↔ constraint_88 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_89 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 14 row))) * (((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) - (mem_aux_col c 153 row)) - 1) - ((mem_aux_col c 154 row) + ((mem_aux_col c 155 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_89_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_89 c row ↔ constraint_89 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_90 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 15 row))) * ((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) - (mem_aux_col c 156 row)) - 1) - ((mem_aux_col c 157 row) + ((mem_aux_col c 158 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_90_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_90 c row ↔ constraint_90 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_91 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 16 row))) * (((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) - (mem_aux_col c 159 row)) - 1) - ((mem_aux_col c 160 row) + ((mem_aux_col c 161 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_91_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_91 c row ↔ constraint_91 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_92 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 17 row))) * ((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) - (mem_aux_col c 162 row)) - 1) - ((mem_aux_col c 163 row) + ((mem_aux_col c 164 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_92_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_92 c row ↔ constraint_92 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_93 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 18 row))) * (((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) - (mem_aux_col c 165 row)) - 1) - ((mem_aux_col c 166 row) + ((mem_aux_col c 167 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_93_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_93 c row ↔ constraint_93 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_94 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 19 row))) * ((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) - (mem_aux_col c 168 row)) - 1) - ((mem_aux_col c 169 row) + ((mem_aux_col c 170 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_94_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_94 c row ↔ constraint_94 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_95 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 20 row))) * (((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) - (mem_aux_col c 171 row)) - 1) - ((mem_aux_col c 172 row) + ((mem_aux_col c 173 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_95_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_95 c row ↔ constraint_95 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_96 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 21 row))) * ((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) - (mem_aux_col c 174 row)) - 1) - ((mem_aux_col c 175 row) + ((mem_aux_col c 176 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_96_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_96 c row ↔ constraint_96 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_97 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 22 row))) * (((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) - (mem_aux_col c 177 row)) - 1) - ((mem_aux_col c 178 row) + ((mem_aux_col c 179 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_97_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_97 c row ↔ constraint_97 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_98 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 23 row))) * ((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) - (mem_aux_col c 180 row)) - 1) - ((mem_aux_col c 181 row) + ((mem_aux_col c 182 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_98_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_98 c row ↔ constraint_98 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_99 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 24 row))) * (((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) - (mem_aux_col c 183 row)) - 1) - ((mem_aux_col c 184 row) + ((mem_aux_col c 185 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_99_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_99 c row ↔ constraint_99 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_100 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 25 row))) * ((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) - (mem_aux_col c 186 row)) - 1) - ((mem_aux_col c 187 row) + ((mem_aux_col c 188 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_100_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_100 c row ↔ constraint_100 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_101 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 26 row))) * (((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) - (mem_aux_col c 189 row)) - 1) - ((mem_aux_col c 190 row) + ((mem_aux_col c 191 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_101_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_101 c row ↔ constraint_101 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_102 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 27 row))) * ((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) - (mem_aux_col c 192 row)) - 1) - ((mem_aux_col c 193 row) + ((mem_aux_col c 194 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_102_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_102 c row ↔ constraint_102 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_103 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 28 row))) * (((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) - (mem_aux_col c 195 row)) - 1) - ((mem_aux_col c 196 row) + ((mem_aux_col c 197 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_103_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_103 c row ↔ constraint_103 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_104 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 29 row))) * ((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) - (mem_aux_col c 198 row)) - 1) - ((mem_aux_col c 199 row) + ((mem_aux_col c 200 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_104_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_104 c row ↔ constraint_104 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_105 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 30 row))) * (((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) - (mem_aux_col c 201 row)) - 1) - ((mem_aux_col c 202 row) + ((mem_aux_col c 203 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_105_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_105 c row ↔ constraint_105 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_106 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 31 row))) * ((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) - (mem_aux_col c 204 row)) - 1) - ((mem_aux_col c 205 row) + ((mem_aux_col c 206 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_106_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_106 c row ↔ constraint_106 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_107 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 32 row))) * (((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) - (mem_aux_col c 207 row)) - 1) - ((mem_aux_col c 208 row) + ((mem_aux_col c 209 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_107_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_107 c row ↔ constraint_107 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_108 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 33 row))) * ((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) - (mem_aux_col c 210 row)) - 1) - ((mem_aux_col c 211 row) + ((mem_aux_col c 212 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_108_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_108 c row ↔ constraint_108 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_109 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 0 row))) * (((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) - (mem_aux_col c 9 row)) - 1) - ((mem_aux_col c 10 row) + ((mem_aux_col c 11 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_109_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_109 c row ↔ constraint_109 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_110 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 1 row))) * ((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) - (mem_aux_col c 12 row)) - 1) - ((mem_aux_col c 13 row) + ((mem_aux_col c 14 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_110_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_110 c row ↔ constraint_110 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_111 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 2 row))) * (((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) - (mem_aux_col c 15 row)) - 1) - ((mem_aux_col c 16 row) + ((mem_aux_col c 17 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_111_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_111 c row ↔ constraint_111 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_112 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 3 row))) * ((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) - (mem_aux_col c 18 row)) - 1) - ((mem_aux_col c 19 row) + ((mem_aux_col c 20 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_112_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_112 c row ↔ constraint_112 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_113 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 4 row))) * (((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) - (mem_aux_col c 21 row)) - 1) - ((mem_aux_col c 22 row) + ((mem_aux_col c 23 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_113_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_113 c row ↔ constraint_113 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_114 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 5 row))) * ((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) - (mem_aux_col c 24 row)) - 1) - ((mem_aux_col c 25 row) + ((mem_aux_col c 26 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_114_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_114 c row ↔ constraint_114 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_115 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 6 row))) * (((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) - (mem_aux_col c 27 row)) - 1) - ((mem_aux_col c 28 row) + ((mem_aux_col c 29 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_115_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_115 c row ↔ constraint_115 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_116 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 7 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) - (mem_aux_col c 30 row)) - 1) - ((mem_aux_col c 31 row) + ((mem_aux_col c 32 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_116_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_116 c row ↔ constraint_116 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_117 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 8 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) - (mem_aux_col c 33 row)) - 1) - ((mem_aux_col c 34 row) + ((mem_aux_col c 35 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_117_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_117 c row ↔ constraint_117 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_118 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 9 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) - (mem_aux_col c 36 row)) - 1) - ((mem_aux_col c 37 row) + ((mem_aux_col c 38 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_118_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_118 c row ↔ constraint_118 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_119 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 10 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) - (mem_aux_col c 39 row)) - 1) - ((mem_aux_col c 40 row) + ((mem_aux_col c 41 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_119_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_119 c row ↔ constraint_119 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_120 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 11 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) - (mem_aux_col c 42 row)) - 1) - ((mem_aux_col c 43 row) + ((mem_aux_col c 44 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_120_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_120 c row ↔ constraint_120 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_121 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 12 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) - (mem_aux_col c 45 row)) - 1) - ((mem_aux_col c 46 row) + ((mem_aux_col c 47 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_121_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_121 c row ↔ constraint_121 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_122 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 13 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) - (mem_aux_col c 48 row)) - 1) - ((mem_aux_col c 49 row) + ((mem_aux_col c 50 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_122_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_122 c row ↔ constraint_122 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_123 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 14 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) - (mem_aux_col c 51 row)) - 1) - ((mem_aux_col c 52 row) + ((mem_aux_col c 53 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_123_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_123 c row ↔ constraint_123 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_124 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 15 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) - (mem_aux_col c 54 row)) - 1) - ((mem_aux_col c 55 row) + ((mem_aux_col c 56 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_124_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_124 c row ↔ constraint_124 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_125 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 16 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) - (mem_aux_col c 57 row)) - 1) - ((mem_aux_col c 58 row) + ((mem_aux_col c 59 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_125_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_125 c row ↔ constraint_125 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_126 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 17 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) - (mem_aux_col c 60 row)) - 1) - ((mem_aux_col c 61 row) + ((mem_aux_col c 62 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_126_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_126 c row ↔ constraint_126 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_127 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 18 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) - (mem_aux_col c 63 row)) - 1) - ((mem_aux_col c 64 row) + ((mem_aux_col c 65 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_127_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_127 c row ↔ constraint_127 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_128 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 19 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) - (mem_aux_col c 66 row)) - 1) - ((mem_aux_col c 67 row) + ((mem_aux_col c 68 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_128_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_128 c row ↔ constraint_128 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_129 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 20 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) - (mem_aux_col c 69 row)) - 1) - ((mem_aux_col c 70 row) + ((mem_aux_col c 71 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_129_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_129 c row ↔ constraint_129 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_130 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 21 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) - (mem_aux_col c 72 row)) - 1) - ((mem_aux_col c 73 row) + ((mem_aux_col c 74 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_130_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_130 c row ↔ constraint_130 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_131 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 22 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) - (mem_aux_col c 75 row)) - 1) - ((mem_aux_col c 76 row) + ((mem_aux_col c 77 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_131_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_131 c row ↔ constraint_131 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_132 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 23 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) - (mem_aux_col c 78 row)) - 1) - ((mem_aux_col c 79 row) + ((mem_aux_col c 80 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_132_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_132 c row ↔ constraint_132 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_133 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 24 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) - (mem_aux_col c 81 row)) - 1) - ((mem_aux_col c 82 row) + ((mem_aux_col c 83 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_133_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_133 c row ↔ constraint_133 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_134 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 25 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) - (mem_aux_col c 84 row)) - 1) - ((mem_aux_col c 85 row) + ((mem_aux_col c 86 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_134_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_134 c row ↔ constraint_134 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_135 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 26 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) - (mem_aux_col c 87 row)) - 1) - ((mem_aux_col c 88 row) + ((mem_aux_col c 89 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_135_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_135 c row ↔ constraint_135 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_136 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 27 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) - (mem_aux_col c 90 row)) - 1) - ((mem_aux_col c 91 row) + ((mem_aux_col c 92 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_136_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_136 c row ↔ constraint_136 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_137 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 28 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) - (mem_aux_col c 93 row)) - 1) - ((mem_aux_col c 94 row) + ((mem_aux_col c 95 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_137_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_137 c row ↔ constraint_137 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_138 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 29 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) - (mem_aux_col c 96 row)) - 1) - ((mem_aux_col c 97 row) + ((mem_aux_col c 98 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_138_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_138 c row ↔ constraint_138 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_139 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 30 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) - (mem_aux_col c 99 row)) - 1) - ((mem_aux_col c 100 row) + ((mem_aux_col c 101 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_139_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_139 c row ↔ constraint_139 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_140 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 31 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) - (mem_aux_col c 102 row)) - 1) - ((mem_aux_col c 103 row) + ((mem_aux_col c 104 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_140_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_140 c row ↔ constraint_140 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_141 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 32 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) - (mem_aux_col c 105 row)) - 1) - ((mem_aux_col c 106 row) + ((mem_aux_col c 107 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_141_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_141 c row ↔ constraint_141 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_142 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 33 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) - (mem_aux_col c 108 row)) - 1) - ((mem_aux_col c 109 row) + ((mem_aux_col c 110 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_142_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_142 c row ↔ constraint_142 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_143 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 0 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) - (mem_aux_col c 213 row)) - 1) - ((mem_aux_col c 214 row) + ((mem_aux_col c 215 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_143_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_143 c row ↔ constraint_143 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_144 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 1 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) - (mem_aux_col c 220 row)) - 1) - ((mem_aux_col c 221 row) + ((mem_aux_col c 222 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_144_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_144 c row ↔ constraint_144 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_145 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 2 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) - (mem_aux_col c 227 row)) - 1) - ((mem_aux_col c 228 row) + ((mem_aux_col c 229 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_145_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_145 c row ↔ constraint_145 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_146 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 3 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) - (mem_aux_col c 234 row)) - 1) - ((mem_aux_col c 235 row) + ((mem_aux_col c 236 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_146_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_146 c row ↔ constraint_146 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_147 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 4 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) - (mem_aux_col c 241 row)) - 1) - ((mem_aux_col c 242 row) + ((mem_aux_col c 243 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_147_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_147 c row ↔ constraint_147 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_148 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 5 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) - (mem_aux_col c 248 row)) - 1) - ((mem_aux_col c 249 row) + ((mem_aux_col c 250 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_148_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_148 c row ↔ constraint_148 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_149 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 6 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) - (mem_aux_col c 255 row)) - 1) - ((mem_aux_col c 256 row) + ((mem_aux_col c 257 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_149_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_149 c row ↔ constraint_149 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_150 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 7 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) - (mem_aux_col c 262 row)) - 1) - ((mem_aux_col c 263 row) + ((mem_aux_col c 264 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_150_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_150 c row ↔ constraint_150 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_151 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 8 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) - (mem_aux_col c 269 row)) - 1) - ((mem_aux_col c 270 row) + ((mem_aux_col c 271 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_151_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_151 c row ↔ constraint_151 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_152 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 9 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) - (mem_aux_col c 276 row)) - 1) - ((mem_aux_col c 277 row) + ((mem_aux_col c 278 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_152_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_152 c row ↔ constraint_152 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_153 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 10 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) - (mem_aux_col c 283 row)) - 1) - ((mem_aux_col c 284 row) + ((mem_aux_col c 285 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_153_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_153 c row ↔ constraint_153 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_154 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 11 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) - (mem_aux_col c 290 row)) - 1) - ((mem_aux_col c 291 row) + ((mem_aux_col c 292 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_154_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_154 c row ↔ constraint_154 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_155 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 12 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) - (mem_aux_col c 297 row)) - 1) - ((mem_aux_col c 298 row) + ((mem_aux_col c 299 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_155_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_155 c row ↔ constraint_155 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_156 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 13 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) - (mem_aux_col c 304 row)) - 1) - ((mem_aux_col c 305 row) + ((mem_aux_col c 306 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_156_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_156 c row ↔ constraint_156 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_157 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 14 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) - (mem_aux_col c 311 row)) - 1) - ((mem_aux_col c 312 row) + ((mem_aux_col c 313 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_157_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_157 c row ↔ constraint_157 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_158 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 15 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) - (mem_aux_col c 318 row)) - 1) - ((mem_aux_col c 319 row) + ((mem_aux_col c 320 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_158_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_158 c row ↔ constraint_158 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_159 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 16 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) - (mem_aux_col c 325 row)) - 1) - ((mem_aux_col c 326 row) + ((mem_aux_col c 327 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_159_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_159 c row ↔ constraint_159 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_160 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 17 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) - (mem_aux_col c 332 row)) - 1) - ((mem_aux_col c 333 row) + ((mem_aux_col c 334 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_160_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_160 c row ↔ constraint_160 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_161 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 18 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) - (mem_aux_col c 339 row)) - 1) - ((mem_aux_col c 340 row) + ((mem_aux_col c 341 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_161_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_161 c row ↔ constraint_161 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_162 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 19 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) - (mem_aux_col c 346 row)) - 1) - ((mem_aux_col c 347 row) + ((mem_aux_col c 348 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_162_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_162 c row ↔ constraint_162 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_163 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 20 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) - (mem_aux_col c 353 row)) - 1) - ((mem_aux_col c 354 row) + ((mem_aux_col c 355 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_163_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_163 c row ↔ constraint_163 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_164 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 21 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) - (mem_aux_col c 360 row)) - 1) - ((mem_aux_col c 361 row) + ((mem_aux_col c 362 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_164_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_164 c row ↔ constraint_164 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_165 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 22 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) - (mem_aux_col c 367 row)) - 1) - ((mem_aux_col c 368 row) + ((mem_aux_col c 369 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_165_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_165 c row ↔ constraint_165 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_166 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 23 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) - (mem_aux_col c 374 row)) - 1) - ((mem_aux_col c 375 row) + ((mem_aux_col c 376 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_166_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_166 c row ↔ constraint_166 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_167 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 24 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) - (mem_aux_col c 381 row)) - 1) - ((mem_aux_col c 382 row) + ((mem_aux_col c 383 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_167_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_167 c row ↔ constraint_167 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_168 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 25 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) - (mem_aux_col c 388 row)) - 1) - ((mem_aux_col c 389 row) + ((mem_aux_col c 390 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_168_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_168 c row ↔ constraint_168 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_169 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 26 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) - (mem_aux_col c 395 row)) - 1) - ((mem_aux_col c 396 row) + ((mem_aux_col c 397 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_169_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_169 c row ↔ constraint_169 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_170 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 27 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) - (mem_aux_col c 402 row)) - 1) - ((mem_aux_col c 403 row) + ((mem_aux_col c 404 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_170_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_170 c row ↔ constraint_170 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_171 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 28 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) - (mem_aux_col c 409 row)) - 1) - ((mem_aux_col c 410 row) + ((mem_aux_col c 411 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_171_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_171 c row ↔ constraint_171 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_172 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 29 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) - (mem_aux_col c 416 row)) - 1) - ((mem_aux_col c 417 row) + ((mem_aux_col c 418 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_172_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_172 c row ↔ constraint_172 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_173 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 30 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) - (mem_aux_col c 423 row)) - 1) - ((mem_aux_col c 424 row) + ((mem_aux_col c 425 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_173_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_173 c row ↔ constraint_173 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_174 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 31 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) - (mem_aux_col c 430 row)) - 1) - ((mem_aux_col c 431 row) + ((mem_aux_col c 432 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_174_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_174 c row ↔ constraint_174 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_175 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 32 row))) * (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) - (mem_aux_col c 437 row)) - 1) - ((mem_aux_col c 438 row) + ((mem_aux_col c 439 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_175_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_175 c row ↔ constraint_175 c row := by
    rfl

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constraint_176 (c : C F ExtF) (row : ℕ) : Prop :=
    (((is_enabled c row) * (1 - (is_padding_byte c 33 row))) * ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((start_timestamp c row) + 1) + 1) + 1) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) + (1 - (is_padding_byte c 33 row))) + (1 - (is_padding_byte c 0 row))) + (1 - (is_padding_byte c 1 row))) + (1 - (is_padding_byte c 2 row))) + (1 - (is_padding_byte c 3 row))) + (1 - (is_padding_byte c 4 row))) + (1 - (is_padding_byte c 5 row))) + (1 - (is_padding_byte c 6 row))) + (1 - (is_padding_byte c 7 row))) + (1 - (is_padding_byte c 8 row))) + (1 - (is_padding_byte c 9 row))) + (1 - (is_padding_byte c 10 row))) + (1 - (is_padding_byte c 11 row))) + (1 - (is_padding_byte c 12 row))) + (1 - (is_padding_byte c 13 row))) + (1 - (is_padding_byte c 14 row))) + (1 - (is_padding_byte c 15 row))) + (1 - (is_padding_byte c 16 row))) + (1 - (is_padding_byte c 17 row))) + (1 - (is_padding_byte c 18 row))) + (1 - (is_padding_byte c 19 row))) + (1 - (is_padding_byte c 20 row))) + (1 - (is_padding_byte c 21 row))) + (1 - (is_padding_byte c 22 row))) + (1 - (is_padding_byte c 23 row))) + (1 - (is_padding_byte c 24 row))) + (1 - (is_padding_byte c 25 row))) + (1 - (is_padding_byte c 26 row))) + (1 - (is_padding_byte c 27 row))) + (1 - (is_padding_byte c 28 row))) + (1 - (is_padding_byte c 29 row))) + (1 - (is_padding_byte c 30 row))) + (1 - (is_padding_byte c 31 row))) + (1 - (is_padding_byte c 32 row))) - (mem_aux_col c 444 row)) - 1) - ((mem_aux_col c 445 row) + ((mem_aux_col c 446 row) * 131072)))) = 0

  @[XorinVmAir_air_simplification]
  lemma constraint_176_of_extraction
    (c : C F ExtF) (row : ℕ)
  : XorinVmAir.extraction.constraint_176 c row ↔ constraint_176 c row := by
    rfl

  end row_constraints

  /-! ## Bus Interactions -/

  section interactions

  @[XorinVmAir_constraint_and_interaction_simplification]
  def constrain_interactions (c : C F ExtF) : Prop :=
    XorinVmAir.extraction.constrain_interactions c

  @[XorinVmAir_air_simplification]
  lemma constrain_interactions_of_extraction
    (c : C F ExtF)
    (h : XorinVmAir.extraction.constrain_interactions c)
  : constrain_interactions c := h

  end interactions

end constraint_simplification

/-! ## allHold Machinery

Consolidates all constraints and interactions into a single entry point.
Specialized to `Valid_XorinVmAir`.
-/

section allHold
  variable {F : Type} {ExtF : Type} [Field F] [Field ExtF]

  def extracted_row_constraint_list
    (air : Valid_XorinVmAir F ExtF)
    (row : ℕ)
  : List Prop :=
    [
      XorinVmAir.extraction.constraint_0 air row,
      XorinVmAir.extraction.constraint_1 air row,
      XorinVmAir.extraction.constraint_2 air row,
      XorinVmAir.extraction.constraint_3 air row,
      XorinVmAir.extraction.constraint_4 air row,
      XorinVmAir.extraction.constraint_5 air row,
      XorinVmAir.extraction.constraint_6 air row,
      XorinVmAir.extraction.constraint_7 air row,
      XorinVmAir.extraction.constraint_8 air row,
      XorinVmAir.extraction.constraint_9 air row,
      XorinVmAir.extraction.constraint_10 air row,
      XorinVmAir.extraction.constraint_11 air row,
      XorinVmAir.extraction.constraint_12 air row,
      XorinVmAir.extraction.constraint_13 air row,
      XorinVmAir.extraction.constraint_14 air row,
      XorinVmAir.extraction.constraint_15 air row,
      XorinVmAir.extraction.constraint_16 air row,
      XorinVmAir.extraction.constraint_17 air row,
      XorinVmAir.extraction.constraint_18 air row,
      XorinVmAir.extraction.constraint_19 air row,
      XorinVmAir.extraction.constraint_20 air row,
      XorinVmAir.extraction.constraint_21 air row,
      XorinVmAir.extraction.constraint_22 air row,
      XorinVmAir.extraction.constraint_23 air row,
      XorinVmAir.extraction.constraint_24 air row,
      XorinVmAir.extraction.constraint_25 air row,
      XorinVmAir.extraction.constraint_26 air row,
      XorinVmAir.extraction.constraint_27 air row,
      XorinVmAir.extraction.constraint_28 air row,
      XorinVmAir.extraction.constraint_29 air row,
      XorinVmAir.extraction.constraint_30 air row,
      XorinVmAir.extraction.constraint_31 air row,
      XorinVmAir.extraction.constraint_32 air row,
      XorinVmAir.extraction.constraint_33 air row,
      XorinVmAir.extraction.constraint_34 air row,
      XorinVmAir.extraction.constraint_35 air row,
      XorinVmAir.extraction.constraint_36 air row,
      XorinVmAir.extraction.constraint_37 air row,
      XorinVmAir.extraction.constraint_38 air row,
      XorinVmAir.extraction.constraint_39 air row,
      XorinVmAir.extraction.constraint_40 air row,
      XorinVmAir.extraction.constraint_41 air row,
      XorinVmAir.extraction.constraint_42 air row,
      XorinVmAir.extraction.constraint_43 air row,
      XorinVmAir.extraction.constraint_44 air row,
      XorinVmAir.extraction.constraint_45 air row,
      XorinVmAir.extraction.constraint_46 air row,
      XorinVmAir.extraction.constraint_47 air row,
      XorinVmAir.extraction.constraint_48 air row,
      XorinVmAir.extraction.constraint_49 air row,
      XorinVmAir.extraction.constraint_50 air row,
      XorinVmAir.extraction.constraint_51 air row,
      XorinVmAir.extraction.constraint_52 air row,
      XorinVmAir.extraction.constraint_53 air row,
      XorinVmAir.extraction.constraint_54 air row,
      XorinVmAir.extraction.constraint_55 air row,
      XorinVmAir.extraction.constraint_56 air row,
      XorinVmAir.extraction.constraint_57 air row,
      XorinVmAir.extraction.constraint_58 air row,
      XorinVmAir.extraction.constraint_59 air row,
      XorinVmAir.extraction.constraint_60 air row,
      XorinVmAir.extraction.constraint_61 air row,
      XorinVmAir.extraction.constraint_62 air row,
      XorinVmAir.extraction.constraint_63 air row,
      XorinVmAir.extraction.constraint_64 air row,
      XorinVmAir.extraction.constraint_65 air row,
      XorinVmAir.extraction.constraint_66 air row,
      XorinVmAir.extraction.constraint_67 air row,
      XorinVmAir.extraction.constraint_68 air row,
      XorinVmAir.extraction.constraint_69 air row,
      XorinVmAir.extraction.constraint_70 air row,
      XorinVmAir.extraction.constraint_71 air row,
      XorinVmAir.extraction.constraint_72 air row,
      XorinVmAir.extraction.constraint_73 air row,
      XorinVmAir.extraction.constraint_74 air row,
      XorinVmAir.extraction.constraint_75 air row,
      XorinVmAir.extraction.constraint_76 air row,
      XorinVmAir.extraction.constraint_77 air row,
      XorinVmAir.extraction.constraint_78 air row,
      XorinVmAir.extraction.constraint_79 air row,
      XorinVmAir.extraction.constraint_80 air row,
      XorinVmAir.extraction.constraint_81 air row,
      XorinVmAir.extraction.constraint_82 air row,
      XorinVmAir.extraction.constraint_83 air row,
      XorinVmAir.extraction.constraint_84 air row,
      XorinVmAir.extraction.constraint_85 air row,
      XorinVmAir.extraction.constraint_86 air row,
      XorinVmAir.extraction.constraint_87 air row,
      XorinVmAir.extraction.constraint_88 air row,
      XorinVmAir.extraction.constraint_89 air row,
      XorinVmAir.extraction.constraint_90 air row,
      XorinVmAir.extraction.constraint_91 air row,
      XorinVmAir.extraction.constraint_92 air row,
      XorinVmAir.extraction.constraint_93 air row,
      XorinVmAir.extraction.constraint_94 air row,
      XorinVmAir.extraction.constraint_95 air row,
      XorinVmAir.extraction.constraint_96 air row,
      XorinVmAir.extraction.constraint_97 air row,
      XorinVmAir.extraction.constraint_98 air row,
      XorinVmAir.extraction.constraint_99 air row,
      XorinVmAir.extraction.constraint_100 air row,
      XorinVmAir.extraction.constraint_101 air row,
      XorinVmAir.extraction.constraint_102 air row,
      XorinVmAir.extraction.constraint_103 air row,
      XorinVmAir.extraction.constraint_104 air row,
      XorinVmAir.extraction.constraint_105 air row,
      XorinVmAir.extraction.constraint_106 air row,
      XorinVmAir.extraction.constraint_107 air row,
      XorinVmAir.extraction.constraint_108 air row,
      XorinVmAir.extraction.constraint_109 air row,
      XorinVmAir.extraction.constraint_110 air row,
      XorinVmAir.extraction.constraint_111 air row,
      XorinVmAir.extraction.constraint_112 air row,
      XorinVmAir.extraction.constraint_113 air row,
      XorinVmAir.extraction.constraint_114 air row,
      XorinVmAir.extraction.constraint_115 air row,
      XorinVmAir.extraction.constraint_116 air row,
      XorinVmAir.extraction.constraint_117 air row,
      XorinVmAir.extraction.constraint_118 air row,
      XorinVmAir.extraction.constraint_119 air row,
      XorinVmAir.extraction.constraint_120 air row,
      XorinVmAir.extraction.constraint_121 air row,
      XorinVmAir.extraction.constraint_122 air row,
      XorinVmAir.extraction.constraint_123 air row,
      XorinVmAir.extraction.constraint_124 air row,
      XorinVmAir.extraction.constraint_125 air row,
      XorinVmAir.extraction.constraint_126 air row,
      XorinVmAir.extraction.constraint_127 air row,
      XorinVmAir.extraction.constraint_128 air row,
      XorinVmAir.extraction.constraint_129 air row,
      XorinVmAir.extraction.constraint_130 air row,
      XorinVmAir.extraction.constraint_131 air row,
      XorinVmAir.extraction.constraint_132 air row,
      XorinVmAir.extraction.constraint_133 air row,
      XorinVmAir.extraction.constraint_134 air row,
      XorinVmAir.extraction.constraint_135 air row,
      XorinVmAir.extraction.constraint_136 air row,
      XorinVmAir.extraction.constraint_137 air row,
      XorinVmAir.extraction.constraint_138 air row,
      XorinVmAir.extraction.constraint_139 air row,
      XorinVmAir.extraction.constraint_140 air row,
      XorinVmAir.extraction.constraint_141 air row,
      XorinVmAir.extraction.constraint_142 air row,
      XorinVmAir.extraction.constraint_143 air row,
      XorinVmAir.extraction.constraint_144 air row,
      XorinVmAir.extraction.constraint_145 air row,
      XorinVmAir.extraction.constraint_146 air row,
      XorinVmAir.extraction.constraint_147 air row,
      XorinVmAir.extraction.constraint_148 air row,
      XorinVmAir.extraction.constraint_149 air row,
      XorinVmAir.extraction.constraint_150 air row,
      XorinVmAir.extraction.constraint_151 air row,
      XorinVmAir.extraction.constraint_152 air row,
      XorinVmAir.extraction.constraint_153 air row,
      XorinVmAir.extraction.constraint_154 air row,
      XorinVmAir.extraction.constraint_155 air row,
      XorinVmAir.extraction.constraint_156 air row,
      XorinVmAir.extraction.constraint_157 air row,
      XorinVmAir.extraction.constraint_158 air row,
      XorinVmAir.extraction.constraint_159 air row,
      XorinVmAir.extraction.constraint_160 air row,
      XorinVmAir.extraction.constraint_161 air row,
      XorinVmAir.extraction.constraint_162 air row,
      XorinVmAir.extraction.constraint_163 air row,
      XorinVmAir.extraction.constraint_164 air row,
      XorinVmAir.extraction.constraint_165 air row,
      XorinVmAir.extraction.constraint_166 air row,
      XorinVmAir.extraction.constraint_167 air row,
      XorinVmAir.extraction.constraint_168 air row,
      XorinVmAir.extraction.constraint_169 air row,
      XorinVmAir.extraction.constraint_170 air row,
      XorinVmAir.extraction.constraint_171 air row,
      XorinVmAir.extraction.constraint_172 air row,
      XorinVmAir.extraction.constraint_173 air row,
      XorinVmAir.extraction.constraint_174 air row,
      XorinVmAir.extraction.constraint_175 air row,
      XorinVmAir.extraction.constraint_176 air row
    ]

  @[simp]
  def allHold
    (air : Valid_XorinVmAir F ExtF)
    (row : ℕ)
    (_ : row ≤ air.last_row)
  : Prop :=
    XorinVmAir.extraction.constrain_interactions air ∧
    List.Forall (·) (extracted_row_constraint_list air row)

  def row_constraint_list
    (air : Valid_XorinVmAir F ExtF)
    (row : ℕ)
  : List Prop :=
    [
      constraint_0 air row,
      constraint_1 air row,
      constraint_2 air row,
      constraint_3 air row,
      constraint_4 air row,
      constraint_5 air row,
      constraint_6 air row,
      constraint_7 air row,
      constraint_8 air row,
      constraint_9 air row,
      constraint_10 air row,
      constraint_11 air row,
      constraint_12 air row,
      constraint_13 air row,
      constraint_14 air row,
      constraint_15 air row,
      constraint_16 air row,
      constraint_17 air row,
      constraint_18 air row,
      constraint_19 air row,
      constraint_20 air row,
      constraint_21 air row,
      constraint_22 air row,
      constraint_23 air row,
      constraint_24 air row,
      constraint_25 air row,
      constraint_26 air row,
      constraint_27 air row,
      constraint_28 air row,
      constraint_29 air row,
      constraint_30 air row,
      constraint_31 air row,
      constraint_32 air row,
      constraint_33 air row,
      constraint_34 air row,
      constraint_35 air row,
      constraint_36 air row,
      constraint_37 air row,
      constraint_38 air row,
      constraint_39 air row,
      constraint_40 air row,
      constraint_41 air row,
      constraint_42 air row,
      constraint_43 air row,
      constraint_44 air row,
      constraint_45 air row,
      constraint_46 air row,
      constraint_47 air row,
      constraint_48 air row,
      constraint_49 air row,
      constraint_50 air row,
      constraint_51 air row,
      constraint_52 air row,
      constraint_53 air row,
      constraint_54 air row,
      constraint_55 air row,
      constraint_56 air row,
      constraint_57 air row,
      constraint_58 air row,
      constraint_59 air row,
      constraint_60 air row,
      constraint_61 air row,
      constraint_62 air row,
      constraint_63 air row,
      constraint_64 air row,
      constraint_65 air row,
      constraint_66 air row,
      constraint_67 air row,
      constraint_68 air row,
      constraint_69 air row,
      constraint_70 air row,
      constraint_71 air row,
      constraint_72 air row,
      constraint_73 air row,
      constraint_74 air row,
      constraint_75 air row,
      constraint_76 air row,
      constraint_77 air row,
      constraint_78 air row,
      constraint_79 air row,
      constraint_80 air row,
      constraint_81 air row,
      constraint_82 air row,
      constraint_83 air row,
      constraint_84 air row,
      constraint_85 air row,
      constraint_86 air row,
      constraint_87 air row,
      constraint_88 air row,
      constraint_89 air row,
      constraint_90 air row,
      constraint_91 air row,
      constraint_92 air row,
      constraint_93 air row,
      constraint_94 air row,
      constraint_95 air row,
      constraint_96 air row,
      constraint_97 air row,
      constraint_98 air row,
      constraint_99 air row,
      constraint_100 air row,
      constraint_101 air row,
      constraint_102 air row,
      constraint_103 air row,
      constraint_104 air row,
      constraint_105 air row,
      constraint_106 air row,
      constraint_107 air row,
      constraint_108 air row,
      constraint_109 air row,
      constraint_110 air row,
      constraint_111 air row,
      constraint_112 air row,
      constraint_113 air row,
      constraint_114 air row,
      constraint_115 air row,
      constraint_116 air row,
      constraint_117 air row,
      constraint_118 air row,
      constraint_119 air row,
      constraint_120 air row,
      constraint_121 air row,
      constraint_122 air row,
      constraint_123 air row,
      constraint_124 air row,
      constraint_125 air row,
      constraint_126 air row,
      constraint_127 air row,
      constraint_128 air row,
      constraint_129 air row,
      constraint_130 air row,
      constraint_131 air row,
      constraint_132 air row,
      constraint_133 air row,
      constraint_134 air row,
      constraint_135 air row,
      constraint_136 air row,
      constraint_137 air row,
      constraint_138 air row,
      constraint_139 air row,
      constraint_140 air row,
      constraint_141 air row,
      constraint_142 air row,
      constraint_143 air row,
      constraint_144 air row,
      constraint_145 air row,
      constraint_146 air row,
      constraint_147 air row,
      constraint_148 air row,
      constraint_149 air row,
      constraint_150 air row,
      constraint_151 air row,
      constraint_152 air row,
      constraint_153 air row,
      constraint_154 air row,
      constraint_155 air row,
      constraint_156 air row,
      constraint_157 air row,
      constraint_158 air row,
      constraint_159 air row,
      constraint_160 air row,
      constraint_161 air row,
      constraint_162 air row,
      constraint_163 air row,
      constraint_164 air row,
      constraint_165 air row,
      constraint_166 air row,
      constraint_167 air row,
      constraint_168 air row,
      constraint_169 air row,
      constraint_170 air row,
      constraint_171 air row,
      constraint_172 air row,
      constraint_173 air row,
      constraint_174 air row,
      constraint_175 air row,
      constraint_176 air row
    ]

  @[simp]
  def allHold_simplified
    (air : Valid_XorinVmAir F ExtF)
    (row : ℕ)
    (_ : row ≤ air.last_row)
  : Prop :=
    constrain_interactions air ∧
    List.Forall (·) (row_constraint_list air row)

  set_option maxRecDepth 8192 in
  lemma allHold_simplified_of_allHold
    (air : Valid_XorinVmAir F ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
  : allHold air row h_row ↔ allHold_simplified air row h_row := by
    rfl

end allHold

end XorinVmAir.constraints
