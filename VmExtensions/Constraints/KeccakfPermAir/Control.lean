import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## Control flow constraints: step flag initialization, export flag, is_last_step -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_0 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * ((step_flag c 0 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_0_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_0 c row ↔ constraint_0 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 1 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1 c row ↔ constraint_1 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 2 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2 c row ↔ constraint_2 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 3 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3 c row ↔ constraint_3 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_4 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 4 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_4_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_4 c row ↔ constraint_4 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_5 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 5 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_5_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_5 c row ↔ constraint_5 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_6 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 6 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_6_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_6 c row ↔ constraint_6 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_7 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 7 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_7_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_7 c row ↔ constraint_7 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_8 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 8 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_8_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_8 c row ↔ constraint_8 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_9 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 9 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_9_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_9 c row ↔ constraint_9 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_10 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 10 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_10_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_10 c row ↔ constraint_10 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_11 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 11 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_11_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_11 c row ↔ constraint_11 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_12 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 12 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_12_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_12 c row ↔ constraint_12 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_13 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 13 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_13_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_13 c row ↔ constraint_13 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_14 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 14 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_14_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_14 c row ↔ constraint_14 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_15 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 15 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_15_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_15 c row ↔ constraint_15 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_16 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 16 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_16_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_16 c row ↔ constraint_16 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_17 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 17 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_17_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_17 c row ↔ constraint_17 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_18 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 18 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_18_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_18 c row ↔ constraint_18 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_19 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 19 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_19_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_19 c row ↔ constraint_19 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_20 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 20 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_20_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_20 c row ↔ constraint_20 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_21 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 21 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_21_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_21 c row ↔ constraint_21 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_22 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 22 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_22_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_22 c row ↔ constraint_22 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_23 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isFirstRow c row) * (step_flag c 23 row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_23_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_23 c row ↔ constraint_23 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_248 (c : C F ExtF) (row : ℕ) : Prop :=
    ((export_flag c row) * ((export_flag c row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_248_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_248 c row ↔ constraint_248 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_249 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * (export_flag c row)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_249_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_249 c row ↔ constraint_249 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3182 (c : C F ExtF) (row : ℕ) : Prop :=
    ((export_flag c row) * ((step_flag c 23 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3182_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3182 c row ↔ constraint_3182 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
