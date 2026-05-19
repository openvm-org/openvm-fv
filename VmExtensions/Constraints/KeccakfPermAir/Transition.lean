import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## Transition constraints: step flag rotation, preimage consistency, output chaining -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_24 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 0 row) - (step_flag_next c 1 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_24_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_24 c row ↔ constraint_24 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_25 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 1 row) - (step_flag_next c 2 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_25_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_25 c row ↔ constraint_25 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_26 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 2 row) - (step_flag_next c 3 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_26_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_26 c row ↔ constraint_26 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_27 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 3 row) - (step_flag_next c 4 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_27_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_27 c row ↔ constraint_27 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_28 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 4 row) - (step_flag_next c 5 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_28_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_28 c row ↔ constraint_28 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_29 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 5 row) - (step_flag_next c 6 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_29_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_29 c row ↔ constraint_29 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_30 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 6 row) - (step_flag_next c 7 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_30_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_30 c row ↔ constraint_30 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_31 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 7 row) - (step_flag_next c 8 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_31_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_31 c row ↔ constraint_31 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_32 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 8 row) - (step_flag_next c 9 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_32_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_32 c row ↔ constraint_32 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_33 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 9 row) - (step_flag_next c 10 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_33_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_33 c row ↔ constraint_33 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_34 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 10 row) - (step_flag_next c 11 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_34_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_34 c row ↔ constraint_34 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_35 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 11 row) - (step_flag_next c 12 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_35_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_35 c row ↔ constraint_35 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_36 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 12 row) - (step_flag_next c 13 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_36_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_36 c row ↔ constraint_36 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_37 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 13 row) - (step_flag_next c 14 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_37_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_37 c row ↔ constraint_37 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_38 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 14 row) - (step_flag_next c 15 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_38_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_38 c row ↔ constraint_38 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_39 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 15 row) - (step_flag_next c 16 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_39_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_39 c row ↔ constraint_39 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_40 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 16 row) - (step_flag_next c 17 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_40_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_40 c row ↔ constraint_40 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_41 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 17 row) - (step_flag_next c 18 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_41_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_41 c row ↔ constraint_41 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_42 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 18 row) - (step_flag_next c 19 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_42_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_42 c row ↔ constraint_42 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_43 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 19 row) - (step_flag_next c 20 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_43_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_43 c row ↔ constraint_43 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_44 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 20 row) - (step_flag_next c 21 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_44_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_44 c row ↔ constraint_44 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_45 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 21 row) - (step_flag_next c 22 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_45_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_45 c row ↔ constraint_45 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_46 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 22 row) - (step_flag_next c 23 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_46_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_46 c row ↔ constraint_46 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_47 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((step_flag c 23 row) - (step_flag_next c 0 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_47_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_47 c row ↔ constraint_47 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_148 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 0 row) - (preimage_next c 0 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_148_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_148 c row ↔ constraint_148 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_149 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 1 row) - (preimage_next c 1 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_149_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_149 c row ↔ constraint_149 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_150 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 2 row) - (preimage_next c 2 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_150_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_150 c row ↔ constraint_150 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_151 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 3 row) - (preimage_next c 3 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_151_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_151 c row ↔ constraint_151 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_152 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 4 row) - (preimage_next c 4 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_152_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_152 c row ↔ constraint_152 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_153 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 5 row) - (preimage_next c 5 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_153_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_153 c row ↔ constraint_153 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_154 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 6 row) - (preimage_next c 6 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_154_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_154 c row ↔ constraint_154 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_155 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 7 row) - (preimage_next c 7 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_155_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_155 c row ↔ constraint_155 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_156 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 8 row) - (preimage_next c 8 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_156_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_156 c row ↔ constraint_156 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_157 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 9 row) - (preimage_next c 9 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_157_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_157 c row ↔ constraint_157 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_158 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 10 row) - (preimage_next c 10 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_158_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_158 c row ↔ constraint_158 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_159 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 11 row) - (preimage_next c 11 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_159_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_159 c row ↔ constraint_159 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_160 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 12 row) - (preimage_next c 12 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_160_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_160 c row ↔ constraint_160 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_161 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 13 row) - (preimage_next c 13 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_161_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_161 c row ↔ constraint_161 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_162 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 14 row) - (preimage_next c 14 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_162_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_162 c row ↔ constraint_162 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_163 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 15 row) - (preimage_next c 15 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_163_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_163 c row ↔ constraint_163 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_164 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 16 row) - (preimage_next c 16 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_164_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_164 c row ↔ constraint_164 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_165 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 17 row) - (preimage_next c 17 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_165_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_165 c row ↔ constraint_165 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_166 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 18 row) - (preimage_next c 18 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_166_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_166 c row ↔ constraint_166 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_167 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 19 row) - (preimage_next c 19 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_167_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_167 c row ↔ constraint_167 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_168 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 20 row) - (preimage_next c 20 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_168_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_168 c row ↔ constraint_168 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_169 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 21 row) - (preimage_next c 21 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_169_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_169 c row ↔ constraint_169 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_170 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 22 row) - (preimage_next c 22 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_170_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_170 c row ↔ constraint_170 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_171 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 23 row) - (preimage_next c 23 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_171_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_171 c row ↔ constraint_171 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_172 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 24 row) - (preimage_next c 24 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_172_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_172 c row ↔ constraint_172 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_173 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 25 row) - (preimage_next c 25 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_173_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_173 c row ↔ constraint_173 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_174 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 26 row) - (preimage_next c 26 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_174_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_174 c row ↔ constraint_174 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_175 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 27 row) - (preimage_next c 27 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_175_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_175 c row ↔ constraint_175 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_176 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 28 row) - (preimage_next c 28 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_176_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_176 c row ↔ constraint_176 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_177 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 29 row) - (preimage_next c 29 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_177_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_177 c row ↔ constraint_177 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_178 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 30 row) - (preimage_next c 30 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_178_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_178 c row ↔ constraint_178 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_179 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 31 row) - (preimage_next c 31 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_179_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_179 c row ↔ constraint_179 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_180 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 32 row) - (preimage_next c 32 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_180_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_180 c row ↔ constraint_180 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_181 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 33 row) - (preimage_next c 33 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_181_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_181 c row ↔ constraint_181 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_182 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 34 row) - (preimage_next c 34 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_182_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_182 c row ↔ constraint_182 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_183 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 35 row) - (preimage_next c 35 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_183_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_183 c row ↔ constraint_183 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_184 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 36 row) - (preimage_next c 36 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_184_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_184 c row ↔ constraint_184 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_185 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 37 row) - (preimage_next c 37 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_185_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_185 c row ↔ constraint_185 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_186 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 38 row) - (preimage_next c 38 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_186_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_186 c row ↔ constraint_186 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_187 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 39 row) - (preimage_next c 39 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_187_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_187 c row ↔ constraint_187 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_188 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 40 row) - (preimage_next c 40 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_188_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_188 c row ↔ constraint_188 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_189 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 41 row) - (preimage_next c 41 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_189_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_189 c row ↔ constraint_189 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_190 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 42 row) - (preimage_next c 42 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_190_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_190 c row ↔ constraint_190 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_191 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 43 row) - (preimage_next c 43 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_191_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_191 c row ↔ constraint_191 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_192 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 44 row) - (preimage_next c 44 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_192_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_192 c row ↔ constraint_192 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_193 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 45 row) - (preimage_next c 45 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_193_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_193 c row ↔ constraint_193 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_194 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 46 row) - (preimage_next c 46 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_194_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_194 c row ↔ constraint_194 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_195 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 47 row) - (preimage_next c 47 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_195_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_195 c row ↔ constraint_195 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_196 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 48 row) - (preimage_next c 48 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_196_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_196 c row ↔ constraint_196 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_197 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 49 row) - (preimage_next c 49 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_197_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_197 c row ↔ constraint_197 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_198 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 50 row) - (preimage_next c 50 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_198_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_198 c row ↔ constraint_198 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_199 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 51 row) - (preimage_next c 51 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_199_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_199 c row ↔ constraint_199 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_200 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 52 row) - (preimage_next c 52 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_200_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_200 c row ↔ constraint_200 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_201 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 53 row) - (preimage_next c 53 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_201_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_201 c row ↔ constraint_201 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_202 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 54 row) - (preimage_next c 54 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_202_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_202 c row ↔ constraint_202 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_203 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 55 row) - (preimage_next c 55 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_203_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_203 c row ↔ constraint_203 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_204 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 56 row) - (preimage_next c 56 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_204_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_204 c row ↔ constraint_204 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_205 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 57 row) - (preimage_next c 57 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_205_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_205 c row ↔ constraint_205 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_206 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 58 row) - (preimage_next c 58 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_206_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_206 c row ↔ constraint_206 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_207 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 59 row) - (preimage_next c 59 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_207_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_207 c row ↔ constraint_207 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_208 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 60 row) - (preimage_next c 60 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_208_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_208 c row ↔ constraint_208 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_209 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 61 row) - (preimage_next c 61 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_209_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_209 c row ↔ constraint_209 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_210 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 62 row) - (preimage_next c 62 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_210_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_210 c row ↔ constraint_210 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_211 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 63 row) - (preimage_next c 63 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_211_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_211 c row ↔ constraint_211 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_212 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 64 row) - (preimage_next c 64 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_212_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_212 c row ↔ constraint_212 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_213 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 65 row) - (preimage_next c 65 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_213_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_213 c row ↔ constraint_213 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_214 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 66 row) - (preimage_next c 66 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_214_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_214 c row ↔ constraint_214 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_215 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 67 row) - (preimage_next c 67 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_215_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_215 c row ↔ constraint_215 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_216 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 68 row) - (preimage_next c 68 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_216_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_216 c row ↔ constraint_216 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_217 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 69 row) - (preimage_next c 69 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_217_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_217 c row ↔ constraint_217 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_218 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 70 row) - (preimage_next c 70 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_218_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_218 c row ↔ constraint_218 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_219 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 71 row) - (preimage_next c 71 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_219_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_219 c row ↔ constraint_219 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_220 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 72 row) - (preimage_next c 72 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_220_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_220 c row ↔ constraint_220 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_221 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 73 row) - (preimage_next c 73 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_221_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_221 c row ↔ constraint_221 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_222 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 74 row) - (preimage_next c 74 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_222_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_222 c row ↔ constraint_222 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_223 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 75 row) - (preimage_next c 75 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_223_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_223 c row ↔ constraint_223 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_224 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 76 row) - (preimage_next c 76 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_224_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_224 c row ↔ constraint_224 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_225 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 77 row) - (preimage_next c 77 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_225_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_225 c row ↔ constraint_225 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_226 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 78 row) - (preimage_next c 78 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_226_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_226 c row ↔ constraint_226 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_227 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 79 row) - (preimage_next c 79 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_227_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_227 c row ↔ constraint_227 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_228 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 80 row) - (preimage_next c 80 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_228_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_228 c row ↔ constraint_228 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_229 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 81 row) - (preimage_next c 81 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_229_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_229 c row ↔ constraint_229 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_230 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 82 row) - (preimage_next c 82 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_230_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_230 c row ↔ constraint_230 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_231 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 83 row) - (preimage_next c 83 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_231_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_231 c row ↔ constraint_231 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_232 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 84 row) - (preimage_next c 84 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_232_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_232 c row ↔ constraint_232 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_233 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 85 row) - (preimage_next c 85 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_233_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_233 c row ↔ constraint_233 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_234 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 86 row) - (preimage_next c 86 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_234_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_234 c row ↔ constraint_234 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_235 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 87 row) - (preimage_next c 87 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_235_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_235 c row ↔ constraint_235 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_236 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 88 row) - (preimage_next c 88 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_236_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_236 c row ↔ constraint_236 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_237 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 89 row) - (preimage_next c 89 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_237_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_237 c row ↔ constraint_237 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_238 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 90 row) - (preimage_next c 90 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_238_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_238 c row ↔ constraint_238 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_239 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 91 row) - (preimage_next c 91 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_239_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_239 c row ↔ constraint_239 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_240 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 92 row) - (preimage_next c 92 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_240_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_240 c row ↔ constraint_240 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_241 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 93 row) - (preimage_next c 93 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_241_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_241 c row ↔ constraint_241 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_242 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 94 row) - (preimage_next c 94 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_242_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_242 c row ↔ constraint_242 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_243 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 95 row) - (preimage_next c 95 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_243_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_243 c row ↔ constraint_243 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_244 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 96 row) - (preimage_next c 96 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_244_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_244 c row ↔ constraint_244 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_245 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 97 row) - (preimage_next c 97 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_245_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_245 c row ↔ constraint_245 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_246 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 98 row) - (preimage_next c 98 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_246_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_246 c row ↔ constraint_246 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_247 (c : C F ExtF) (row : ℕ) : Prop :=
    ((1 - (step_flag c 23 row)) * ((Circuit.isTransitionRow c row) * ((preimage c 99 row) - (preimage_next c 99 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_247_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_247 c row ↔ constraint_247 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3082 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_ppp_00_limb c 0 row) - (a_next c 0 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3082_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3082 c row ↔ constraint_3082 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3083 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_ppp_00_limb c 1 row) - (a_next c 1 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3083_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3083 c row ↔ constraint_3083 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3084 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_ppp_00_limb c 2 row) - (a_next c 2 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3084_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3084 c row ↔ constraint_3084 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3085 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_ppp_00_limb c 3 row) - (a_next c 3 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3085_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3085 c row ↔ constraint_3085 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3086 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 20 row) - (a_next c 20 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3086_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3086 c row ↔ constraint_3086 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3087 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 21 row) - (a_next c 21 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3087_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3087 c row ↔ constraint_3087 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3088 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 22 row) - (a_next c 22 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3088_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3088 c row ↔ constraint_3088 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3089 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 23 row) - (a_next c 23 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3089_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3089 c row ↔ constraint_3089 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3090 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 40 row) - (a_next c 40 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3090_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3090 c row ↔ constraint_3090 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3091 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 41 row) - (a_next c 41 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3091_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3091 c row ↔ constraint_3091 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3092 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 42 row) - (a_next c 42 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3092_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3092 c row ↔ constraint_3092 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3093 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 43 row) - (a_next c 43 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3093_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3093 c row ↔ constraint_3093 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3094 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 60 row) - (a_next c 60 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3094_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3094 c row ↔ constraint_3094 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3095 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 61 row) - (a_next c 61 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3095_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3095 c row ↔ constraint_3095 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3096 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 62 row) - (a_next c 62 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3096_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3096 c row ↔ constraint_3096 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3097 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 63 row) - (a_next c 63 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3097_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3097 c row ↔ constraint_3097 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3098 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 80 row) - (a_next c 80 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3098_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3098 c row ↔ constraint_3098 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3099 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 81 row) - (a_next c 81 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3099_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3099 c row ↔ constraint_3099 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3100 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 82 row) - (a_next c 82 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3100_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3100 c row ↔ constraint_3100 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3101 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 83 row) - (a_next c 83 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3101_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3101 c row ↔ constraint_3101 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3102 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 4 row) - (a_next c 4 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3102_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3102 c row ↔ constraint_3102 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3103 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 5 row) - (a_next c 5 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3103_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3103 c row ↔ constraint_3103 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3104 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 6 row) - (a_next c 6 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3104_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3104 c row ↔ constraint_3104 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3105 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 7 row) - (a_next c 7 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3105_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3105 c row ↔ constraint_3105 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3106 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 24 row) - (a_next c 24 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3106_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3106 c row ↔ constraint_3106 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3107 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 25 row) - (a_next c 25 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3107_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3107 c row ↔ constraint_3107 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3108 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 26 row) - (a_next c 26 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3108_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3108 c row ↔ constraint_3108 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3109 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 27 row) - (a_next c 27 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3109_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3109 c row ↔ constraint_3109 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3110 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 44 row) - (a_next c 44 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3110_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3110 c row ↔ constraint_3110 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3111 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 45 row) - (a_next c 45 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3111_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3111 c row ↔ constraint_3111 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3112 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 46 row) - (a_next c 46 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3112_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3112 c row ↔ constraint_3112 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3113 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 47 row) - (a_next c 47 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3113_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3113 c row ↔ constraint_3113 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3114 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 64 row) - (a_next c 64 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3114_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3114 c row ↔ constraint_3114 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3115 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 65 row) - (a_next c 65 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3115_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3115 c row ↔ constraint_3115 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3116 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 66 row) - (a_next c 66 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3116_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3116 c row ↔ constraint_3116 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3117 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 67 row) - (a_next c 67 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3117_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3117 c row ↔ constraint_3117 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3118 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 84 row) - (a_next c 84 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3118_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3118 c row ↔ constraint_3118 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3119 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 85 row) - (a_next c 85 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3119_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3119 c row ↔ constraint_3119 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3120 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 86 row) - (a_next c 86 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3120_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3120 c row ↔ constraint_3120 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3121 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 87 row) - (a_next c 87 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3121_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3121 c row ↔ constraint_3121 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3122 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 8 row) - (a_next c 8 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3122_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3122 c row ↔ constraint_3122 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3123 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 9 row) - (a_next c 9 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3123_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3123 c row ↔ constraint_3123 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3124 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 10 row) - (a_next c 10 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3124_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3124 c row ↔ constraint_3124 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3125 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 11 row) - (a_next c 11 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3125_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3125 c row ↔ constraint_3125 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3126 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 28 row) - (a_next c 28 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3126_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3126 c row ↔ constraint_3126 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3127 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 29 row) - (a_next c 29 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3127_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3127 c row ↔ constraint_3127 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3128 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 30 row) - (a_next c 30 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3128_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3128 c row ↔ constraint_3128 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3129 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 31 row) - (a_next c 31 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3129_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3129 c row ↔ constraint_3129 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3130 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 48 row) - (a_next c 48 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3130_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3130 c row ↔ constraint_3130 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3131 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 49 row) - (a_next c 49 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3131_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3131 c row ↔ constraint_3131 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3132 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 50 row) - (a_next c 50 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3132_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3132 c row ↔ constraint_3132 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3133 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 51 row) - (a_next c 51 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3133_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3133 c row ↔ constraint_3133 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3134 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 68 row) - (a_next c 68 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3134_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3134 c row ↔ constraint_3134 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3135 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 69 row) - (a_next c 69 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3135_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3135 c row ↔ constraint_3135 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3136 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 70 row) - (a_next c 70 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3136_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3136 c row ↔ constraint_3136 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3137 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 71 row) - (a_next c 71 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3137_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3137 c row ↔ constraint_3137 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3138 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 88 row) - (a_next c 88 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3138_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3138 c row ↔ constraint_3138 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3139 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 89 row) - (a_next c 89 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3139_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3139 c row ↔ constraint_3139 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3140 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 90 row) - (a_next c 90 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3140_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3140 c row ↔ constraint_3140 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3141 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 91 row) - (a_next c 91 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3141_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3141 c row ↔ constraint_3141 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3142 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 12 row) - (a_next c 12 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3142_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3142 c row ↔ constraint_3142 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3143 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 13 row) - (a_next c 13 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3143_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3143 c row ↔ constraint_3143 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3144 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 14 row) - (a_next c 14 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3144_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3144 c row ↔ constraint_3144 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3145 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 15 row) - (a_next c 15 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3145_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3145 c row ↔ constraint_3145 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3146 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 32 row) - (a_next c 32 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3146_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3146 c row ↔ constraint_3146 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3147 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 33 row) - (a_next c 33 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3147_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3147 c row ↔ constraint_3147 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3148 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 34 row) - (a_next c 34 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3148_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3148 c row ↔ constraint_3148 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3149 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 35 row) - (a_next c 35 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3149_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3149 c row ↔ constraint_3149 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3150 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 52 row) - (a_next c 52 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3150_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3150 c row ↔ constraint_3150 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3151 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 53 row) - (a_next c 53 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3151_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3151 c row ↔ constraint_3151 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3152 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 54 row) - (a_next c 54 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3152_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3152 c row ↔ constraint_3152 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3153 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 55 row) - (a_next c 55 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3153_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3153 c row ↔ constraint_3153 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3154 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 72 row) - (a_next c 72 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3154_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3154 c row ↔ constraint_3154 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3155 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 73 row) - (a_next c 73 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3155_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3155 c row ↔ constraint_3155 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3156 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 74 row) - (a_next c 74 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3156_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3156 c row ↔ constraint_3156 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3157 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 75 row) - (a_next c 75 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3157_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3157 c row ↔ constraint_3157 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3158 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 92 row) - (a_next c 92 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3158_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3158 c row ↔ constraint_3158 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3159 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 93 row) - (a_next c 93 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3159_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3159 c row ↔ constraint_3159 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3160 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 94 row) - (a_next c 94 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3160_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3160 c row ↔ constraint_3160 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3161 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 95 row) - (a_next c 95 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3161_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3161 c row ↔ constraint_3161 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3162 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 16 row) - (a_next c 16 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3162_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3162 c row ↔ constraint_3162 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3163 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 17 row) - (a_next c 17 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3163_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3163 c row ↔ constraint_3163 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3164 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 18 row) - (a_next c 18 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3164_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3164 c row ↔ constraint_3164 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3165 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 19 row) - (a_next c 19 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3165_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3165 c row ↔ constraint_3165 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3166 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 36 row) - (a_next c 36 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3166_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3166 c row ↔ constraint_3166 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3167 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 37 row) - (a_next c 37 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3167_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3167 c row ↔ constraint_3167 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3168 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 38 row) - (a_next c 38 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3168_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3168 c row ↔ constraint_3168 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3169 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 39 row) - (a_next c 39 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3169_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3169 c row ↔ constraint_3169 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3170 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 56 row) - (a_next c 56 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3170_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3170 c row ↔ constraint_3170 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3171 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 57 row) - (a_next c 57 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3171_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3171 c row ↔ constraint_3171 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3172 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 58 row) - (a_next c 58 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3172_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3172 c row ↔ constraint_3172 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3173 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 59 row) - (a_next c 59 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3173_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3173 c row ↔ constraint_3173 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3174 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 76 row) - (a_next c 76 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3174_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3174 c row ↔ constraint_3174 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3175 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 77 row) - (a_next c 77 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3175_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3175 c row ↔ constraint_3175 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3176 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 78 row) - (a_next c 78 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3176_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3176 c row ↔ constraint_3176 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3177 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 79 row) - (a_next c 79 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3177_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3177 c row ↔ constraint_3177 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3178 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 96 row) - (a_next c 96 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3178_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3178 c row ↔ constraint_3178 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3179 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 97 row) - (a_next c 97 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3179_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3179 c row ↔ constraint_3179 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3180 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 98 row) - (a_next c 98 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3180_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3180 c row ↔ constraint_3180 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3181 (c : C F ExtF) (row : ℕ) : Prop :=
    ((Circuit.isTransitionRow c row) * ((1 - (step_flag c 23 row)) * ((a_prime_prime c 99 row) - (a_next c 99 row)))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3181_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3181 c row ↔ constraint_3181 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
