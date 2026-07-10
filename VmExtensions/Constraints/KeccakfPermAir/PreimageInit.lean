import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## Preimage initialization: preimage[i] = a[i] at step 0 -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_48 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 0 row) - (a c 0 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_48_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_48 c row ↔ constraint_48 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_49 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 1 row) - (a c 1 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_49_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_49 c row ↔ constraint_49 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_50 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 2 row) - (a c 2 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_50_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_50 c row ↔ constraint_50 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_51 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 3 row) - (a c 3 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_51_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_51 c row ↔ constraint_51 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_52 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 4 row) - (a c 4 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_52_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_52 c row ↔ constraint_52 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_53 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 5 row) - (a c 5 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_53_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_53 c row ↔ constraint_53 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_54 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 6 row) - (a c 6 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_54_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_54 c row ↔ constraint_54 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_55 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 7 row) - (a c 7 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_55_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_55 c row ↔ constraint_55 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_56 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 8 row) - (a c 8 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_56_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_56 c row ↔ constraint_56 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_57 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 9 row) - (a c 9 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_57_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_57 c row ↔ constraint_57 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_58 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 10 row) - (a c 10 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_58_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_58 c row ↔ constraint_58 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_59 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 11 row) - (a c 11 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_59_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_59 c row ↔ constraint_59 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_60 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 12 row) - (a c 12 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_60_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_60 c row ↔ constraint_60 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_61 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 13 row) - (a c 13 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_61_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_61 c row ↔ constraint_61 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_62 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 14 row) - (a c 14 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_62_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_62 c row ↔ constraint_62 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_63 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 15 row) - (a c 15 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_63_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_63 c row ↔ constraint_63 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_64 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 16 row) - (a c 16 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_64_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_64 c row ↔ constraint_64 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_65 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 17 row) - (a c 17 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_65_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_65 c row ↔ constraint_65 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_66 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 18 row) - (a c 18 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_66_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_66 c row ↔ constraint_66 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_67 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 19 row) - (a c 19 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_67_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_67 c row ↔ constraint_67 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_68 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 20 row) - (a c 20 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_68_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_68 c row ↔ constraint_68 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_69 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 21 row) - (a c 21 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_69_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_69 c row ↔ constraint_69 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_70 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 22 row) - (a c 22 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_70_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_70 c row ↔ constraint_70 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_71 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 23 row) - (a c 23 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_71_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_71 c row ↔ constraint_71 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_72 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 24 row) - (a c 24 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_72_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_72 c row ↔ constraint_72 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_73 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 25 row) - (a c 25 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_73_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_73 c row ↔ constraint_73 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_74 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 26 row) - (a c 26 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_74_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_74 c row ↔ constraint_74 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_75 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 27 row) - (a c 27 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_75_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_75 c row ↔ constraint_75 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_76 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 28 row) - (a c 28 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_76_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_76 c row ↔ constraint_76 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_77 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 29 row) - (a c 29 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_77_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_77 c row ↔ constraint_77 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_78 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 30 row) - (a c 30 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_78_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_78 c row ↔ constraint_78 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_79 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 31 row) - (a c 31 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_79_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_79 c row ↔ constraint_79 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_80 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 32 row) - (a c 32 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_80_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_80 c row ↔ constraint_80 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_81 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 33 row) - (a c 33 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_81_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_81 c row ↔ constraint_81 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_82 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 34 row) - (a c 34 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_82_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_82 c row ↔ constraint_82 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_83 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 35 row) - (a c 35 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_83_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_83 c row ↔ constraint_83 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_84 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 36 row) - (a c 36 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_84_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_84 c row ↔ constraint_84 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_85 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 37 row) - (a c 37 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_85_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_85 c row ↔ constraint_85 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_86 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 38 row) - (a c 38 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_86_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_86 c row ↔ constraint_86 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_87 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 39 row) - (a c 39 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_87_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_87 c row ↔ constraint_87 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_88 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 40 row) - (a c 40 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_88_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_88 c row ↔ constraint_88 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_89 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 41 row) - (a c 41 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_89_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_89 c row ↔ constraint_89 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_90 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 42 row) - (a c 42 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_90_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_90 c row ↔ constraint_90 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_91 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 43 row) - (a c 43 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_91_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_91 c row ↔ constraint_91 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_92 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 44 row) - (a c 44 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_92_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_92 c row ↔ constraint_92 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_93 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 45 row) - (a c 45 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_93_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_93 c row ↔ constraint_93 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_94 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 46 row) - (a c 46 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_94_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_94 c row ↔ constraint_94 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_95 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 47 row) - (a c 47 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_95_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_95 c row ↔ constraint_95 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_96 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 48 row) - (a c 48 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_96_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_96 c row ↔ constraint_96 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_97 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 49 row) - (a c 49 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_97_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_97 c row ↔ constraint_97 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_98 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 50 row) - (a c 50 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_98_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_98 c row ↔ constraint_98 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_99 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 51 row) - (a c 51 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_99_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_99 c row ↔ constraint_99 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_100 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 52 row) - (a c 52 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_100_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_100 c row ↔ constraint_100 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_101 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 53 row) - (a c 53 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_101_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_101 c row ↔ constraint_101 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_102 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 54 row) - (a c 54 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_102_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_102 c row ↔ constraint_102 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_103 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 55 row) - (a c 55 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_103_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_103 c row ↔ constraint_103 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_104 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 56 row) - (a c 56 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_104_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_104 c row ↔ constraint_104 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_105 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 57 row) - (a c 57 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_105_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_105 c row ↔ constraint_105 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_106 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 58 row) - (a c 58 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_106_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_106 c row ↔ constraint_106 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_107 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 59 row) - (a c 59 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_107_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_107 c row ↔ constraint_107 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_108 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 60 row) - (a c 60 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_108_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_108 c row ↔ constraint_108 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_109 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 61 row) - (a c 61 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_109_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_109 c row ↔ constraint_109 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_110 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 62 row) - (a c 62 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_110_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_110 c row ↔ constraint_110 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_111 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 63 row) - (a c 63 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_111_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_111 c row ↔ constraint_111 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_112 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 64 row) - (a c 64 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_112_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_112 c row ↔ constraint_112 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_113 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 65 row) - (a c 65 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_113_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_113 c row ↔ constraint_113 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_114 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 66 row) - (a c 66 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_114_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_114 c row ↔ constraint_114 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_115 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 67 row) - (a c 67 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_115_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_115 c row ↔ constraint_115 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_116 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 68 row) - (a c 68 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_116_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_116 c row ↔ constraint_116 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_117 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 69 row) - (a c 69 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_117_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_117 c row ↔ constraint_117 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_118 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 70 row) - (a c 70 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_118_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_118 c row ↔ constraint_118 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_119 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 71 row) - (a c 71 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_119_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_119 c row ↔ constraint_119 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_120 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 72 row) - (a c 72 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_120_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_120 c row ↔ constraint_120 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_121 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 73 row) - (a c 73 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_121_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_121 c row ↔ constraint_121 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_122 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 74 row) - (a c 74 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_122_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_122 c row ↔ constraint_122 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_123 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 75 row) - (a c 75 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_123_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_123 c row ↔ constraint_123 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_124 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 76 row) - (a c 76 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_124_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_124 c row ↔ constraint_124 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_125 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 77 row) - (a c 77 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_125_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_125 c row ↔ constraint_125 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_126 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 78 row) - (a c 78 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_126_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_126 c row ↔ constraint_126 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_127 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 79 row) - (a c 79 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_127_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_127 c row ↔ constraint_127 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_128 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 80 row) - (a c 80 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_128_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_128 c row ↔ constraint_128 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_129 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 81 row) - (a c 81 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_129_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_129 c row ↔ constraint_129 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_130 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 82 row) - (a c 82 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_130_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_130 c row ↔ constraint_130 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_131 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 83 row) - (a c 83 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_131_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_131 c row ↔ constraint_131 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_132 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 84 row) - (a c 84 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_132_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_132 c row ↔ constraint_132 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_133 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 85 row) - (a c 85 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_133_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_133 c row ↔ constraint_133 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_134 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 86 row) - (a c 86 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_134_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_134 c row ↔ constraint_134 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_135 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 87 row) - (a c 87 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_135_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_135 c row ↔ constraint_135 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_136 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 88 row) - (a c 88 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_136_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_136 c row ↔ constraint_136 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_137 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 89 row) - (a c 89 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_137_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_137 c row ↔ constraint_137 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_138 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 90 row) - (a c 90 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_138_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_138 c row ↔ constraint_138 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_139 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 91 row) - (a c 91 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_139_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_139 c row ↔ constraint_139 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_140 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 92 row) - (a c 92 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_140_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_140 c row ↔ constraint_140 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_141 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 93 row) - (a c 93 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_141_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_141 c row ↔ constraint_141 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_142 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 94 row) - (a c 94 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_142_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_142 c row ↔ constraint_142 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_143 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 95 row) - (a c 95 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_143_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_143 c row ↔ constraint_143 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_144 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 96 row) - (a c 96 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_144_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_144 c row ↔ constraint_144 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_145 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 97 row) - (a c 97 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_145_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_145 c row ↔ constraint_145 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_146 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 98 row) - (a c 98 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_146_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_146 c row ↔ constraint_146 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_147 (c : C F ExtF) (row : ℕ) : Prop :=
    ((step_flag c 0 row) * ((preimage c 99 row) - (a c 99 row))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_147_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_147 c row ↔ constraint_147 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
