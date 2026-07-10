import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## ι constraints: iota bits boolean + RC XOR + limb composition -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3010 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 0 row) * ((a_pp_00_bit c 0 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3010_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3010 c row ↔ constraint_3010 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3011 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 1 row) * ((a_pp_00_bit c 1 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3011_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3011 c row ↔ constraint_3011 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3012 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 2 row) * ((a_pp_00_bit c 2 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3012_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3012 c row ↔ constraint_3012 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3013 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 3 row) * ((a_pp_00_bit c 3 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3013_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3013 c row ↔ constraint_3013 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3014 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 4 row) * ((a_pp_00_bit c 4 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3014_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3014 c row ↔ constraint_3014 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3015 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 5 row) * ((a_pp_00_bit c 5 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3015_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3015 c row ↔ constraint_3015 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3016 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 6 row) * ((a_pp_00_bit c 6 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3016_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3016 c row ↔ constraint_3016 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3017 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 7 row) * ((a_pp_00_bit c 7 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3017_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3017 c row ↔ constraint_3017 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3018 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 8 row) * ((a_pp_00_bit c 8 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3018_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3018 c row ↔ constraint_3018 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3019 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 9 row) * ((a_pp_00_bit c 9 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3019_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3019 c row ↔ constraint_3019 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3020 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 10 row) * ((a_pp_00_bit c 10 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3020_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3020 c row ↔ constraint_3020 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3021 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 11 row) * ((a_pp_00_bit c 11 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3021_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3021 c row ↔ constraint_3021 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3022 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 12 row) * ((a_pp_00_bit c 12 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3022_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3022 c row ↔ constraint_3022 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3023 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 13 row) * ((a_pp_00_bit c 13 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3023_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3023 c row ↔ constraint_3023 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3024 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 14 row) * ((a_pp_00_bit c 14 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3024_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3024 c row ↔ constraint_3024 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3025 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 15 row) * ((a_pp_00_bit c 15 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3025_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3025 c row ↔ constraint_3025 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3026 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 16 row) * ((a_pp_00_bit c 16 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3026_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3026 c row ↔ constraint_3026 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3027 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 17 row) * ((a_pp_00_bit c 17 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3027_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3027 c row ↔ constraint_3027 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3028 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 18 row) * ((a_pp_00_bit c 18 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3028_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3028 c row ↔ constraint_3028 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3029 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 19 row) * ((a_pp_00_bit c 19 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3029_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3029 c row ↔ constraint_3029 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3030 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 20 row) * ((a_pp_00_bit c 20 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3030_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3030 c row ↔ constraint_3030 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3031 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 21 row) * ((a_pp_00_bit c 21 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3031_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3031 c row ↔ constraint_3031 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3032 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 22 row) * ((a_pp_00_bit c 22 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3032_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3032 c row ↔ constraint_3032 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3033 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 23 row) * ((a_pp_00_bit c 23 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3033_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3033 c row ↔ constraint_3033 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3034 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 24 row) * ((a_pp_00_bit c 24 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3034_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3034 c row ↔ constraint_3034 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3035 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 25 row) * ((a_pp_00_bit c 25 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3035_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3035 c row ↔ constraint_3035 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3036 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 26 row) * ((a_pp_00_bit c 26 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3036_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3036 c row ↔ constraint_3036 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3037 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 27 row) * ((a_pp_00_bit c 27 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3037_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3037 c row ↔ constraint_3037 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3038 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 28 row) * ((a_pp_00_bit c 28 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3038_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3038 c row ↔ constraint_3038 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3039 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 29 row) * ((a_pp_00_bit c 29 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3039_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3039 c row ↔ constraint_3039 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3040 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 30 row) * ((a_pp_00_bit c 30 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3040_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3040 c row ↔ constraint_3040 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3041 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 31 row) * ((a_pp_00_bit c 31 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3041_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3041 c row ↔ constraint_3041 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3042 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 32 row) * ((a_pp_00_bit c 32 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3042_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3042 c row ↔ constraint_3042 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3043 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 33 row) * ((a_pp_00_bit c 33 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3043_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3043 c row ↔ constraint_3043 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3044 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 34 row) * ((a_pp_00_bit c 34 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3044_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3044 c row ↔ constraint_3044 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3045 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 35 row) * ((a_pp_00_bit c 35 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3045_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3045 c row ↔ constraint_3045 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3046 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 36 row) * ((a_pp_00_bit c 36 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3046_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3046 c row ↔ constraint_3046 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3047 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 37 row) * ((a_pp_00_bit c 37 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3047_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3047 c row ↔ constraint_3047 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3048 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 38 row) * ((a_pp_00_bit c 38 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3048_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3048 c row ↔ constraint_3048 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3049 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 39 row) * ((a_pp_00_bit c 39 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3049_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3049 c row ↔ constraint_3049 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3050 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 40 row) * ((a_pp_00_bit c 40 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3050_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3050 c row ↔ constraint_3050 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3051 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 41 row) * ((a_pp_00_bit c 41 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3051_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3051 c row ↔ constraint_3051 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3052 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 42 row) * ((a_pp_00_bit c 42 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3052_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3052 c row ↔ constraint_3052 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3053 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 43 row) * ((a_pp_00_bit c 43 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3053_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3053 c row ↔ constraint_3053 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3054 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 44 row) * ((a_pp_00_bit c 44 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3054_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3054 c row ↔ constraint_3054 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3055 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 45 row) * ((a_pp_00_bit c 45 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3055_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3055 c row ↔ constraint_3055 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3056 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 46 row) * ((a_pp_00_bit c 46 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3056_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3056 c row ↔ constraint_3056 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3057 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 47 row) * ((a_pp_00_bit c 47 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3057_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3057 c row ↔ constraint_3057 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3058 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 48 row) * ((a_pp_00_bit c 48 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3058_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3058 c row ↔ constraint_3058 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3059 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 49 row) * ((a_pp_00_bit c 49 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3059_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3059 c row ↔ constraint_3059 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3060 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 50 row) * ((a_pp_00_bit c 50 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3060_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3060 c row ↔ constraint_3060 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3061 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 51 row) * ((a_pp_00_bit c 51 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3061_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3061 c row ↔ constraint_3061 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3062 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 52 row) * ((a_pp_00_bit c 52 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3062_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3062 c row ↔ constraint_3062 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3063 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 53 row) * ((a_pp_00_bit c 53 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3063_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3063 c row ↔ constraint_3063 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3064 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 54 row) * ((a_pp_00_bit c 54 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3064_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3064 c row ↔ constraint_3064 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3065 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 55 row) * ((a_pp_00_bit c 55 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3065_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3065 c row ↔ constraint_3065 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3066 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 56 row) * ((a_pp_00_bit c 56 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3066_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3066 c row ↔ constraint_3066 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3067 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 57 row) * ((a_pp_00_bit c 57 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3067_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3067 c row ↔ constraint_3067 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3068 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 58 row) * ((a_pp_00_bit c 58 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3068_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3068 c row ↔ constraint_3068 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3069 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 59 row) * ((a_pp_00_bit c 59 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3069_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3069 c row ↔ constraint_3069 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3070 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 60 row) * ((a_pp_00_bit c 60 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3070_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3070 c row ↔ constraint_3070 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3071 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 61 row) * ((a_pp_00_bit c 61 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3071_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3071 c row ↔ constraint_3071 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3072 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 62 row) * ((a_pp_00_bit c 62 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3072_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3072 c row ↔ constraint_3072 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3073 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_pp_00_bit c 63 row) * ((a_pp_00_bit c 63 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3073_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3073 c row ↔ constraint_3073 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3074 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.recompose16_eq c 2565 2465 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3074_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3074 c row ↔ constraint_3074 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3075 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.recompose16_eq c 2581 2466 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3075_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3075 c row ↔ constraint_3075 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3076 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.recompose16_eq c 2597 2467 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3076_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3076 c row ↔ constraint_3076 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3077 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.recompose16_eq c 2613 2468 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3077_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3077 c row ↔ constraint_3077 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3078 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3078 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3078_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3078 c row ↔ constraint_3078 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3079 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3079 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3079_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3079 c row ↔ constraint_3079 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3080 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.recompose16_eq c 2597 2631 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3080_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3080 c row ↔ constraint_3080 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3081 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3081 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3081_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3081 c row ↔ constraint_3081 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
