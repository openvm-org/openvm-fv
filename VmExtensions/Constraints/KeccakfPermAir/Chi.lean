import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## χ step constraints -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2910 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 865 1269 1654 2465 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2910_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2910 c row ↔ constraint_2910 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2911 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 881 1285 1670 2466 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2911_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2911 c row ↔ constraint_2911 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2912 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2912 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2912_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2912 c row ↔ constraint_2912 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2913 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 913 1253 1638 2468 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2913_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2913 c row ↔ constraint_2913 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2914 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1269 1654 2060 2469 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2914_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2914 c row ↔ constraint_2914 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2915 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2915 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2915_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2915 c row ↔ constraint_2915 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2916 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2916 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2916_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2916 c row ↔ constraint_2916 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2917 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1253 1638 2044 2472 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2917_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2917 c row ↔ constraint_2917 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2918 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2918 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2918_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2918 c row ↔ constraint_2918 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2919 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2919 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2919_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2919 c row ↔ constraint_2919 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2920 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2920 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2920_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2920 c row ↔ constraint_2920 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2921 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1638 2044 2435 2476 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2921_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2921 c row ↔ constraint_2921 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2922 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2922 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2922_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2922 c row ↔ constraint_2922 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2923 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2923 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2923_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2923 c row ↔ constraint_2923 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2924 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2028 2419 897 2479 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2924_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2924 c row ↔ constraint_2924 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2925 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2044 2435 913 2480 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2925_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2925 c row ↔ constraint_2925 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2926 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2926 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2926_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2926 c row ↔ constraint_2926 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2927 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2403 881 1285 2482 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2927_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2927 c row ↔ constraint_2927 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2928 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2928 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2928_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2928 c row ↔ constraint_2928 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2929 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2435 913 1253 2484 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2929_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2929 c row ↔ constraint_2929 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2930 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2930 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2930_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2930 c row ↔ constraint_2930 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2931 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2931 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2931_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2931 c row ↔ constraint_2931 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2932 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1061 1453 1534 2487 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2932_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2932 c row ↔ constraint_2932 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2933 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1077 1469 1550 2488 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2933_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2933 c row ↔ constraint_2933 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2934 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2934 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2934_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2934 c row ↔ constraint_2934 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2935 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2935 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2935_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2935 c row ↔ constraint_2935 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2936 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2936 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2936_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2936 c row ↔ constraint_2936 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2937 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1469 1550 1892 2492 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2937_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2937 c row ↔ constraint_2937 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2938 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2938 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2938_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2938 c row ↔ constraint_2938 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2939 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1518 1924 2292 2494 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2939_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2939 c row ↔ constraint_2939 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2940 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2940 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2940_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2940 c row ↔ constraint_2940 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2941 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2941 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2941_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2941 c row ↔ constraint_2941 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2942 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1908 2276 1093 2497 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2942_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2942 c row ↔ constraint_2942 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2943 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2943 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2943_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2943 c row ↔ constraint_2943 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2944 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2944 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2944_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2944 c row ↔ constraint_2944 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2945 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2945 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2945_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2945 c row ↔ constraint_2945 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2946 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2276 1093 1485 2501 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2946_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2946 c row ↔ constraint_2946 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2947 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2947 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2947_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2947 c row ↔ constraint_2947 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2948 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2308 1061 1453 2503 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2948_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2948 c row ↔ constraint_2948 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2949 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2949 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2949_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2949 c row ↔ constraint_2949 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2950 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2950 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2950_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2950 c row ↔ constraint_2950 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2951 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2951 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2951_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2951 c row ↔ constraint_2951 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2952 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 960 1339 1704 2507 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2952_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2952 c row ↔ constraint_2952 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2953 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 976 1355 1720 2508 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2953_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2953 c row ↔ constraint_2953 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2954 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2954 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2954_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2954 c row ↔ constraint_2954 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2955 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2955 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2955_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2955 c row ↔ constraint_2955 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2956 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1339 1704 2105 2511 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2956_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2956 c row ↔ constraint_2956 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2957 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1355 1720 2121 2512 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2957_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2957 c row ↔ constraint_2957 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2958 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2958 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2958_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2958 c row ↔ constraint_2958 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2959 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2959 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2959_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2959 c row ↔ constraint_2959 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2960 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1704 2105 2159 2515 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2960_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2960 c row ↔ constraint_2960 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2961 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1720 2121 2175 2516 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2961_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2961 c row ↔ constraint_2961 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2962 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2962 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2962_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2962 c row ↔ constraint_2962 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2963 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2963 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2963_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2963 c row ↔ constraint_2963 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2964 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2105 2159 960 2519 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2964_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2964 c row ↔ constraint_2964 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2965 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2121 2175 976 2520 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2965_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2965 c row ↔ constraint_2965 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2966 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2966 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2966_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2966 c row ↔ constraint_2966 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2967 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2967 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2967_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2967 c row ↔ constraint_2967 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2968 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2159 960 1339 2523 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2968_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2968 c row ↔ constraint_2968 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2969 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2175 976 1355 2524 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2969_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2969 c row ↔ constraint_2969 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2970 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2970 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2970_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2970 c row ↔ constraint_2970 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2971 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2971 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2971_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2971 c row ↔ constraint_2971 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2972 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2972 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2972_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2972 c row ↔ constraint_2972 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2973 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1142 1197 1607 2528 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2973_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2973 c row ↔ constraint_2973 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2974 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2974 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2974_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2974 c row ↔ constraint_2974 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2975 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1229 1575 1954 2530 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2975_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2975 c row ↔ constraint_2975 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2976 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2976 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2976_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2976 c row ↔ constraint_2976 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2977 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1197 1607 1986 2532 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2977_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2977 c row ↔ constraint_2977 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2978 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2978 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2978_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2978 c row ↔ constraint_2978 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2979 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1575 1954 2361 2534 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2979_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2979 c row ↔ constraint_2979 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2980 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1591 1970 2377 2535 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2980_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2980 c row ↔ constraint_2980 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2981 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2981 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2981_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2981 c row ↔ constraint_2981 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2982 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2982 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2982_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2982 c row ↔ constraint_2982 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2983 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2983 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2983_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2983 c row ↔ constraint_2983 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2984 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1970 2377 1126 2539 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2984_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2984 c row ↔ constraint_2984 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2985 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2985 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2985_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2985 c row ↔ constraint_2985 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2986 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2345 1158 1213 2541 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2986_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2986 c row ↔ constraint_2986 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2987 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2987 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2987_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2987 c row ↔ constraint_2987 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2988 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2988 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2988_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2988 c row ↔ constraint_2988 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2989 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2989 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2989_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2989 c row ↔ constraint_2989 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2990 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 995 1386 1786 2545 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2990_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2990 c row ↔ constraint_2990 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2991 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1011 1402 1802 2546 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2991_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2991 c row ↔ constraint_2991 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2992 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2992 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2992_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2992 c row ↔ constraint_2992 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2993 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2993 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2993_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2993 c row ↔ constraint_2993 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2994 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1386 1786 1848 2549 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2994_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2994 c row ↔ constraint_2994 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2995 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1402 1802 1864 2550 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2995_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2995 c row ↔ constraint_2995 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2996 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2996 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2996_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2996 c row ↔ constraint_2996 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2997 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2997 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2997_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2997 c row ↔ constraint_2997 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2998 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_2998 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2998_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2998 c row ↔ constraint_2998 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2999 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1802 1864 2223 2554 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2999_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2999 c row ↔ constraint_2999 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3000 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3000 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3000_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3000 c row ↔ constraint_3000 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3001 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1770 1832 2255 2556 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3001_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3001 c row ↔ constraint_3001 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3002 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3002 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3002_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3002 c row ↔ constraint_3002 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3003 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 1864 2223 1011 2558 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3003_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3003 c row ↔ constraint_3003 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3004 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3004 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3004_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3004 c row ↔ constraint_3004 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3005 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3005 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3005_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3005 c row ↔ constraint_3005 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3006 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3006 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3006_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3006 c row ↔ constraint_3006 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3007 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2223 1011 1402 2562 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3007_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3007 c row ↔ constraint_3007 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3008 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.chi_recompose16_eq c 2239 1027 1418 2563 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3008_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3008 c row ↔ constraint_3008 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_3009 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.constraint_3009 c row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_3009_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_3009 c row ↔ constraint_3009 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
