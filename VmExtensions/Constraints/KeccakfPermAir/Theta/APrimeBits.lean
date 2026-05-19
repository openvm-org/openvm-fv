import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## θ result boolean constraints: a_prime_bit[x][y][z] * (a_prime_bit[x][y][z] - 1) = 0 -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_890 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 0 row) * ((a_prime_bit c 0 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_890_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_890 c row ↔ constraint_890 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_891 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1 row) * ((a_prime_bit c 1 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_891_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_891 c row ↔ constraint_891 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_892 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 2 row) * ((a_prime_bit c 2 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_892_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_892 c row ↔ constraint_892 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_893 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 3 row) * ((a_prime_bit c 3 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_893_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_893 c row ↔ constraint_893 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_894 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 4 row) * ((a_prime_bit c 4 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_894_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_894 c row ↔ constraint_894 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_895 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 5 row) * ((a_prime_bit c 5 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_895_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_895 c row ↔ constraint_895 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_896 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 6 row) * ((a_prime_bit c 6 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_896_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_896 c row ↔ constraint_896 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_897 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 7 row) * ((a_prime_bit c 7 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_897_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_897 c row ↔ constraint_897 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_898 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 8 row) * ((a_prime_bit c 8 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_898_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_898 c row ↔ constraint_898 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_899 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 9 row) * ((a_prime_bit c 9 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_899_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_899 c row ↔ constraint_899 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_900 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 10 row) * ((a_prime_bit c 10 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_900_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_900 c row ↔ constraint_900 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_901 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 11 row) * ((a_prime_bit c 11 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_901_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_901 c row ↔ constraint_901 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_902 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 12 row) * ((a_prime_bit c 12 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_902_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_902 c row ↔ constraint_902 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_903 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 13 row) * ((a_prime_bit c 13 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_903_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_903 c row ↔ constraint_903 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_904 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 14 row) * ((a_prime_bit c 14 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_904_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_904 c row ↔ constraint_904 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_905 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 15 row) * ((a_prime_bit c 15 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_905_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_905 c row ↔ constraint_905 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_906 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 16 row) * ((a_prime_bit c 16 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_906_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_906 c row ↔ constraint_906 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_907 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 17 row) * ((a_prime_bit c 17 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_907_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_907 c row ↔ constraint_907 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_908 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 18 row) * ((a_prime_bit c 18 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_908_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_908 c row ↔ constraint_908 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_909 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 19 row) * ((a_prime_bit c 19 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_909_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_909 c row ↔ constraint_909 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_910 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 20 row) * ((a_prime_bit c 20 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_910_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_910 c row ↔ constraint_910 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_911 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 21 row) * ((a_prime_bit c 21 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_911_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_911 c row ↔ constraint_911 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_912 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 22 row) * ((a_prime_bit c 22 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_912_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_912 c row ↔ constraint_912 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_913 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 23 row) * ((a_prime_bit c 23 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_913_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_913 c row ↔ constraint_913 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_914 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 24 row) * ((a_prime_bit c 24 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_914_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_914 c row ↔ constraint_914 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_915 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 25 row) * ((a_prime_bit c 25 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_915_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_915 c row ↔ constraint_915 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_916 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 26 row) * ((a_prime_bit c 26 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_916_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_916 c row ↔ constraint_916 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_917 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 27 row) * ((a_prime_bit c 27 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_917_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_917 c row ↔ constraint_917 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_918 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 28 row) * ((a_prime_bit c 28 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_918_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_918 c row ↔ constraint_918 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_919 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 29 row) * ((a_prime_bit c 29 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_919_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_919 c row ↔ constraint_919 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_920 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 30 row) * ((a_prime_bit c 30 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_920_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_920 c row ↔ constraint_920 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_921 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 31 row) * ((a_prime_bit c 31 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_921_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_921 c row ↔ constraint_921 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_922 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 32 row) * ((a_prime_bit c 32 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_922_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_922 c row ↔ constraint_922 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_923 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 33 row) * ((a_prime_bit c 33 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_923_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_923 c row ↔ constraint_923 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_924 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 34 row) * ((a_prime_bit c 34 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_924_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_924 c row ↔ constraint_924 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_925 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 35 row) * ((a_prime_bit c 35 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_925_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_925 c row ↔ constraint_925 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_926 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 36 row) * ((a_prime_bit c 36 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_926_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_926 c row ↔ constraint_926 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_927 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 37 row) * ((a_prime_bit c 37 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_927_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_927 c row ↔ constraint_927 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_928 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 38 row) * ((a_prime_bit c 38 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_928_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_928 c row ↔ constraint_928 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_929 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 39 row) * ((a_prime_bit c 39 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_929_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_929 c row ↔ constraint_929 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_930 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 40 row) * ((a_prime_bit c 40 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_930_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_930 c row ↔ constraint_930 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_931 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 41 row) * ((a_prime_bit c 41 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_931_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_931 c row ↔ constraint_931 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_932 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 42 row) * ((a_prime_bit c 42 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_932_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_932 c row ↔ constraint_932 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_933 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 43 row) * ((a_prime_bit c 43 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_933_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_933 c row ↔ constraint_933 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_934 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 44 row) * ((a_prime_bit c 44 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_934_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_934 c row ↔ constraint_934 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_935 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 45 row) * ((a_prime_bit c 45 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_935_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_935 c row ↔ constraint_935 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_936 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 46 row) * ((a_prime_bit c 46 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_936_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_936 c row ↔ constraint_936 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_937 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 47 row) * ((a_prime_bit c 47 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_937_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_937 c row ↔ constraint_937 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_938 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 48 row) * ((a_prime_bit c 48 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_938_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_938 c row ↔ constraint_938 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_939 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 49 row) * ((a_prime_bit c 49 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_939_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_939 c row ↔ constraint_939 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_940 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 50 row) * ((a_prime_bit c 50 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_940_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_940 c row ↔ constraint_940 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_941 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 51 row) * ((a_prime_bit c 51 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_941_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_941 c row ↔ constraint_941 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_942 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 52 row) * ((a_prime_bit c 52 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_942_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_942 c row ↔ constraint_942 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_943 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 53 row) * ((a_prime_bit c 53 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_943_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_943 c row ↔ constraint_943 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_944 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 54 row) * ((a_prime_bit c 54 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_944_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_944 c row ↔ constraint_944 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_945 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 55 row) * ((a_prime_bit c 55 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_945_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_945 c row ↔ constraint_945 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_946 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 56 row) * ((a_prime_bit c 56 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_946_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_946 c row ↔ constraint_946 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_947 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 57 row) * ((a_prime_bit c 57 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_947_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_947 c row ↔ constraint_947 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_948 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 58 row) * ((a_prime_bit c 58 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_948_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_948 c row ↔ constraint_948 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_949 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 59 row) * ((a_prime_bit c 59 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_949_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_949 c row ↔ constraint_949 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_950 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 60 row) * ((a_prime_bit c 60 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_950_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_950 c row ↔ constraint_950 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_951 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 61 row) * ((a_prime_bit c 61 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_951_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_951 c row ↔ constraint_951 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_952 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 62 row) * ((a_prime_bit c 62 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_952_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_952 c row ↔ constraint_952 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_953 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 63 row) * ((a_prime_bit c 63 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_953_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_953 c row ↔ constraint_953 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_954 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 865 125 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_954_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_954 c row ↔ constraint_954 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_955 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 881 126 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_955_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_955 c row ↔ constraint_955 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_956 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 897 127 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_956_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_956 c row ↔ constraint_956 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_957 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 913 128 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_957_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_957 c row ↔ constraint_957 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_958 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 64 row) * ((a_prime_bit c 64 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_958_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_958 c row ↔ constraint_958 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_959 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 65 row) * ((a_prime_bit c 65 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_959_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_959 c row ↔ constraint_959 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_960 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 66 row) * ((a_prime_bit c 66 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_960_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_960 c row ↔ constraint_960 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_961 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 67 row) * ((a_prime_bit c 67 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_961_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_961 c row ↔ constraint_961 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_962 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 68 row) * ((a_prime_bit c 68 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_962_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_962 c row ↔ constraint_962 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_963 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 69 row) * ((a_prime_bit c 69 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_963_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_963 c row ↔ constraint_963 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_964 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 70 row) * ((a_prime_bit c 70 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_964_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_964 c row ↔ constraint_964 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_965 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 71 row) * ((a_prime_bit c 71 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_965_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_965 c row ↔ constraint_965 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_966 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 72 row) * ((a_prime_bit c 72 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_966_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_966 c row ↔ constraint_966 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_967 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 73 row) * ((a_prime_bit c 73 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_967_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_967 c row ↔ constraint_967 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_968 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 74 row) * ((a_prime_bit c 74 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_968_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_968 c row ↔ constraint_968 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_969 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 75 row) * ((a_prime_bit c 75 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_969_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_969 c row ↔ constraint_969 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_970 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 76 row) * ((a_prime_bit c 76 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_970_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_970 c row ↔ constraint_970 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_971 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 77 row) * ((a_prime_bit c 77 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_971_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_971 c row ↔ constraint_971 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_972 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 78 row) * ((a_prime_bit c 78 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_972_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_972 c row ↔ constraint_972 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_973 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 79 row) * ((a_prime_bit c 79 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_973_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_973 c row ↔ constraint_973 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_974 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 80 row) * ((a_prime_bit c 80 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_974_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_974 c row ↔ constraint_974 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_975 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 81 row) * ((a_prime_bit c 81 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_975_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_975 c row ↔ constraint_975 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_976 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 82 row) * ((a_prime_bit c 82 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_976_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_976 c row ↔ constraint_976 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_977 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 83 row) * ((a_prime_bit c 83 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_977_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_977 c row ↔ constraint_977 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_978 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 84 row) * ((a_prime_bit c 84 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_978_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_978 c row ↔ constraint_978 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_979 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 85 row) * ((a_prime_bit c 85 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_979_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_979 c row ↔ constraint_979 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_980 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 86 row) * ((a_prime_bit c 86 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_980_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_980 c row ↔ constraint_980 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_981 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 87 row) * ((a_prime_bit c 87 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_981_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_981 c row ↔ constraint_981 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_982 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 88 row) * ((a_prime_bit c 88 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_982_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_982 c row ↔ constraint_982 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_983 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 89 row) * ((a_prime_bit c 89 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_983_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_983 c row ↔ constraint_983 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_984 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 90 row) * ((a_prime_bit c 90 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_984_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_984 c row ↔ constraint_984 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_985 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 91 row) * ((a_prime_bit c 91 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_985_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_985 c row ↔ constraint_985 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_986 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 92 row) * ((a_prime_bit c 92 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_986_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_986 c row ↔ constraint_986 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_987 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 93 row) * ((a_prime_bit c 93 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_987_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_987 c row ↔ constraint_987 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_988 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 94 row) * ((a_prime_bit c 94 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_988_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_988 c row ↔ constraint_988 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_989 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 95 row) * ((a_prime_bit c 95 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_989_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_989 c row ↔ constraint_989 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_990 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 96 row) * ((a_prime_bit c 96 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_990_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_990 c row ↔ constraint_990 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_991 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 97 row) * ((a_prime_bit c 97 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_991_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_991 c row ↔ constraint_991 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_992 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 98 row) * ((a_prime_bit c 98 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_992_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_992 c row ↔ constraint_992 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_993 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 99 row) * ((a_prime_bit c 99 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_993_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_993 c row ↔ constraint_993 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_994 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 100 row) * ((a_prime_bit c 100 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_994_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_994 c row ↔ constraint_994 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_995 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 101 row) * ((a_prime_bit c 101 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_995_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_995 c row ↔ constraint_995 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_996 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 102 row) * ((a_prime_bit c 102 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_996_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_996 c row ↔ constraint_996 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_997 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 103 row) * ((a_prime_bit c 103 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_997_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_997 c row ↔ constraint_997 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_998 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 104 row) * ((a_prime_bit c 104 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_998_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_998 c row ↔ constraint_998 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_999 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 105 row) * ((a_prime_bit c 105 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_999_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_999 c row ↔ constraint_999 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1000 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 106 row) * ((a_prime_bit c 106 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1000_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1000 c row ↔ constraint_1000 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1001 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 107 row) * ((a_prime_bit c 107 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1001_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1001 c row ↔ constraint_1001 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1002 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 108 row) * ((a_prime_bit c 108 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1002_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1002 c row ↔ constraint_1002 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1003 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 109 row) * ((a_prime_bit c 109 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1003_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1003 c row ↔ constraint_1003 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1004 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 110 row) * ((a_prime_bit c 110 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1004_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1004 c row ↔ constraint_1004 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1005 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 111 row) * ((a_prime_bit c 111 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1005_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1005 c row ↔ constraint_1005 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1006 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 112 row) * ((a_prime_bit c 112 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1006_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1006 c row ↔ constraint_1006 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1007 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 113 row) * ((a_prime_bit c 113 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1007_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1007 c row ↔ constraint_1007 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1008 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 114 row) * ((a_prime_bit c 114 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1008_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1008 c row ↔ constraint_1008 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1009 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 115 row) * ((a_prime_bit c 115 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1009_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1009 c row ↔ constraint_1009 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1010 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 116 row) * ((a_prime_bit c 116 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1010_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1010 c row ↔ constraint_1010 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1011 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 117 row) * ((a_prime_bit c 117 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1011_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1011 c row ↔ constraint_1011 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1012 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 118 row) * ((a_prime_bit c 118 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1012_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1012 c row ↔ constraint_1012 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1013 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 119 row) * ((a_prime_bit c 119 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1013_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1013 c row ↔ constraint_1013 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1014 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 120 row) * ((a_prime_bit c 120 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1014_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1014 c row ↔ constraint_1014 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1015 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 121 row) * ((a_prime_bit c 121 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1015_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1015 c row ↔ constraint_1015 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1016 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 122 row) * ((a_prime_bit c 122 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1016_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1016 c row ↔ constraint_1016 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1017 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 123 row) * ((a_prime_bit c 123 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1017_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1017 c row ↔ constraint_1017 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1018 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 124 row) * ((a_prime_bit c 124 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1018_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1018 c row ↔ constraint_1018 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1019 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 125 row) * ((a_prime_bit c 125 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1019_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1019 c row ↔ constraint_1019 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1020 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 126 row) * ((a_prime_bit c 126 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1020_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1020 c row ↔ constraint_1020 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1021 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 127 row) * ((a_prime_bit c 127 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1021_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1021 c row ↔ constraint_1021 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1022 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 929 129 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1022_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1022 c row ↔ constraint_1022 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1023 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 945 130 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1023_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1023 c row ↔ constraint_1023 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1024 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 961 131 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1024_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1024 c row ↔ constraint_1024 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1025 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 977 132 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1025_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1025 c row ↔ constraint_1025 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1026 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 128 row) * ((a_prime_bit c 128 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1026_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1026 c row ↔ constraint_1026 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1027 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 129 row) * ((a_prime_bit c 129 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1027_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1027 c row ↔ constraint_1027 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1028 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 130 row) * ((a_prime_bit c 130 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1028_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1028 c row ↔ constraint_1028 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1029 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 131 row) * ((a_prime_bit c 131 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1029_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1029 c row ↔ constraint_1029 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1030 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 132 row) * ((a_prime_bit c 132 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1030_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1030 c row ↔ constraint_1030 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1031 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 133 row) * ((a_prime_bit c 133 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1031_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1031 c row ↔ constraint_1031 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1032 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 134 row) * ((a_prime_bit c 134 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1032_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1032 c row ↔ constraint_1032 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1033 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 135 row) * ((a_prime_bit c 135 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1033_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1033 c row ↔ constraint_1033 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1034 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 136 row) * ((a_prime_bit c 136 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1034_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1034 c row ↔ constraint_1034 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1035 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 137 row) * ((a_prime_bit c 137 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1035_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1035 c row ↔ constraint_1035 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1036 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 138 row) * ((a_prime_bit c 138 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1036_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1036 c row ↔ constraint_1036 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1037 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 139 row) * ((a_prime_bit c 139 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1037_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1037 c row ↔ constraint_1037 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1038 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 140 row) * ((a_prime_bit c 140 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1038_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1038 c row ↔ constraint_1038 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1039 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 141 row) * ((a_prime_bit c 141 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1039_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1039 c row ↔ constraint_1039 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1040 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 142 row) * ((a_prime_bit c 142 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1040_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1040 c row ↔ constraint_1040 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1041 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 143 row) * ((a_prime_bit c 143 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1041_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1041 c row ↔ constraint_1041 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1042 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 144 row) * ((a_prime_bit c 144 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1042_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1042 c row ↔ constraint_1042 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1043 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 145 row) * ((a_prime_bit c 145 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1043_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1043 c row ↔ constraint_1043 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1044 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 146 row) * ((a_prime_bit c 146 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1044_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1044 c row ↔ constraint_1044 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1045 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 147 row) * ((a_prime_bit c 147 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1045_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1045 c row ↔ constraint_1045 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1046 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 148 row) * ((a_prime_bit c 148 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1046_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1046 c row ↔ constraint_1046 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1047 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 149 row) * ((a_prime_bit c 149 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1047_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1047 c row ↔ constraint_1047 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1048 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 150 row) * ((a_prime_bit c 150 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1048_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1048 c row ↔ constraint_1048 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1049 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 151 row) * ((a_prime_bit c 151 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1049_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1049 c row ↔ constraint_1049 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1050 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 152 row) * ((a_prime_bit c 152 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1050_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1050 c row ↔ constraint_1050 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1051 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 153 row) * ((a_prime_bit c 153 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1051_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1051 c row ↔ constraint_1051 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1052 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 154 row) * ((a_prime_bit c 154 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1052_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1052 c row ↔ constraint_1052 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1053 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 155 row) * ((a_prime_bit c 155 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1053_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1053 c row ↔ constraint_1053 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1054 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 156 row) * ((a_prime_bit c 156 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1054_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1054 c row ↔ constraint_1054 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1055 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 157 row) * ((a_prime_bit c 157 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1055_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1055 c row ↔ constraint_1055 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1056 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 158 row) * ((a_prime_bit c 158 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1056_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1056 c row ↔ constraint_1056 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1057 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 159 row) * ((a_prime_bit c 159 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1057_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1057 c row ↔ constraint_1057 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1058 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 160 row) * ((a_prime_bit c 160 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1058_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1058 c row ↔ constraint_1058 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1059 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 161 row) * ((a_prime_bit c 161 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1059_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1059 c row ↔ constraint_1059 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1060 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 162 row) * ((a_prime_bit c 162 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1060_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1060 c row ↔ constraint_1060 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1061 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 163 row) * ((a_prime_bit c 163 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1061_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1061 c row ↔ constraint_1061 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1062 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 164 row) * ((a_prime_bit c 164 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1062_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1062 c row ↔ constraint_1062 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1063 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 165 row) * ((a_prime_bit c 165 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1063_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1063 c row ↔ constraint_1063 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1064 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 166 row) * ((a_prime_bit c 166 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1064_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1064 c row ↔ constraint_1064 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1065 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 167 row) * ((a_prime_bit c 167 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1065_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1065 c row ↔ constraint_1065 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1066 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 168 row) * ((a_prime_bit c 168 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1066_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1066 c row ↔ constraint_1066 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1067 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 169 row) * ((a_prime_bit c 169 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1067_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1067 c row ↔ constraint_1067 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1068 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 170 row) * ((a_prime_bit c 170 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1068_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1068 c row ↔ constraint_1068 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1069 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 171 row) * ((a_prime_bit c 171 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1069_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1069 c row ↔ constraint_1069 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1070 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 172 row) * ((a_prime_bit c 172 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1070_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1070 c row ↔ constraint_1070 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1071 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 173 row) * ((a_prime_bit c 173 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1071_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1071 c row ↔ constraint_1071 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1072 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 174 row) * ((a_prime_bit c 174 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1072_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1072 c row ↔ constraint_1072 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1073 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 175 row) * ((a_prime_bit c 175 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1073_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1073 c row ↔ constraint_1073 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1074 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 176 row) * ((a_prime_bit c 176 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1074_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1074 c row ↔ constraint_1074 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1075 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 177 row) * ((a_prime_bit c 177 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1075_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1075 c row ↔ constraint_1075 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1076 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 178 row) * ((a_prime_bit c 178 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1076_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1076 c row ↔ constraint_1076 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1077 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 179 row) * ((a_prime_bit c 179 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1077_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1077 c row ↔ constraint_1077 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1078 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 180 row) * ((a_prime_bit c 180 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1078_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1078 c row ↔ constraint_1078 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1079 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 181 row) * ((a_prime_bit c 181 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1079_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1079 c row ↔ constraint_1079 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1080 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 182 row) * ((a_prime_bit c 182 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1080_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1080 c row ↔ constraint_1080 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1081 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 183 row) * ((a_prime_bit c 183 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1081_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1081 c row ↔ constraint_1081 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1082 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 184 row) * ((a_prime_bit c 184 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1082_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1082 c row ↔ constraint_1082 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1083 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 185 row) * ((a_prime_bit c 185 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1083_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1083 c row ↔ constraint_1083 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1084 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 186 row) * ((a_prime_bit c 186 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1084_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1084 c row ↔ constraint_1084 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1085 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 187 row) * ((a_prime_bit c 187 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1085_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1085 c row ↔ constraint_1085 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1086 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 188 row) * ((a_prime_bit c 188 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1086_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1086 c row ↔ constraint_1086 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1087 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 189 row) * ((a_prime_bit c 189 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1087_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1087 c row ↔ constraint_1087 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1088 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 190 row) * ((a_prime_bit c 190 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1088_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1088 c row ↔ constraint_1088 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1089 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 191 row) * ((a_prime_bit c 191 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1089_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1089 c row ↔ constraint_1089 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1090 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 993 133 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1090_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1090 c row ↔ constraint_1090 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1091 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1009 134 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1091_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1091 c row ↔ constraint_1091 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1092 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1025 135 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1092_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1092 c row ↔ constraint_1092 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1093 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 1041 136 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1093_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1093 c row ↔ constraint_1093 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1094 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 192 row) * ((a_prime_bit c 192 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1094_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1094 c row ↔ constraint_1094 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1095 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 193 row) * ((a_prime_bit c 193 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1095_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1095 c row ↔ constraint_1095 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1096 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 194 row) * ((a_prime_bit c 194 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1096_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1096 c row ↔ constraint_1096 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1097 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 195 row) * ((a_prime_bit c 195 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1097_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1097 c row ↔ constraint_1097 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1098 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 196 row) * ((a_prime_bit c 196 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1098_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1098 c row ↔ constraint_1098 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1099 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 197 row) * ((a_prime_bit c 197 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1099_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1099 c row ↔ constraint_1099 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1100 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 198 row) * ((a_prime_bit c 198 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1100_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1100 c row ↔ constraint_1100 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1101 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 199 row) * ((a_prime_bit c 199 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1101_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1101 c row ↔ constraint_1101 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1102 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 200 row) * ((a_prime_bit c 200 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1102_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1102 c row ↔ constraint_1102 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1103 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 201 row) * ((a_prime_bit c 201 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1103_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1103 c row ↔ constraint_1103 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1104 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 202 row) * ((a_prime_bit c 202 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1104_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1104 c row ↔ constraint_1104 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1105 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 203 row) * ((a_prime_bit c 203 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1105_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1105 c row ↔ constraint_1105 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1106 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 204 row) * ((a_prime_bit c 204 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1106_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1106 c row ↔ constraint_1106 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1107 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 205 row) * ((a_prime_bit c 205 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1107_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1107 c row ↔ constraint_1107 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1108 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 206 row) * ((a_prime_bit c 206 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1108_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1108 c row ↔ constraint_1108 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1109 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 207 row) * ((a_prime_bit c 207 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1109_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1109 c row ↔ constraint_1109 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1110 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 208 row) * ((a_prime_bit c 208 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1110_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1110 c row ↔ constraint_1110 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1111 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 209 row) * ((a_prime_bit c 209 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1111_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1111 c row ↔ constraint_1111 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1112 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 210 row) * ((a_prime_bit c 210 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1112_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1112 c row ↔ constraint_1112 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1113 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 211 row) * ((a_prime_bit c 211 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1113_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1113 c row ↔ constraint_1113 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1114 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 212 row) * ((a_prime_bit c 212 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1114_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1114 c row ↔ constraint_1114 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1115 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 213 row) * ((a_prime_bit c 213 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1115_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1115 c row ↔ constraint_1115 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1116 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 214 row) * ((a_prime_bit c 214 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1116_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1116 c row ↔ constraint_1116 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1117 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 215 row) * ((a_prime_bit c 215 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1117_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1117 c row ↔ constraint_1117 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1118 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 216 row) * ((a_prime_bit c 216 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1118_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1118 c row ↔ constraint_1118 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1119 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 217 row) * ((a_prime_bit c 217 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1119_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1119 c row ↔ constraint_1119 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1120 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 218 row) * ((a_prime_bit c 218 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1120_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1120 c row ↔ constraint_1120 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1121 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 219 row) * ((a_prime_bit c 219 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1121_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1121 c row ↔ constraint_1121 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1122 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 220 row) * ((a_prime_bit c 220 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1122_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1122 c row ↔ constraint_1122 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1123 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 221 row) * ((a_prime_bit c 221 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1123_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1123 c row ↔ constraint_1123 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1124 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 222 row) * ((a_prime_bit c 222 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1124_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1124 c row ↔ constraint_1124 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1125 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 223 row) * ((a_prime_bit c 223 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1125_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1125 c row ↔ constraint_1125 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1126 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 224 row) * ((a_prime_bit c 224 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1126_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1126 c row ↔ constraint_1126 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1127 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 225 row) * ((a_prime_bit c 225 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1127_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1127 c row ↔ constraint_1127 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1128 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 226 row) * ((a_prime_bit c 226 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1128_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1128 c row ↔ constraint_1128 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1129 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 227 row) * ((a_prime_bit c 227 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1129_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1129 c row ↔ constraint_1129 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1130 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 228 row) * ((a_prime_bit c 228 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1130_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1130 c row ↔ constraint_1130 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1131 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 229 row) * ((a_prime_bit c 229 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1131_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1131 c row ↔ constraint_1131 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1132 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 230 row) * ((a_prime_bit c 230 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1132_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1132 c row ↔ constraint_1132 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1133 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 231 row) * ((a_prime_bit c 231 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1133_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1133 c row ↔ constraint_1133 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1134 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 232 row) * ((a_prime_bit c 232 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1134_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1134 c row ↔ constraint_1134 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1135 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 233 row) * ((a_prime_bit c 233 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1135_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1135 c row ↔ constraint_1135 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1136 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 234 row) * ((a_prime_bit c 234 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1136_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1136 c row ↔ constraint_1136 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1137 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 235 row) * ((a_prime_bit c 235 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1137_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1137 c row ↔ constraint_1137 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1138 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 236 row) * ((a_prime_bit c 236 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1138_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1138 c row ↔ constraint_1138 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1139 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 237 row) * ((a_prime_bit c 237 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1139_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1139 c row ↔ constraint_1139 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1140 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 238 row) * ((a_prime_bit c 238 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1140_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1140 c row ↔ constraint_1140 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1141 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 239 row) * ((a_prime_bit c 239 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1141_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1141 c row ↔ constraint_1141 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1142 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 240 row) * ((a_prime_bit c 240 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1142_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1142 c row ↔ constraint_1142 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1143 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 241 row) * ((a_prime_bit c 241 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1143_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1143 c row ↔ constraint_1143 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1144 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 242 row) * ((a_prime_bit c 242 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1144_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1144 c row ↔ constraint_1144 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1145 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 243 row) * ((a_prime_bit c 243 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1145_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1145 c row ↔ constraint_1145 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1146 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 244 row) * ((a_prime_bit c 244 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1146_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1146 c row ↔ constraint_1146 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1147 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 245 row) * ((a_prime_bit c 245 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1147_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1147 c row ↔ constraint_1147 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1148 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 246 row) * ((a_prime_bit c 246 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1148_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1148 c row ↔ constraint_1148 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1149 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 247 row) * ((a_prime_bit c 247 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1149_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1149 c row ↔ constraint_1149 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1150 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 248 row) * ((a_prime_bit c 248 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1150_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1150 c row ↔ constraint_1150 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1151 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 249 row) * ((a_prime_bit c 249 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1151_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1151 c row ↔ constraint_1151 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1152 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 250 row) * ((a_prime_bit c 250 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1152_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1152 c row ↔ constraint_1152 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1153 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 251 row) * ((a_prime_bit c 251 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1153_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1153 c row ↔ constraint_1153 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1154 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 252 row) * ((a_prime_bit c 252 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1154_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1154 c row ↔ constraint_1154 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1155 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 253 row) * ((a_prime_bit c 253 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1155_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1155 c row ↔ constraint_1155 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1156 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 254 row) * ((a_prime_bit c 254 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1156_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1156 c row ↔ constraint_1156 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1157 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 255 row) * ((a_prime_bit c 255 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1157_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1157 c row ↔ constraint_1157 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1158 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 1057 137 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1158_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1158 c row ↔ constraint_1158 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1159 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 1073 138 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1159_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1159 c row ↔ constraint_1159 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1160 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 1089 139 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1160_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1160 c row ↔ constraint_1160 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1161 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 1105 140 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1161_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1161 c row ↔ constraint_1161 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1162 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 256 row) * ((a_prime_bit c 256 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1162_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1162 c row ↔ constraint_1162 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1163 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 257 row) * ((a_prime_bit c 257 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1163_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1163 c row ↔ constraint_1163 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1164 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 258 row) * ((a_prime_bit c 258 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1164_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1164 c row ↔ constraint_1164 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1165 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 259 row) * ((a_prime_bit c 259 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1165_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1165 c row ↔ constraint_1165 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1166 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 260 row) * ((a_prime_bit c 260 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1166_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1166 c row ↔ constraint_1166 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1167 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 261 row) * ((a_prime_bit c 261 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1167_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1167 c row ↔ constraint_1167 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1168 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 262 row) * ((a_prime_bit c 262 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1168_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1168 c row ↔ constraint_1168 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1169 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 263 row) * ((a_prime_bit c 263 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1169_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1169 c row ↔ constraint_1169 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1170 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 264 row) * ((a_prime_bit c 264 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1170_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1170 c row ↔ constraint_1170 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1171 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 265 row) * ((a_prime_bit c 265 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1171_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1171 c row ↔ constraint_1171 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1172 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 266 row) * ((a_prime_bit c 266 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1172_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1172 c row ↔ constraint_1172 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1173 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 267 row) * ((a_prime_bit c 267 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1173_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1173 c row ↔ constraint_1173 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1174 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 268 row) * ((a_prime_bit c 268 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1174_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1174 c row ↔ constraint_1174 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1175 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 269 row) * ((a_prime_bit c 269 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1175_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1175 c row ↔ constraint_1175 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1176 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 270 row) * ((a_prime_bit c 270 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1176_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1176 c row ↔ constraint_1176 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1177 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 271 row) * ((a_prime_bit c 271 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1177_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1177 c row ↔ constraint_1177 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1178 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 272 row) * ((a_prime_bit c 272 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1178_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1178 c row ↔ constraint_1178 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1179 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 273 row) * ((a_prime_bit c 273 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1179_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1179 c row ↔ constraint_1179 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1180 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 274 row) * ((a_prime_bit c 274 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1180_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1180 c row ↔ constraint_1180 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1181 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 275 row) * ((a_prime_bit c 275 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1181_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1181 c row ↔ constraint_1181 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1182 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 276 row) * ((a_prime_bit c 276 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1182_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1182 c row ↔ constraint_1182 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1183 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 277 row) * ((a_prime_bit c 277 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1183_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1183 c row ↔ constraint_1183 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1184 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 278 row) * ((a_prime_bit c 278 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1184_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1184 c row ↔ constraint_1184 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1185 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 279 row) * ((a_prime_bit c 279 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1185_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1185 c row ↔ constraint_1185 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1186 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 280 row) * ((a_prime_bit c 280 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1186_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1186 c row ↔ constraint_1186 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1187 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 281 row) * ((a_prime_bit c 281 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1187_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1187 c row ↔ constraint_1187 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1188 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 282 row) * ((a_prime_bit c 282 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1188_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1188 c row ↔ constraint_1188 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1189 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 283 row) * ((a_prime_bit c 283 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1189_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1189 c row ↔ constraint_1189 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1190 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 284 row) * ((a_prime_bit c 284 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1190_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1190 c row ↔ constraint_1190 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1191 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 285 row) * ((a_prime_bit c 285 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1191_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1191 c row ↔ constraint_1191 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1192 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 286 row) * ((a_prime_bit c 286 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1192_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1192 c row ↔ constraint_1192 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1193 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 287 row) * ((a_prime_bit c 287 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1193_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1193 c row ↔ constraint_1193 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1194 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 288 row) * ((a_prime_bit c 288 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1194_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1194 c row ↔ constraint_1194 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1195 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 289 row) * ((a_prime_bit c 289 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1195_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1195 c row ↔ constraint_1195 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1196 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 290 row) * ((a_prime_bit c 290 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1196_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1196 c row ↔ constraint_1196 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1197 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 291 row) * ((a_prime_bit c 291 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1197_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1197 c row ↔ constraint_1197 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1198 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 292 row) * ((a_prime_bit c 292 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1198_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1198 c row ↔ constraint_1198 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1199 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 293 row) * ((a_prime_bit c 293 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1199_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1199 c row ↔ constraint_1199 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1200 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 294 row) * ((a_prime_bit c 294 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1200_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1200 c row ↔ constraint_1200 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1201 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 295 row) * ((a_prime_bit c 295 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1201_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1201 c row ↔ constraint_1201 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1202 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 296 row) * ((a_prime_bit c 296 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1202_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1202 c row ↔ constraint_1202 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1203 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 297 row) * ((a_prime_bit c 297 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1203_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1203 c row ↔ constraint_1203 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1204 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 298 row) * ((a_prime_bit c 298 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1204_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1204 c row ↔ constraint_1204 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1205 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 299 row) * ((a_prime_bit c 299 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1205_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1205 c row ↔ constraint_1205 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1206 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 300 row) * ((a_prime_bit c 300 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1206_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1206 c row ↔ constraint_1206 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1207 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 301 row) * ((a_prime_bit c 301 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1207_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1207 c row ↔ constraint_1207 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1208 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 302 row) * ((a_prime_bit c 302 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1208_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1208 c row ↔ constraint_1208 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1209 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 303 row) * ((a_prime_bit c 303 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1209_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1209 c row ↔ constraint_1209 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1210 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 304 row) * ((a_prime_bit c 304 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1210_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1210 c row ↔ constraint_1210 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1211 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 305 row) * ((a_prime_bit c 305 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1211_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1211 c row ↔ constraint_1211 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1212 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 306 row) * ((a_prime_bit c 306 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1212_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1212 c row ↔ constraint_1212 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1213 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 307 row) * ((a_prime_bit c 307 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1213_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1213 c row ↔ constraint_1213 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1214 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 308 row) * ((a_prime_bit c 308 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1214_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1214 c row ↔ constraint_1214 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1215 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 309 row) * ((a_prime_bit c 309 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1215_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1215 c row ↔ constraint_1215 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1216 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 310 row) * ((a_prime_bit c 310 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1216_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1216 c row ↔ constraint_1216 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1217 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 311 row) * ((a_prime_bit c 311 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1217_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1217 c row ↔ constraint_1217 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1218 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 312 row) * ((a_prime_bit c 312 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1218_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1218 c row ↔ constraint_1218 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1219 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 313 row) * ((a_prime_bit c 313 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1219_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1219 c row ↔ constraint_1219 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1220 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 314 row) * ((a_prime_bit c 314 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1220_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1220 c row ↔ constraint_1220 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1221 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 315 row) * ((a_prime_bit c 315 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1221_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1221 c row ↔ constraint_1221 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1222 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 316 row) * ((a_prime_bit c 316 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1222_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1222 c row ↔ constraint_1222 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1223 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 317 row) * ((a_prime_bit c 317 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1223_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1223 c row ↔ constraint_1223 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1224 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 318 row) * ((a_prime_bit c 318 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1224_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1224 c row ↔ constraint_1224 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1225 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 319 row) * ((a_prime_bit c 319 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1225_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1225 c row ↔ constraint_1225 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1226 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 1121 141 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1226_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1226 c row ↔ constraint_1226 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1227 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 1137 142 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1227_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1227 c row ↔ constraint_1227 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1228 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 1153 143 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1228_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1228 c row ↔ constraint_1228 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1229 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 1169 144 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1229_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1229 c row ↔ constraint_1229 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1230 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 320 row) * ((a_prime_bit c 320 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1230_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1230 c row ↔ constraint_1230 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1231 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 321 row) * ((a_prime_bit c 321 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1231_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1231 c row ↔ constraint_1231 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1232 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 322 row) * ((a_prime_bit c 322 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1232_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1232 c row ↔ constraint_1232 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1233 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 323 row) * ((a_prime_bit c 323 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1233_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1233 c row ↔ constraint_1233 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1234 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 324 row) * ((a_prime_bit c 324 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1234_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1234 c row ↔ constraint_1234 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1235 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 325 row) * ((a_prime_bit c 325 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1235_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1235 c row ↔ constraint_1235 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1236 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 326 row) * ((a_prime_bit c 326 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1236_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1236 c row ↔ constraint_1236 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1237 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 327 row) * ((a_prime_bit c 327 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1237_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1237 c row ↔ constraint_1237 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1238 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 328 row) * ((a_prime_bit c 328 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1238_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1238 c row ↔ constraint_1238 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1239 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 329 row) * ((a_prime_bit c 329 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1239_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1239 c row ↔ constraint_1239 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1240 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 330 row) * ((a_prime_bit c 330 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1240_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1240 c row ↔ constraint_1240 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1241 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 331 row) * ((a_prime_bit c 331 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1241_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1241 c row ↔ constraint_1241 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1242 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 332 row) * ((a_prime_bit c 332 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1242_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1242 c row ↔ constraint_1242 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1243 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 333 row) * ((a_prime_bit c 333 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1243_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1243 c row ↔ constraint_1243 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1244 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 334 row) * ((a_prime_bit c 334 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1244_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1244 c row ↔ constraint_1244 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1245 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 335 row) * ((a_prime_bit c 335 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1245_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1245 c row ↔ constraint_1245 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1246 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 336 row) * ((a_prime_bit c 336 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1246_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1246 c row ↔ constraint_1246 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1247 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 337 row) * ((a_prime_bit c 337 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1247_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1247 c row ↔ constraint_1247 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1248 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 338 row) * ((a_prime_bit c 338 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1248_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1248 c row ↔ constraint_1248 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1249 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 339 row) * ((a_prime_bit c 339 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1249_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1249 c row ↔ constraint_1249 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1250 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 340 row) * ((a_prime_bit c 340 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1250_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1250 c row ↔ constraint_1250 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1251 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 341 row) * ((a_prime_bit c 341 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1251_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1251 c row ↔ constraint_1251 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1252 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 342 row) * ((a_prime_bit c 342 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1252_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1252 c row ↔ constraint_1252 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1253 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 343 row) * ((a_prime_bit c 343 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1253_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1253 c row ↔ constraint_1253 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1254 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 344 row) * ((a_prime_bit c 344 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1254_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1254 c row ↔ constraint_1254 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1255 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 345 row) * ((a_prime_bit c 345 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1255_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1255 c row ↔ constraint_1255 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1256 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 346 row) * ((a_prime_bit c 346 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1256_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1256 c row ↔ constraint_1256 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1257 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 347 row) * ((a_prime_bit c 347 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1257_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1257 c row ↔ constraint_1257 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1258 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 348 row) * ((a_prime_bit c 348 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1258_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1258 c row ↔ constraint_1258 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1259 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 349 row) * ((a_prime_bit c 349 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1259_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1259 c row ↔ constraint_1259 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1260 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 350 row) * ((a_prime_bit c 350 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1260_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1260 c row ↔ constraint_1260 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1261 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 351 row) * ((a_prime_bit c 351 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1261_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1261 c row ↔ constraint_1261 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1262 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 352 row) * ((a_prime_bit c 352 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1262_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1262 c row ↔ constraint_1262 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1263 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 353 row) * ((a_prime_bit c 353 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1263_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1263 c row ↔ constraint_1263 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1264 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 354 row) * ((a_prime_bit c 354 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1264_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1264 c row ↔ constraint_1264 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1265 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 355 row) * ((a_prime_bit c 355 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1265_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1265 c row ↔ constraint_1265 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1266 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 356 row) * ((a_prime_bit c 356 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1266_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1266 c row ↔ constraint_1266 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1267 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 357 row) * ((a_prime_bit c 357 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1267_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1267 c row ↔ constraint_1267 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1268 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 358 row) * ((a_prime_bit c 358 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1268_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1268 c row ↔ constraint_1268 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1269 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 359 row) * ((a_prime_bit c 359 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1269_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1269 c row ↔ constraint_1269 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1270 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 360 row) * ((a_prime_bit c 360 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1270_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1270 c row ↔ constraint_1270 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1271 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 361 row) * ((a_prime_bit c 361 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1271_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1271 c row ↔ constraint_1271 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1272 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 362 row) * ((a_prime_bit c 362 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1272_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1272 c row ↔ constraint_1272 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1273 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 363 row) * ((a_prime_bit c 363 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1273_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1273 c row ↔ constraint_1273 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1274 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 364 row) * ((a_prime_bit c 364 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1274_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1274 c row ↔ constraint_1274 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1275 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 365 row) * ((a_prime_bit c 365 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1275_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1275 c row ↔ constraint_1275 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1276 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 366 row) * ((a_prime_bit c 366 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1276_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1276 c row ↔ constraint_1276 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1277 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 367 row) * ((a_prime_bit c 367 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1277_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1277 c row ↔ constraint_1277 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1278 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 368 row) * ((a_prime_bit c 368 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1278_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1278 c row ↔ constraint_1278 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1279 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 369 row) * ((a_prime_bit c 369 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1279_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1279 c row ↔ constraint_1279 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1280 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 370 row) * ((a_prime_bit c 370 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1280_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1280 c row ↔ constraint_1280 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1281 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 371 row) * ((a_prime_bit c 371 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1281_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1281 c row ↔ constraint_1281 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1282 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 372 row) * ((a_prime_bit c 372 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1282_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1282 c row ↔ constraint_1282 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1283 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 373 row) * ((a_prime_bit c 373 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1283_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1283 c row ↔ constraint_1283 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1284 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 374 row) * ((a_prime_bit c 374 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1284_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1284 c row ↔ constraint_1284 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1285 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 375 row) * ((a_prime_bit c 375 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1285_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1285 c row ↔ constraint_1285 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1286 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 376 row) * ((a_prime_bit c 376 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1286_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1286 c row ↔ constraint_1286 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1287 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 377 row) * ((a_prime_bit c 377 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1287_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1287 c row ↔ constraint_1287 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1288 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 378 row) * ((a_prime_bit c 378 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1288_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1288 c row ↔ constraint_1288 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1289 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 379 row) * ((a_prime_bit c 379 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1289_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1289 c row ↔ constraint_1289 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1290 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 380 row) * ((a_prime_bit c 380 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1290_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1290 c row ↔ constraint_1290 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1291 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 381 row) * ((a_prime_bit c 381 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1291_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1291 c row ↔ constraint_1291 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1292 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 382 row) * ((a_prime_bit c 382 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1292_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1292 c row ↔ constraint_1292 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1293 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 383 row) * ((a_prime_bit c 383 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1293_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1293 c row ↔ constraint_1293 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1294 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 1185 145 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1294_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1294 c row ↔ constraint_1294 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1295 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 1201 146 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1295_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1295 c row ↔ constraint_1295 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1296 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 1217 147 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1296_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1296 c row ↔ constraint_1296 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1297 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 1233 148 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1297_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1297 c row ↔ constraint_1297 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1298 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 384 row) * ((a_prime_bit c 384 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1298_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1298 c row ↔ constraint_1298 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1299 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 385 row) * ((a_prime_bit c 385 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1299_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1299 c row ↔ constraint_1299 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1300 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 386 row) * ((a_prime_bit c 386 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1300_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1300 c row ↔ constraint_1300 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1301 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 387 row) * ((a_prime_bit c 387 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1301_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1301 c row ↔ constraint_1301 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1302 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 388 row) * ((a_prime_bit c 388 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1302_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1302 c row ↔ constraint_1302 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1303 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 389 row) * ((a_prime_bit c 389 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1303_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1303 c row ↔ constraint_1303 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1304 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 390 row) * ((a_prime_bit c 390 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1304_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1304 c row ↔ constraint_1304 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1305 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 391 row) * ((a_prime_bit c 391 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1305_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1305 c row ↔ constraint_1305 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1306 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 392 row) * ((a_prime_bit c 392 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1306_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1306 c row ↔ constraint_1306 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1307 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 393 row) * ((a_prime_bit c 393 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1307_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1307 c row ↔ constraint_1307 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1308 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 394 row) * ((a_prime_bit c 394 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1308_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1308 c row ↔ constraint_1308 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1309 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 395 row) * ((a_prime_bit c 395 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1309_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1309 c row ↔ constraint_1309 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1310 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 396 row) * ((a_prime_bit c 396 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1310_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1310 c row ↔ constraint_1310 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1311 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 397 row) * ((a_prime_bit c 397 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1311_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1311 c row ↔ constraint_1311 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1312 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 398 row) * ((a_prime_bit c 398 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1312_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1312 c row ↔ constraint_1312 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1313 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 399 row) * ((a_prime_bit c 399 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1313_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1313 c row ↔ constraint_1313 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1314 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 400 row) * ((a_prime_bit c 400 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1314_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1314 c row ↔ constraint_1314 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1315 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 401 row) * ((a_prime_bit c 401 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1315_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1315 c row ↔ constraint_1315 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1316 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 402 row) * ((a_prime_bit c 402 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1316_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1316 c row ↔ constraint_1316 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1317 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 403 row) * ((a_prime_bit c 403 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1317_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1317 c row ↔ constraint_1317 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1318 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 404 row) * ((a_prime_bit c 404 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1318_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1318 c row ↔ constraint_1318 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1319 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 405 row) * ((a_prime_bit c 405 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1319_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1319 c row ↔ constraint_1319 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1320 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 406 row) * ((a_prime_bit c 406 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1320_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1320 c row ↔ constraint_1320 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1321 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 407 row) * ((a_prime_bit c 407 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1321_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1321 c row ↔ constraint_1321 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1322 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 408 row) * ((a_prime_bit c 408 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1322_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1322 c row ↔ constraint_1322 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1323 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 409 row) * ((a_prime_bit c 409 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1323_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1323 c row ↔ constraint_1323 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1324 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 410 row) * ((a_prime_bit c 410 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1324_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1324 c row ↔ constraint_1324 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1325 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 411 row) * ((a_prime_bit c 411 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1325_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1325 c row ↔ constraint_1325 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1326 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 412 row) * ((a_prime_bit c 412 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1326_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1326 c row ↔ constraint_1326 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1327 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 413 row) * ((a_prime_bit c 413 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1327_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1327 c row ↔ constraint_1327 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1328 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 414 row) * ((a_prime_bit c 414 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1328_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1328 c row ↔ constraint_1328 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1329 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 415 row) * ((a_prime_bit c 415 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1329_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1329 c row ↔ constraint_1329 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1330 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 416 row) * ((a_prime_bit c 416 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1330_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1330 c row ↔ constraint_1330 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1331 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 417 row) * ((a_prime_bit c 417 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1331_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1331 c row ↔ constraint_1331 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1332 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 418 row) * ((a_prime_bit c 418 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1332_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1332 c row ↔ constraint_1332 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1333 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 419 row) * ((a_prime_bit c 419 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1333_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1333 c row ↔ constraint_1333 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1334 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 420 row) * ((a_prime_bit c 420 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1334_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1334 c row ↔ constraint_1334 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1335 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 421 row) * ((a_prime_bit c 421 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1335_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1335 c row ↔ constraint_1335 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1336 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 422 row) * ((a_prime_bit c 422 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1336_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1336 c row ↔ constraint_1336 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1337 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 423 row) * ((a_prime_bit c 423 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1337_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1337 c row ↔ constraint_1337 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1338 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 424 row) * ((a_prime_bit c 424 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1338_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1338 c row ↔ constraint_1338 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1339 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 425 row) * ((a_prime_bit c 425 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1339_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1339 c row ↔ constraint_1339 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1340 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 426 row) * ((a_prime_bit c 426 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1340_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1340 c row ↔ constraint_1340 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1341 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 427 row) * ((a_prime_bit c 427 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1341_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1341 c row ↔ constraint_1341 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1342 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 428 row) * ((a_prime_bit c 428 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1342_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1342 c row ↔ constraint_1342 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1343 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 429 row) * ((a_prime_bit c 429 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1343_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1343 c row ↔ constraint_1343 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1344 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 430 row) * ((a_prime_bit c 430 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1344_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1344 c row ↔ constraint_1344 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1345 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 431 row) * ((a_prime_bit c 431 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1345_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1345 c row ↔ constraint_1345 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1346 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 432 row) * ((a_prime_bit c 432 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1346_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1346 c row ↔ constraint_1346 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1347 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 433 row) * ((a_prime_bit c 433 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1347_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1347 c row ↔ constraint_1347 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1348 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 434 row) * ((a_prime_bit c 434 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1348_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1348 c row ↔ constraint_1348 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1349 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 435 row) * ((a_prime_bit c 435 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1349_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1349 c row ↔ constraint_1349 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1350 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 436 row) * ((a_prime_bit c 436 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1350_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1350 c row ↔ constraint_1350 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1351 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 437 row) * ((a_prime_bit c 437 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1351_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1351 c row ↔ constraint_1351 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1352 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 438 row) * ((a_prime_bit c 438 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1352_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1352 c row ↔ constraint_1352 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1353 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 439 row) * ((a_prime_bit c 439 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1353_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1353 c row ↔ constraint_1353 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1354 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 440 row) * ((a_prime_bit c 440 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1354_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1354 c row ↔ constraint_1354 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1355 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 441 row) * ((a_prime_bit c 441 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1355_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1355 c row ↔ constraint_1355 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1356 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 442 row) * ((a_prime_bit c 442 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1356_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1356 c row ↔ constraint_1356 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1357 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 443 row) * ((a_prime_bit c 443 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1357_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1357 c row ↔ constraint_1357 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1358 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 444 row) * ((a_prime_bit c 444 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1358_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1358 c row ↔ constraint_1358 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1359 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 445 row) * ((a_prime_bit c 445 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1359_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1359 c row ↔ constraint_1359 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1360 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 446 row) * ((a_prime_bit c 446 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1360_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1360 c row ↔ constraint_1360 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1361 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 447 row) * ((a_prime_bit c 447 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1361_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1361 c row ↔ constraint_1361 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1362 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 1249 149 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1362_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1362 c row ↔ constraint_1362 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1363 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 1265 150 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1363_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1363 c row ↔ constraint_1363 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1364 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 1281 151 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1364_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1364 c row ↔ constraint_1364 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1365 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 1297 152 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1365_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1365 c row ↔ constraint_1365 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1366 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 448 row) * ((a_prime_bit c 448 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1366_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1366 c row ↔ constraint_1366 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1367 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 449 row) * ((a_prime_bit c 449 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1367_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1367 c row ↔ constraint_1367 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1368 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 450 row) * ((a_prime_bit c 450 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1368_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1368 c row ↔ constraint_1368 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1369 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 451 row) * ((a_prime_bit c 451 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1369_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1369 c row ↔ constraint_1369 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1370 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 452 row) * ((a_prime_bit c 452 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1370_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1370 c row ↔ constraint_1370 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1371 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 453 row) * ((a_prime_bit c 453 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1371_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1371 c row ↔ constraint_1371 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1372 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 454 row) * ((a_prime_bit c 454 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1372_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1372 c row ↔ constraint_1372 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1373 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 455 row) * ((a_prime_bit c 455 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1373_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1373 c row ↔ constraint_1373 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1374 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 456 row) * ((a_prime_bit c 456 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1374_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1374 c row ↔ constraint_1374 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1375 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 457 row) * ((a_prime_bit c 457 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1375_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1375 c row ↔ constraint_1375 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1376 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 458 row) * ((a_prime_bit c 458 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1376_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1376 c row ↔ constraint_1376 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1377 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 459 row) * ((a_prime_bit c 459 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1377_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1377 c row ↔ constraint_1377 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1378 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 460 row) * ((a_prime_bit c 460 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1378_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1378 c row ↔ constraint_1378 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1379 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 461 row) * ((a_prime_bit c 461 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1379_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1379 c row ↔ constraint_1379 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1380 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 462 row) * ((a_prime_bit c 462 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1380_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1380 c row ↔ constraint_1380 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1381 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 463 row) * ((a_prime_bit c 463 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1381_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1381 c row ↔ constraint_1381 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1382 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 464 row) * ((a_prime_bit c 464 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1382_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1382 c row ↔ constraint_1382 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1383 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 465 row) * ((a_prime_bit c 465 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1383_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1383 c row ↔ constraint_1383 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1384 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 466 row) * ((a_prime_bit c 466 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1384_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1384 c row ↔ constraint_1384 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1385 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 467 row) * ((a_prime_bit c 467 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1385_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1385 c row ↔ constraint_1385 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1386 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 468 row) * ((a_prime_bit c 468 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1386_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1386 c row ↔ constraint_1386 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1387 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 469 row) * ((a_prime_bit c 469 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1387_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1387 c row ↔ constraint_1387 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1388 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 470 row) * ((a_prime_bit c 470 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1388_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1388 c row ↔ constraint_1388 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1389 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 471 row) * ((a_prime_bit c 471 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1389_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1389 c row ↔ constraint_1389 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1390 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 472 row) * ((a_prime_bit c 472 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1390_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1390 c row ↔ constraint_1390 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1391 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 473 row) * ((a_prime_bit c 473 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1391_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1391 c row ↔ constraint_1391 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1392 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 474 row) * ((a_prime_bit c 474 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1392_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1392 c row ↔ constraint_1392 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1393 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 475 row) * ((a_prime_bit c 475 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1393_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1393 c row ↔ constraint_1393 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1394 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 476 row) * ((a_prime_bit c 476 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1394_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1394 c row ↔ constraint_1394 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1395 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 477 row) * ((a_prime_bit c 477 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1395_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1395 c row ↔ constraint_1395 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1396 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 478 row) * ((a_prime_bit c 478 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1396_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1396 c row ↔ constraint_1396 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1397 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 479 row) * ((a_prime_bit c 479 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1397_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1397 c row ↔ constraint_1397 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1398 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 480 row) * ((a_prime_bit c 480 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1398_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1398 c row ↔ constraint_1398 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1399 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 481 row) * ((a_prime_bit c 481 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1399_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1399 c row ↔ constraint_1399 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1400 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 482 row) * ((a_prime_bit c 482 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1400_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1400 c row ↔ constraint_1400 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1401 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 483 row) * ((a_prime_bit c 483 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1401_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1401 c row ↔ constraint_1401 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1402 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 484 row) * ((a_prime_bit c 484 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1402_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1402 c row ↔ constraint_1402 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1403 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 485 row) * ((a_prime_bit c 485 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1403_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1403 c row ↔ constraint_1403 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1404 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 486 row) * ((a_prime_bit c 486 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1404_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1404 c row ↔ constraint_1404 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1405 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 487 row) * ((a_prime_bit c 487 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1405_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1405 c row ↔ constraint_1405 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1406 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 488 row) * ((a_prime_bit c 488 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1406_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1406 c row ↔ constraint_1406 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1407 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 489 row) * ((a_prime_bit c 489 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1407_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1407 c row ↔ constraint_1407 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1408 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 490 row) * ((a_prime_bit c 490 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1408_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1408 c row ↔ constraint_1408 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1409 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 491 row) * ((a_prime_bit c 491 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1409_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1409 c row ↔ constraint_1409 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1410 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 492 row) * ((a_prime_bit c 492 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1410_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1410 c row ↔ constraint_1410 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1411 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 493 row) * ((a_prime_bit c 493 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1411_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1411 c row ↔ constraint_1411 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1412 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 494 row) * ((a_prime_bit c 494 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1412_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1412 c row ↔ constraint_1412 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1413 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 495 row) * ((a_prime_bit c 495 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1413_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1413 c row ↔ constraint_1413 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1414 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 496 row) * ((a_prime_bit c 496 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1414_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1414 c row ↔ constraint_1414 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1415 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 497 row) * ((a_prime_bit c 497 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1415_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1415 c row ↔ constraint_1415 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1416 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 498 row) * ((a_prime_bit c 498 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1416_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1416 c row ↔ constraint_1416 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1417 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 499 row) * ((a_prime_bit c 499 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1417_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1417 c row ↔ constraint_1417 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1418 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 500 row) * ((a_prime_bit c 500 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1418_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1418 c row ↔ constraint_1418 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1419 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 501 row) * ((a_prime_bit c 501 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1419_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1419 c row ↔ constraint_1419 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1420 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 502 row) * ((a_prime_bit c 502 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1420_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1420 c row ↔ constraint_1420 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1421 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 503 row) * ((a_prime_bit c 503 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1421_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1421 c row ↔ constraint_1421 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1422 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 504 row) * ((a_prime_bit c 504 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1422_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1422 c row ↔ constraint_1422 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1423 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 505 row) * ((a_prime_bit c 505 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1423_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1423 c row ↔ constraint_1423 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1424 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 506 row) * ((a_prime_bit c 506 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1424_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1424 c row ↔ constraint_1424 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1425 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 507 row) * ((a_prime_bit c 507 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1425_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1425 c row ↔ constraint_1425 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1426 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 508 row) * ((a_prime_bit c 508 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1426_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1426 c row ↔ constraint_1426 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1427 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 509 row) * ((a_prime_bit c 509 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1427_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1427 c row ↔ constraint_1427 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1428 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 510 row) * ((a_prime_bit c 510 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1428_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1428 c row ↔ constraint_1428 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1429 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 511 row) * ((a_prime_bit c 511 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1429_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1429 c row ↔ constraint_1429 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1430 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 1313 153 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1430_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1430 c row ↔ constraint_1430 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1431 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1329 154 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1431_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1431 c row ↔ constraint_1431 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1432 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1345 155 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1432_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1432 c row ↔ constraint_1432 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1433 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 1361 156 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1433_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1433 c row ↔ constraint_1433 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1434 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 512 row) * ((a_prime_bit c 512 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1434_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1434 c row ↔ constraint_1434 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1435 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 513 row) * ((a_prime_bit c 513 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1435_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1435 c row ↔ constraint_1435 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1436 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 514 row) * ((a_prime_bit c 514 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1436_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1436 c row ↔ constraint_1436 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1437 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 515 row) * ((a_prime_bit c 515 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1437_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1437 c row ↔ constraint_1437 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1438 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 516 row) * ((a_prime_bit c 516 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1438_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1438 c row ↔ constraint_1438 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1439 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 517 row) * ((a_prime_bit c 517 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1439_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1439 c row ↔ constraint_1439 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1440 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 518 row) * ((a_prime_bit c 518 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1440_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1440 c row ↔ constraint_1440 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1441 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 519 row) * ((a_prime_bit c 519 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1441_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1441 c row ↔ constraint_1441 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1442 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 520 row) * ((a_prime_bit c 520 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1442_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1442 c row ↔ constraint_1442 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1443 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 521 row) * ((a_prime_bit c 521 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1443_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1443 c row ↔ constraint_1443 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1444 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 522 row) * ((a_prime_bit c 522 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1444_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1444 c row ↔ constraint_1444 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1445 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 523 row) * ((a_prime_bit c 523 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1445_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1445 c row ↔ constraint_1445 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1446 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 524 row) * ((a_prime_bit c 524 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1446_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1446 c row ↔ constraint_1446 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1447 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 525 row) * ((a_prime_bit c 525 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1447_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1447 c row ↔ constraint_1447 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1448 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 526 row) * ((a_prime_bit c 526 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1448_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1448 c row ↔ constraint_1448 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1449 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 527 row) * ((a_prime_bit c 527 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1449_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1449 c row ↔ constraint_1449 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1450 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 528 row) * ((a_prime_bit c 528 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1450_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1450 c row ↔ constraint_1450 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1451 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 529 row) * ((a_prime_bit c 529 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1451_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1451 c row ↔ constraint_1451 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1452 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 530 row) * ((a_prime_bit c 530 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1452_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1452 c row ↔ constraint_1452 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1453 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 531 row) * ((a_prime_bit c 531 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1453_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1453 c row ↔ constraint_1453 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1454 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 532 row) * ((a_prime_bit c 532 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1454_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1454 c row ↔ constraint_1454 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1455 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 533 row) * ((a_prime_bit c 533 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1455_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1455 c row ↔ constraint_1455 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1456 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 534 row) * ((a_prime_bit c 534 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1456_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1456 c row ↔ constraint_1456 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1457 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 535 row) * ((a_prime_bit c 535 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1457_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1457 c row ↔ constraint_1457 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1458 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 536 row) * ((a_prime_bit c 536 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1458_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1458 c row ↔ constraint_1458 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1459 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 537 row) * ((a_prime_bit c 537 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1459_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1459 c row ↔ constraint_1459 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1460 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 538 row) * ((a_prime_bit c 538 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1460_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1460 c row ↔ constraint_1460 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1461 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 539 row) * ((a_prime_bit c 539 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1461_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1461 c row ↔ constraint_1461 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1462 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 540 row) * ((a_prime_bit c 540 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1462_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1462 c row ↔ constraint_1462 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1463 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 541 row) * ((a_prime_bit c 541 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1463_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1463 c row ↔ constraint_1463 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1464 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 542 row) * ((a_prime_bit c 542 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1464_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1464 c row ↔ constraint_1464 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1465 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 543 row) * ((a_prime_bit c 543 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1465_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1465 c row ↔ constraint_1465 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1466 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 544 row) * ((a_prime_bit c 544 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1466_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1466 c row ↔ constraint_1466 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1467 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 545 row) * ((a_prime_bit c 545 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1467_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1467 c row ↔ constraint_1467 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1468 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 546 row) * ((a_prime_bit c 546 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1468_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1468 c row ↔ constraint_1468 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1469 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 547 row) * ((a_prime_bit c 547 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1469_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1469 c row ↔ constraint_1469 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1470 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 548 row) * ((a_prime_bit c 548 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1470_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1470 c row ↔ constraint_1470 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1471 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 549 row) * ((a_prime_bit c 549 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1471_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1471 c row ↔ constraint_1471 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1472 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 550 row) * ((a_prime_bit c 550 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1472_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1472 c row ↔ constraint_1472 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1473 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 551 row) * ((a_prime_bit c 551 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1473_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1473 c row ↔ constraint_1473 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1474 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 552 row) * ((a_prime_bit c 552 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1474_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1474 c row ↔ constraint_1474 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1475 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 553 row) * ((a_prime_bit c 553 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1475_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1475 c row ↔ constraint_1475 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1476 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 554 row) * ((a_prime_bit c 554 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1476_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1476 c row ↔ constraint_1476 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1477 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 555 row) * ((a_prime_bit c 555 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1477_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1477 c row ↔ constraint_1477 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1478 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 556 row) * ((a_prime_bit c 556 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1478_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1478 c row ↔ constraint_1478 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1479 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 557 row) * ((a_prime_bit c 557 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1479_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1479 c row ↔ constraint_1479 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1480 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 558 row) * ((a_prime_bit c 558 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1480_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1480 c row ↔ constraint_1480 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1481 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 559 row) * ((a_prime_bit c 559 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1481_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1481 c row ↔ constraint_1481 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1482 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 560 row) * ((a_prime_bit c 560 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1482_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1482 c row ↔ constraint_1482 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1483 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 561 row) * ((a_prime_bit c 561 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1483_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1483 c row ↔ constraint_1483 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1484 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 562 row) * ((a_prime_bit c 562 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1484_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1484 c row ↔ constraint_1484 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1485 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 563 row) * ((a_prime_bit c 563 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1485_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1485 c row ↔ constraint_1485 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1486 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 564 row) * ((a_prime_bit c 564 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1486_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1486 c row ↔ constraint_1486 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1487 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 565 row) * ((a_prime_bit c 565 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1487_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1487 c row ↔ constraint_1487 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1488 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 566 row) * ((a_prime_bit c 566 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1488_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1488 c row ↔ constraint_1488 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1489 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 567 row) * ((a_prime_bit c 567 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1489_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1489 c row ↔ constraint_1489 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1490 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 568 row) * ((a_prime_bit c 568 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1490_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1490 c row ↔ constraint_1490 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1491 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 569 row) * ((a_prime_bit c 569 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1491_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1491 c row ↔ constraint_1491 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1492 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 570 row) * ((a_prime_bit c 570 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1492_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1492 c row ↔ constraint_1492 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1493 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 571 row) * ((a_prime_bit c 571 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1493_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1493 c row ↔ constraint_1493 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1494 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 572 row) * ((a_prime_bit c 572 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1494_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1494 c row ↔ constraint_1494 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1495 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 573 row) * ((a_prime_bit c 573 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1495_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1495 c row ↔ constraint_1495 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1496 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 574 row) * ((a_prime_bit c 574 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1496_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1496 c row ↔ constraint_1496 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1497 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 575 row) * ((a_prime_bit c 575 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1497_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1497 c row ↔ constraint_1497 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1498 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 1377 157 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1498_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1498 c row ↔ constraint_1498 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1499 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 1393 158 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1499_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1499 c row ↔ constraint_1499 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1500 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 1409 159 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1500_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1500 c row ↔ constraint_1500 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1501 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 1425 160 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1501_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1501 c row ↔ constraint_1501 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1502 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 576 row) * ((a_prime_bit c 576 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1502_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1502 c row ↔ constraint_1502 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1503 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 577 row) * ((a_prime_bit c 577 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1503_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1503 c row ↔ constraint_1503 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1504 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 578 row) * ((a_prime_bit c 578 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1504_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1504 c row ↔ constraint_1504 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1505 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 579 row) * ((a_prime_bit c 579 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1505_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1505 c row ↔ constraint_1505 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1506 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 580 row) * ((a_prime_bit c 580 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1506_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1506 c row ↔ constraint_1506 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1507 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 581 row) * ((a_prime_bit c 581 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1507_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1507 c row ↔ constraint_1507 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1508 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 582 row) * ((a_prime_bit c 582 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1508_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1508 c row ↔ constraint_1508 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1509 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 583 row) * ((a_prime_bit c 583 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1509_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1509 c row ↔ constraint_1509 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1510 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 584 row) * ((a_prime_bit c 584 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1510_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1510 c row ↔ constraint_1510 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1511 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 585 row) * ((a_prime_bit c 585 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1511_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1511 c row ↔ constraint_1511 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1512 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 586 row) * ((a_prime_bit c 586 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1512_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1512 c row ↔ constraint_1512 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1513 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 587 row) * ((a_prime_bit c 587 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1513_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1513 c row ↔ constraint_1513 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1514 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 588 row) * ((a_prime_bit c 588 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1514_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1514 c row ↔ constraint_1514 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1515 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 589 row) * ((a_prime_bit c 589 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1515_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1515 c row ↔ constraint_1515 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1516 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 590 row) * ((a_prime_bit c 590 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1516_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1516 c row ↔ constraint_1516 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1517 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 591 row) * ((a_prime_bit c 591 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1517_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1517 c row ↔ constraint_1517 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1518 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 592 row) * ((a_prime_bit c 592 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1518_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1518 c row ↔ constraint_1518 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1519 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 593 row) * ((a_prime_bit c 593 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1519_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1519 c row ↔ constraint_1519 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1520 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 594 row) * ((a_prime_bit c 594 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1520_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1520 c row ↔ constraint_1520 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1521 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 595 row) * ((a_prime_bit c 595 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1521_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1521 c row ↔ constraint_1521 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1522 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 596 row) * ((a_prime_bit c 596 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1522_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1522 c row ↔ constraint_1522 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1523 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 597 row) * ((a_prime_bit c 597 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1523_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1523 c row ↔ constraint_1523 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1524 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 598 row) * ((a_prime_bit c 598 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1524_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1524 c row ↔ constraint_1524 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1525 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 599 row) * ((a_prime_bit c 599 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1525_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1525 c row ↔ constraint_1525 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1526 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 600 row) * ((a_prime_bit c 600 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1526_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1526 c row ↔ constraint_1526 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1527 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 601 row) * ((a_prime_bit c 601 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1527_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1527 c row ↔ constraint_1527 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1528 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 602 row) * ((a_prime_bit c 602 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1528_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1528 c row ↔ constraint_1528 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1529 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 603 row) * ((a_prime_bit c 603 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1529_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1529 c row ↔ constraint_1529 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1530 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 604 row) * ((a_prime_bit c 604 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1530_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1530 c row ↔ constraint_1530 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1531 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 605 row) * ((a_prime_bit c 605 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1531_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1531 c row ↔ constraint_1531 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1532 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 606 row) * ((a_prime_bit c 606 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1532_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1532 c row ↔ constraint_1532 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1533 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 607 row) * ((a_prime_bit c 607 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1533_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1533 c row ↔ constraint_1533 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1534 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 608 row) * ((a_prime_bit c 608 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1534_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1534 c row ↔ constraint_1534 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1535 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 609 row) * ((a_prime_bit c 609 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1535_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1535 c row ↔ constraint_1535 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1536 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 610 row) * ((a_prime_bit c 610 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1536_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1536 c row ↔ constraint_1536 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1537 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 611 row) * ((a_prime_bit c 611 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1537_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1537 c row ↔ constraint_1537 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1538 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 612 row) * ((a_prime_bit c 612 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1538_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1538 c row ↔ constraint_1538 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1539 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 613 row) * ((a_prime_bit c 613 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1539_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1539 c row ↔ constraint_1539 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1540 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 614 row) * ((a_prime_bit c 614 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1540_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1540 c row ↔ constraint_1540 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1541 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 615 row) * ((a_prime_bit c 615 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1541_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1541 c row ↔ constraint_1541 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1542 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 616 row) * ((a_prime_bit c 616 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1542_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1542 c row ↔ constraint_1542 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1543 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 617 row) * ((a_prime_bit c 617 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1543_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1543 c row ↔ constraint_1543 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1544 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 618 row) * ((a_prime_bit c 618 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1544_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1544 c row ↔ constraint_1544 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1545 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 619 row) * ((a_prime_bit c 619 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1545_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1545 c row ↔ constraint_1545 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1546 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 620 row) * ((a_prime_bit c 620 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1546_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1546 c row ↔ constraint_1546 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1547 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 621 row) * ((a_prime_bit c 621 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1547_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1547 c row ↔ constraint_1547 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1548 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 622 row) * ((a_prime_bit c 622 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1548_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1548 c row ↔ constraint_1548 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1549 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 623 row) * ((a_prime_bit c 623 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1549_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1549 c row ↔ constraint_1549 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1550 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 624 row) * ((a_prime_bit c 624 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1550_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1550 c row ↔ constraint_1550 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1551 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 625 row) * ((a_prime_bit c 625 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1551_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1551 c row ↔ constraint_1551 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1552 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 626 row) * ((a_prime_bit c 626 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1552_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1552 c row ↔ constraint_1552 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1553 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 627 row) * ((a_prime_bit c 627 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1553_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1553 c row ↔ constraint_1553 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1554 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 628 row) * ((a_prime_bit c 628 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1554_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1554 c row ↔ constraint_1554 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1555 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 629 row) * ((a_prime_bit c 629 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1555_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1555 c row ↔ constraint_1555 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1556 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 630 row) * ((a_prime_bit c 630 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1556_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1556 c row ↔ constraint_1556 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1557 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 631 row) * ((a_prime_bit c 631 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1557_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1557 c row ↔ constraint_1557 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1558 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 632 row) * ((a_prime_bit c 632 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1558_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1558 c row ↔ constraint_1558 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1559 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 633 row) * ((a_prime_bit c 633 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1559_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1559 c row ↔ constraint_1559 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1560 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 634 row) * ((a_prime_bit c 634 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1560_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1560 c row ↔ constraint_1560 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1561 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 635 row) * ((a_prime_bit c 635 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1561_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1561 c row ↔ constraint_1561 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1562 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 636 row) * ((a_prime_bit c 636 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1562_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1562 c row ↔ constraint_1562 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1563 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 637 row) * ((a_prime_bit c 637 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1563_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1563 c row ↔ constraint_1563 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1564 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 638 row) * ((a_prime_bit c 638 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1564_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1564 c row ↔ constraint_1564 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1565 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 639 row) * ((a_prime_bit c 639 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1565_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1565 c row ↔ constraint_1565 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1566 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 1441 161 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1566_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1566 c row ↔ constraint_1566 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1567 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 1457 162 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1567_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1567 c row ↔ constraint_1567 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1568 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 1473 163 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1568_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1568 c row ↔ constraint_1568 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1569 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 1489 164 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1569_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1569 c row ↔ constraint_1569 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1570 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 640 row) * ((a_prime_bit c 640 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1570_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1570 c row ↔ constraint_1570 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1571 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 641 row) * ((a_prime_bit c 641 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1571_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1571 c row ↔ constraint_1571 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1572 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 642 row) * ((a_prime_bit c 642 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1572_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1572 c row ↔ constraint_1572 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1573 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 643 row) * ((a_prime_bit c 643 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1573_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1573 c row ↔ constraint_1573 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1574 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 644 row) * ((a_prime_bit c 644 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1574_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1574 c row ↔ constraint_1574 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1575 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 645 row) * ((a_prime_bit c 645 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1575_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1575 c row ↔ constraint_1575 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1576 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 646 row) * ((a_prime_bit c 646 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1576_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1576 c row ↔ constraint_1576 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1577 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 647 row) * ((a_prime_bit c 647 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1577_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1577 c row ↔ constraint_1577 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1578 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 648 row) * ((a_prime_bit c 648 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1578_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1578 c row ↔ constraint_1578 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1579 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 649 row) * ((a_prime_bit c 649 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1579_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1579 c row ↔ constraint_1579 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1580 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 650 row) * ((a_prime_bit c 650 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1580_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1580 c row ↔ constraint_1580 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1581 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 651 row) * ((a_prime_bit c 651 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1581_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1581 c row ↔ constraint_1581 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1582 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 652 row) * ((a_prime_bit c 652 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1582_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1582 c row ↔ constraint_1582 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1583 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 653 row) * ((a_prime_bit c 653 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1583_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1583 c row ↔ constraint_1583 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1584 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 654 row) * ((a_prime_bit c 654 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1584_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1584 c row ↔ constraint_1584 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1585 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 655 row) * ((a_prime_bit c 655 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1585_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1585 c row ↔ constraint_1585 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1586 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 656 row) * ((a_prime_bit c 656 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1586_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1586 c row ↔ constraint_1586 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1587 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 657 row) * ((a_prime_bit c 657 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1587_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1587 c row ↔ constraint_1587 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1588 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 658 row) * ((a_prime_bit c 658 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1588_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1588 c row ↔ constraint_1588 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1589 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 659 row) * ((a_prime_bit c 659 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1589_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1589 c row ↔ constraint_1589 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1590 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 660 row) * ((a_prime_bit c 660 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1590_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1590 c row ↔ constraint_1590 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1591 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 661 row) * ((a_prime_bit c 661 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1591_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1591 c row ↔ constraint_1591 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1592 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 662 row) * ((a_prime_bit c 662 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1592_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1592 c row ↔ constraint_1592 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1593 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 663 row) * ((a_prime_bit c 663 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1593_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1593 c row ↔ constraint_1593 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1594 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 664 row) * ((a_prime_bit c 664 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1594_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1594 c row ↔ constraint_1594 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1595 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 665 row) * ((a_prime_bit c 665 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1595_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1595 c row ↔ constraint_1595 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1596 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 666 row) * ((a_prime_bit c 666 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1596_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1596 c row ↔ constraint_1596 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1597 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 667 row) * ((a_prime_bit c 667 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1597_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1597 c row ↔ constraint_1597 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1598 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 668 row) * ((a_prime_bit c 668 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1598_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1598 c row ↔ constraint_1598 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1599 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 669 row) * ((a_prime_bit c 669 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1599_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1599 c row ↔ constraint_1599 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1600 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 670 row) * ((a_prime_bit c 670 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1600_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1600 c row ↔ constraint_1600 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1601 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 671 row) * ((a_prime_bit c 671 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1601_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1601 c row ↔ constraint_1601 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1602 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 672 row) * ((a_prime_bit c 672 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1602_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1602 c row ↔ constraint_1602 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1603 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 673 row) * ((a_prime_bit c 673 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1603_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1603 c row ↔ constraint_1603 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1604 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 674 row) * ((a_prime_bit c 674 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1604_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1604 c row ↔ constraint_1604 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1605 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 675 row) * ((a_prime_bit c 675 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1605_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1605 c row ↔ constraint_1605 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1606 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 676 row) * ((a_prime_bit c 676 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1606_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1606 c row ↔ constraint_1606 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1607 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 677 row) * ((a_prime_bit c 677 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1607_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1607 c row ↔ constraint_1607 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1608 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 678 row) * ((a_prime_bit c 678 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1608_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1608 c row ↔ constraint_1608 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1609 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 679 row) * ((a_prime_bit c 679 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1609_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1609 c row ↔ constraint_1609 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1610 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 680 row) * ((a_prime_bit c 680 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1610_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1610 c row ↔ constraint_1610 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1611 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 681 row) * ((a_prime_bit c 681 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1611_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1611 c row ↔ constraint_1611 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1612 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 682 row) * ((a_prime_bit c 682 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1612_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1612 c row ↔ constraint_1612 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1613 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 683 row) * ((a_prime_bit c 683 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1613_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1613 c row ↔ constraint_1613 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1614 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 684 row) * ((a_prime_bit c 684 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1614_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1614 c row ↔ constraint_1614 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1615 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 685 row) * ((a_prime_bit c 685 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1615_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1615 c row ↔ constraint_1615 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1616 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 686 row) * ((a_prime_bit c 686 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1616_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1616 c row ↔ constraint_1616 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1617 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 687 row) * ((a_prime_bit c 687 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1617_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1617 c row ↔ constraint_1617 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1618 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 688 row) * ((a_prime_bit c 688 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1618_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1618 c row ↔ constraint_1618 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1619 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 689 row) * ((a_prime_bit c 689 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1619_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1619 c row ↔ constraint_1619 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1620 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 690 row) * ((a_prime_bit c 690 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1620_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1620 c row ↔ constraint_1620 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1621 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 691 row) * ((a_prime_bit c 691 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1621_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1621 c row ↔ constraint_1621 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1622 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 692 row) * ((a_prime_bit c 692 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1622_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1622 c row ↔ constraint_1622 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1623 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 693 row) * ((a_prime_bit c 693 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1623_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1623 c row ↔ constraint_1623 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1624 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 694 row) * ((a_prime_bit c 694 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1624_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1624 c row ↔ constraint_1624 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1625 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 695 row) * ((a_prime_bit c 695 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1625_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1625 c row ↔ constraint_1625 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1626 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 696 row) * ((a_prime_bit c 696 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1626_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1626 c row ↔ constraint_1626 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1627 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 697 row) * ((a_prime_bit c 697 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1627_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1627 c row ↔ constraint_1627 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1628 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 698 row) * ((a_prime_bit c 698 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1628_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1628 c row ↔ constraint_1628 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1629 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 699 row) * ((a_prime_bit c 699 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1629_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1629 c row ↔ constraint_1629 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1630 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 700 row) * ((a_prime_bit c 700 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1630_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1630 c row ↔ constraint_1630 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1631 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 701 row) * ((a_prime_bit c 701 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1631_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1631 c row ↔ constraint_1631 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1632 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 702 row) * ((a_prime_bit c 702 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1632_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1632 c row ↔ constraint_1632 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1633 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 703 row) * ((a_prime_bit c 703 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1633_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1633 c row ↔ constraint_1633 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1634 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 1505 165 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1634_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1634 c row ↔ constraint_1634 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1635 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 1521 166 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1635_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1635 c row ↔ constraint_1635 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1636 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 1537 167 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1636_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1636 c row ↔ constraint_1636 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1637 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 1553 168 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1637_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1637 c row ↔ constraint_1637 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1638 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 704 row) * ((a_prime_bit c 704 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1638_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1638 c row ↔ constraint_1638 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1639 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 705 row) * ((a_prime_bit c 705 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1639_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1639 c row ↔ constraint_1639 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1640 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 706 row) * ((a_prime_bit c 706 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1640_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1640 c row ↔ constraint_1640 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1641 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 707 row) * ((a_prime_bit c 707 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1641_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1641 c row ↔ constraint_1641 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1642 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 708 row) * ((a_prime_bit c 708 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1642_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1642 c row ↔ constraint_1642 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1643 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 709 row) * ((a_prime_bit c 709 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1643_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1643 c row ↔ constraint_1643 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1644 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 710 row) * ((a_prime_bit c 710 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1644_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1644 c row ↔ constraint_1644 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1645 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 711 row) * ((a_prime_bit c 711 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1645_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1645 c row ↔ constraint_1645 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1646 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 712 row) * ((a_prime_bit c 712 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1646_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1646 c row ↔ constraint_1646 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1647 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 713 row) * ((a_prime_bit c 713 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1647_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1647 c row ↔ constraint_1647 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1648 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 714 row) * ((a_prime_bit c 714 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1648_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1648 c row ↔ constraint_1648 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1649 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 715 row) * ((a_prime_bit c 715 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1649_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1649 c row ↔ constraint_1649 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1650 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 716 row) * ((a_prime_bit c 716 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1650_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1650 c row ↔ constraint_1650 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1651 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 717 row) * ((a_prime_bit c 717 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1651_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1651 c row ↔ constraint_1651 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1652 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 718 row) * ((a_prime_bit c 718 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1652_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1652 c row ↔ constraint_1652 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1653 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 719 row) * ((a_prime_bit c 719 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1653_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1653 c row ↔ constraint_1653 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1654 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 720 row) * ((a_prime_bit c 720 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1654_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1654 c row ↔ constraint_1654 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1655 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 721 row) * ((a_prime_bit c 721 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1655_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1655 c row ↔ constraint_1655 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1656 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 722 row) * ((a_prime_bit c 722 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1656_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1656 c row ↔ constraint_1656 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1657 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 723 row) * ((a_prime_bit c 723 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1657_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1657 c row ↔ constraint_1657 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1658 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 724 row) * ((a_prime_bit c 724 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1658_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1658 c row ↔ constraint_1658 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1659 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 725 row) * ((a_prime_bit c 725 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1659_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1659 c row ↔ constraint_1659 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1660 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 726 row) * ((a_prime_bit c 726 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1660_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1660 c row ↔ constraint_1660 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1661 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 727 row) * ((a_prime_bit c 727 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1661_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1661 c row ↔ constraint_1661 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1662 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 728 row) * ((a_prime_bit c 728 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1662_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1662 c row ↔ constraint_1662 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1663 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 729 row) * ((a_prime_bit c 729 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1663_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1663 c row ↔ constraint_1663 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1664 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 730 row) * ((a_prime_bit c 730 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1664_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1664 c row ↔ constraint_1664 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1665 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 731 row) * ((a_prime_bit c 731 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1665_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1665 c row ↔ constraint_1665 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1666 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 732 row) * ((a_prime_bit c 732 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1666_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1666 c row ↔ constraint_1666 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1667 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 733 row) * ((a_prime_bit c 733 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1667_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1667 c row ↔ constraint_1667 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1668 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 734 row) * ((a_prime_bit c 734 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1668_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1668 c row ↔ constraint_1668 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1669 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 735 row) * ((a_prime_bit c 735 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1669_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1669 c row ↔ constraint_1669 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1670 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 736 row) * ((a_prime_bit c 736 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1670_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1670 c row ↔ constraint_1670 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1671 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 737 row) * ((a_prime_bit c 737 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1671_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1671 c row ↔ constraint_1671 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1672 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 738 row) * ((a_prime_bit c 738 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1672_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1672 c row ↔ constraint_1672 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1673 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 739 row) * ((a_prime_bit c 739 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1673_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1673 c row ↔ constraint_1673 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1674 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 740 row) * ((a_prime_bit c 740 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1674_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1674 c row ↔ constraint_1674 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1675 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 741 row) * ((a_prime_bit c 741 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1675_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1675 c row ↔ constraint_1675 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1676 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 742 row) * ((a_prime_bit c 742 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1676_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1676 c row ↔ constraint_1676 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1677 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 743 row) * ((a_prime_bit c 743 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1677_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1677 c row ↔ constraint_1677 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1678 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 744 row) * ((a_prime_bit c 744 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1678_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1678 c row ↔ constraint_1678 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1679 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 745 row) * ((a_prime_bit c 745 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1679_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1679 c row ↔ constraint_1679 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1680 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 746 row) * ((a_prime_bit c 746 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1680_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1680 c row ↔ constraint_1680 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1681 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 747 row) * ((a_prime_bit c 747 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1681_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1681 c row ↔ constraint_1681 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1682 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 748 row) * ((a_prime_bit c 748 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1682_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1682 c row ↔ constraint_1682 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1683 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 749 row) * ((a_prime_bit c 749 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1683_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1683 c row ↔ constraint_1683 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1684 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 750 row) * ((a_prime_bit c 750 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1684_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1684 c row ↔ constraint_1684 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1685 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 751 row) * ((a_prime_bit c 751 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1685_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1685 c row ↔ constraint_1685 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1686 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 752 row) * ((a_prime_bit c 752 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1686_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1686 c row ↔ constraint_1686 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1687 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 753 row) * ((a_prime_bit c 753 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1687_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1687 c row ↔ constraint_1687 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1688 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 754 row) * ((a_prime_bit c 754 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1688_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1688 c row ↔ constraint_1688 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1689 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 755 row) * ((a_prime_bit c 755 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1689_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1689 c row ↔ constraint_1689 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1690 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 756 row) * ((a_prime_bit c 756 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1690_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1690 c row ↔ constraint_1690 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1691 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 757 row) * ((a_prime_bit c 757 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1691_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1691 c row ↔ constraint_1691 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1692 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 758 row) * ((a_prime_bit c 758 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1692_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1692 c row ↔ constraint_1692 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1693 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 759 row) * ((a_prime_bit c 759 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1693_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1693 c row ↔ constraint_1693 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1694 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 760 row) * ((a_prime_bit c 760 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1694_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1694 c row ↔ constraint_1694 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1695 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 761 row) * ((a_prime_bit c 761 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1695_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1695 c row ↔ constraint_1695 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1696 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 762 row) * ((a_prime_bit c 762 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1696_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1696 c row ↔ constraint_1696 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1697 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 763 row) * ((a_prime_bit c 763 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1697_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1697 c row ↔ constraint_1697 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1698 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 764 row) * ((a_prime_bit c 764 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1698_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1698 c row ↔ constraint_1698 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1699 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 765 row) * ((a_prime_bit c 765 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1699_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1699 c row ↔ constraint_1699 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1700 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 766 row) * ((a_prime_bit c 766 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1700_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1700 c row ↔ constraint_1700 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1701 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 767 row) * ((a_prime_bit c 767 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1701_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1701 c row ↔ constraint_1701 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1702 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 1569 169 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1702_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1702 c row ↔ constraint_1702 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1703 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 1585 170 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1703_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1703 c row ↔ constraint_1703 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1704 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 1601 171 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1704_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1704 c row ↔ constraint_1704 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1705 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 1617 172 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1705_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1705 c row ↔ constraint_1705 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1706 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 768 row) * ((a_prime_bit c 768 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1706_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1706 c row ↔ constraint_1706 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1707 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 769 row) * ((a_prime_bit c 769 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1707_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1707 c row ↔ constraint_1707 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1708 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 770 row) * ((a_prime_bit c 770 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1708_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1708 c row ↔ constraint_1708 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1709 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 771 row) * ((a_prime_bit c 771 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1709_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1709 c row ↔ constraint_1709 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1710 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 772 row) * ((a_prime_bit c 772 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1710_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1710 c row ↔ constraint_1710 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1711 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 773 row) * ((a_prime_bit c 773 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1711_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1711 c row ↔ constraint_1711 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1712 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 774 row) * ((a_prime_bit c 774 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1712_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1712 c row ↔ constraint_1712 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1713 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 775 row) * ((a_prime_bit c 775 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1713_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1713 c row ↔ constraint_1713 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1714 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 776 row) * ((a_prime_bit c 776 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1714_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1714 c row ↔ constraint_1714 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1715 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 777 row) * ((a_prime_bit c 777 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1715_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1715 c row ↔ constraint_1715 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1716 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 778 row) * ((a_prime_bit c 778 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1716_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1716 c row ↔ constraint_1716 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1717 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 779 row) * ((a_prime_bit c 779 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1717_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1717 c row ↔ constraint_1717 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1718 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 780 row) * ((a_prime_bit c 780 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1718_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1718 c row ↔ constraint_1718 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1719 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 781 row) * ((a_prime_bit c 781 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1719_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1719 c row ↔ constraint_1719 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1720 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 782 row) * ((a_prime_bit c 782 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1720_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1720 c row ↔ constraint_1720 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1721 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 783 row) * ((a_prime_bit c 783 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1721_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1721 c row ↔ constraint_1721 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1722 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 784 row) * ((a_prime_bit c 784 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1722_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1722 c row ↔ constraint_1722 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1723 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 785 row) * ((a_prime_bit c 785 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1723_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1723 c row ↔ constraint_1723 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1724 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 786 row) * ((a_prime_bit c 786 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1724_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1724 c row ↔ constraint_1724 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1725 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 787 row) * ((a_prime_bit c 787 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1725_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1725 c row ↔ constraint_1725 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1726 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 788 row) * ((a_prime_bit c 788 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1726_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1726 c row ↔ constraint_1726 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1727 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 789 row) * ((a_prime_bit c 789 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1727_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1727 c row ↔ constraint_1727 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1728 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 790 row) * ((a_prime_bit c 790 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1728_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1728 c row ↔ constraint_1728 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1729 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 791 row) * ((a_prime_bit c 791 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1729_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1729 c row ↔ constraint_1729 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1730 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 792 row) * ((a_prime_bit c 792 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1730_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1730 c row ↔ constraint_1730 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1731 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 793 row) * ((a_prime_bit c 793 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1731_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1731 c row ↔ constraint_1731 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1732 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 794 row) * ((a_prime_bit c 794 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1732_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1732 c row ↔ constraint_1732 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1733 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 795 row) * ((a_prime_bit c 795 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1733_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1733 c row ↔ constraint_1733 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1734 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 796 row) * ((a_prime_bit c 796 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1734_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1734 c row ↔ constraint_1734 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1735 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 797 row) * ((a_prime_bit c 797 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1735_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1735 c row ↔ constraint_1735 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1736 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 798 row) * ((a_prime_bit c 798 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1736_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1736 c row ↔ constraint_1736 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1737 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 799 row) * ((a_prime_bit c 799 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1737_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1737 c row ↔ constraint_1737 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1738 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 800 row) * ((a_prime_bit c 800 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1738_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1738 c row ↔ constraint_1738 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1739 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 801 row) * ((a_prime_bit c 801 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1739_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1739 c row ↔ constraint_1739 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1740 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 802 row) * ((a_prime_bit c 802 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1740_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1740 c row ↔ constraint_1740 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1741 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 803 row) * ((a_prime_bit c 803 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1741_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1741 c row ↔ constraint_1741 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1742 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 804 row) * ((a_prime_bit c 804 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1742_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1742 c row ↔ constraint_1742 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1743 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 805 row) * ((a_prime_bit c 805 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1743_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1743 c row ↔ constraint_1743 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1744 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 806 row) * ((a_prime_bit c 806 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1744_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1744 c row ↔ constraint_1744 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1745 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 807 row) * ((a_prime_bit c 807 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1745_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1745 c row ↔ constraint_1745 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1746 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 808 row) * ((a_prime_bit c 808 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1746_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1746 c row ↔ constraint_1746 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1747 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 809 row) * ((a_prime_bit c 809 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1747_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1747 c row ↔ constraint_1747 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1748 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 810 row) * ((a_prime_bit c 810 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1748_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1748 c row ↔ constraint_1748 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1749 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 811 row) * ((a_prime_bit c 811 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1749_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1749 c row ↔ constraint_1749 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1750 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 812 row) * ((a_prime_bit c 812 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1750_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1750 c row ↔ constraint_1750 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1751 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 813 row) * ((a_prime_bit c 813 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1751_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1751 c row ↔ constraint_1751 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1752 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 814 row) * ((a_prime_bit c 814 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1752_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1752 c row ↔ constraint_1752 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1753 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 815 row) * ((a_prime_bit c 815 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1753_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1753 c row ↔ constraint_1753 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1754 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 816 row) * ((a_prime_bit c 816 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1754_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1754 c row ↔ constraint_1754 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1755 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 817 row) * ((a_prime_bit c 817 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1755_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1755 c row ↔ constraint_1755 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1756 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 818 row) * ((a_prime_bit c 818 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1756_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1756 c row ↔ constraint_1756 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1757 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 819 row) * ((a_prime_bit c 819 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1757_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1757 c row ↔ constraint_1757 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1758 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 820 row) * ((a_prime_bit c 820 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1758_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1758 c row ↔ constraint_1758 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1759 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 821 row) * ((a_prime_bit c 821 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1759_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1759 c row ↔ constraint_1759 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1760 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 822 row) * ((a_prime_bit c 822 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1760_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1760 c row ↔ constraint_1760 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1761 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 823 row) * ((a_prime_bit c 823 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1761_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1761 c row ↔ constraint_1761 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1762 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 824 row) * ((a_prime_bit c 824 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1762_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1762 c row ↔ constraint_1762 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1763 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 825 row) * ((a_prime_bit c 825 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1763_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1763 c row ↔ constraint_1763 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1764 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 826 row) * ((a_prime_bit c 826 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1764_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1764 c row ↔ constraint_1764 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1765 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 827 row) * ((a_prime_bit c 827 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1765_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1765 c row ↔ constraint_1765 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1766 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 828 row) * ((a_prime_bit c 828 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1766_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1766 c row ↔ constraint_1766 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1767 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 829 row) * ((a_prime_bit c 829 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1767_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1767 c row ↔ constraint_1767 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1768 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 830 row) * ((a_prime_bit c 830 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1768_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1768 c row ↔ constraint_1768 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1769 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 831 row) * ((a_prime_bit c 831 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1769_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1769 c row ↔ constraint_1769 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1770 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 1633 173 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1770_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1770 c row ↔ constraint_1770 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1771 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1649 174 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1771_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1771 c row ↔ constraint_1771 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1772 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1665 175 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1772_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1772 c row ↔ constraint_1772 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1773 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 1681 176 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1773_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1773 c row ↔ constraint_1773 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1774 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 832 row) * ((a_prime_bit c 832 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1774_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1774 c row ↔ constraint_1774 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1775 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 833 row) * ((a_prime_bit c 833 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1775_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1775 c row ↔ constraint_1775 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1776 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 834 row) * ((a_prime_bit c 834 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1776_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1776 c row ↔ constraint_1776 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1777 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 835 row) * ((a_prime_bit c 835 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1777_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1777 c row ↔ constraint_1777 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1778 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 836 row) * ((a_prime_bit c 836 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1778_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1778 c row ↔ constraint_1778 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1779 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 837 row) * ((a_prime_bit c 837 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1779_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1779 c row ↔ constraint_1779 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1780 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 838 row) * ((a_prime_bit c 838 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1780_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1780 c row ↔ constraint_1780 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1781 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 839 row) * ((a_prime_bit c 839 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1781_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1781 c row ↔ constraint_1781 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1782 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 840 row) * ((a_prime_bit c 840 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1782_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1782 c row ↔ constraint_1782 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1783 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 841 row) * ((a_prime_bit c 841 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1783_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1783 c row ↔ constraint_1783 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1784 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 842 row) * ((a_prime_bit c 842 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1784_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1784 c row ↔ constraint_1784 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1785 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 843 row) * ((a_prime_bit c 843 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1785_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1785 c row ↔ constraint_1785 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1786 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 844 row) * ((a_prime_bit c 844 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1786_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1786 c row ↔ constraint_1786 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1787 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 845 row) * ((a_prime_bit c 845 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1787_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1787 c row ↔ constraint_1787 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1788 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 846 row) * ((a_prime_bit c 846 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1788_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1788 c row ↔ constraint_1788 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1789 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 847 row) * ((a_prime_bit c 847 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1789_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1789 c row ↔ constraint_1789 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1790 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 848 row) * ((a_prime_bit c 848 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1790_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1790 c row ↔ constraint_1790 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1791 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 849 row) * ((a_prime_bit c 849 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1791_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1791 c row ↔ constraint_1791 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1792 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 850 row) * ((a_prime_bit c 850 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1792_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1792 c row ↔ constraint_1792 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1793 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 851 row) * ((a_prime_bit c 851 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1793_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1793 c row ↔ constraint_1793 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1794 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 852 row) * ((a_prime_bit c 852 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1794_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1794 c row ↔ constraint_1794 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1795 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 853 row) * ((a_prime_bit c 853 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1795_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1795 c row ↔ constraint_1795 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1796 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 854 row) * ((a_prime_bit c 854 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1796_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1796 c row ↔ constraint_1796 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1797 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 855 row) * ((a_prime_bit c 855 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1797_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1797 c row ↔ constraint_1797 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1798 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 856 row) * ((a_prime_bit c 856 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1798_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1798 c row ↔ constraint_1798 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1799 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 857 row) * ((a_prime_bit c 857 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1799_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1799 c row ↔ constraint_1799 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1800 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 858 row) * ((a_prime_bit c 858 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1800_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1800 c row ↔ constraint_1800 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1801 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 859 row) * ((a_prime_bit c 859 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1801_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1801 c row ↔ constraint_1801 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1802 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 860 row) * ((a_prime_bit c 860 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1802_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1802 c row ↔ constraint_1802 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1803 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 861 row) * ((a_prime_bit c 861 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1803_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1803 c row ↔ constraint_1803 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1804 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 862 row) * ((a_prime_bit c 862 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1804_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1804 c row ↔ constraint_1804 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1805 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 863 row) * ((a_prime_bit c 863 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1805_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1805 c row ↔ constraint_1805 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1806 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 864 row) * ((a_prime_bit c 864 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1806_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1806 c row ↔ constraint_1806 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1807 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 865 row) * ((a_prime_bit c 865 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1807_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1807 c row ↔ constraint_1807 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1808 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 866 row) * ((a_prime_bit c 866 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1808_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1808 c row ↔ constraint_1808 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1809 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 867 row) * ((a_prime_bit c 867 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1809_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1809 c row ↔ constraint_1809 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1810 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 868 row) * ((a_prime_bit c 868 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1810_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1810 c row ↔ constraint_1810 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1811 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 869 row) * ((a_prime_bit c 869 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1811_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1811 c row ↔ constraint_1811 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1812 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 870 row) * ((a_prime_bit c 870 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1812_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1812 c row ↔ constraint_1812 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1813 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 871 row) * ((a_prime_bit c 871 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1813_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1813 c row ↔ constraint_1813 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1814 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 872 row) * ((a_prime_bit c 872 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1814_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1814 c row ↔ constraint_1814 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1815 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 873 row) * ((a_prime_bit c 873 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1815_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1815 c row ↔ constraint_1815 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1816 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 874 row) * ((a_prime_bit c 874 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1816_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1816 c row ↔ constraint_1816 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1817 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 875 row) * ((a_prime_bit c 875 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1817_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1817 c row ↔ constraint_1817 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1818 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 876 row) * ((a_prime_bit c 876 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1818_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1818 c row ↔ constraint_1818 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1819 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 877 row) * ((a_prime_bit c 877 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1819_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1819 c row ↔ constraint_1819 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1820 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 878 row) * ((a_prime_bit c 878 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1820_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1820 c row ↔ constraint_1820 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1821 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 879 row) * ((a_prime_bit c 879 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1821_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1821 c row ↔ constraint_1821 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1822 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 880 row) * ((a_prime_bit c 880 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1822_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1822 c row ↔ constraint_1822 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1823 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 881 row) * ((a_prime_bit c 881 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1823_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1823 c row ↔ constraint_1823 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1824 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 882 row) * ((a_prime_bit c 882 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1824_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1824 c row ↔ constraint_1824 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1825 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 883 row) * ((a_prime_bit c 883 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1825_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1825 c row ↔ constraint_1825 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1826 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 884 row) * ((a_prime_bit c 884 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1826_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1826 c row ↔ constraint_1826 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1827 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 885 row) * ((a_prime_bit c 885 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1827_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1827 c row ↔ constraint_1827 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1828 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 886 row) * ((a_prime_bit c 886 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1828_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1828 c row ↔ constraint_1828 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1829 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 887 row) * ((a_prime_bit c 887 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1829_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1829 c row ↔ constraint_1829 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1830 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 888 row) * ((a_prime_bit c 888 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1830_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1830 c row ↔ constraint_1830 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1831 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 889 row) * ((a_prime_bit c 889 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1831_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1831 c row ↔ constraint_1831 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1832 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 890 row) * ((a_prime_bit c 890 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1832_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1832 c row ↔ constraint_1832 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1833 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 891 row) * ((a_prime_bit c 891 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1833_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1833 c row ↔ constraint_1833 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1834 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 892 row) * ((a_prime_bit c 892 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1834_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1834 c row ↔ constraint_1834 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1835 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 893 row) * ((a_prime_bit c 893 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1835_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1835 c row ↔ constraint_1835 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1836 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 894 row) * ((a_prime_bit c 894 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1836_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1836 c row ↔ constraint_1836 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1837 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 895 row) * ((a_prime_bit c 895 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1837_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1837 c row ↔ constraint_1837 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1838 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 1697 177 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1838_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1838 c row ↔ constraint_1838 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1839 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 1713 178 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1839_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1839 c row ↔ constraint_1839 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1840 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 1729 179 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1840_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1840 c row ↔ constraint_1840 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1841 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 1745 180 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1841_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1841 c row ↔ constraint_1841 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1842 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 896 row) * ((a_prime_bit c 896 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1842_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1842 c row ↔ constraint_1842 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1843 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 897 row) * ((a_prime_bit c 897 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1843_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1843 c row ↔ constraint_1843 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1844 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 898 row) * ((a_prime_bit c 898 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1844_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1844 c row ↔ constraint_1844 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1845 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 899 row) * ((a_prime_bit c 899 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1845_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1845 c row ↔ constraint_1845 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1846 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 900 row) * ((a_prime_bit c 900 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1846_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1846 c row ↔ constraint_1846 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1847 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 901 row) * ((a_prime_bit c 901 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1847_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1847 c row ↔ constraint_1847 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1848 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 902 row) * ((a_prime_bit c 902 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1848_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1848 c row ↔ constraint_1848 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1849 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 903 row) * ((a_prime_bit c 903 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1849_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1849 c row ↔ constraint_1849 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1850 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 904 row) * ((a_prime_bit c 904 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1850_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1850 c row ↔ constraint_1850 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1851 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 905 row) * ((a_prime_bit c 905 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1851_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1851 c row ↔ constraint_1851 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1852 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 906 row) * ((a_prime_bit c 906 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1852_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1852 c row ↔ constraint_1852 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1853 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 907 row) * ((a_prime_bit c 907 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1853_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1853 c row ↔ constraint_1853 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1854 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 908 row) * ((a_prime_bit c 908 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1854_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1854 c row ↔ constraint_1854 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1855 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 909 row) * ((a_prime_bit c 909 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1855_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1855 c row ↔ constraint_1855 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1856 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 910 row) * ((a_prime_bit c 910 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1856_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1856 c row ↔ constraint_1856 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1857 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 911 row) * ((a_prime_bit c 911 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1857_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1857 c row ↔ constraint_1857 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1858 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 912 row) * ((a_prime_bit c 912 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1858_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1858 c row ↔ constraint_1858 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1859 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 913 row) * ((a_prime_bit c 913 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1859_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1859 c row ↔ constraint_1859 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1860 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 914 row) * ((a_prime_bit c 914 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1860_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1860 c row ↔ constraint_1860 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1861 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 915 row) * ((a_prime_bit c 915 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1861_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1861 c row ↔ constraint_1861 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1862 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 916 row) * ((a_prime_bit c 916 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1862_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1862 c row ↔ constraint_1862 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1863 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 917 row) * ((a_prime_bit c 917 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1863_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1863 c row ↔ constraint_1863 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1864 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 918 row) * ((a_prime_bit c 918 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1864_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1864 c row ↔ constraint_1864 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1865 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 919 row) * ((a_prime_bit c 919 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1865_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1865 c row ↔ constraint_1865 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1866 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 920 row) * ((a_prime_bit c 920 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1866_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1866 c row ↔ constraint_1866 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1867 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 921 row) * ((a_prime_bit c 921 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1867_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1867 c row ↔ constraint_1867 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1868 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 922 row) * ((a_prime_bit c 922 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1868_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1868 c row ↔ constraint_1868 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1869 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 923 row) * ((a_prime_bit c 923 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1869_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1869 c row ↔ constraint_1869 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1870 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 924 row) * ((a_prime_bit c 924 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1870_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1870 c row ↔ constraint_1870 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1871 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 925 row) * ((a_prime_bit c 925 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1871_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1871 c row ↔ constraint_1871 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1872 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 926 row) * ((a_prime_bit c 926 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1872_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1872 c row ↔ constraint_1872 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1873 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 927 row) * ((a_prime_bit c 927 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1873_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1873 c row ↔ constraint_1873 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1874 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 928 row) * ((a_prime_bit c 928 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1874_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1874 c row ↔ constraint_1874 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1875 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 929 row) * ((a_prime_bit c 929 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1875_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1875 c row ↔ constraint_1875 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1876 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 930 row) * ((a_prime_bit c 930 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1876_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1876 c row ↔ constraint_1876 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1877 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 931 row) * ((a_prime_bit c 931 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1877_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1877 c row ↔ constraint_1877 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1878 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 932 row) * ((a_prime_bit c 932 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1878_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1878 c row ↔ constraint_1878 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1879 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 933 row) * ((a_prime_bit c 933 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1879_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1879 c row ↔ constraint_1879 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1880 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 934 row) * ((a_prime_bit c 934 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1880_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1880 c row ↔ constraint_1880 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1881 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 935 row) * ((a_prime_bit c 935 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1881_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1881 c row ↔ constraint_1881 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1882 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 936 row) * ((a_prime_bit c 936 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1882_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1882 c row ↔ constraint_1882 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1883 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 937 row) * ((a_prime_bit c 937 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1883_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1883 c row ↔ constraint_1883 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1884 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 938 row) * ((a_prime_bit c 938 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1884_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1884 c row ↔ constraint_1884 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1885 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 939 row) * ((a_prime_bit c 939 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1885_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1885 c row ↔ constraint_1885 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1886 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 940 row) * ((a_prime_bit c 940 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1886_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1886 c row ↔ constraint_1886 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1887 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 941 row) * ((a_prime_bit c 941 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1887_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1887 c row ↔ constraint_1887 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1888 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 942 row) * ((a_prime_bit c 942 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1888_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1888 c row ↔ constraint_1888 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1889 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 943 row) * ((a_prime_bit c 943 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1889_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1889 c row ↔ constraint_1889 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1890 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 944 row) * ((a_prime_bit c 944 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1890_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1890 c row ↔ constraint_1890 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1891 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 945 row) * ((a_prime_bit c 945 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1891_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1891 c row ↔ constraint_1891 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1892 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 946 row) * ((a_prime_bit c 946 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1892_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1892 c row ↔ constraint_1892 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1893 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 947 row) * ((a_prime_bit c 947 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1893_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1893 c row ↔ constraint_1893 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1894 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 948 row) * ((a_prime_bit c 948 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1894_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1894 c row ↔ constraint_1894 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1895 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 949 row) * ((a_prime_bit c 949 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1895_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1895 c row ↔ constraint_1895 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1896 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 950 row) * ((a_prime_bit c 950 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1896_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1896 c row ↔ constraint_1896 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1897 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 951 row) * ((a_prime_bit c 951 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1897_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1897 c row ↔ constraint_1897 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1898 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 952 row) * ((a_prime_bit c 952 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1898_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1898 c row ↔ constraint_1898 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1899 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 953 row) * ((a_prime_bit c 953 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1899_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1899 c row ↔ constraint_1899 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1900 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 954 row) * ((a_prime_bit c 954 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1900_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1900 c row ↔ constraint_1900 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1901 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 955 row) * ((a_prime_bit c 955 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1901_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1901 c row ↔ constraint_1901 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1902 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 956 row) * ((a_prime_bit c 956 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1902_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1902 c row ↔ constraint_1902 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1903 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 957 row) * ((a_prime_bit c 957 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1903_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1903 c row ↔ constraint_1903 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1904 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 958 row) * ((a_prime_bit c 958 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1904_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1904 c row ↔ constraint_1904 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1905 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 959 row) * ((a_prime_bit c 959 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1905_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1905 c row ↔ constraint_1905 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1906 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 1761 181 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1906_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1906 c row ↔ constraint_1906 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1907 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 1777 182 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1907_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1907 c row ↔ constraint_1907 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1908 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 1793 183 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1908_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1908 c row ↔ constraint_1908 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1909 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 1809 184 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1909_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1909 c row ↔ constraint_1909 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1910 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 960 row) * ((a_prime_bit c 960 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1910_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1910 c row ↔ constraint_1910 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1911 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 961 row) * ((a_prime_bit c 961 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1911_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1911 c row ↔ constraint_1911 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1912 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 962 row) * ((a_prime_bit c 962 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1912_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1912 c row ↔ constraint_1912 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1913 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 963 row) * ((a_prime_bit c 963 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1913_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1913 c row ↔ constraint_1913 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1914 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 964 row) * ((a_prime_bit c 964 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1914_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1914 c row ↔ constraint_1914 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1915 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 965 row) * ((a_prime_bit c 965 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1915_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1915 c row ↔ constraint_1915 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1916 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 966 row) * ((a_prime_bit c 966 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1916_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1916 c row ↔ constraint_1916 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1917 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 967 row) * ((a_prime_bit c 967 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1917_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1917 c row ↔ constraint_1917 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1918 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 968 row) * ((a_prime_bit c 968 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1918_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1918 c row ↔ constraint_1918 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1919 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 969 row) * ((a_prime_bit c 969 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1919_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1919 c row ↔ constraint_1919 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1920 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 970 row) * ((a_prime_bit c 970 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1920_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1920 c row ↔ constraint_1920 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1921 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 971 row) * ((a_prime_bit c 971 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1921_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1921 c row ↔ constraint_1921 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1922 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 972 row) * ((a_prime_bit c 972 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1922_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1922 c row ↔ constraint_1922 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1923 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 973 row) * ((a_prime_bit c 973 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1923_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1923 c row ↔ constraint_1923 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1924 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 974 row) * ((a_prime_bit c 974 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1924_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1924 c row ↔ constraint_1924 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1925 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 975 row) * ((a_prime_bit c 975 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1925_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1925 c row ↔ constraint_1925 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1926 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 976 row) * ((a_prime_bit c 976 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1926_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1926 c row ↔ constraint_1926 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1927 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 977 row) * ((a_prime_bit c 977 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1927_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1927 c row ↔ constraint_1927 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1928 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 978 row) * ((a_prime_bit c 978 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1928_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1928 c row ↔ constraint_1928 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1929 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 979 row) * ((a_prime_bit c 979 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1929_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1929 c row ↔ constraint_1929 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1930 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 980 row) * ((a_prime_bit c 980 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1930_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1930 c row ↔ constraint_1930 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1931 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 981 row) * ((a_prime_bit c 981 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1931_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1931 c row ↔ constraint_1931 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1932 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 982 row) * ((a_prime_bit c 982 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1932_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1932 c row ↔ constraint_1932 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1933 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 983 row) * ((a_prime_bit c 983 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1933_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1933 c row ↔ constraint_1933 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1934 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 984 row) * ((a_prime_bit c 984 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1934_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1934 c row ↔ constraint_1934 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1935 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 985 row) * ((a_prime_bit c 985 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1935_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1935 c row ↔ constraint_1935 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1936 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 986 row) * ((a_prime_bit c 986 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1936_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1936 c row ↔ constraint_1936 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1937 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 987 row) * ((a_prime_bit c 987 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1937_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1937 c row ↔ constraint_1937 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1938 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 988 row) * ((a_prime_bit c 988 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1938_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1938 c row ↔ constraint_1938 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1939 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 989 row) * ((a_prime_bit c 989 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1939_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1939 c row ↔ constraint_1939 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1940 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 990 row) * ((a_prime_bit c 990 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1940_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1940 c row ↔ constraint_1940 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1941 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 991 row) * ((a_prime_bit c 991 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1941_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1941 c row ↔ constraint_1941 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1942 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 992 row) * ((a_prime_bit c 992 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1942_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1942 c row ↔ constraint_1942 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1943 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 993 row) * ((a_prime_bit c 993 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1943_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1943 c row ↔ constraint_1943 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1944 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 994 row) * ((a_prime_bit c 994 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1944_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1944 c row ↔ constraint_1944 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1945 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 995 row) * ((a_prime_bit c 995 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1945_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1945 c row ↔ constraint_1945 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1946 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 996 row) * ((a_prime_bit c 996 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1946_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1946 c row ↔ constraint_1946 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1947 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 997 row) * ((a_prime_bit c 997 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1947_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1947 c row ↔ constraint_1947 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1948 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 998 row) * ((a_prime_bit c 998 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1948_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1948 c row ↔ constraint_1948 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1949 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 999 row) * ((a_prime_bit c 999 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1949_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1949 c row ↔ constraint_1949 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1950 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1000 row) * ((a_prime_bit c 1000 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1950_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1950 c row ↔ constraint_1950 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1951 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1001 row) * ((a_prime_bit c 1001 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1951_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1951 c row ↔ constraint_1951 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1952 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1002 row) * ((a_prime_bit c 1002 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1952_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1952 c row ↔ constraint_1952 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1953 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1003 row) * ((a_prime_bit c 1003 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1953_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1953 c row ↔ constraint_1953 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1954 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1004 row) * ((a_prime_bit c 1004 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1954_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1954 c row ↔ constraint_1954 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1955 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1005 row) * ((a_prime_bit c 1005 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1955_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1955 c row ↔ constraint_1955 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1956 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1006 row) * ((a_prime_bit c 1006 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1956_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1956 c row ↔ constraint_1956 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1957 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1007 row) * ((a_prime_bit c 1007 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1957_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1957 c row ↔ constraint_1957 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1958 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1008 row) * ((a_prime_bit c 1008 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1958_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1958 c row ↔ constraint_1958 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1959 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1009 row) * ((a_prime_bit c 1009 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1959_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1959 c row ↔ constraint_1959 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1960 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1010 row) * ((a_prime_bit c 1010 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1960_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1960 c row ↔ constraint_1960 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1961 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1011 row) * ((a_prime_bit c 1011 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1961_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1961 c row ↔ constraint_1961 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1962 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1012 row) * ((a_prime_bit c 1012 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1962_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1962 c row ↔ constraint_1962 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1963 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1013 row) * ((a_prime_bit c 1013 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1963_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1963 c row ↔ constraint_1963 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1964 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1014 row) * ((a_prime_bit c 1014 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1964_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1964 c row ↔ constraint_1964 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1965 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1015 row) * ((a_prime_bit c 1015 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1965_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1965 c row ↔ constraint_1965 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1966 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1016 row) * ((a_prime_bit c 1016 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1966_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1966 c row ↔ constraint_1966 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1967 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1017 row) * ((a_prime_bit c 1017 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1967_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1967 c row ↔ constraint_1967 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1968 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1018 row) * ((a_prime_bit c 1018 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1968_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1968 c row ↔ constraint_1968 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1969 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1019 row) * ((a_prime_bit c 1019 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1969_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1969 c row ↔ constraint_1969 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1970 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1020 row) * ((a_prime_bit c 1020 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1970_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1970 c row ↔ constraint_1970 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1971 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1021 row) * ((a_prime_bit c 1021 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1971_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1971 c row ↔ constraint_1971 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1972 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1022 row) * ((a_prime_bit c 1022 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1972_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1972 c row ↔ constraint_1972 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1973 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1023 row) * ((a_prime_bit c 1023 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1973_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1973 c row ↔ constraint_1973 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1974 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 1825 185 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1974_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1974 c row ↔ constraint_1974 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1975 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 1841 186 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1975_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1975 c row ↔ constraint_1975 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1976 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 1857 187 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1976_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1976 c row ↔ constraint_1976 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1977 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 1873 188 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1977_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1977 c row ↔ constraint_1977 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1978 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1024 row) * ((a_prime_bit c 1024 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1978_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1978 c row ↔ constraint_1978 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1979 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1025 row) * ((a_prime_bit c 1025 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1979_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1979 c row ↔ constraint_1979 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1980 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1026 row) * ((a_prime_bit c 1026 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1980_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1980 c row ↔ constraint_1980 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1981 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1027 row) * ((a_prime_bit c 1027 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1981_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1981 c row ↔ constraint_1981 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1982 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1028 row) * ((a_prime_bit c 1028 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1982_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1982 c row ↔ constraint_1982 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1983 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1029 row) * ((a_prime_bit c 1029 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1983_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1983 c row ↔ constraint_1983 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1984 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1030 row) * ((a_prime_bit c 1030 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1984_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1984 c row ↔ constraint_1984 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1985 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1031 row) * ((a_prime_bit c 1031 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1985_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1985 c row ↔ constraint_1985 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1986 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1032 row) * ((a_prime_bit c 1032 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1986_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1986 c row ↔ constraint_1986 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1987 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1033 row) * ((a_prime_bit c 1033 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1987_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1987 c row ↔ constraint_1987 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1988 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1034 row) * ((a_prime_bit c 1034 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1988_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1988 c row ↔ constraint_1988 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1989 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1035 row) * ((a_prime_bit c 1035 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1989_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1989 c row ↔ constraint_1989 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1990 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1036 row) * ((a_prime_bit c 1036 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1990_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1990 c row ↔ constraint_1990 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1991 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1037 row) * ((a_prime_bit c 1037 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1991_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1991 c row ↔ constraint_1991 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1992 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1038 row) * ((a_prime_bit c 1038 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1992_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1992 c row ↔ constraint_1992 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1993 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1039 row) * ((a_prime_bit c 1039 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1993_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1993 c row ↔ constraint_1993 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1994 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1040 row) * ((a_prime_bit c 1040 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1994_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1994 c row ↔ constraint_1994 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1995 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1041 row) * ((a_prime_bit c 1041 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1995_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1995 c row ↔ constraint_1995 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1996 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1042 row) * ((a_prime_bit c 1042 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1996_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1996 c row ↔ constraint_1996 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1997 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1043 row) * ((a_prime_bit c 1043 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1997_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1997 c row ↔ constraint_1997 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1998 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1044 row) * ((a_prime_bit c 1044 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1998_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1998 c row ↔ constraint_1998 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_1999 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1045 row) * ((a_prime_bit c 1045 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_1999_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_1999 c row ↔ constraint_1999 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2000 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1046 row) * ((a_prime_bit c 1046 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2000_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2000 c row ↔ constraint_2000 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2001 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1047 row) * ((a_prime_bit c 1047 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2001_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2001 c row ↔ constraint_2001 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2002 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1048 row) * ((a_prime_bit c 1048 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2002_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2002 c row ↔ constraint_2002 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2003 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1049 row) * ((a_prime_bit c 1049 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2003_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2003 c row ↔ constraint_2003 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2004 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1050 row) * ((a_prime_bit c 1050 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2004_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2004 c row ↔ constraint_2004 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2005 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1051 row) * ((a_prime_bit c 1051 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2005_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2005 c row ↔ constraint_2005 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2006 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1052 row) * ((a_prime_bit c 1052 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2006_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2006 c row ↔ constraint_2006 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2007 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1053 row) * ((a_prime_bit c 1053 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2007_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2007 c row ↔ constraint_2007 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2008 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1054 row) * ((a_prime_bit c 1054 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2008_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2008 c row ↔ constraint_2008 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2009 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1055 row) * ((a_prime_bit c 1055 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2009_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2009 c row ↔ constraint_2009 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2010 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1056 row) * ((a_prime_bit c 1056 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2010_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2010 c row ↔ constraint_2010 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2011 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1057 row) * ((a_prime_bit c 1057 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2011_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2011 c row ↔ constraint_2011 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2012 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1058 row) * ((a_prime_bit c 1058 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2012_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2012 c row ↔ constraint_2012 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2013 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1059 row) * ((a_prime_bit c 1059 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2013_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2013 c row ↔ constraint_2013 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2014 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1060 row) * ((a_prime_bit c 1060 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2014_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2014 c row ↔ constraint_2014 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2015 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1061 row) * ((a_prime_bit c 1061 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2015_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2015 c row ↔ constraint_2015 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2016 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1062 row) * ((a_prime_bit c 1062 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2016_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2016 c row ↔ constraint_2016 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2017 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1063 row) * ((a_prime_bit c 1063 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2017_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2017 c row ↔ constraint_2017 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2018 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1064 row) * ((a_prime_bit c 1064 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2018_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2018 c row ↔ constraint_2018 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2019 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1065 row) * ((a_prime_bit c 1065 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2019_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2019 c row ↔ constraint_2019 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2020 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1066 row) * ((a_prime_bit c 1066 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2020_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2020 c row ↔ constraint_2020 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2021 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1067 row) * ((a_prime_bit c 1067 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2021_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2021 c row ↔ constraint_2021 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2022 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1068 row) * ((a_prime_bit c 1068 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2022_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2022 c row ↔ constraint_2022 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2023 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1069 row) * ((a_prime_bit c 1069 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2023_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2023 c row ↔ constraint_2023 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2024 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1070 row) * ((a_prime_bit c 1070 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2024_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2024 c row ↔ constraint_2024 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2025 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1071 row) * ((a_prime_bit c 1071 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2025_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2025 c row ↔ constraint_2025 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2026 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1072 row) * ((a_prime_bit c 1072 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2026_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2026 c row ↔ constraint_2026 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2027 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1073 row) * ((a_prime_bit c 1073 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2027_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2027 c row ↔ constraint_2027 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2028 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1074 row) * ((a_prime_bit c 1074 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2028_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2028 c row ↔ constraint_2028 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2029 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1075 row) * ((a_prime_bit c 1075 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2029_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2029 c row ↔ constraint_2029 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2030 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1076 row) * ((a_prime_bit c 1076 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2030_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2030 c row ↔ constraint_2030 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2031 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1077 row) * ((a_prime_bit c 1077 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2031_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2031 c row ↔ constraint_2031 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2032 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1078 row) * ((a_prime_bit c 1078 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2032_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2032 c row ↔ constraint_2032 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2033 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1079 row) * ((a_prime_bit c 1079 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2033_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2033 c row ↔ constraint_2033 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2034 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1080 row) * ((a_prime_bit c 1080 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2034_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2034 c row ↔ constraint_2034 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2035 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1081 row) * ((a_prime_bit c 1081 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2035_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2035 c row ↔ constraint_2035 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2036 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1082 row) * ((a_prime_bit c 1082 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2036_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2036 c row ↔ constraint_2036 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2037 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1083 row) * ((a_prime_bit c 1083 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2037_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2037 c row ↔ constraint_2037 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2038 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1084 row) * ((a_prime_bit c 1084 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2038_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2038 c row ↔ constraint_2038 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2039 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1085 row) * ((a_prime_bit c 1085 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2039_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2039 c row ↔ constraint_2039 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2040 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1086 row) * ((a_prime_bit c 1086 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2040_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2040 c row ↔ constraint_2040 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2041 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1087 row) * ((a_prime_bit c 1087 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2041_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2041 c row ↔ constraint_2041 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2042 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 1889 189 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2042_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2042 c row ↔ constraint_2042 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2043 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 1905 190 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2043_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2043 c row ↔ constraint_2043 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2044 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 1921 191 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2044_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2044 c row ↔ constraint_2044 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2045 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 1937 192 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2045_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2045 c row ↔ constraint_2045 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2046 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1088 row) * ((a_prime_bit c 1088 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2046_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2046 c row ↔ constraint_2046 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2047 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1089 row) * ((a_prime_bit c 1089 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2047_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2047 c row ↔ constraint_2047 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2048 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1090 row) * ((a_prime_bit c 1090 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2048_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2048 c row ↔ constraint_2048 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2049 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1091 row) * ((a_prime_bit c 1091 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2049_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2049 c row ↔ constraint_2049 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2050 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1092 row) * ((a_prime_bit c 1092 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2050_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2050 c row ↔ constraint_2050 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2051 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1093 row) * ((a_prime_bit c 1093 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2051_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2051 c row ↔ constraint_2051 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2052 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1094 row) * ((a_prime_bit c 1094 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2052_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2052 c row ↔ constraint_2052 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2053 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1095 row) * ((a_prime_bit c 1095 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2053_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2053 c row ↔ constraint_2053 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2054 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1096 row) * ((a_prime_bit c 1096 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2054_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2054 c row ↔ constraint_2054 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2055 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1097 row) * ((a_prime_bit c 1097 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2055_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2055 c row ↔ constraint_2055 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2056 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1098 row) * ((a_prime_bit c 1098 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2056_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2056 c row ↔ constraint_2056 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2057 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1099 row) * ((a_prime_bit c 1099 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2057_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2057 c row ↔ constraint_2057 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2058 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1100 row) * ((a_prime_bit c 1100 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2058_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2058 c row ↔ constraint_2058 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2059 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1101 row) * ((a_prime_bit c 1101 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2059_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2059 c row ↔ constraint_2059 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2060 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1102 row) * ((a_prime_bit c 1102 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2060_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2060 c row ↔ constraint_2060 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2061 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1103 row) * ((a_prime_bit c 1103 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2061_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2061 c row ↔ constraint_2061 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2062 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1104 row) * ((a_prime_bit c 1104 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2062_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2062 c row ↔ constraint_2062 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2063 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1105 row) * ((a_prime_bit c 1105 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2063_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2063 c row ↔ constraint_2063 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2064 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1106 row) * ((a_prime_bit c 1106 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2064_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2064 c row ↔ constraint_2064 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2065 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1107 row) * ((a_prime_bit c 1107 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2065_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2065 c row ↔ constraint_2065 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2066 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1108 row) * ((a_prime_bit c 1108 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2066_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2066 c row ↔ constraint_2066 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2067 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1109 row) * ((a_prime_bit c 1109 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2067_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2067 c row ↔ constraint_2067 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2068 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1110 row) * ((a_prime_bit c 1110 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2068_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2068 c row ↔ constraint_2068 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2069 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1111 row) * ((a_prime_bit c 1111 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2069_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2069 c row ↔ constraint_2069 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2070 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1112 row) * ((a_prime_bit c 1112 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2070_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2070 c row ↔ constraint_2070 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2071 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1113 row) * ((a_prime_bit c 1113 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2071_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2071 c row ↔ constraint_2071 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2072 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1114 row) * ((a_prime_bit c 1114 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2072_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2072 c row ↔ constraint_2072 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2073 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1115 row) * ((a_prime_bit c 1115 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2073_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2073 c row ↔ constraint_2073 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2074 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1116 row) * ((a_prime_bit c 1116 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2074_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2074 c row ↔ constraint_2074 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2075 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1117 row) * ((a_prime_bit c 1117 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2075_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2075 c row ↔ constraint_2075 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2076 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1118 row) * ((a_prime_bit c 1118 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2076_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2076 c row ↔ constraint_2076 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2077 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1119 row) * ((a_prime_bit c 1119 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2077_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2077 c row ↔ constraint_2077 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2078 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1120 row) * ((a_prime_bit c 1120 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2078_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2078 c row ↔ constraint_2078 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2079 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1121 row) * ((a_prime_bit c 1121 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2079_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2079 c row ↔ constraint_2079 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2080 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1122 row) * ((a_prime_bit c 1122 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2080_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2080 c row ↔ constraint_2080 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2081 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1123 row) * ((a_prime_bit c 1123 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2081_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2081 c row ↔ constraint_2081 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2082 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1124 row) * ((a_prime_bit c 1124 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2082_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2082 c row ↔ constraint_2082 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2083 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1125 row) * ((a_prime_bit c 1125 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2083_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2083 c row ↔ constraint_2083 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2084 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1126 row) * ((a_prime_bit c 1126 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2084_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2084 c row ↔ constraint_2084 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2085 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1127 row) * ((a_prime_bit c 1127 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2085_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2085 c row ↔ constraint_2085 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2086 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1128 row) * ((a_prime_bit c 1128 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2086_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2086 c row ↔ constraint_2086 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2087 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1129 row) * ((a_prime_bit c 1129 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2087_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2087 c row ↔ constraint_2087 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2088 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1130 row) * ((a_prime_bit c 1130 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2088_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2088 c row ↔ constraint_2088 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2089 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1131 row) * ((a_prime_bit c 1131 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2089_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2089 c row ↔ constraint_2089 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2090 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1132 row) * ((a_prime_bit c 1132 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2090_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2090 c row ↔ constraint_2090 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2091 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1133 row) * ((a_prime_bit c 1133 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2091_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2091 c row ↔ constraint_2091 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2092 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1134 row) * ((a_prime_bit c 1134 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2092_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2092 c row ↔ constraint_2092 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2093 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1135 row) * ((a_prime_bit c 1135 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2093_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2093 c row ↔ constraint_2093 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2094 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1136 row) * ((a_prime_bit c 1136 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2094_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2094 c row ↔ constraint_2094 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2095 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1137 row) * ((a_prime_bit c 1137 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2095_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2095 c row ↔ constraint_2095 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2096 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1138 row) * ((a_prime_bit c 1138 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2096_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2096 c row ↔ constraint_2096 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2097 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1139 row) * ((a_prime_bit c 1139 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2097_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2097 c row ↔ constraint_2097 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2098 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1140 row) * ((a_prime_bit c 1140 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2098_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2098 c row ↔ constraint_2098 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2099 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1141 row) * ((a_prime_bit c 1141 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2099_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2099 c row ↔ constraint_2099 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2100 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1142 row) * ((a_prime_bit c 1142 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2100_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2100 c row ↔ constraint_2100 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2101 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1143 row) * ((a_prime_bit c 1143 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2101_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2101 c row ↔ constraint_2101 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2102 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1144 row) * ((a_prime_bit c 1144 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2102_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2102 c row ↔ constraint_2102 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2103 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1145 row) * ((a_prime_bit c 1145 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2103_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2103 c row ↔ constraint_2103 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2104 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1146 row) * ((a_prime_bit c 1146 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2104_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2104 c row ↔ constraint_2104 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2105 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1147 row) * ((a_prime_bit c 1147 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2105_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2105 c row ↔ constraint_2105 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2106 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1148 row) * ((a_prime_bit c 1148 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2106_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2106 c row ↔ constraint_2106 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2107 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1149 row) * ((a_prime_bit c 1149 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2107_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2107 c row ↔ constraint_2107 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2108 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1150 row) * ((a_prime_bit c 1150 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2108_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2108 c row ↔ constraint_2108 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2109 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1151 row) * ((a_prime_bit c 1151 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2109_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2109 c row ↔ constraint_2109 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2110 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 1953 193 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2110_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2110 c row ↔ constraint_2110 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2111 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 1969 194 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2111_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2111 c row ↔ constraint_2111 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2112 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 1985 195 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2112_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2112 c row ↔ constraint_2112 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2113 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 2001 196 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2113_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2113 c row ↔ constraint_2113 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2114 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1152 row) * ((a_prime_bit c 1152 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2114_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2114 c row ↔ constraint_2114 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2115 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1153 row) * ((a_prime_bit c 1153 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2115_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2115 c row ↔ constraint_2115 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2116 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1154 row) * ((a_prime_bit c 1154 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2116_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2116 c row ↔ constraint_2116 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2117 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1155 row) * ((a_prime_bit c 1155 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2117_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2117 c row ↔ constraint_2117 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2118 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1156 row) * ((a_prime_bit c 1156 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2118_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2118 c row ↔ constraint_2118 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2119 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1157 row) * ((a_prime_bit c 1157 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2119_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2119 c row ↔ constraint_2119 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2120 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1158 row) * ((a_prime_bit c 1158 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2120_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2120 c row ↔ constraint_2120 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2121 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1159 row) * ((a_prime_bit c 1159 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2121_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2121 c row ↔ constraint_2121 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2122 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1160 row) * ((a_prime_bit c 1160 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2122_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2122 c row ↔ constraint_2122 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2123 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1161 row) * ((a_prime_bit c 1161 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2123_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2123 c row ↔ constraint_2123 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2124 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1162 row) * ((a_prime_bit c 1162 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2124_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2124 c row ↔ constraint_2124 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2125 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1163 row) * ((a_prime_bit c 1163 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2125_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2125 c row ↔ constraint_2125 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2126 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1164 row) * ((a_prime_bit c 1164 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2126_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2126 c row ↔ constraint_2126 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2127 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1165 row) * ((a_prime_bit c 1165 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2127_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2127 c row ↔ constraint_2127 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2128 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1166 row) * ((a_prime_bit c 1166 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2128_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2128 c row ↔ constraint_2128 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2129 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1167 row) * ((a_prime_bit c 1167 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2129_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2129 c row ↔ constraint_2129 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2130 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1168 row) * ((a_prime_bit c 1168 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2130_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2130 c row ↔ constraint_2130 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2131 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1169 row) * ((a_prime_bit c 1169 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2131_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2131 c row ↔ constraint_2131 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2132 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1170 row) * ((a_prime_bit c 1170 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2132_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2132 c row ↔ constraint_2132 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2133 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1171 row) * ((a_prime_bit c 1171 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2133_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2133 c row ↔ constraint_2133 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2134 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1172 row) * ((a_prime_bit c 1172 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2134_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2134 c row ↔ constraint_2134 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2135 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1173 row) * ((a_prime_bit c 1173 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2135_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2135 c row ↔ constraint_2135 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2136 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1174 row) * ((a_prime_bit c 1174 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2136_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2136 c row ↔ constraint_2136 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2137 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1175 row) * ((a_prime_bit c 1175 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2137_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2137 c row ↔ constraint_2137 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2138 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1176 row) * ((a_prime_bit c 1176 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2138_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2138 c row ↔ constraint_2138 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2139 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1177 row) * ((a_prime_bit c 1177 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2139_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2139 c row ↔ constraint_2139 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2140 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1178 row) * ((a_prime_bit c 1178 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2140_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2140 c row ↔ constraint_2140 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2141 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1179 row) * ((a_prime_bit c 1179 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2141_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2141 c row ↔ constraint_2141 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2142 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1180 row) * ((a_prime_bit c 1180 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2142_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2142 c row ↔ constraint_2142 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2143 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1181 row) * ((a_prime_bit c 1181 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2143_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2143 c row ↔ constraint_2143 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2144 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1182 row) * ((a_prime_bit c 1182 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2144_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2144 c row ↔ constraint_2144 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2145 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1183 row) * ((a_prime_bit c 1183 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2145_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2145 c row ↔ constraint_2145 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2146 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1184 row) * ((a_prime_bit c 1184 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2146_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2146 c row ↔ constraint_2146 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2147 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1185 row) * ((a_prime_bit c 1185 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2147_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2147 c row ↔ constraint_2147 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2148 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1186 row) * ((a_prime_bit c 1186 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2148_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2148 c row ↔ constraint_2148 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2149 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1187 row) * ((a_prime_bit c 1187 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2149_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2149 c row ↔ constraint_2149 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2150 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1188 row) * ((a_prime_bit c 1188 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2150_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2150 c row ↔ constraint_2150 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2151 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1189 row) * ((a_prime_bit c 1189 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2151_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2151 c row ↔ constraint_2151 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2152 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1190 row) * ((a_prime_bit c 1190 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2152_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2152 c row ↔ constraint_2152 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2153 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1191 row) * ((a_prime_bit c 1191 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2153_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2153 c row ↔ constraint_2153 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2154 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1192 row) * ((a_prime_bit c 1192 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2154_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2154 c row ↔ constraint_2154 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2155 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1193 row) * ((a_prime_bit c 1193 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2155_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2155 c row ↔ constraint_2155 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2156 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1194 row) * ((a_prime_bit c 1194 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2156_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2156 c row ↔ constraint_2156 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2157 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1195 row) * ((a_prime_bit c 1195 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2157_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2157 c row ↔ constraint_2157 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2158 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1196 row) * ((a_prime_bit c 1196 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2158_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2158 c row ↔ constraint_2158 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2159 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1197 row) * ((a_prime_bit c 1197 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2159_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2159 c row ↔ constraint_2159 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2160 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1198 row) * ((a_prime_bit c 1198 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2160_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2160 c row ↔ constraint_2160 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2161 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1199 row) * ((a_prime_bit c 1199 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2161_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2161 c row ↔ constraint_2161 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2162 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1200 row) * ((a_prime_bit c 1200 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2162_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2162 c row ↔ constraint_2162 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2163 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1201 row) * ((a_prime_bit c 1201 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2163_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2163 c row ↔ constraint_2163 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2164 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1202 row) * ((a_prime_bit c 1202 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2164_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2164 c row ↔ constraint_2164 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2165 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1203 row) * ((a_prime_bit c 1203 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2165_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2165 c row ↔ constraint_2165 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2166 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1204 row) * ((a_prime_bit c 1204 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2166_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2166 c row ↔ constraint_2166 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2167 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1205 row) * ((a_prime_bit c 1205 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2167_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2167 c row ↔ constraint_2167 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2168 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1206 row) * ((a_prime_bit c 1206 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2168_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2168 c row ↔ constraint_2168 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2169 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1207 row) * ((a_prime_bit c 1207 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2169_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2169 c row ↔ constraint_2169 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2170 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1208 row) * ((a_prime_bit c 1208 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2170_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2170 c row ↔ constraint_2170 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2171 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1209 row) * ((a_prime_bit c 1209 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2171_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2171 c row ↔ constraint_2171 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2172 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1210 row) * ((a_prime_bit c 1210 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2172_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2172 c row ↔ constraint_2172 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2173 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1211 row) * ((a_prime_bit c 1211 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2173_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2173 c row ↔ constraint_2173 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2174 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1212 row) * ((a_prime_bit c 1212 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2174_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2174 c row ↔ constraint_2174 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2175 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1213 row) * ((a_prime_bit c 1213 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2175_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2175 c row ↔ constraint_2175 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2176 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1214 row) * ((a_prime_bit c 1214 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2176_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2176 c row ↔ constraint_2176 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2177 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1215 row) * ((a_prime_bit c 1215 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2177_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2177 c row ↔ constraint_2177 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2178 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 2017 197 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2178_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2178 c row ↔ constraint_2178 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2179 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 2033 198 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2179_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2179 c row ↔ constraint_2179 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2180 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 2049 199 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2180_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2180 c row ↔ constraint_2180 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2181 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 2065 200 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2181_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2181 c row ↔ constraint_2181 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2182 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1216 row) * ((a_prime_bit c 1216 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2182_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2182 c row ↔ constraint_2182 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2183 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1217 row) * ((a_prime_bit c 1217 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2183_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2183 c row ↔ constraint_2183 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2184 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1218 row) * ((a_prime_bit c 1218 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2184_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2184 c row ↔ constraint_2184 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2185 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1219 row) * ((a_prime_bit c 1219 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2185_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2185 c row ↔ constraint_2185 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2186 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1220 row) * ((a_prime_bit c 1220 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2186_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2186 c row ↔ constraint_2186 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2187 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1221 row) * ((a_prime_bit c 1221 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2187_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2187 c row ↔ constraint_2187 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2188 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1222 row) * ((a_prime_bit c 1222 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2188_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2188 c row ↔ constraint_2188 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2189 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1223 row) * ((a_prime_bit c 1223 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2189_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2189 c row ↔ constraint_2189 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2190 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1224 row) * ((a_prime_bit c 1224 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2190_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2190 c row ↔ constraint_2190 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2191 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1225 row) * ((a_prime_bit c 1225 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2191_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2191 c row ↔ constraint_2191 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2192 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1226 row) * ((a_prime_bit c 1226 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2192_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2192 c row ↔ constraint_2192 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2193 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1227 row) * ((a_prime_bit c 1227 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2193_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2193 c row ↔ constraint_2193 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2194 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1228 row) * ((a_prime_bit c 1228 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2194_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2194 c row ↔ constraint_2194 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2195 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1229 row) * ((a_prime_bit c 1229 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2195_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2195 c row ↔ constraint_2195 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2196 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1230 row) * ((a_prime_bit c 1230 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2196_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2196 c row ↔ constraint_2196 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2197 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1231 row) * ((a_prime_bit c 1231 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2197_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2197 c row ↔ constraint_2197 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2198 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1232 row) * ((a_prime_bit c 1232 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2198_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2198 c row ↔ constraint_2198 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2199 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1233 row) * ((a_prime_bit c 1233 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2199_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2199 c row ↔ constraint_2199 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2200 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1234 row) * ((a_prime_bit c 1234 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2200_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2200 c row ↔ constraint_2200 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2201 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1235 row) * ((a_prime_bit c 1235 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2201_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2201 c row ↔ constraint_2201 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2202 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1236 row) * ((a_prime_bit c 1236 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2202_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2202 c row ↔ constraint_2202 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2203 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1237 row) * ((a_prime_bit c 1237 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2203_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2203 c row ↔ constraint_2203 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2204 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1238 row) * ((a_prime_bit c 1238 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2204_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2204 c row ↔ constraint_2204 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2205 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1239 row) * ((a_prime_bit c 1239 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2205_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2205 c row ↔ constraint_2205 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2206 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1240 row) * ((a_prime_bit c 1240 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2206_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2206 c row ↔ constraint_2206 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2207 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1241 row) * ((a_prime_bit c 1241 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2207_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2207 c row ↔ constraint_2207 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2208 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1242 row) * ((a_prime_bit c 1242 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2208_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2208 c row ↔ constraint_2208 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2209 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1243 row) * ((a_prime_bit c 1243 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2209_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2209 c row ↔ constraint_2209 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2210 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1244 row) * ((a_prime_bit c 1244 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2210_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2210 c row ↔ constraint_2210 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2211 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1245 row) * ((a_prime_bit c 1245 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2211_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2211 c row ↔ constraint_2211 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2212 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1246 row) * ((a_prime_bit c 1246 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2212_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2212 c row ↔ constraint_2212 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2213 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1247 row) * ((a_prime_bit c 1247 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2213_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2213 c row ↔ constraint_2213 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2214 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1248 row) * ((a_prime_bit c 1248 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2214_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2214 c row ↔ constraint_2214 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2215 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1249 row) * ((a_prime_bit c 1249 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2215_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2215 c row ↔ constraint_2215 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2216 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1250 row) * ((a_prime_bit c 1250 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2216_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2216 c row ↔ constraint_2216 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2217 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1251 row) * ((a_prime_bit c 1251 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2217_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2217 c row ↔ constraint_2217 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2218 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1252 row) * ((a_prime_bit c 1252 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2218_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2218 c row ↔ constraint_2218 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2219 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1253 row) * ((a_prime_bit c 1253 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2219_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2219 c row ↔ constraint_2219 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2220 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1254 row) * ((a_prime_bit c 1254 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2220_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2220 c row ↔ constraint_2220 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2221 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1255 row) * ((a_prime_bit c 1255 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2221_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2221 c row ↔ constraint_2221 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2222 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1256 row) * ((a_prime_bit c 1256 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2222_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2222 c row ↔ constraint_2222 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2223 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1257 row) * ((a_prime_bit c 1257 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2223_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2223 c row ↔ constraint_2223 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2224 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1258 row) * ((a_prime_bit c 1258 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2224_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2224 c row ↔ constraint_2224 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2225 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1259 row) * ((a_prime_bit c 1259 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2225_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2225 c row ↔ constraint_2225 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2226 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1260 row) * ((a_prime_bit c 1260 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2226_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2226 c row ↔ constraint_2226 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2227 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1261 row) * ((a_prime_bit c 1261 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2227_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2227 c row ↔ constraint_2227 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2228 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1262 row) * ((a_prime_bit c 1262 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2228_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2228 c row ↔ constraint_2228 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2229 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1263 row) * ((a_prime_bit c 1263 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2229_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2229 c row ↔ constraint_2229 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2230 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1264 row) * ((a_prime_bit c 1264 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2230_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2230 c row ↔ constraint_2230 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2231 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1265 row) * ((a_prime_bit c 1265 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2231_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2231 c row ↔ constraint_2231 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2232 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1266 row) * ((a_prime_bit c 1266 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2232_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2232 c row ↔ constraint_2232 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2233 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1267 row) * ((a_prime_bit c 1267 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2233_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2233 c row ↔ constraint_2233 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2234 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1268 row) * ((a_prime_bit c 1268 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2234_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2234 c row ↔ constraint_2234 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2235 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1269 row) * ((a_prime_bit c 1269 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2235_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2235 c row ↔ constraint_2235 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2236 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1270 row) * ((a_prime_bit c 1270 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2236_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2236 c row ↔ constraint_2236 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2237 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1271 row) * ((a_prime_bit c 1271 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2237_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2237 c row ↔ constraint_2237 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2238 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1272 row) * ((a_prime_bit c 1272 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2238_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2238 c row ↔ constraint_2238 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2239 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1273 row) * ((a_prime_bit c 1273 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2239_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2239 c row ↔ constraint_2239 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2240 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1274 row) * ((a_prime_bit c 1274 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2240_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2240 c row ↔ constraint_2240 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2241 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1275 row) * ((a_prime_bit c 1275 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2241_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2241 c row ↔ constraint_2241 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2242 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1276 row) * ((a_prime_bit c 1276 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2242_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2242 c row ↔ constraint_2242 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2243 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1277 row) * ((a_prime_bit c 1277 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2243_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2243 c row ↔ constraint_2243 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2244 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1278 row) * ((a_prime_bit c 1278 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2244_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2244 c row ↔ constraint_2244 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2245 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1279 row) * ((a_prime_bit c 1279 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2245_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2245 c row ↔ constraint_2245 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2246 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 2081 201 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2246_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2246 c row ↔ constraint_2246 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2247 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 2097 202 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2247_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2247 c row ↔ constraint_2247 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2248 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 2113 203 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2248_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2248 c row ↔ constraint_2248 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2249 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 2129 204 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2249_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2249 c row ↔ constraint_2249 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2250 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1280 row) * ((a_prime_bit c 1280 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2250_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2250 c row ↔ constraint_2250 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2251 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1281 row) * ((a_prime_bit c 1281 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2251_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2251 c row ↔ constraint_2251 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2252 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1282 row) * ((a_prime_bit c 1282 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2252_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2252 c row ↔ constraint_2252 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2253 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1283 row) * ((a_prime_bit c 1283 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2253_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2253 c row ↔ constraint_2253 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2254 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1284 row) * ((a_prime_bit c 1284 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2254_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2254 c row ↔ constraint_2254 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2255 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1285 row) * ((a_prime_bit c 1285 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2255_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2255 c row ↔ constraint_2255 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2256 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1286 row) * ((a_prime_bit c 1286 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2256_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2256 c row ↔ constraint_2256 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2257 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1287 row) * ((a_prime_bit c 1287 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2257_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2257 c row ↔ constraint_2257 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2258 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1288 row) * ((a_prime_bit c 1288 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2258_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2258 c row ↔ constraint_2258 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2259 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1289 row) * ((a_prime_bit c 1289 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2259_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2259 c row ↔ constraint_2259 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2260 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1290 row) * ((a_prime_bit c 1290 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2260_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2260 c row ↔ constraint_2260 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2261 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1291 row) * ((a_prime_bit c 1291 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2261_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2261 c row ↔ constraint_2261 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2262 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1292 row) * ((a_prime_bit c 1292 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2262_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2262 c row ↔ constraint_2262 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2263 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1293 row) * ((a_prime_bit c 1293 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2263_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2263 c row ↔ constraint_2263 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2264 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1294 row) * ((a_prime_bit c 1294 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2264_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2264 c row ↔ constraint_2264 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2265 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1295 row) * ((a_prime_bit c 1295 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2265_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2265 c row ↔ constraint_2265 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2266 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1296 row) * ((a_prime_bit c 1296 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2266_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2266 c row ↔ constraint_2266 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2267 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1297 row) * ((a_prime_bit c 1297 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2267_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2267 c row ↔ constraint_2267 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2268 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1298 row) * ((a_prime_bit c 1298 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2268_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2268 c row ↔ constraint_2268 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2269 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1299 row) * ((a_prime_bit c 1299 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2269_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2269 c row ↔ constraint_2269 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2270 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1300 row) * ((a_prime_bit c 1300 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2270_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2270 c row ↔ constraint_2270 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2271 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1301 row) * ((a_prime_bit c 1301 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2271_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2271 c row ↔ constraint_2271 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2272 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1302 row) * ((a_prime_bit c 1302 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2272_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2272 c row ↔ constraint_2272 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2273 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1303 row) * ((a_prime_bit c 1303 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2273_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2273 c row ↔ constraint_2273 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2274 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1304 row) * ((a_prime_bit c 1304 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2274_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2274 c row ↔ constraint_2274 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2275 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1305 row) * ((a_prime_bit c 1305 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2275_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2275 c row ↔ constraint_2275 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2276 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1306 row) * ((a_prime_bit c 1306 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2276_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2276 c row ↔ constraint_2276 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2277 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1307 row) * ((a_prime_bit c 1307 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2277_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2277 c row ↔ constraint_2277 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2278 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1308 row) * ((a_prime_bit c 1308 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2278_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2278 c row ↔ constraint_2278 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2279 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1309 row) * ((a_prime_bit c 1309 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2279_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2279 c row ↔ constraint_2279 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2280 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1310 row) * ((a_prime_bit c 1310 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2280_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2280 c row ↔ constraint_2280 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2281 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1311 row) * ((a_prime_bit c 1311 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2281_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2281 c row ↔ constraint_2281 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2282 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1312 row) * ((a_prime_bit c 1312 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2282_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2282 c row ↔ constraint_2282 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2283 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1313 row) * ((a_prime_bit c 1313 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2283_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2283 c row ↔ constraint_2283 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2284 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1314 row) * ((a_prime_bit c 1314 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2284_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2284 c row ↔ constraint_2284 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2285 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1315 row) * ((a_prime_bit c 1315 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2285_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2285 c row ↔ constraint_2285 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2286 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1316 row) * ((a_prime_bit c 1316 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2286_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2286 c row ↔ constraint_2286 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2287 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1317 row) * ((a_prime_bit c 1317 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2287_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2287 c row ↔ constraint_2287 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2288 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1318 row) * ((a_prime_bit c 1318 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2288_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2288 c row ↔ constraint_2288 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2289 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1319 row) * ((a_prime_bit c 1319 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2289_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2289 c row ↔ constraint_2289 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2290 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1320 row) * ((a_prime_bit c 1320 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2290_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2290 c row ↔ constraint_2290 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2291 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1321 row) * ((a_prime_bit c 1321 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2291_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2291 c row ↔ constraint_2291 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2292 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1322 row) * ((a_prime_bit c 1322 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2292_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2292 c row ↔ constraint_2292 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2293 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1323 row) * ((a_prime_bit c 1323 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2293_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2293 c row ↔ constraint_2293 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2294 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1324 row) * ((a_prime_bit c 1324 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2294_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2294 c row ↔ constraint_2294 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2295 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1325 row) * ((a_prime_bit c 1325 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2295_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2295 c row ↔ constraint_2295 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2296 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1326 row) * ((a_prime_bit c 1326 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2296_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2296 c row ↔ constraint_2296 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2297 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1327 row) * ((a_prime_bit c 1327 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2297_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2297 c row ↔ constraint_2297 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2298 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1328 row) * ((a_prime_bit c 1328 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2298_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2298 c row ↔ constraint_2298 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2299 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1329 row) * ((a_prime_bit c 1329 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2299_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2299 c row ↔ constraint_2299 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2300 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1330 row) * ((a_prime_bit c 1330 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2300_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2300 c row ↔ constraint_2300 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2301 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1331 row) * ((a_prime_bit c 1331 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2301_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2301 c row ↔ constraint_2301 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2302 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1332 row) * ((a_prime_bit c 1332 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2302_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2302 c row ↔ constraint_2302 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2303 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1333 row) * ((a_prime_bit c 1333 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2303_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2303 c row ↔ constraint_2303 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2304 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1334 row) * ((a_prime_bit c 1334 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2304_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2304 c row ↔ constraint_2304 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2305 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1335 row) * ((a_prime_bit c 1335 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2305_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2305 c row ↔ constraint_2305 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2306 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1336 row) * ((a_prime_bit c 1336 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2306_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2306 c row ↔ constraint_2306 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2307 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1337 row) * ((a_prime_bit c 1337 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2307_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2307 c row ↔ constraint_2307 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2308 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1338 row) * ((a_prime_bit c 1338 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2308_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2308 c row ↔ constraint_2308 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2309 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1339 row) * ((a_prime_bit c 1339 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2309_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2309 c row ↔ constraint_2309 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2310 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1340 row) * ((a_prime_bit c 1340 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2310_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2310 c row ↔ constraint_2310 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2311 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1341 row) * ((a_prime_bit c 1341 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2311_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2311 c row ↔ constraint_2311 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2312 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1342 row) * ((a_prime_bit c 1342 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2312_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2312 c row ↔ constraint_2312 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2313 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1343 row) * ((a_prime_bit c 1343 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2313_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2313 c row ↔ constraint_2313 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2314 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 225 545 2145 205 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2314_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2314 c row ↔ constraint_2314 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2315 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 241 561 2161 206 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2315_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2315 c row ↔ constraint_2315 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2316 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 257 577 2177 207 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2316_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2316 c row ↔ constraint_2316 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2317 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 273 593 2193 208 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2317_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2317 c row ↔ constraint_2317 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2318 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1344 row) * ((a_prime_bit c 1344 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2318_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2318 c row ↔ constraint_2318 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2319 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1345 row) * ((a_prime_bit c 1345 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2319_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2319 c row ↔ constraint_2319 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2320 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1346 row) * ((a_prime_bit c 1346 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2320_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2320 c row ↔ constraint_2320 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2321 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1347 row) * ((a_prime_bit c 1347 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2321_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2321 c row ↔ constraint_2321 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2322 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1348 row) * ((a_prime_bit c 1348 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2322_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2322 c row ↔ constraint_2322 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2323 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1349 row) * ((a_prime_bit c 1349 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2323_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2323 c row ↔ constraint_2323 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2324 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1350 row) * ((a_prime_bit c 1350 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2324_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2324 c row ↔ constraint_2324 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2325 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1351 row) * ((a_prime_bit c 1351 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2325_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2325 c row ↔ constraint_2325 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2326 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1352 row) * ((a_prime_bit c 1352 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2326_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2326 c row ↔ constraint_2326 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2327 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1353 row) * ((a_prime_bit c 1353 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2327_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2327 c row ↔ constraint_2327 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2328 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1354 row) * ((a_prime_bit c 1354 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2328_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2328 c row ↔ constraint_2328 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2329 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1355 row) * ((a_prime_bit c 1355 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2329_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2329 c row ↔ constraint_2329 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2330 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1356 row) * ((a_prime_bit c 1356 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2330_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2330 c row ↔ constraint_2330 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2331 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1357 row) * ((a_prime_bit c 1357 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2331_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2331 c row ↔ constraint_2331 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2332 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1358 row) * ((a_prime_bit c 1358 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2332_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2332 c row ↔ constraint_2332 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2333 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1359 row) * ((a_prime_bit c 1359 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2333_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2333 c row ↔ constraint_2333 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2334 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1360 row) * ((a_prime_bit c 1360 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2334_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2334 c row ↔ constraint_2334 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2335 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1361 row) * ((a_prime_bit c 1361 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2335_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2335 c row ↔ constraint_2335 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2336 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1362 row) * ((a_prime_bit c 1362 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2336_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2336 c row ↔ constraint_2336 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2337 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1363 row) * ((a_prime_bit c 1363 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2337_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2337 c row ↔ constraint_2337 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2338 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1364 row) * ((a_prime_bit c 1364 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2338_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2338 c row ↔ constraint_2338 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2339 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1365 row) * ((a_prime_bit c 1365 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2339_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2339 c row ↔ constraint_2339 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2340 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1366 row) * ((a_prime_bit c 1366 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2340_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2340 c row ↔ constraint_2340 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2341 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1367 row) * ((a_prime_bit c 1367 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2341_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2341 c row ↔ constraint_2341 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2342 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1368 row) * ((a_prime_bit c 1368 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2342_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2342 c row ↔ constraint_2342 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2343 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1369 row) * ((a_prime_bit c 1369 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2343_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2343 c row ↔ constraint_2343 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2344 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1370 row) * ((a_prime_bit c 1370 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2344_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2344 c row ↔ constraint_2344 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2345 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1371 row) * ((a_prime_bit c 1371 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2345_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2345 c row ↔ constraint_2345 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2346 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1372 row) * ((a_prime_bit c 1372 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2346_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2346 c row ↔ constraint_2346 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2347 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1373 row) * ((a_prime_bit c 1373 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2347_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2347 c row ↔ constraint_2347 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2348 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1374 row) * ((a_prime_bit c 1374 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2348_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2348 c row ↔ constraint_2348 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2349 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1375 row) * ((a_prime_bit c 1375 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2349_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2349 c row ↔ constraint_2349 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2350 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1376 row) * ((a_prime_bit c 1376 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2350_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2350 c row ↔ constraint_2350 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2351 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1377 row) * ((a_prime_bit c 1377 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2351_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2351 c row ↔ constraint_2351 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2352 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1378 row) * ((a_prime_bit c 1378 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2352_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2352 c row ↔ constraint_2352 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2353 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1379 row) * ((a_prime_bit c 1379 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2353_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2353 c row ↔ constraint_2353 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2354 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1380 row) * ((a_prime_bit c 1380 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2354_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2354 c row ↔ constraint_2354 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2355 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1381 row) * ((a_prime_bit c 1381 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2355_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2355 c row ↔ constraint_2355 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2356 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1382 row) * ((a_prime_bit c 1382 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2356_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2356 c row ↔ constraint_2356 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2357 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1383 row) * ((a_prime_bit c 1383 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2357_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2357 c row ↔ constraint_2357 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2358 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1384 row) * ((a_prime_bit c 1384 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2358_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2358 c row ↔ constraint_2358 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2359 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1385 row) * ((a_prime_bit c 1385 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2359_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2359 c row ↔ constraint_2359 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2360 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1386 row) * ((a_prime_bit c 1386 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2360_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2360 c row ↔ constraint_2360 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2361 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1387 row) * ((a_prime_bit c 1387 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2361_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2361 c row ↔ constraint_2361 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2362 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1388 row) * ((a_prime_bit c 1388 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2362_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2362 c row ↔ constraint_2362 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2363 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1389 row) * ((a_prime_bit c 1389 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2363_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2363 c row ↔ constraint_2363 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2364 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1390 row) * ((a_prime_bit c 1390 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2364_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2364 c row ↔ constraint_2364 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2365 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1391 row) * ((a_prime_bit c 1391 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2365_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2365 c row ↔ constraint_2365 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2366 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1392 row) * ((a_prime_bit c 1392 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2366_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2366 c row ↔ constraint_2366 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2367 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1393 row) * ((a_prime_bit c 1393 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2367_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2367 c row ↔ constraint_2367 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2368 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1394 row) * ((a_prime_bit c 1394 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2368_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2368 c row ↔ constraint_2368 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2369 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1395 row) * ((a_prime_bit c 1395 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2369_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2369 c row ↔ constraint_2369 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2370 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1396 row) * ((a_prime_bit c 1396 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2370_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2370 c row ↔ constraint_2370 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2371 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1397 row) * ((a_prime_bit c 1397 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2371_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2371 c row ↔ constraint_2371 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2372 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1398 row) * ((a_prime_bit c 1398 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2372_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2372 c row ↔ constraint_2372 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2373 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1399 row) * ((a_prime_bit c 1399 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2373_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2373 c row ↔ constraint_2373 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2374 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1400 row) * ((a_prime_bit c 1400 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2374_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2374 c row ↔ constraint_2374 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2375 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1401 row) * ((a_prime_bit c 1401 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2375_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2375 c row ↔ constraint_2375 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2376 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1402 row) * ((a_prime_bit c 1402 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2376_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2376 c row ↔ constraint_2376 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2377 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1403 row) * ((a_prime_bit c 1403 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2377_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2377 c row ↔ constraint_2377 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2378 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1404 row) * ((a_prime_bit c 1404 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2378_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2378 c row ↔ constraint_2378 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2379 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1405 row) * ((a_prime_bit c 1405 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2379_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2379 c row ↔ constraint_2379 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2380 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1406 row) * ((a_prime_bit c 1406 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2380_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2380 c row ↔ constraint_2380 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2381 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1407 row) * ((a_prime_bit c 1407 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2381_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2381 c row ↔ constraint_2381 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2382 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 289 609 2209 209 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2382_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2382 c row ↔ constraint_2382 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2383 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 305 625 2225 210 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2383_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2383 c row ↔ constraint_2383 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2384 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 321 641 2241 211 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2384_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2384 c row ↔ constraint_2384 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2385 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 337 657 2257 212 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2385_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2385 c row ↔ constraint_2385 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2386 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1408 row) * ((a_prime_bit c 1408 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2386_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2386 c row ↔ constraint_2386 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2387 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1409 row) * ((a_prime_bit c 1409 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2387_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2387 c row ↔ constraint_2387 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2388 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1410 row) * ((a_prime_bit c 1410 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2388_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2388 c row ↔ constraint_2388 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2389 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1411 row) * ((a_prime_bit c 1411 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2389_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2389 c row ↔ constraint_2389 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2390 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1412 row) * ((a_prime_bit c 1412 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2390_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2390 c row ↔ constraint_2390 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2391 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1413 row) * ((a_prime_bit c 1413 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2391_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2391 c row ↔ constraint_2391 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2392 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1414 row) * ((a_prime_bit c 1414 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2392_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2392 c row ↔ constraint_2392 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2393 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1415 row) * ((a_prime_bit c 1415 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2393_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2393 c row ↔ constraint_2393 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2394 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1416 row) * ((a_prime_bit c 1416 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2394_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2394 c row ↔ constraint_2394 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2395 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1417 row) * ((a_prime_bit c 1417 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2395_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2395 c row ↔ constraint_2395 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2396 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1418 row) * ((a_prime_bit c 1418 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2396_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2396 c row ↔ constraint_2396 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2397 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1419 row) * ((a_prime_bit c 1419 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2397_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2397 c row ↔ constraint_2397 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2398 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1420 row) * ((a_prime_bit c 1420 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2398_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2398 c row ↔ constraint_2398 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2399 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1421 row) * ((a_prime_bit c 1421 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2399_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2399 c row ↔ constraint_2399 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2400 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1422 row) * ((a_prime_bit c 1422 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2400_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2400 c row ↔ constraint_2400 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2401 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1423 row) * ((a_prime_bit c 1423 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2401_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2401 c row ↔ constraint_2401 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2402 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1424 row) * ((a_prime_bit c 1424 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2402_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2402 c row ↔ constraint_2402 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2403 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1425 row) * ((a_prime_bit c 1425 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2403_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2403 c row ↔ constraint_2403 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2404 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1426 row) * ((a_prime_bit c 1426 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2404_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2404 c row ↔ constraint_2404 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2405 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1427 row) * ((a_prime_bit c 1427 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2405_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2405 c row ↔ constraint_2405 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2406 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1428 row) * ((a_prime_bit c 1428 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2406_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2406 c row ↔ constraint_2406 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2407 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1429 row) * ((a_prime_bit c 1429 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2407_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2407 c row ↔ constraint_2407 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2408 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1430 row) * ((a_prime_bit c 1430 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2408_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2408 c row ↔ constraint_2408 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2409 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1431 row) * ((a_prime_bit c 1431 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2409_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2409 c row ↔ constraint_2409 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2410 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1432 row) * ((a_prime_bit c 1432 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2410_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2410 c row ↔ constraint_2410 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2411 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1433 row) * ((a_prime_bit c 1433 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2411_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2411 c row ↔ constraint_2411 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2412 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1434 row) * ((a_prime_bit c 1434 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2412_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2412 c row ↔ constraint_2412 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2413 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1435 row) * ((a_prime_bit c 1435 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2413_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2413 c row ↔ constraint_2413 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2414 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1436 row) * ((a_prime_bit c 1436 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2414_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2414 c row ↔ constraint_2414 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2415 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1437 row) * ((a_prime_bit c 1437 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2415_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2415 c row ↔ constraint_2415 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2416 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1438 row) * ((a_prime_bit c 1438 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2416_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2416 c row ↔ constraint_2416 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2417 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1439 row) * ((a_prime_bit c 1439 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2417_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2417 c row ↔ constraint_2417 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2418 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1440 row) * ((a_prime_bit c 1440 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2418_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2418 c row ↔ constraint_2418 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2419 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1441 row) * ((a_prime_bit c 1441 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2419_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2419 c row ↔ constraint_2419 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2420 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1442 row) * ((a_prime_bit c 1442 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2420_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2420 c row ↔ constraint_2420 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2421 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1443 row) * ((a_prime_bit c 1443 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2421_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2421 c row ↔ constraint_2421 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2422 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1444 row) * ((a_prime_bit c 1444 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2422_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2422 c row ↔ constraint_2422 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2423 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1445 row) * ((a_prime_bit c 1445 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2423_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2423 c row ↔ constraint_2423 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2424 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1446 row) * ((a_prime_bit c 1446 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2424_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2424 c row ↔ constraint_2424 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2425 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1447 row) * ((a_prime_bit c 1447 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2425_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2425 c row ↔ constraint_2425 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2426 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1448 row) * ((a_prime_bit c 1448 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2426_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2426 c row ↔ constraint_2426 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2427 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1449 row) * ((a_prime_bit c 1449 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2427_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2427 c row ↔ constraint_2427 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2428 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1450 row) * ((a_prime_bit c 1450 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2428_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2428 c row ↔ constraint_2428 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2429 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1451 row) * ((a_prime_bit c 1451 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2429_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2429 c row ↔ constraint_2429 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2430 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1452 row) * ((a_prime_bit c 1452 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2430_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2430 c row ↔ constraint_2430 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2431 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1453 row) * ((a_prime_bit c 1453 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2431_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2431 c row ↔ constraint_2431 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2432 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1454 row) * ((a_prime_bit c 1454 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2432_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2432 c row ↔ constraint_2432 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2433 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1455 row) * ((a_prime_bit c 1455 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2433_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2433 c row ↔ constraint_2433 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2434 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1456 row) * ((a_prime_bit c 1456 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2434_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2434 c row ↔ constraint_2434 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2435 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1457 row) * ((a_prime_bit c 1457 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2435_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2435 c row ↔ constraint_2435 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2436 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1458 row) * ((a_prime_bit c 1458 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2436_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2436 c row ↔ constraint_2436 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2437 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1459 row) * ((a_prime_bit c 1459 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2437_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2437 c row ↔ constraint_2437 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2438 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1460 row) * ((a_prime_bit c 1460 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2438_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2438 c row ↔ constraint_2438 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2439 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1461 row) * ((a_prime_bit c 1461 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2439_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2439 c row ↔ constraint_2439 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2440 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1462 row) * ((a_prime_bit c 1462 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2440_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2440 c row ↔ constraint_2440 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2441 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1463 row) * ((a_prime_bit c 1463 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2441_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2441 c row ↔ constraint_2441 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2442 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1464 row) * ((a_prime_bit c 1464 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2442_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2442 c row ↔ constraint_2442 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2443 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1465 row) * ((a_prime_bit c 1465 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2443_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2443 c row ↔ constraint_2443 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2444 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1466 row) * ((a_prime_bit c 1466 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2444_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2444 c row ↔ constraint_2444 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2445 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1467 row) * ((a_prime_bit c 1467 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2445_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2445 c row ↔ constraint_2445 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2446 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1468 row) * ((a_prime_bit c 1468 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2446_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2446 c row ↔ constraint_2446 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2447 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1469 row) * ((a_prime_bit c 1469 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2447_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2447 c row ↔ constraint_2447 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2448 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1470 row) * ((a_prime_bit c 1470 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2448_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2448 c row ↔ constraint_2448 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2449 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1471 row) * ((a_prime_bit c 1471 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2449_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2449 c row ↔ constraint_2449 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2450 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 353 673 2273 213 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2450_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2450 c row ↔ constraint_2450 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2451 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 369 689 2289 214 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2451_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2451 c row ↔ constraint_2451 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2452 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 385 705 2305 215 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2452_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2452 c row ↔ constraint_2452 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2453 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 401 721 2321 216 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2453_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2453 c row ↔ constraint_2453 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2454 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1472 row) * ((a_prime_bit c 1472 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2454_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2454 c row ↔ constraint_2454 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2455 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1473 row) * ((a_prime_bit c 1473 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2455_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2455 c row ↔ constraint_2455 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2456 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1474 row) * ((a_prime_bit c 1474 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2456_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2456 c row ↔ constraint_2456 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2457 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1475 row) * ((a_prime_bit c 1475 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2457_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2457 c row ↔ constraint_2457 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2458 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1476 row) * ((a_prime_bit c 1476 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2458_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2458 c row ↔ constraint_2458 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2459 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1477 row) * ((a_prime_bit c 1477 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2459_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2459 c row ↔ constraint_2459 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2460 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1478 row) * ((a_prime_bit c 1478 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2460_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2460 c row ↔ constraint_2460 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2461 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1479 row) * ((a_prime_bit c 1479 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2461_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2461 c row ↔ constraint_2461 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2462 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1480 row) * ((a_prime_bit c 1480 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2462_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2462 c row ↔ constraint_2462 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2463 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1481 row) * ((a_prime_bit c 1481 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2463_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2463 c row ↔ constraint_2463 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2464 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1482 row) * ((a_prime_bit c 1482 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2464_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2464 c row ↔ constraint_2464 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2465 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1483 row) * ((a_prime_bit c 1483 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2465_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2465 c row ↔ constraint_2465 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2466 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1484 row) * ((a_prime_bit c 1484 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2466_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2466 c row ↔ constraint_2466 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2467 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1485 row) * ((a_prime_bit c 1485 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2467_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2467 c row ↔ constraint_2467 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2468 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1486 row) * ((a_prime_bit c 1486 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2468_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2468 c row ↔ constraint_2468 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2469 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1487 row) * ((a_prime_bit c 1487 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2469_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2469 c row ↔ constraint_2469 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2470 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1488 row) * ((a_prime_bit c 1488 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2470_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2470 c row ↔ constraint_2470 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2471 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1489 row) * ((a_prime_bit c 1489 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2471_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2471 c row ↔ constraint_2471 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2472 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1490 row) * ((a_prime_bit c 1490 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2472_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2472 c row ↔ constraint_2472 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2473 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1491 row) * ((a_prime_bit c 1491 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2473_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2473 c row ↔ constraint_2473 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2474 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1492 row) * ((a_prime_bit c 1492 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2474_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2474 c row ↔ constraint_2474 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2475 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1493 row) * ((a_prime_bit c 1493 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2475_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2475 c row ↔ constraint_2475 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2476 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1494 row) * ((a_prime_bit c 1494 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2476_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2476 c row ↔ constraint_2476 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2477 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1495 row) * ((a_prime_bit c 1495 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2477_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2477 c row ↔ constraint_2477 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2478 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1496 row) * ((a_prime_bit c 1496 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2478_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2478 c row ↔ constraint_2478 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2479 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1497 row) * ((a_prime_bit c 1497 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2479_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2479 c row ↔ constraint_2479 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2480 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1498 row) * ((a_prime_bit c 1498 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2480_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2480 c row ↔ constraint_2480 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2481 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1499 row) * ((a_prime_bit c 1499 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2481_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2481 c row ↔ constraint_2481 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2482 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1500 row) * ((a_prime_bit c 1500 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2482_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2482 c row ↔ constraint_2482 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2483 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1501 row) * ((a_prime_bit c 1501 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2483_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2483 c row ↔ constraint_2483 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2484 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1502 row) * ((a_prime_bit c 1502 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2484_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2484 c row ↔ constraint_2484 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2485 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1503 row) * ((a_prime_bit c 1503 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2485_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2485 c row ↔ constraint_2485 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2486 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1504 row) * ((a_prime_bit c 1504 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2486_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2486 c row ↔ constraint_2486 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2487 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1505 row) * ((a_prime_bit c 1505 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2487_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2487 c row ↔ constraint_2487 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2488 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1506 row) * ((a_prime_bit c 1506 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2488_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2488 c row ↔ constraint_2488 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2489 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1507 row) * ((a_prime_bit c 1507 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2489_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2489 c row ↔ constraint_2489 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
