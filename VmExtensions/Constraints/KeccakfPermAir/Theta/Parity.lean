import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## θ parity check constraints: diff*(diff-2)*(diff-4)=0 -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2590 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 0 row) + (a_prime_bit c 320 row)) + (a_prime_bit c 640 row)) + (a_prime_bit c 960 row)) + (a_prime_bit c 1280 row)) - (c_prime_bit c 0 row)) * (((((((a_prime_bit c 0 row) + (a_prime_bit c 320 row)) + (a_prime_bit c 640 row)) + (a_prime_bit c 960 row)) + (a_prime_bit c 1280 row)) - (c_prime_bit c 0 row)) - 2)) * (((((((a_prime_bit c 0 row) + (a_prime_bit c 320 row)) + (a_prime_bit c 640 row)) + (a_prime_bit c 960 row)) + (a_prime_bit c 1280 row)) - (c_prime_bit c 0 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2590_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2590 c row ↔ constraint_2590 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2591 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 1 row) + (a_prime_bit c 321 row)) + (a_prime_bit c 641 row)) + (a_prime_bit c 961 row)) + (a_prime_bit c 1281 row)) - (c_prime_bit c 1 row)) * (((((((a_prime_bit c 1 row) + (a_prime_bit c 321 row)) + (a_prime_bit c 641 row)) + (a_prime_bit c 961 row)) + (a_prime_bit c 1281 row)) - (c_prime_bit c 1 row)) - 2)) * (((((((a_prime_bit c 1 row) + (a_prime_bit c 321 row)) + (a_prime_bit c 641 row)) + (a_prime_bit c 961 row)) + (a_prime_bit c 1281 row)) - (c_prime_bit c 1 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2591_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2591 c row ↔ constraint_2591 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2592 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 2 row) + (a_prime_bit c 322 row)) + (a_prime_bit c 642 row)) + (a_prime_bit c 962 row)) + (a_prime_bit c 1282 row)) - (c_prime_bit c 2 row)) * (((((((a_prime_bit c 2 row) + (a_prime_bit c 322 row)) + (a_prime_bit c 642 row)) + (a_prime_bit c 962 row)) + (a_prime_bit c 1282 row)) - (c_prime_bit c 2 row)) - 2)) * (((((((a_prime_bit c 2 row) + (a_prime_bit c 322 row)) + (a_prime_bit c 642 row)) + (a_prime_bit c 962 row)) + (a_prime_bit c 1282 row)) - (c_prime_bit c 2 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2592_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2592 c row ↔ constraint_2592 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2593 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 3 row) + (a_prime_bit c 323 row)) + (a_prime_bit c 643 row)) + (a_prime_bit c 963 row)) + (a_prime_bit c 1283 row)) - (c_prime_bit c 3 row)) * (((((((a_prime_bit c 3 row) + (a_prime_bit c 323 row)) + (a_prime_bit c 643 row)) + (a_prime_bit c 963 row)) + (a_prime_bit c 1283 row)) - (c_prime_bit c 3 row)) - 2)) * (((((((a_prime_bit c 3 row) + (a_prime_bit c 323 row)) + (a_prime_bit c 643 row)) + (a_prime_bit c 963 row)) + (a_prime_bit c 1283 row)) - (c_prime_bit c 3 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2593_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2593 c row ↔ constraint_2593 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2594 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 4 row) + (a_prime_bit c 324 row)) + (a_prime_bit c 644 row)) + (a_prime_bit c 964 row)) + (a_prime_bit c 1284 row)) - (c_prime_bit c 4 row)) * (((((((a_prime_bit c 4 row) + (a_prime_bit c 324 row)) + (a_prime_bit c 644 row)) + (a_prime_bit c 964 row)) + (a_prime_bit c 1284 row)) - (c_prime_bit c 4 row)) - 2)) * (((((((a_prime_bit c 4 row) + (a_prime_bit c 324 row)) + (a_prime_bit c 644 row)) + (a_prime_bit c 964 row)) + (a_prime_bit c 1284 row)) - (c_prime_bit c 4 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2594_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2594 c row ↔ constraint_2594 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2595 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 5 row) + (a_prime_bit c 325 row)) + (a_prime_bit c 645 row)) + (a_prime_bit c 965 row)) + (a_prime_bit c 1285 row)) - (c_prime_bit c 5 row)) * (((((((a_prime_bit c 5 row) + (a_prime_bit c 325 row)) + (a_prime_bit c 645 row)) + (a_prime_bit c 965 row)) + (a_prime_bit c 1285 row)) - (c_prime_bit c 5 row)) - 2)) * (((((((a_prime_bit c 5 row) + (a_prime_bit c 325 row)) + (a_prime_bit c 645 row)) + (a_prime_bit c 965 row)) + (a_prime_bit c 1285 row)) - (c_prime_bit c 5 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2595_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2595 c row ↔ constraint_2595 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2596 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 6 row) + (a_prime_bit c 326 row)) + (a_prime_bit c 646 row)) + (a_prime_bit c 966 row)) + (a_prime_bit c 1286 row)) - (c_prime_bit c 6 row)) * (((((((a_prime_bit c 6 row) + (a_prime_bit c 326 row)) + (a_prime_bit c 646 row)) + (a_prime_bit c 966 row)) + (a_prime_bit c 1286 row)) - (c_prime_bit c 6 row)) - 2)) * (((((((a_prime_bit c 6 row) + (a_prime_bit c 326 row)) + (a_prime_bit c 646 row)) + (a_prime_bit c 966 row)) + (a_prime_bit c 1286 row)) - (c_prime_bit c 6 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2596_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2596 c row ↔ constraint_2596 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2597 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 7 row) + (a_prime_bit c 327 row)) + (a_prime_bit c 647 row)) + (a_prime_bit c 967 row)) + (a_prime_bit c 1287 row)) - (c_prime_bit c 7 row)) * (((((((a_prime_bit c 7 row) + (a_prime_bit c 327 row)) + (a_prime_bit c 647 row)) + (a_prime_bit c 967 row)) + (a_prime_bit c 1287 row)) - (c_prime_bit c 7 row)) - 2)) * (((((((a_prime_bit c 7 row) + (a_prime_bit c 327 row)) + (a_prime_bit c 647 row)) + (a_prime_bit c 967 row)) + (a_prime_bit c 1287 row)) - (c_prime_bit c 7 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2597_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2597 c row ↔ constraint_2597 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2598 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 8 row) + (a_prime_bit c 328 row)) + (a_prime_bit c 648 row)) + (a_prime_bit c 968 row)) + (a_prime_bit c 1288 row)) - (c_prime_bit c 8 row)) * (((((((a_prime_bit c 8 row) + (a_prime_bit c 328 row)) + (a_prime_bit c 648 row)) + (a_prime_bit c 968 row)) + (a_prime_bit c 1288 row)) - (c_prime_bit c 8 row)) - 2)) * (((((((a_prime_bit c 8 row) + (a_prime_bit c 328 row)) + (a_prime_bit c 648 row)) + (a_prime_bit c 968 row)) + (a_prime_bit c 1288 row)) - (c_prime_bit c 8 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2598_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2598 c row ↔ constraint_2598 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2599 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 9 row) + (a_prime_bit c 329 row)) + (a_prime_bit c 649 row)) + (a_prime_bit c 969 row)) + (a_prime_bit c 1289 row)) - (c_prime_bit c 9 row)) * (((((((a_prime_bit c 9 row) + (a_prime_bit c 329 row)) + (a_prime_bit c 649 row)) + (a_prime_bit c 969 row)) + (a_prime_bit c 1289 row)) - (c_prime_bit c 9 row)) - 2)) * (((((((a_prime_bit c 9 row) + (a_prime_bit c 329 row)) + (a_prime_bit c 649 row)) + (a_prime_bit c 969 row)) + (a_prime_bit c 1289 row)) - (c_prime_bit c 9 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2599_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2599 c row ↔ constraint_2599 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2600 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 10 row) + (a_prime_bit c 330 row)) + (a_prime_bit c 650 row)) + (a_prime_bit c 970 row)) + (a_prime_bit c 1290 row)) - (c_prime_bit c 10 row)) * (((((((a_prime_bit c 10 row) + (a_prime_bit c 330 row)) + (a_prime_bit c 650 row)) + (a_prime_bit c 970 row)) + (a_prime_bit c 1290 row)) - (c_prime_bit c 10 row)) - 2)) * (((((((a_prime_bit c 10 row) + (a_prime_bit c 330 row)) + (a_prime_bit c 650 row)) + (a_prime_bit c 970 row)) + (a_prime_bit c 1290 row)) - (c_prime_bit c 10 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2600_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2600 c row ↔ constraint_2600 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2601 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 11 row) + (a_prime_bit c 331 row)) + (a_prime_bit c 651 row)) + (a_prime_bit c 971 row)) + (a_prime_bit c 1291 row)) - (c_prime_bit c 11 row)) * (((((((a_prime_bit c 11 row) + (a_prime_bit c 331 row)) + (a_prime_bit c 651 row)) + (a_prime_bit c 971 row)) + (a_prime_bit c 1291 row)) - (c_prime_bit c 11 row)) - 2)) * (((((((a_prime_bit c 11 row) + (a_prime_bit c 331 row)) + (a_prime_bit c 651 row)) + (a_prime_bit c 971 row)) + (a_prime_bit c 1291 row)) - (c_prime_bit c 11 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2601_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2601 c row ↔ constraint_2601 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2602 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 12 row) + (a_prime_bit c 332 row)) + (a_prime_bit c 652 row)) + (a_prime_bit c 972 row)) + (a_prime_bit c 1292 row)) - (c_prime_bit c 12 row)) * (((((((a_prime_bit c 12 row) + (a_prime_bit c 332 row)) + (a_prime_bit c 652 row)) + (a_prime_bit c 972 row)) + (a_prime_bit c 1292 row)) - (c_prime_bit c 12 row)) - 2)) * (((((((a_prime_bit c 12 row) + (a_prime_bit c 332 row)) + (a_prime_bit c 652 row)) + (a_prime_bit c 972 row)) + (a_prime_bit c 1292 row)) - (c_prime_bit c 12 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2602_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2602 c row ↔ constraint_2602 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2603 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 13 row) + (a_prime_bit c 333 row)) + (a_prime_bit c 653 row)) + (a_prime_bit c 973 row)) + (a_prime_bit c 1293 row)) - (c_prime_bit c 13 row)) * (((((((a_prime_bit c 13 row) + (a_prime_bit c 333 row)) + (a_prime_bit c 653 row)) + (a_prime_bit c 973 row)) + (a_prime_bit c 1293 row)) - (c_prime_bit c 13 row)) - 2)) * (((((((a_prime_bit c 13 row) + (a_prime_bit c 333 row)) + (a_prime_bit c 653 row)) + (a_prime_bit c 973 row)) + (a_prime_bit c 1293 row)) - (c_prime_bit c 13 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2603_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2603 c row ↔ constraint_2603 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2604 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 14 row) + (a_prime_bit c 334 row)) + (a_prime_bit c 654 row)) + (a_prime_bit c 974 row)) + (a_prime_bit c 1294 row)) - (c_prime_bit c 14 row)) * (((((((a_prime_bit c 14 row) + (a_prime_bit c 334 row)) + (a_prime_bit c 654 row)) + (a_prime_bit c 974 row)) + (a_prime_bit c 1294 row)) - (c_prime_bit c 14 row)) - 2)) * (((((((a_prime_bit c 14 row) + (a_prime_bit c 334 row)) + (a_prime_bit c 654 row)) + (a_prime_bit c 974 row)) + (a_prime_bit c 1294 row)) - (c_prime_bit c 14 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2604_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2604 c row ↔ constraint_2604 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2605 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 15 row) + (a_prime_bit c 335 row)) + (a_prime_bit c 655 row)) + (a_prime_bit c 975 row)) + (a_prime_bit c 1295 row)) - (c_prime_bit c 15 row)) * (((((((a_prime_bit c 15 row) + (a_prime_bit c 335 row)) + (a_prime_bit c 655 row)) + (a_prime_bit c 975 row)) + (a_prime_bit c 1295 row)) - (c_prime_bit c 15 row)) - 2)) * (((((((a_prime_bit c 15 row) + (a_prime_bit c 335 row)) + (a_prime_bit c 655 row)) + (a_prime_bit c 975 row)) + (a_prime_bit c 1295 row)) - (c_prime_bit c 15 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2605_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2605 c row ↔ constraint_2605 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2606 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 16 row) + (a_prime_bit c 336 row)) + (a_prime_bit c 656 row)) + (a_prime_bit c 976 row)) + (a_prime_bit c 1296 row)) - (c_prime_bit c 16 row)) * (((((((a_prime_bit c 16 row) + (a_prime_bit c 336 row)) + (a_prime_bit c 656 row)) + (a_prime_bit c 976 row)) + (a_prime_bit c 1296 row)) - (c_prime_bit c 16 row)) - 2)) * (((((((a_prime_bit c 16 row) + (a_prime_bit c 336 row)) + (a_prime_bit c 656 row)) + (a_prime_bit c 976 row)) + (a_prime_bit c 1296 row)) - (c_prime_bit c 16 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2606_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2606 c row ↔ constraint_2606 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2607 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 17 row) + (a_prime_bit c 337 row)) + (a_prime_bit c 657 row)) + (a_prime_bit c 977 row)) + (a_prime_bit c 1297 row)) - (c_prime_bit c 17 row)) * (((((((a_prime_bit c 17 row) + (a_prime_bit c 337 row)) + (a_prime_bit c 657 row)) + (a_prime_bit c 977 row)) + (a_prime_bit c 1297 row)) - (c_prime_bit c 17 row)) - 2)) * (((((((a_prime_bit c 17 row) + (a_prime_bit c 337 row)) + (a_prime_bit c 657 row)) + (a_prime_bit c 977 row)) + (a_prime_bit c 1297 row)) - (c_prime_bit c 17 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2607_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2607 c row ↔ constraint_2607 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2608 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 18 row) + (a_prime_bit c 338 row)) + (a_prime_bit c 658 row)) + (a_prime_bit c 978 row)) + (a_prime_bit c 1298 row)) - (c_prime_bit c 18 row)) * (((((((a_prime_bit c 18 row) + (a_prime_bit c 338 row)) + (a_prime_bit c 658 row)) + (a_prime_bit c 978 row)) + (a_prime_bit c 1298 row)) - (c_prime_bit c 18 row)) - 2)) * (((((((a_prime_bit c 18 row) + (a_prime_bit c 338 row)) + (a_prime_bit c 658 row)) + (a_prime_bit c 978 row)) + (a_prime_bit c 1298 row)) - (c_prime_bit c 18 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2608_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2608 c row ↔ constraint_2608 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2609 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 19 row) + (a_prime_bit c 339 row)) + (a_prime_bit c 659 row)) + (a_prime_bit c 979 row)) + (a_prime_bit c 1299 row)) - (c_prime_bit c 19 row)) * (((((((a_prime_bit c 19 row) + (a_prime_bit c 339 row)) + (a_prime_bit c 659 row)) + (a_prime_bit c 979 row)) + (a_prime_bit c 1299 row)) - (c_prime_bit c 19 row)) - 2)) * (((((((a_prime_bit c 19 row) + (a_prime_bit c 339 row)) + (a_prime_bit c 659 row)) + (a_prime_bit c 979 row)) + (a_prime_bit c 1299 row)) - (c_prime_bit c 19 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2609_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2609 c row ↔ constraint_2609 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2610 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 20 row) + (a_prime_bit c 340 row)) + (a_prime_bit c 660 row)) + (a_prime_bit c 980 row)) + (a_prime_bit c 1300 row)) - (c_prime_bit c 20 row)) * (((((((a_prime_bit c 20 row) + (a_prime_bit c 340 row)) + (a_prime_bit c 660 row)) + (a_prime_bit c 980 row)) + (a_prime_bit c 1300 row)) - (c_prime_bit c 20 row)) - 2)) * (((((((a_prime_bit c 20 row) + (a_prime_bit c 340 row)) + (a_prime_bit c 660 row)) + (a_prime_bit c 980 row)) + (a_prime_bit c 1300 row)) - (c_prime_bit c 20 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2610_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2610 c row ↔ constraint_2610 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2611 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 21 row) + (a_prime_bit c 341 row)) + (a_prime_bit c 661 row)) + (a_prime_bit c 981 row)) + (a_prime_bit c 1301 row)) - (c_prime_bit c 21 row)) * (((((((a_prime_bit c 21 row) + (a_prime_bit c 341 row)) + (a_prime_bit c 661 row)) + (a_prime_bit c 981 row)) + (a_prime_bit c 1301 row)) - (c_prime_bit c 21 row)) - 2)) * (((((((a_prime_bit c 21 row) + (a_prime_bit c 341 row)) + (a_prime_bit c 661 row)) + (a_prime_bit c 981 row)) + (a_prime_bit c 1301 row)) - (c_prime_bit c 21 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2611_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2611 c row ↔ constraint_2611 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2612 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 22 row) + (a_prime_bit c 342 row)) + (a_prime_bit c 662 row)) + (a_prime_bit c 982 row)) + (a_prime_bit c 1302 row)) - (c_prime_bit c 22 row)) * (((((((a_prime_bit c 22 row) + (a_prime_bit c 342 row)) + (a_prime_bit c 662 row)) + (a_prime_bit c 982 row)) + (a_prime_bit c 1302 row)) - (c_prime_bit c 22 row)) - 2)) * (((((((a_prime_bit c 22 row) + (a_prime_bit c 342 row)) + (a_prime_bit c 662 row)) + (a_prime_bit c 982 row)) + (a_prime_bit c 1302 row)) - (c_prime_bit c 22 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2612_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2612 c row ↔ constraint_2612 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2613 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 23 row) + (a_prime_bit c 343 row)) + (a_prime_bit c 663 row)) + (a_prime_bit c 983 row)) + (a_prime_bit c 1303 row)) - (c_prime_bit c 23 row)) * (((((((a_prime_bit c 23 row) + (a_prime_bit c 343 row)) + (a_prime_bit c 663 row)) + (a_prime_bit c 983 row)) + (a_prime_bit c 1303 row)) - (c_prime_bit c 23 row)) - 2)) * (((((((a_prime_bit c 23 row) + (a_prime_bit c 343 row)) + (a_prime_bit c 663 row)) + (a_prime_bit c 983 row)) + (a_prime_bit c 1303 row)) - (c_prime_bit c 23 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2613_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2613 c row ↔ constraint_2613 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2614 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 24 row) + (a_prime_bit c 344 row)) + (a_prime_bit c 664 row)) + (a_prime_bit c 984 row)) + (a_prime_bit c 1304 row)) - (c_prime_bit c 24 row)) * (((((((a_prime_bit c 24 row) + (a_prime_bit c 344 row)) + (a_prime_bit c 664 row)) + (a_prime_bit c 984 row)) + (a_prime_bit c 1304 row)) - (c_prime_bit c 24 row)) - 2)) * (((((((a_prime_bit c 24 row) + (a_prime_bit c 344 row)) + (a_prime_bit c 664 row)) + (a_prime_bit c 984 row)) + (a_prime_bit c 1304 row)) - (c_prime_bit c 24 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2614_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2614 c row ↔ constraint_2614 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2615 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 25 row) + (a_prime_bit c 345 row)) + (a_prime_bit c 665 row)) + (a_prime_bit c 985 row)) + (a_prime_bit c 1305 row)) - (c_prime_bit c 25 row)) * (((((((a_prime_bit c 25 row) + (a_prime_bit c 345 row)) + (a_prime_bit c 665 row)) + (a_prime_bit c 985 row)) + (a_prime_bit c 1305 row)) - (c_prime_bit c 25 row)) - 2)) * (((((((a_prime_bit c 25 row) + (a_prime_bit c 345 row)) + (a_prime_bit c 665 row)) + (a_prime_bit c 985 row)) + (a_prime_bit c 1305 row)) - (c_prime_bit c 25 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2615_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2615 c row ↔ constraint_2615 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2616 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 26 row) + (a_prime_bit c 346 row)) + (a_prime_bit c 666 row)) + (a_prime_bit c 986 row)) + (a_prime_bit c 1306 row)) - (c_prime_bit c 26 row)) * (((((((a_prime_bit c 26 row) + (a_prime_bit c 346 row)) + (a_prime_bit c 666 row)) + (a_prime_bit c 986 row)) + (a_prime_bit c 1306 row)) - (c_prime_bit c 26 row)) - 2)) * (((((((a_prime_bit c 26 row) + (a_prime_bit c 346 row)) + (a_prime_bit c 666 row)) + (a_prime_bit c 986 row)) + (a_prime_bit c 1306 row)) - (c_prime_bit c 26 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2616_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2616 c row ↔ constraint_2616 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2617 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 27 row) + (a_prime_bit c 347 row)) + (a_prime_bit c 667 row)) + (a_prime_bit c 987 row)) + (a_prime_bit c 1307 row)) - (c_prime_bit c 27 row)) * (((((((a_prime_bit c 27 row) + (a_prime_bit c 347 row)) + (a_prime_bit c 667 row)) + (a_prime_bit c 987 row)) + (a_prime_bit c 1307 row)) - (c_prime_bit c 27 row)) - 2)) * (((((((a_prime_bit c 27 row) + (a_prime_bit c 347 row)) + (a_prime_bit c 667 row)) + (a_prime_bit c 987 row)) + (a_prime_bit c 1307 row)) - (c_prime_bit c 27 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2617_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2617 c row ↔ constraint_2617 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2618 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 28 row) + (a_prime_bit c 348 row)) + (a_prime_bit c 668 row)) + (a_prime_bit c 988 row)) + (a_prime_bit c 1308 row)) - (c_prime_bit c 28 row)) * (((((((a_prime_bit c 28 row) + (a_prime_bit c 348 row)) + (a_prime_bit c 668 row)) + (a_prime_bit c 988 row)) + (a_prime_bit c 1308 row)) - (c_prime_bit c 28 row)) - 2)) * (((((((a_prime_bit c 28 row) + (a_prime_bit c 348 row)) + (a_prime_bit c 668 row)) + (a_prime_bit c 988 row)) + (a_prime_bit c 1308 row)) - (c_prime_bit c 28 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2618_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2618 c row ↔ constraint_2618 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2619 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 29 row) + (a_prime_bit c 349 row)) + (a_prime_bit c 669 row)) + (a_prime_bit c 989 row)) + (a_prime_bit c 1309 row)) - (c_prime_bit c 29 row)) * (((((((a_prime_bit c 29 row) + (a_prime_bit c 349 row)) + (a_prime_bit c 669 row)) + (a_prime_bit c 989 row)) + (a_prime_bit c 1309 row)) - (c_prime_bit c 29 row)) - 2)) * (((((((a_prime_bit c 29 row) + (a_prime_bit c 349 row)) + (a_prime_bit c 669 row)) + (a_prime_bit c 989 row)) + (a_prime_bit c 1309 row)) - (c_prime_bit c 29 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2619_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2619 c row ↔ constraint_2619 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2620 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 30 row) + (a_prime_bit c 350 row)) + (a_prime_bit c 670 row)) + (a_prime_bit c 990 row)) + (a_prime_bit c 1310 row)) - (c_prime_bit c 30 row)) * (((((((a_prime_bit c 30 row) + (a_prime_bit c 350 row)) + (a_prime_bit c 670 row)) + (a_prime_bit c 990 row)) + (a_prime_bit c 1310 row)) - (c_prime_bit c 30 row)) - 2)) * (((((((a_prime_bit c 30 row) + (a_prime_bit c 350 row)) + (a_prime_bit c 670 row)) + (a_prime_bit c 990 row)) + (a_prime_bit c 1310 row)) - (c_prime_bit c 30 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2620_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2620 c row ↔ constraint_2620 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2621 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 31 row) + (a_prime_bit c 351 row)) + (a_prime_bit c 671 row)) + (a_prime_bit c 991 row)) + (a_prime_bit c 1311 row)) - (c_prime_bit c 31 row)) * (((((((a_prime_bit c 31 row) + (a_prime_bit c 351 row)) + (a_prime_bit c 671 row)) + (a_prime_bit c 991 row)) + (a_prime_bit c 1311 row)) - (c_prime_bit c 31 row)) - 2)) * (((((((a_prime_bit c 31 row) + (a_prime_bit c 351 row)) + (a_prime_bit c 671 row)) + (a_prime_bit c 991 row)) + (a_prime_bit c 1311 row)) - (c_prime_bit c 31 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2621_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2621 c row ↔ constraint_2621 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2622 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 32 row) + (a_prime_bit c 352 row)) + (a_prime_bit c 672 row)) + (a_prime_bit c 992 row)) + (a_prime_bit c 1312 row)) - (c_prime_bit c 32 row)) * (((((((a_prime_bit c 32 row) + (a_prime_bit c 352 row)) + (a_prime_bit c 672 row)) + (a_prime_bit c 992 row)) + (a_prime_bit c 1312 row)) - (c_prime_bit c 32 row)) - 2)) * (((((((a_prime_bit c 32 row) + (a_prime_bit c 352 row)) + (a_prime_bit c 672 row)) + (a_prime_bit c 992 row)) + (a_prime_bit c 1312 row)) - (c_prime_bit c 32 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2622_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2622 c row ↔ constraint_2622 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2623 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 33 row) + (a_prime_bit c 353 row)) + (a_prime_bit c 673 row)) + (a_prime_bit c 993 row)) + (a_prime_bit c 1313 row)) - (c_prime_bit c 33 row)) * (((((((a_prime_bit c 33 row) + (a_prime_bit c 353 row)) + (a_prime_bit c 673 row)) + (a_prime_bit c 993 row)) + (a_prime_bit c 1313 row)) - (c_prime_bit c 33 row)) - 2)) * (((((((a_prime_bit c 33 row) + (a_prime_bit c 353 row)) + (a_prime_bit c 673 row)) + (a_prime_bit c 993 row)) + (a_prime_bit c 1313 row)) - (c_prime_bit c 33 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2623_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2623 c row ↔ constraint_2623 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2624 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 34 row) + (a_prime_bit c 354 row)) + (a_prime_bit c 674 row)) + (a_prime_bit c 994 row)) + (a_prime_bit c 1314 row)) - (c_prime_bit c 34 row)) * (((((((a_prime_bit c 34 row) + (a_prime_bit c 354 row)) + (a_prime_bit c 674 row)) + (a_prime_bit c 994 row)) + (a_prime_bit c 1314 row)) - (c_prime_bit c 34 row)) - 2)) * (((((((a_prime_bit c 34 row) + (a_prime_bit c 354 row)) + (a_prime_bit c 674 row)) + (a_prime_bit c 994 row)) + (a_prime_bit c 1314 row)) - (c_prime_bit c 34 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2624_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2624 c row ↔ constraint_2624 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2625 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 35 row) + (a_prime_bit c 355 row)) + (a_prime_bit c 675 row)) + (a_prime_bit c 995 row)) + (a_prime_bit c 1315 row)) - (c_prime_bit c 35 row)) * (((((((a_prime_bit c 35 row) + (a_prime_bit c 355 row)) + (a_prime_bit c 675 row)) + (a_prime_bit c 995 row)) + (a_prime_bit c 1315 row)) - (c_prime_bit c 35 row)) - 2)) * (((((((a_prime_bit c 35 row) + (a_prime_bit c 355 row)) + (a_prime_bit c 675 row)) + (a_prime_bit c 995 row)) + (a_prime_bit c 1315 row)) - (c_prime_bit c 35 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2625_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2625 c row ↔ constraint_2625 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2626 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 36 row) + (a_prime_bit c 356 row)) + (a_prime_bit c 676 row)) + (a_prime_bit c 996 row)) + (a_prime_bit c 1316 row)) - (c_prime_bit c 36 row)) * (((((((a_prime_bit c 36 row) + (a_prime_bit c 356 row)) + (a_prime_bit c 676 row)) + (a_prime_bit c 996 row)) + (a_prime_bit c 1316 row)) - (c_prime_bit c 36 row)) - 2)) * (((((((a_prime_bit c 36 row) + (a_prime_bit c 356 row)) + (a_prime_bit c 676 row)) + (a_prime_bit c 996 row)) + (a_prime_bit c 1316 row)) - (c_prime_bit c 36 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2626_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2626 c row ↔ constraint_2626 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2627 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 37 row) + (a_prime_bit c 357 row)) + (a_prime_bit c 677 row)) + (a_prime_bit c 997 row)) + (a_prime_bit c 1317 row)) - (c_prime_bit c 37 row)) * (((((((a_prime_bit c 37 row) + (a_prime_bit c 357 row)) + (a_prime_bit c 677 row)) + (a_prime_bit c 997 row)) + (a_prime_bit c 1317 row)) - (c_prime_bit c 37 row)) - 2)) * (((((((a_prime_bit c 37 row) + (a_prime_bit c 357 row)) + (a_prime_bit c 677 row)) + (a_prime_bit c 997 row)) + (a_prime_bit c 1317 row)) - (c_prime_bit c 37 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2627_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2627 c row ↔ constraint_2627 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2628 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 38 row) + (a_prime_bit c 358 row)) + (a_prime_bit c 678 row)) + (a_prime_bit c 998 row)) + (a_prime_bit c 1318 row)) - (c_prime_bit c 38 row)) * (((((((a_prime_bit c 38 row) + (a_prime_bit c 358 row)) + (a_prime_bit c 678 row)) + (a_prime_bit c 998 row)) + (a_prime_bit c 1318 row)) - (c_prime_bit c 38 row)) - 2)) * (((((((a_prime_bit c 38 row) + (a_prime_bit c 358 row)) + (a_prime_bit c 678 row)) + (a_prime_bit c 998 row)) + (a_prime_bit c 1318 row)) - (c_prime_bit c 38 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2628_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2628 c row ↔ constraint_2628 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2629 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 39 row) + (a_prime_bit c 359 row)) + (a_prime_bit c 679 row)) + (a_prime_bit c 999 row)) + (a_prime_bit c 1319 row)) - (c_prime_bit c 39 row)) * (((((((a_prime_bit c 39 row) + (a_prime_bit c 359 row)) + (a_prime_bit c 679 row)) + (a_prime_bit c 999 row)) + (a_prime_bit c 1319 row)) - (c_prime_bit c 39 row)) - 2)) * (((((((a_prime_bit c 39 row) + (a_prime_bit c 359 row)) + (a_prime_bit c 679 row)) + (a_prime_bit c 999 row)) + (a_prime_bit c 1319 row)) - (c_prime_bit c 39 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2629_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2629 c row ↔ constraint_2629 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2630 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 40 row) + (a_prime_bit c 360 row)) + (a_prime_bit c 680 row)) + (a_prime_bit c 1000 row)) + (a_prime_bit c 1320 row)) - (c_prime_bit c 40 row)) * (((((((a_prime_bit c 40 row) + (a_prime_bit c 360 row)) + (a_prime_bit c 680 row)) + (a_prime_bit c 1000 row)) + (a_prime_bit c 1320 row)) - (c_prime_bit c 40 row)) - 2)) * (((((((a_prime_bit c 40 row) + (a_prime_bit c 360 row)) + (a_prime_bit c 680 row)) + (a_prime_bit c 1000 row)) + (a_prime_bit c 1320 row)) - (c_prime_bit c 40 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2630_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2630 c row ↔ constraint_2630 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2631 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 41 row) + (a_prime_bit c 361 row)) + (a_prime_bit c 681 row)) + (a_prime_bit c 1001 row)) + (a_prime_bit c 1321 row)) - (c_prime_bit c 41 row)) * (((((((a_prime_bit c 41 row) + (a_prime_bit c 361 row)) + (a_prime_bit c 681 row)) + (a_prime_bit c 1001 row)) + (a_prime_bit c 1321 row)) - (c_prime_bit c 41 row)) - 2)) * (((((((a_prime_bit c 41 row) + (a_prime_bit c 361 row)) + (a_prime_bit c 681 row)) + (a_prime_bit c 1001 row)) + (a_prime_bit c 1321 row)) - (c_prime_bit c 41 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2631_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2631 c row ↔ constraint_2631 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2632 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 42 row) + (a_prime_bit c 362 row)) + (a_prime_bit c 682 row)) + (a_prime_bit c 1002 row)) + (a_prime_bit c 1322 row)) - (c_prime_bit c 42 row)) * (((((((a_prime_bit c 42 row) + (a_prime_bit c 362 row)) + (a_prime_bit c 682 row)) + (a_prime_bit c 1002 row)) + (a_prime_bit c 1322 row)) - (c_prime_bit c 42 row)) - 2)) * (((((((a_prime_bit c 42 row) + (a_prime_bit c 362 row)) + (a_prime_bit c 682 row)) + (a_prime_bit c 1002 row)) + (a_prime_bit c 1322 row)) - (c_prime_bit c 42 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2632_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2632 c row ↔ constraint_2632 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2633 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 43 row) + (a_prime_bit c 363 row)) + (a_prime_bit c 683 row)) + (a_prime_bit c 1003 row)) + (a_prime_bit c 1323 row)) - (c_prime_bit c 43 row)) * (((((((a_prime_bit c 43 row) + (a_prime_bit c 363 row)) + (a_prime_bit c 683 row)) + (a_prime_bit c 1003 row)) + (a_prime_bit c 1323 row)) - (c_prime_bit c 43 row)) - 2)) * (((((((a_prime_bit c 43 row) + (a_prime_bit c 363 row)) + (a_prime_bit c 683 row)) + (a_prime_bit c 1003 row)) + (a_prime_bit c 1323 row)) - (c_prime_bit c 43 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2633_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2633 c row ↔ constraint_2633 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2634 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 44 row) + (a_prime_bit c 364 row)) + (a_prime_bit c 684 row)) + (a_prime_bit c 1004 row)) + (a_prime_bit c 1324 row)) - (c_prime_bit c 44 row)) * (((((((a_prime_bit c 44 row) + (a_prime_bit c 364 row)) + (a_prime_bit c 684 row)) + (a_prime_bit c 1004 row)) + (a_prime_bit c 1324 row)) - (c_prime_bit c 44 row)) - 2)) * (((((((a_prime_bit c 44 row) + (a_prime_bit c 364 row)) + (a_prime_bit c 684 row)) + (a_prime_bit c 1004 row)) + (a_prime_bit c 1324 row)) - (c_prime_bit c 44 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2634_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2634 c row ↔ constraint_2634 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2635 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 45 row) + (a_prime_bit c 365 row)) + (a_prime_bit c 685 row)) + (a_prime_bit c 1005 row)) + (a_prime_bit c 1325 row)) - (c_prime_bit c 45 row)) * (((((((a_prime_bit c 45 row) + (a_prime_bit c 365 row)) + (a_prime_bit c 685 row)) + (a_prime_bit c 1005 row)) + (a_prime_bit c 1325 row)) - (c_prime_bit c 45 row)) - 2)) * (((((((a_prime_bit c 45 row) + (a_prime_bit c 365 row)) + (a_prime_bit c 685 row)) + (a_prime_bit c 1005 row)) + (a_prime_bit c 1325 row)) - (c_prime_bit c 45 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2635_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2635 c row ↔ constraint_2635 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2636 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 46 row) + (a_prime_bit c 366 row)) + (a_prime_bit c 686 row)) + (a_prime_bit c 1006 row)) + (a_prime_bit c 1326 row)) - (c_prime_bit c 46 row)) * (((((((a_prime_bit c 46 row) + (a_prime_bit c 366 row)) + (a_prime_bit c 686 row)) + (a_prime_bit c 1006 row)) + (a_prime_bit c 1326 row)) - (c_prime_bit c 46 row)) - 2)) * (((((((a_prime_bit c 46 row) + (a_prime_bit c 366 row)) + (a_prime_bit c 686 row)) + (a_prime_bit c 1006 row)) + (a_prime_bit c 1326 row)) - (c_prime_bit c 46 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2636_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2636 c row ↔ constraint_2636 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2637 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 47 row) + (a_prime_bit c 367 row)) + (a_prime_bit c 687 row)) + (a_prime_bit c 1007 row)) + (a_prime_bit c 1327 row)) - (c_prime_bit c 47 row)) * (((((((a_prime_bit c 47 row) + (a_prime_bit c 367 row)) + (a_prime_bit c 687 row)) + (a_prime_bit c 1007 row)) + (a_prime_bit c 1327 row)) - (c_prime_bit c 47 row)) - 2)) * (((((((a_prime_bit c 47 row) + (a_prime_bit c 367 row)) + (a_prime_bit c 687 row)) + (a_prime_bit c 1007 row)) + (a_prime_bit c 1327 row)) - (c_prime_bit c 47 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2637_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2637 c row ↔ constraint_2637 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2638 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 48 row) + (a_prime_bit c 368 row)) + (a_prime_bit c 688 row)) + (a_prime_bit c 1008 row)) + (a_prime_bit c 1328 row)) - (c_prime_bit c 48 row)) * (((((((a_prime_bit c 48 row) + (a_prime_bit c 368 row)) + (a_prime_bit c 688 row)) + (a_prime_bit c 1008 row)) + (a_prime_bit c 1328 row)) - (c_prime_bit c 48 row)) - 2)) * (((((((a_prime_bit c 48 row) + (a_prime_bit c 368 row)) + (a_prime_bit c 688 row)) + (a_prime_bit c 1008 row)) + (a_prime_bit c 1328 row)) - (c_prime_bit c 48 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2638_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2638 c row ↔ constraint_2638 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2639 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 49 row) + (a_prime_bit c 369 row)) + (a_prime_bit c 689 row)) + (a_prime_bit c 1009 row)) + (a_prime_bit c 1329 row)) - (c_prime_bit c 49 row)) * (((((((a_prime_bit c 49 row) + (a_prime_bit c 369 row)) + (a_prime_bit c 689 row)) + (a_prime_bit c 1009 row)) + (a_prime_bit c 1329 row)) - (c_prime_bit c 49 row)) - 2)) * (((((((a_prime_bit c 49 row) + (a_prime_bit c 369 row)) + (a_prime_bit c 689 row)) + (a_prime_bit c 1009 row)) + (a_prime_bit c 1329 row)) - (c_prime_bit c 49 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2639_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2639 c row ↔ constraint_2639 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2640 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 50 row) + (a_prime_bit c 370 row)) + (a_prime_bit c 690 row)) + (a_prime_bit c 1010 row)) + (a_prime_bit c 1330 row)) - (c_prime_bit c 50 row)) * (((((((a_prime_bit c 50 row) + (a_prime_bit c 370 row)) + (a_prime_bit c 690 row)) + (a_prime_bit c 1010 row)) + (a_prime_bit c 1330 row)) - (c_prime_bit c 50 row)) - 2)) * (((((((a_prime_bit c 50 row) + (a_prime_bit c 370 row)) + (a_prime_bit c 690 row)) + (a_prime_bit c 1010 row)) + (a_prime_bit c 1330 row)) - (c_prime_bit c 50 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2640_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2640 c row ↔ constraint_2640 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2641 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 51 row) + (a_prime_bit c 371 row)) + (a_prime_bit c 691 row)) + (a_prime_bit c 1011 row)) + (a_prime_bit c 1331 row)) - (c_prime_bit c 51 row)) * (((((((a_prime_bit c 51 row) + (a_prime_bit c 371 row)) + (a_prime_bit c 691 row)) + (a_prime_bit c 1011 row)) + (a_prime_bit c 1331 row)) - (c_prime_bit c 51 row)) - 2)) * (((((((a_prime_bit c 51 row) + (a_prime_bit c 371 row)) + (a_prime_bit c 691 row)) + (a_prime_bit c 1011 row)) + (a_prime_bit c 1331 row)) - (c_prime_bit c 51 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2641_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2641 c row ↔ constraint_2641 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2642 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 52 row) + (a_prime_bit c 372 row)) + (a_prime_bit c 692 row)) + (a_prime_bit c 1012 row)) + (a_prime_bit c 1332 row)) - (c_prime_bit c 52 row)) * (((((((a_prime_bit c 52 row) + (a_prime_bit c 372 row)) + (a_prime_bit c 692 row)) + (a_prime_bit c 1012 row)) + (a_prime_bit c 1332 row)) - (c_prime_bit c 52 row)) - 2)) * (((((((a_prime_bit c 52 row) + (a_prime_bit c 372 row)) + (a_prime_bit c 692 row)) + (a_prime_bit c 1012 row)) + (a_prime_bit c 1332 row)) - (c_prime_bit c 52 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2642_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2642 c row ↔ constraint_2642 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2643 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 53 row) + (a_prime_bit c 373 row)) + (a_prime_bit c 693 row)) + (a_prime_bit c 1013 row)) + (a_prime_bit c 1333 row)) - (c_prime_bit c 53 row)) * (((((((a_prime_bit c 53 row) + (a_prime_bit c 373 row)) + (a_prime_bit c 693 row)) + (a_prime_bit c 1013 row)) + (a_prime_bit c 1333 row)) - (c_prime_bit c 53 row)) - 2)) * (((((((a_prime_bit c 53 row) + (a_prime_bit c 373 row)) + (a_prime_bit c 693 row)) + (a_prime_bit c 1013 row)) + (a_prime_bit c 1333 row)) - (c_prime_bit c 53 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2643_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2643 c row ↔ constraint_2643 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2644 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 54 row) + (a_prime_bit c 374 row)) + (a_prime_bit c 694 row)) + (a_prime_bit c 1014 row)) + (a_prime_bit c 1334 row)) - (c_prime_bit c 54 row)) * (((((((a_prime_bit c 54 row) + (a_prime_bit c 374 row)) + (a_prime_bit c 694 row)) + (a_prime_bit c 1014 row)) + (a_prime_bit c 1334 row)) - (c_prime_bit c 54 row)) - 2)) * (((((((a_prime_bit c 54 row) + (a_prime_bit c 374 row)) + (a_prime_bit c 694 row)) + (a_prime_bit c 1014 row)) + (a_prime_bit c 1334 row)) - (c_prime_bit c 54 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2644_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2644 c row ↔ constraint_2644 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2645 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 55 row) + (a_prime_bit c 375 row)) + (a_prime_bit c 695 row)) + (a_prime_bit c 1015 row)) + (a_prime_bit c 1335 row)) - (c_prime_bit c 55 row)) * (((((((a_prime_bit c 55 row) + (a_prime_bit c 375 row)) + (a_prime_bit c 695 row)) + (a_prime_bit c 1015 row)) + (a_prime_bit c 1335 row)) - (c_prime_bit c 55 row)) - 2)) * (((((((a_prime_bit c 55 row) + (a_prime_bit c 375 row)) + (a_prime_bit c 695 row)) + (a_prime_bit c 1015 row)) + (a_prime_bit c 1335 row)) - (c_prime_bit c 55 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2645_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2645 c row ↔ constraint_2645 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2646 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 56 row) + (a_prime_bit c 376 row)) + (a_prime_bit c 696 row)) + (a_prime_bit c 1016 row)) + (a_prime_bit c 1336 row)) - (c_prime_bit c 56 row)) * (((((((a_prime_bit c 56 row) + (a_prime_bit c 376 row)) + (a_prime_bit c 696 row)) + (a_prime_bit c 1016 row)) + (a_prime_bit c 1336 row)) - (c_prime_bit c 56 row)) - 2)) * (((((((a_prime_bit c 56 row) + (a_prime_bit c 376 row)) + (a_prime_bit c 696 row)) + (a_prime_bit c 1016 row)) + (a_prime_bit c 1336 row)) - (c_prime_bit c 56 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2646_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2646 c row ↔ constraint_2646 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2647 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 57 row) + (a_prime_bit c 377 row)) + (a_prime_bit c 697 row)) + (a_prime_bit c 1017 row)) + (a_prime_bit c 1337 row)) - (c_prime_bit c 57 row)) * (((((((a_prime_bit c 57 row) + (a_prime_bit c 377 row)) + (a_prime_bit c 697 row)) + (a_prime_bit c 1017 row)) + (a_prime_bit c 1337 row)) - (c_prime_bit c 57 row)) - 2)) * (((((((a_prime_bit c 57 row) + (a_prime_bit c 377 row)) + (a_prime_bit c 697 row)) + (a_prime_bit c 1017 row)) + (a_prime_bit c 1337 row)) - (c_prime_bit c 57 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2647_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2647 c row ↔ constraint_2647 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2648 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 58 row) + (a_prime_bit c 378 row)) + (a_prime_bit c 698 row)) + (a_prime_bit c 1018 row)) + (a_prime_bit c 1338 row)) - (c_prime_bit c 58 row)) * (((((((a_prime_bit c 58 row) + (a_prime_bit c 378 row)) + (a_prime_bit c 698 row)) + (a_prime_bit c 1018 row)) + (a_prime_bit c 1338 row)) - (c_prime_bit c 58 row)) - 2)) * (((((((a_prime_bit c 58 row) + (a_prime_bit c 378 row)) + (a_prime_bit c 698 row)) + (a_prime_bit c 1018 row)) + (a_prime_bit c 1338 row)) - (c_prime_bit c 58 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2648_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2648 c row ↔ constraint_2648 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2649 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 59 row) + (a_prime_bit c 379 row)) + (a_prime_bit c 699 row)) + (a_prime_bit c 1019 row)) + (a_prime_bit c 1339 row)) - (c_prime_bit c 59 row)) * (((((((a_prime_bit c 59 row) + (a_prime_bit c 379 row)) + (a_prime_bit c 699 row)) + (a_prime_bit c 1019 row)) + (a_prime_bit c 1339 row)) - (c_prime_bit c 59 row)) - 2)) * (((((((a_prime_bit c 59 row) + (a_prime_bit c 379 row)) + (a_prime_bit c 699 row)) + (a_prime_bit c 1019 row)) + (a_prime_bit c 1339 row)) - (c_prime_bit c 59 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2649_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2649 c row ↔ constraint_2649 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2650 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 60 row) + (a_prime_bit c 380 row)) + (a_prime_bit c 700 row)) + (a_prime_bit c 1020 row)) + (a_prime_bit c 1340 row)) - (c_prime_bit c 60 row)) * (((((((a_prime_bit c 60 row) + (a_prime_bit c 380 row)) + (a_prime_bit c 700 row)) + (a_prime_bit c 1020 row)) + (a_prime_bit c 1340 row)) - (c_prime_bit c 60 row)) - 2)) * (((((((a_prime_bit c 60 row) + (a_prime_bit c 380 row)) + (a_prime_bit c 700 row)) + (a_prime_bit c 1020 row)) + (a_prime_bit c 1340 row)) - (c_prime_bit c 60 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2650_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2650 c row ↔ constraint_2650 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2651 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 61 row) + (a_prime_bit c 381 row)) + (a_prime_bit c 701 row)) + (a_prime_bit c 1021 row)) + (a_prime_bit c 1341 row)) - (c_prime_bit c 61 row)) * (((((((a_prime_bit c 61 row) + (a_prime_bit c 381 row)) + (a_prime_bit c 701 row)) + (a_prime_bit c 1021 row)) + (a_prime_bit c 1341 row)) - (c_prime_bit c 61 row)) - 2)) * (((((((a_prime_bit c 61 row) + (a_prime_bit c 381 row)) + (a_prime_bit c 701 row)) + (a_prime_bit c 1021 row)) + (a_prime_bit c 1341 row)) - (c_prime_bit c 61 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2651_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2651 c row ↔ constraint_2651 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2652 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 62 row) + (a_prime_bit c 382 row)) + (a_prime_bit c 702 row)) + (a_prime_bit c 1022 row)) + (a_prime_bit c 1342 row)) - (c_prime_bit c 62 row)) * (((((((a_prime_bit c 62 row) + (a_prime_bit c 382 row)) + (a_prime_bit c 702 row)) + (a_prime_bit c 1022 row)) + (a_prime_bit c 1342 row)) - (c_prime_bit c 62 row)) - 2)) * (((((((a_prime_bit c 62 row) + (a_prime_bit c 382 row)) + (a_prime_bit c 702 row)) + (a_prime_bit c 1022 row)) + (a_prime_bit c 1342 row)) - (c_prime_bit c 62 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2652_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2652 c row ↔ constraint_2652 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2653 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 63 row) + (a_prime_bit c 383 row)) + (a_prime_bit c 703 row)) + (a_prime_bit c 1023 row)) + (a_prime_bit c 1343 row)) - (c_prime_bit c 63 row)) * (((((((a_prime_bit c 63 row) + (a_prime_bit c 383 row)) + (a_prime_bit c 703 row)) + (a_prime_bit c 1023 row)) + (a_prime_bit c 1343 row)) - (c_prime_bit c 63 row)) - 2)) * (((((((a_prime_bit c 63 row) + (a_prime_bit c 383 row)) + (a_prime_bit c 703 row)) + (a_prime_bit c 1023 row)) + (a_prime_bit c 1343 row)) - (c_prime_bit c 63 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2653_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2653 c row ↔ constraint_2653 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2654 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 64 row) + (a_prime_bit c 384 row)) + (a_prime_bit c 704 row)) + (a_prime_bit c 1024 row)) + (a_prime_bit c 1344 row)) - (c_prime_bit c 64 row)) * (((((((a_prime_bit c 64 row) + (a_prime_bit c 384 row)) + (a_prime_bit c 704 row)) + (a_prime_bit c 1024 row)) + (a_prime_bit c 1344 row)) - (c_prime_bit c 64 row)) - 2)) * (((((((a_prime_bit c 64 row) + (a_prime_bit c 384 row)) + (a_prime_bit c 704 row)) + (a_prime_bit c 1024 row)) + (a_prime_bit c 1344 row)) - (c_prime_bit c 64 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2654_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2654 c row ↔ constraint_2654 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2655 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 65 row) + (a_prime_bit c 385 row)) + (a_prime_bit c 705 row)) + (a_prime_bit c 1025 row)) + (a_prime_bit c 1345 row)) - (c_prime_bit c 65 row)) * (((((((a_prime_bit c 65 row) + (a_prime_bit c 385 row)) + (a_prime_bit c 705 row)) + (a_prime_bit c 1025 row)) + (a_prime_bit c 1345 row)) - (c_prime_bit c 65 row)) - 2)) * (((((((a_prime_bit c 65 row) + (a_prime_bit c 385 row)) + (a_prime_bit c 705 row)) + (a_prime_bit c 1025 row)) + (a_prime_bit c 1345 row)) - (c_prime_bit c 65 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2655_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2655 c row ↔ constraint_2655 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2656 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 66 row) + (a_prime_bit c 386 row)) + (a_prime_bit c 706 row)) + (a_prime_bit c 1026 row)) + (a_prime_bit c 1346 row)) - (c_prime_bit c 66 row)) * (((((((a_prime_bit c 66 row) + (a_prime_bit c 386 row)) + (a_prime_bit c 706 row)) + (a_prime_bit c 1026 row)) + (a_prime_bit c 1346 row)) - (c_prime_bit c 66 row)) - 2)) * (((((((a_prime_bit c 66 row) + (a_prime_bit c 386 row)) + (a_prime_bit c 706 row)) + (a_prime_bit c 1026 row)) + (a_prime_bit c 1346 row)) - (c_prime_bit c 66 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2656_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2656 c row ↔ constraint_2656 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2657 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 67 row) + (a_prime_bit c 387 row)) + (a_prime_bit c 707 row)) + (a_prime_bit c 1027 row)) + (a_prime_bit c 1347 row)) - (c_prime_bit c 67 row)) * (((((((a_prime_bit c 67 row) + (a_prime_bit c 387 row)) + (a_prime_bit c 707 row)) + (a_prime_bit c 1027 row)) + (a_prime_bit c 1347 row)) - (c_prime_bit c 67 row)) - 2)) * (((((((a_prime_bit c 67 row) + (a_prime_bit c 387 row)) + (a_prime_bit c 707 row)) + (a_prime_bit c 1027 row)) + (a_prime_bit c 1347 row)) - (c_prime_bit c 67 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2657_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2657 c row ↔ constraint_2657 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2658 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 68 row) + (a_prime_bit c 388 row)) + (a_prime_bit c 708 row)) + (a_prime_bit c 1028 row)) + (a_prime_bit c 1348 row)) - (c_prime_bit c 68 row)) * (((((((a_prime_bit c 68 row) + (a_prime_bit c 388 row)) + (a_prime_bit c 708 row)) + (a_prime_bit c 1028 row)) + (a_prime_bit c 1348 row)) - (c_prime_bit c 68 row)) - 2)) * (((((((a_prime_bit c 68 row) + (a_prime_bit c 388 row)) + (a_prime_bit c 708 row)) + (a_prime_bit c 1028 row)) + (a_prime_bit c 1348 row)) - (c_prime_bit c 68 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2658_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2658 c row ↔ constraint_2658 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2659 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 69 row) + (a_prime_bit c 389 row)) + (a_prime_bit c 709 row)) + (a_prime_bit c 1029 row)) + (a_prime_bit c 1349 row)) - (c_prime_bit c 69 row)) * (((((((a_prime_bit c 69 row) + (a_prime_bit c 389 row)) + (a_prime_bit c 709 row)) + (a_prime_bit c 1029 row)) + (a_prime_bit c 1349 row)) - (c_prime_bit c 69 row)) - 2)) * (((((((a_prime_bit c 69 row) + (a_prime_bit c 389 row)) + (a_prime_bit c 709 row)) + (a_prime_bit c 1029 row)) + (a_prime_bit c 1349 row)) - (c_prime_bit c 69 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2659_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2659 c row ↔ constraint_2659 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2660 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 70 row) + (a_prime_bit c 390 row)) + (a_prime_bit c 710 row)) + (a_prime_bit c 1030 row)) + (a_prime_bit c 1350 row)) - (c_prime_bit c 70 row)) * (((((((a_prime_bit c 70 row) + (a_prime_bit c 390 row)) + (a_prime_bit c 710 row)) + (a_prime_bit c 1030 row)) + (a_prime_bit c 1350 row)) - (c_prime_bit c 70 row)) - 2)) * (((((((a_prime_bit c 70 row) + (a_prime_bit c 390 row)) + (a_prime_bit c 710 row)) + (a_prime_bit c 1030 row)) + (a_prime_bit c 1350 row)) - (c_prime_bit c 70 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2660_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2660 c row ↔ constraint_2660 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2661 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 71 row) + (a_prime_bit c 391 row)) + (a_prime_bit c 711 row)) + (a_prime_bit c 1031 row)) + (a_prime_bit c 1351 row)) - (c_prime_bit c 71 row)) * (((((((a_prime_bit c 71 row) + (a_prime_bit c 391 row)) + (a_prime_bit c 711 row)) + (a_prime_bit c 1031 row)) + (a_prime_bit c 1351 row)) - (c_prime_bit c 71 row)) - 2)) * (((((((a_prime_bit c 71 row) + (a_prime_bit c 391 row)) + (a_prime_bit c 711 row)) + (a_prime_bit c 1031 row)) + (a_prime_bit c 1351 row)) - (c_prime_bit c 71 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2661_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2661 c row ↔ constraint_2661 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2662 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 72 row) + (a_prime_bit c 392 row)) + (a_prime_bit c 712 row)) + (a_prime_bit c 1032 row)) + (a_prime_bit c 1352 row)) - (c_prime_bit c 72 row)) * (((((((a_prime_bit c 72 row) + (a_prime_bit c 392 row)) + (a_prime_bit c 712 row)) + (a_prime_bit c 1032 row)) + (a_prime_bit c 1352 row)) - (c_prime_bit c 72 row)) - 2)) * (((((((a_prime_bit c 72 row) + (a_prime_bit c 392 row)) + (a_prime_bit c 712 row)) + (a_prime_bit c 1032 row)) + (a_prime_bit c 1352 row)) - (c_prime_bit c 72 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2662_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2662 c row ↔ constraint_2662 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2663 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 73 row) + (a_prime_bit c 393 row)) + (a_prime_bit c 713 row)) + (a_prime_bit c 1033 row)) + (a_prime_bit c 1353 row)) - (c_prime_bit c 73 row)) * (((((((a_prime_bit c 73 row) + (a_prime_bit c 393 row)) + (a_prime_bit c 713 row)) + (a_prime_bit c 1033 row)) + (a_prime_bit c 1353 row)) - (c_prime_bit c 73 row)) - 2)) * (((((((a_prime_bit c 73 row) + (a_prime_bit c 393 row)) + (a_prime_bit c 713 row)) + (a_prime_bit c 1033 row)) + (a_prime_bit c 1353 row)) - (c_prime_bit c 73 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2663_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2663 c row ↔ constraint_2663 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2664 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 74 row) + (a_prime_bit c 394 row)) + (a_prime_bit c 714 row)) + (a_prime_bit c 1034 row)) + (a_prime_bit c 1354 row)) - (c_prime_bit c 74 row)) * (((((((a_prime_bit c 74 row) + (a_prime_bit c 394 row)) + (a_prime_bit c 714 row)) + (a_prime_bit c 1034 row)) + (a_prime_bit c 1354 row)) - (c_prime_bit c 74 row)) - 2)) * (((((((a_prime_bit c 74 row) + (a_prime_bit c 394 row)) + (a_prime_bit c 714 row)) + (a_prime_bit c 1034 row)) + (a_prime_bit c 1354 row)) - (c_prime_bit c 74 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2664_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2664 c row ↔ constraint_2664 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2665 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 75 row) + (a_prime_bit c 395 row)) + (a_prime_bit c 715 row)) + (a_prime_bit c 1035 row)) + (a_prime_bit c 1355 row)) - (c_prime_bit c 75 row)) * (((((((a_prime_bit c 75 row) + (a_prime_bit c 395 row)) + (a_prime_bit c 715 row)) + (a_prime_bit c 1035 row)) + (a_prime_bit c 1355 row)) - (c_prime_bit c 75 row)) - 2)) * (((((((a_prime_bit c 75 row) + (a_prime_bit c 395 row)) + (a_prime_bit c 715 row)) + (a_prime_bit c 1035 row)) + (a_prime_bit c 1355 row)) - (c_prime_bit c 75 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2665_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2665 c row ↔ constraint_2665 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2666 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 76 row) + (a_prime_bit c 396 row)) + (a_prime_bit c 716 row)) + (a_prime_bit c 1036 row)) + (a_prime_bit c 1356 row)) - (c_prime_bit c 76 row)) * (((((((a_prime_bit c 76 row) + (a_prime_bit c 396 row)) + (a_prime_bit c 716 row)) + (a_prime_bit c 1036 row)) + (a_prime_bit c 1356 row)) - (c_prime_bit c 76 row)) - 2)) * (((((((a_prime_bit c 76 row) + (a_prime_bit c 396 row)) + (a_prime_bit c 716 row)) + (a_prime_bit c 1036 row)) + (a_prime_bit c 1356 row)) - (c_prime_bit c 76 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2666_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2666 c row ↔ constraint_2666 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2667 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 77 row) + (a_prime_bit c 397 row)) + (a_prime_bit c 717 row)) + (a_prime_bit c 1037 row)) + (a_prime_bit c 1357 row)) - (c_prime_bit c 77 row)) * (((((((a_prime_bit c 77 row) + (a_prime_bit c 397 row)) + (a_prime_bit c 717 row)) + (a_prime_bit c 1037 row)) + (a_prime_bit c 1357 row)) - (c_prime_bit c 77 row)) - 2)) * (((((((a_prime_bit c 77 row) + (a_prime_bit c 397 row)) + (a_prime_bit c 717 row)) + (a_prime_bit c 1037 row)) + (a_prime_bit c 1357 row)) - (c_prime_bit c 77 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2667_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2667 c row ↔ constraint_2667 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2668 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 78 row) + (a_prime_bit c 398 row)) + (a_prime_bit c 718 row)) + (a_prime_bit c 1038 row)) + (a_prime_bit c 1358 row)) - (c_prime_bit c 78 row)) * (((((((a_prime_bit c 78 row) + (a_prime_bit c 398 row)) + (a_prime_bit c 718 row)) + (a_prime_bit c 1038 row)) + (a_prime_bit c 1358 row)) - (c_prime_bit c 78 row)) - 2)) * (((((((a_prime_bit c 78 row) + (a_prime_bit c 398 row)) + (a_prime_bit c 718 row)) + (a_prime_bit c 1038 row)) + (a_prime_bit c 1358 row)) - (c_prime_bit c 78 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2668_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2668 c row ↔ constraint_2668 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2669 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 79 row) + (a_prime_bit c 399 row)) + (a_prime_bit c 719 row)) + (a_prime_bit c 1039 row)) + (a_prime_bit c 1359 row)) - (c_prime_bit c 79 row)) * (((((((a_prime_bit c 79 row) + (a_prime_bit c 399 row)) + (a_prime_bit c 719 row)) + (a_prime_bit c 1039 row)) + (a_prime_bit c 1359 row)) - (c_prime_bit c 79 row)) - 2)) * (((((((a_prime_bit c 79 row) + (a_prime_bit c 399 row)) + (a_prime_bit c 719 row)) + (a_prime_bit c 1039 row)) + (a_prime_bit c 1359 row)) - (c_prime_bit c 79 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2669_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2669 c row ↔ constraint_2669 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2670 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 80 row) + (a_prime_bit c 400 row)) + (a_prime_bit c 720 row)) + (a_prime_bit c 1040 row)) + (a_prime_bit c 1360 row)) - (c_prime_bit c 80 row)) * (((((((a_prime_bit c 80 row) + (a_prime_bit c 400 row)) + (a_prime_bit c 720 row)) + (a_prime_bit c 1040 row)) + (a_prime_bit c 1360 row)) - (c_prime_bit c 80 row)) - 2)) * (((((((a_prime_bit c 80 row) + (a_prime_bit c 400 row)) + (a_prime_bit c 720 row)) + (a_prime_bit c 1040 row)) + (a_prime_bit c 1360 row)) - (c_prime_bit c 80 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2670_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2670 c row ↔ constraint_2670 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2671 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 81 row) + (a_prime_bit c 401 row)) + (a_prime_bit c 721 row)) + (a_prime_bit c 1041 row)) + (a_prime_bit c 1361 row)) - (c_prime_bit c 81 row)) * (((((((a_prime_bit c 81 row) + (a_prime_bit c 401 row)) + (a_prime_bit c 721 row)) + (a_prime_bit c 1041 row)) + (a_prime_bit c 1361 row)) - (c_prime_bit c 81 row)) - 2)) * (((((((a_prime_bit c 81 row) + (a_prime_bit c 401 row)) + (a_prime_bit c 721 row)) + (a_prime_bit c 1041 row)) + (a_prime_bit c 1361 row)) - (c_prime_bit c 81 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2671_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2671 c row ↔ constraint_2671 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2672 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 82 row) + (a_prime_bit c 402 row)) + (a_prime_bit c 722 row)) + (a_prime_bit c 1042 row)) + (a_prime_bit c 1362 row)) - (c_prime_bit c 82 row)) * (((((((a_prime_bit c 82 row) + (a_prime_bit c 402 row)) + (a_prime_bit c 722 row)) + (a_prime_bit c 1042 row)) + (a_prime_bit c 1362 row)) - (c_prime_bit c 82 row)) - 2)) * (((((((a_prime_bit c 82 row) + (a_prime_bit c 402 row)) + (a_prime_bit c 722 row)) + (a_prime_bit c 1042 row)) + (a_prime_bit c 1362 row)) - (c_prime_bit c 82 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2672_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2672 c row ↔ constraint_2672 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2673 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 83 row) + (a_prime_bit c 403 row)) + (a_prime_bit c 723 row)) + (a_prime_bit c 1043 row)) + (a_prime_bit c 1363 row)) - (c_prime_bit c 83 row)) * (((((((a_prime_bit c 83 row) + (a_prime_bit c 403 row)) + (a_prime_bit c 723 row)) + (a_prime_bit c 1043 row)) + (a_prime_bit c 1363 row)) - (c_prime_bit c 83 row)) - 2)) * (((((((a_prime_bit c 83 row) + (a_prime_bit c 403 row)) + (a_prime_bit c 723 row)) + (a_prime_bit c 1043 row)) + (a_prime_bit c 1363 row)) - (c_prime_bit c 83 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2673_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2673 c row ↔ constraint_2673 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2674 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 84 row) + (a_prime_bit c 404 row)) + (a_prime_bit c 724 row)) + (a_prime_bit c 1044 row)) + (a_prime_bit c 1364 row)) - (c_prime_bit c 84 row)) * (((((((a_prime_bit c 84 row) + (a_prime_bit c 404 row)) + (a_prime_bit c 724 row)) + (a_prime_bit c 1044 row)) + (a_prime_bit c 1364 row)) - (c_prime_bit c 84 row)) - 2)) * (((((((a_prime_bit c 84 row) + (a_prime_bit c 404 row)) + (a_prime_bit c 724 row)) + (a_prime_bit c 1044 row)) + (a_prime_bit c 1364 row)) - (c_prime_bit c 84 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2674_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2674 c row ↔ constraint_2674 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2675 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 85 row) + (a_prime_bit c 405 row)) + (a_prime_bit c 725 row)) + (a_prime_bit c 1045 row)) + (a_prime_bit c 1365 row)) - (c_prime_bit c 85 row)) * (((((((a_prime_bit c 85 row) + (a_prime_bit c 405 row)) + (a_prime_bit c 725 row)) + (a_prime_bit c 1045 row)) + (a_prime_bit c 1365 row)) - (c_prime_bit c 85 row)) - 2)) * (((((((a_prime_bit c 85 row) + (a_prime_bit c 405 row)) + (a_prime_bit c 725 row)) + (a_prime_bit c 1045 row)) + (a_prime_bit c 1365 row)) - (c_prime_bit c 85 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2675_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2675 c row ↔ constraint_2675 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2676 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 86 row) + (a_prime_bit c 406 row)) + (a_prime_bit c 726 row)) + (a_prime_bit c 1046 row)) + (a_prime_bit c 1366 row)) - (c_prime_bit c 86 row)) * (((((((a_prime_bit c 86 row) + (a_prime_bit c 406 row)) + (a_prime_bit c 726 row)) + (a_prime_bit c 1046 row)) + (a_prime_bit c 1366 row)) - (c_prime_bit c 86 row)) - 2)) * (((((((a_prime_bit c 86 row) + (a_prime_bit c 406 row)) + (a_prime_bit c 726 row)) + (a_prime_bit c 1046 row)) + (a_prime_bit c 1366 row)) - (c_prime_bit c 86 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2676_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2676 c row ↔ constraint_2676 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2677 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 87 row) + (a_prime_bit c 407 row)) + (a_prime_bit c 727 row)) + (a_prime_bit c 1047 row)) + (a_prime_bit c 1367 row)) - (c_prime_bit c 87 row)) * (((((((a_prime_bit c 87 row) + (a_prime_bit c 407 row)) + (a_prime_bit c 727 row)) + (a_prime_bit c 1047 row)) + (a_prime_bit c 1367 row)) - (c_prime_bit c 87 row)) - 2)) * (((((((a_prime_bit c 87 row) + (a_prime_bit c 407 row)) + (a_prime_bit c 727 row)) + (a_prime_bit c 1047 row)) + (a_prime_bit c 1367 row)) - (c_prime_bit c 87 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2677_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2677 c row ↔ constraint_2677 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2678 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 88 row) + (a_prime_bit c 408 row)) + (a_prime_bit c 728 row)) + (a_prime_bit c 1048 row)) + (a_prime_bit c 1368 row)) - (c_prime_bit c 88 row)) * (((((((a_prime_bit c 88 row) + (a_prime_bit c 408 row)) + (a_prime_bit c 728 row)) + (a_prime_bit c 1048 row)) + (a_prime_bit c 1368 row)) - (c_prime_bit c 88 row)) - 2)) * (((((((a_prime_bit c 88 row) + (a_prime_bit c 408 row)) + (a_prime_bit c 728 row)) + (a_prime_bit c 1048 row)) + (a_prime_bit c 1368 row)) - (c_prime_bit c 88 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2678_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2678 c row ↔ constraint_2678 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2679 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 89 row) + (a_prime_bit c 409 row)) + (a_prime_bit c 729 row)) + (a_prime_bit c 1049 row)) + (a_prime_bit c 1369 row)) - (c_prime_bit c 89 row)) * (((((((a_prime_bit c 89 row) + (a_prime_bit c 409 row)) + (a_prime_bit c 729 row)) + (a_prime_bit c 1049 row)) + (a_prime_bit c 1369 row)) - (c_prime_bit c 89 row)) - 2)) * (((((((a_prime_bit c 89 row) + (a_prime_bit c 409 row)) + (a_prime_bit c 729 row)) + (a_prime_bit c 1049 row)) + (a_prime_bit c 1369 row)) - (c_prime_bit c 89 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2679_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2679 c row ↔ constraint_2679 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2680 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 90 row) + (a_prime_bit c 410 row)) + (a_prime_bit c 730 row)) + (a_prime_bit c 1050 row)) + (a_prime_bit c 1370 row)) - (c_prime_bit c 90 row)) * (((((((a_prime_bit c 90 row) + (a_prime_bit c 410 row)) + (a_prime_bit c 730 row)) + (a_prime_bit c 1050 row)) + (a_prime_bit c 1370 row)) - (c_prime_bit c 90 row)) - 2)) * (((((((a_prime_bit c 90 row) + (a_prime_bit c 410 row)) + (a_prime_bit c 730 row)) + (a_prime_bit c 1050 row)) + (a_prime_bit c 1370 row)) - (c_prime_bit c 90 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2680_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2680 c row ↔ constraint_2680 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2681 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 91 row) + (a_prime_bit c 411 row)) + (a_prime_bit c 731 row)) + (a_prime_bit c 1051 row)) + (a_prime_bit c 1371 row)) - (c_prime_bit c 91 row)) * (((((((a_prime_bit c 91 row) + (a_prime_bit c 411 row)) + (a_prime_bit c 731 row)) + (a_prime_bit c 1051 row)) + (a_prime_bit c 1371 row)) - (c_prime_bit c 91 row)) - 2)) * (((((((a_prime_bit c 91 row) + (a_prime_bit c 411 row)) + (a_prime_bit c 731 row)) + (a_prime_bit c 1051 row)) + (a_prime_bit c 1371 row)) - (c_prime_bit c 91 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2681_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2681 c row ↔ constraint_2681 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2682 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 92 row) + (a_prime_bit c 412 row)) + (a_prime_bit c 732 row)) + (a_prime_bit c 1052 row)) + (a_prime_bit c 1372 row)) - (c_prime_bit c 92 row)) * (((((((a_prime_bit c 92 row) + (a_prime_bit c 412 row)) + (a_prime_bit c 732 row)) + (a_prime_bit c 1052 row)) + (a_prime_bit c 1372 row)) - (c_prime_bit c 92 row)) - 2)) * (((((((a_prime_bit c 92 row) + (a_prime_bit c 412 row)) + (a_prime_bit c 732 row)) + (a_prime_bit c 1052 row)) + (a_prime_bit c 1372 row)) - (c_prime_bit c 92 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2682_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2682 c row ↔ constraint_2682 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2683 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 93 row) + (a_prime_bit c 413 row)) + (a_prime_bit c 733 row)) + (a_prime_bit c 1053 row)) + (a_prime_bit c 1373 row)) - (c_prime_bit c 93 row)) * (((((((a_prime_bit c 93 row) + (a_prime_bit c 413 row)) + (a_prime_bit c 733 row)) + (a_prime_bit c 1053 row)) + (a_prime_bit c 1373 row)) - (c_prime_bit c 93 row)) - 2)) * (((((((a_prime_bit c 93 row) + (a_prime_bit c 413 row)) + (a_prime_bit c 733 row)) + (a_prime_bit c 1053 row)) + (a_prime_bit c 1373 row)) - (c_prime_bit c 93 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2683_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2683 c row ↔ constraint_2683 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2684 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 94 row) + (a_prime_bit c 414 row)) + (a_prime_bit c 734 row)) + (a_prime_bit c 1054 row)) + (a_prime_bit c 1374 row)) - (c_prime_bit c 94 row)) * (((((((a_prime_bit c 94 row) + (a_prime_bit c 414 row)) + (a_prime_bit c 734 row)) + (a_prime_bit c 1054 row)) + (a_prime_bit c 1374 row)) - (c_prime_bit c 94 row)) - 2)) * (((((((a_prime_bit c 94 row) + (a_prime_bit c 414 row)) + (a_prime_bit c 734 row)) + (a_prime_bit c 1054 row)) + (a_prime_bit c 1374 row)) - (c_prime_bit c 94 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2684_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2684 c row ↔ constraint_2684 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2685 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 95 row) + (a_prime_bit c 415 row)) + (a_prime_bit c 735 row)) + (a_prime_bit c 1055 row)) + (a_prime_bit c 1375 row)) - (c_prime_bit c 95 row)) * (((((((a_prime_bit c 95 row) + (a_prime_bit c 415 row)) + (a_prime_bit c 735 row)) + (a_prime_bit c 1055 row)) + (a_prime_bit c 1375 row)) - (c_prime_bit c 95 row)) - 2)) * (((((((a_prime_bit c 95 row) + (a_prime_bit c 415 row)) + (a_prime_bit c 735 row)) + (a_prime_bit c 1055 row)) + (a_prime_bit c 1375 row)) - (c_prime_bit c 95 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2685_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2685 c row ↔ constraint_2685 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2686 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 96 row) + (a_prime_bit c 416 row)) + (a_prime_bit c 736 row)) + (a_prime_bit c 1056 row)) + (a_prime_bit c 1376 row)) - (c_prime_bit c 96 row)) * (((((((a_prime_bit c 96 row) + (a_prime_bit c 416 row)) + (a_prime_bit c 736 row)) + (a_prime_bit c 1056 row)) + (a_prime_bit c 1376 row)) - (c_prime_bit c 96 row)) - 2)) * (((((((a_prime_bit c 96 row) + (a_prime_bit c 416 row)) + (a_prime_bit c 736 row)) + (a_prime_bit c 1056 row)) + (a_prime_bit c 1376 row)) - (c_prime_bit c 96 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2686_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2686 c row ↔ constraint_2686 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2687 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 97 row) + (a_prime_bit c 417 row)) + (a_prime_bit c 737 row)) + (a_prime_bit c 1057 row)) + (a_prime_bit c 1377 row)) - (c_prime_bit c 97 row)) * (((((((a_prime_bit c 97 row) + (a_prime_bit c 417 row)) + (a_prime_bit c 737 row)) + (a_prime_bit c 1057 row)) + (a_prime_bit c 1377 row)) - (c_prime_bit c 97 row)) - 2)) * (((((((a_prime_bit c 97 row) + (a_prime_bit c 417 row)) + (a_prime_bit c 737 row)) + (a_prime_bit c 1057 row)) + (a_prime_bit c 1377 row)) - (c_prime_bit c 97 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2687_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2687 c row ↔ constraint_2687 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2688 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 98 row) + (a_prime_bit c 418 row)) + (a_prime_bit c 738 row)) + (a_prime_bit c 1058 row)) + (a_prime_bit c 1378 row)) - (c_prime_bit c 98 row)) * (((((((a_prime_bit c 98 row) + (a_prime_bit c 418 row)) + (a_prime_bit c 738 row)) + (a_prime_bit c 1058 row)) + (a_prime_bit c 1378 row)) - (c_prime_bit c 98 row)) - 2)) * (((((((a_prime_bit c 98 row) + (a_prime_bit c 418 row)) + (a_prime_bit c 738 row)) + (a_prime_bit c 1058 row)) + (a_prime_bit c 1378 row)) - (c_prime_bit c 98 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2688_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2688 c row ↔ constraint_2688 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2689 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 99 row) + (a_prime_bit c 419 row)) + (a_prime_bit c 739 row)) + (a_prime_bit c 1059 row)) + (a_prime_bit c 1379 row)) - (c_prime_bit c 99 row)) * (((((((a_prime_bit c 99 row) + (a_prime_bit c 419 row)) + (a_prime_bit c 739 row)) + (a_prime_bit c 1059 row)) + (a_prime_bit c 1379 row)) - (c_prime_bit c 99 row)) - 2)) * (((((((a_prime_bit c 99 row) + (a_prime_bit c 419 row)) + (a_prime_bit c 739 row)) + (a_prime_bit c 1059 row)) + (a_prime_bit c 1379 row)) - (c_prime_bit c 99 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2689_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2689 c row ↔ constraint_2689 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2690 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 100 row) + (a_prime_bit c 420 row)) + (a_prime_bit c 740 row)) + (a_prime_bit c 1060 row)) + (a_prime_bit c 1380 row)) - (c_prime_bit c 100 row)) * (((((((a_prime_bit c 100 row) + (a_prime_bit c 420 row)) + (a_prime_bit c 740 row)) + (a_prime_bit c 1060 row)) + (a_prime_bit c 1380 row)) - (c_prime_bit c 100 row)) - 2)) * (((((((a_prime_bit c 100 row) + (a_prime_bit c 420 row)) + (a_prime_bit c 740 row)) + (a_prime_bit c 1060 row)) + (a_prime_bit c 1380 row)) - (c_prime_bit c 100 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2690_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2690 c row ↔ constraint_2690 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2691 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 101 row) + (a_prime_bit c 421 row)) + (a_prime_bit c 741 row)) + (a_prime_bit c 1061 row)) + (a_prime_bit c 1381 row)) - (c_prime_bit c 101 row)) * (((((((a_prime_bit c 101 row) + (a_prime_bit c 421 row)) + (a_prime_bit c 741 row)) + (a_prime_bit c 1061 row)) + (a_prime_bit c 1381 row)) - (c_prime_bit c 101 row)) - 2)) * (((((((a_prime_bit c 101 row) + (a_prime_bit c 421 row)) + (a_prime_bit c 741 row)) + (a_prime_bit c 1061 row)) + (a_prime_bit c 1381 row)) - (c_prime_bit c 101 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2691_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2691 c row ↔ constraint_2691 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2692 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 102 row) + (a_prime_bit c 422 row)) + (a_prime_bit c 742 row)) + (a_prime_bit c 1062 row)) + (a_prime_bit c 1382 row)) - (c_prime_bit c 102 row)) * (((((((a_prime_bit c 102 row) + (a_prime_bit c 422 row)) + (a_prime_bit c 742 row)) + (a_prime_bit c 1062 row)) + (a_prime_bit c 1382 row)) - (c_prime_bit c 102 row)) - 2)) * (((((((a_prime_bit c 102 row) + (a_prime_bit c 422 row)) + (a_prime_bit c 742 row)) + (a_prime_bit c 1062 row)) + (a_prime_bit c 1382 row)) - (c_prime_bit c 102 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2692_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2692 c row ↔ constraint_2692 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2693 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 103 row) + (a_prime_bit c 423 row)) + (a_prime_bit c 743 row)) + (a_prime_bit c 1063 row)) + (a_prime_bit c 1383 row)) - (c_prime_bit c 103 row)) * (((((((a_prime_bit c 103 row) + (a_prime_bit c 423 row)) + (a_prime_bit c 743 row)) + (a_prime_bit c 1063 row)) + (a_prime_bit c 1383 row)) - (c_prime_bit c 103 row)) - 2)) * (((((((a_prime_bit c 103 row) + (a_prime_bit c 423 row)) + (a_prime_bit c 743 row)) + (a_prime_bit c 1063 row)) + (a_prime_bit c 1383 row)) - (c_prime_bit c 103 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2693_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2693 c row ↔ constraint_2693 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2694 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 104 row) + (a_prime_bit c 424 row)) + (a_prime_bit c 744 row)) + (a_prime_bit c 1064 row)) + (a_prime_bit c 1384 row)) - (c_prime_bit c 104 row)) * (((((((a_prime_bit c 104 row) + (a_prime_bit c 424 row)) + (a_prime_bit c 744 row)) + (a_prime_bit c 1064 row)) + (a_prime_bit c 1384 row)) - (c_prime_bit c 104 row)) - 2)) * (((((((a_prime_bit c 104 row) + (a_prime_bit c 424 row)) + (a_prime_bit c 744 row)) + (a_prime_bit c 1064 row)) + (a_prime_bit c 1384 row)) - (c_prime_bit c 104 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2694_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2694 c row ↔ constraint_2694 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2695 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 105 row) + (a_prime_bit c 425 row)) + (a_prime_bit c 745 row)) + (a_prime_bit c 1065 row)) + (a_prime_bit c 1385 row)) - (c_prime_bit c 105 row)) * (((((((a_prime_bit c 105 row) + (a_prime_bit c 425 row)) + (a_prime_bit c 745 row)) + (a_prime_bit c 1065 row)) + (a_prime_bit c 1385 row)) - (c_prime_bit c 105 row)) - 2)) * (((((((a_prime_bit c 105 row) + (a_prime_bit c 425 row)) + (a_prime_bit c 745 row)) + (a_prime_bit c 1065 row)) + (a_prime_bit c 1385 row)) - (c_prime_bit c 105 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2695_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2695 c row ↔ constraint_2695 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2696 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 106 row) + (a_prime_bit c 426 row)) + (a_prime_bit c 746 row)) + (a_prime_bit c 1066 row)) + (a_prime_bit c 1386 row)) - (c_prime_bit c 106 row)) * (((((((a_prime_bit c 106 row) + (a_prime_bit c 426 row)) + (a_prime_bit c 746 row)) + (a_prime_bit c 1066 row)) + (a_prime_bit c 1386 row)) - (c_prime_bit c 106 row)) - 2)) * (((((((a_prime_bit c 106 row) + (a_prime_bit c 426 row)) + (a_prime_bit c 746 row)) + (a_prime_bit c 1066 row)) + (a_prime_bit c 1386 row)) - (c_prime_bit c 106 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2696_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2696 c row ↔ constraint_2696 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2697 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 107 row) + (a_prime_bit c 427 row)) + (a_prime_bit c 747 row)) + (a_prime_bit c 1067 row)) + (a_prime_bit c 1387 row)) - (c_prime_bit c 107 row)) * (((((((a_prime_bit c 107 row) + (a_prime_bit c 427 row)) + (a_prime_bit c 747 row)) + (a_prime_bit c 1067 row)) + (a_prime_bit c 1387 row)) - (c_prime_bit c 107 row)) - 2)) * (((((((a_prime_bit c 107 row) + (a_prime_bit c 427 row)) + (a_prime_bit c 747 row)) + (a_prime_bit c 1067 row)) + (a_prime_bit c 1387 row)) - (c_prime_bit c 107 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2697_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2697 c row ↔ constraint_2697 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2698 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 108 row) + (a_prime_bit c 428 row)) + (a_prime_bit c 748 row)) + (a_prime_bit c 1068 row)) + (a_prime_bit c 1388 row)) - (c_prime_bit c 108 row)) * (((((((a_prime_bit c 108 row) + (a_prime_bit c 428 row)) + (a_prime_bit c 748 row)) + (a_prime_bit c 1068 row)) + (a_prime_bit c 1388 row)) - (c_prime_bit c 108 row)) - 2)) * (((((((a_prime_bit c 108 row) + (a_prime_bit c 428 row)) + (a_prime_bit c 748 row)) + (a_prime_bit c 1068 row)) + (a_prime_bit c 1388 row)) - (c_prime_bit c 108 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2698_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2698 c row ↔ constraint_2698 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2699 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 109 row) + (a_prime_bit c 429 row)) + (a_prime_bit c 749 row)) + (a_prime_bit c 1069 row)) + (a_prime_bit c 1389 row)) - (c_prime_bit c 109 row)) * (((((((a_prime_bit c 109 row) + (a_prime_bit c 429 row)) + (a_prime_bit c 749 row)) + (a_prime_bit c 1069 row)) + (a_prime_bit c 1389 row)) - (c_prime_bit c 109 row)) - 2)) * (((((((a_prime_bit c 109 row) + (a_prime_bit c 429 row)) + (a_prime_bit c 749 row)) + (a_prime_bit c 1069 row)) + (a_prime_bit c 1389 row)) - (c_prime_bit c 109 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2699_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2699 c row ↔ constraint_2699 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2700 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 110 row) + (a_prime_bit c 430 row)) + (a_prime_bit c 750 row)) + (a_prime_bit c 1070 row)) + (a_prime_bit c 1390 row)) - (c_prime_bit c 110 row)) * (((((((a_prime_bit c 110 row) + (a_prime_bit c 430 row)) + (a_prime_bit c 750 row)) + (a_prime_bit c 1070 row)) + (a_prime_bit c 1390 row)) - (c_prime_bit c 110 row)) - 2)) * (((((((a_prime_bit c 110 row) + (a_prime_bit c 430 row)) + (a_prime_bit c 750 row)) + (a_prime_bit c 1070 row)) + (a_prime_bit c 1390 row)) - (c_prime_bit c 110 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2700_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2700 c row ↔ constraint_2700 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2701 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 111 row) + (a_prime_bit c 431 row)) + (a_prime_bit c 751 row)) + (a_prime_bit c 1071 row)) + (a_prime_bit c 1391 row)) - (c_prime_bit c 111 row)) * (((((((a_prime_bit c 111 row) + (a_prime_bit c 431 row)) + (a_prime_bit c 751 row)) + (a_prime_bit c 1071 row)) + (a_prime_bit c 1391 row)) - (c_prime_bit c 111 row)) - 2)) * (((((((a_prime_bit c 111 row) + (a_prime_bit c 431 row)) + (a_prime_bit c 751 row)) + (a_prime_bit c 1071 row)) + (a_prime_bit c 1391 row)) - (c_prime_bit c 111 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2701_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2701 c row ↔ constraint_2701 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2702 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 112 row) + (a_prime_bit c 432 row)) + (a_prime_bit c 752 row)) + (a_prime_bit c 1072 row)) + (a_prime_bit c 1392 row)) - (c_prime_bit c 112 row)) * (((((((a_prime_bit c 112 row) + (a_prime_bit c 432 row)) + (a_prime_bit c 752 row)) + (a_prime_bit c 1072 row)) + (a_prime_bit c 1392 row)) - (c_prime_bit c 112 row)) - 2)) * (((((((a_prime_bit c 112 row) + (a_prime_bit c 432 row)) + (a_prime_bit c 752 row)) + (a_prime_bit c 1072 row)) + (a_prime_bit c 1392 row)) - (c_prime_bit c 112 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2702_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2702 c row ↔ constraint_2702 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2703 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 113 row) + (a_prime_bit c 433 row)) + (a_prime_bit c 753 row)) + (a_prime_bit c 1073 row)) + (a_prime_bit c 1393 row)) - (c_prime_bit c 113 row)) * (((((((a_prime_bit c 113 row) + (a_prime_bit c 433 row)) + (a_prime_bit c 753 row)) + (a_prime_bit c 1073 row)) + (a_prime_bit c 1393 row)) - (c_prime_bit c 113 row)) - 2)) * (((((((a_prime_bit c 113 row) + (a_prime_bit c 433 row)) + (a_prime_bit c 753 row)) + (a_prime_bit c 1073 row)) + (a_prime_bit c 1393 row)) - (c_prime_bit c 113 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2703_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2703 c row ↔ constraint_2703 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2704 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 114 row) + (a_prime_bit c 434 row)) + (a_prime_bit c 754 row)) + (a_prime_bit c 1074 row)) + (a_prime_bit c 1394 row)) - (c_prime_bit c 114 row)) * (((((((a_prime_bit c 114 row) + (a_prime_bit c 434 row)) + (a_prime_bit c 754 row)) + (a_prime_bit c 1074 row)) + (a_prime_bit c 1394 row)) - (c_prime_bit c 114 row)) - 2)) * (((((((a_prime_bit c 114 row) + (a_prime_bit c 434 row)) + (a_prime_bit c 754 row)) + (a_prime_bit c 1074 row)) + (a_prime_bit c 1394 row)) - (c_prime_bit c 114 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2704_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2704 c row ↔ constraint_2704 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2705 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 115 row) + (a_prime_bit c 435 row)) + (a_prime_bit c 755 row)) + (a_prime_bit c 1075 row)) + (a_prime_bit c 1395 row)) - (c_prime_bit c 115 row)) * (((((((a_prime_bit c 115 row) + (a_prime_bit c 435 row)) + (a_prime_bit c 755 row)) + (a_prime_bit c 1075 row)) + (a_prime_bit c 1395 row)) - (c_prime_bit c 115 row)) - 2)) * (((((((a_prime_bit c 115 row) + (a_prime_bit c 435 row)) + (a_prime_bit c 755 row)) + (a_prime_bit c 1075 row)) + (a_prime_bit c 1395 row)) - (c_prime_bit c 115 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2705_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2705 c row ↔ constraint_2705 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2706 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 116 row) + (a_prime_bit c 436 row)) + (a_prime_bit c 756 row)) + (a_prime_bit c 1076 row)) + (a_prime_bit c 1396 row)) - (c_prime_bit c 116 row)) * (((((((a_prime_bit c 116 row) + (a_prime_bit c 436 row)) + (a_prime_bit c 756 row)) + (a_prime_bit c 1076 row)) + (a_prime_bit c 1396 row)) - (c_prime_bit c 116 row)) - 2)) * (((((((a_prime_bit c 116 row) + (a_prime_bit c 436 row)) + (a_prime_bit c 756 row)) + (a_prime_bit c 1076 row)) + (a_prime_bit c 1396 row)) - (c_prime_bit c 116 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2706_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2706 c row ↔ constraint_2706 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2707 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 117 row) + (a_prime_bit c 437 row)) + (a_prime_bit c 757 row)) + (a_prime_bit c 1077 row)) + (a_prime_bit c 1397 row)) - (c_prime_bit c 117 row)) * (((((((a_prime_bit c 117 row) + (a_prime_bit c 437 row)) + (a_prime_bit c 757 row)) + (a_prime_bit c 1077 row)) + (a_prime_bit c 1397 row)) - (c_prime_bit c 117 row)) - 2)) * (((((((a_prime_bit c 117 row) + (a_prime_bit c 437 row)) + (a_prime_bit c 757 row)) + (a_prime_bit c 1077 row)) + (a_prime_bit c 1397 row)) - (c_prime_bit c 117 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2707_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2707 c row ↔ constraint_2707 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2708 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 118 row) + (a_prime_bit c 438 row)) + (a_prime_bit c 758 row)) + (a_prime_bit c 1078 row)) + (a_prime_bit c 1398 row)) - (c_prime_bit c 118 row)) * (((((((a_prime_bit c 118 row) + (a_prime_bit c 438 row)) + (a_prime_bit c 758 row)) + (a_prime_bit c 1078 row)) + (a_prime_bit c 1398 row)) - (c_prime_bit c 118 row)) - 2)) * (((((((a_prime_bit c 118 row) + (a_prime_bit c 438 row)) + (a_prime_bit c 758 row)) + (a_prime_bit c 1078 row)) + (a_prime_bit c 1398 row)) - (c_prime_bit c 118 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2708_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2708 c row ↔ constraint_2708 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2709 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 119 row) + (a_prime_bit c 439 row)) + (a_prime_bit c 759 row)) + (a_prime_bit c 1079 row)) + (a_prime_bit c 1399 row)) - (c_prime_bit c 119 row)) * (((((((a_prime_bit c 119 row) + (a_prime_bit c 439 row)) + (a_prime_bit c 759 row)) + (a_prime_bit c 1079 row)) + (a_prime_bit c 1399 row)) - (c_prime_bit c 119 row)) - 2)) * (((((((a_prime_bit c 119 row) + (a_prime_bit c 439 row)) + (a_prime_bit c 759 row)) + (a_prime_bit c 1079 row)) + (a_prime_bit c 1399 row)) - (c_prime_bit c 119 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2709_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2709 c row ↔ constraint_2709 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2710 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 120 row) + (a_prime_bit c 440 row)) + (a_prime_bit c 760 row)) + (a_prime_bit c 1080 row)) + (a_prime_bit c 1400 row)) - (c_prime_bit c 120 row)) * (((((((a_prime_bit c 120 row) + (a_prime_bit c 440 row)) + (a_prime_bit c 760 row)) + (a_prime_bit c 1080 row)) + (a_prime_bit c 1400 row)) - (c_prime_bit c 120 row)) - 2)) * (((((((a_prime_bit c 120 row) + (a_prime_bit c 440 row)) + (a_prime_bit c 760 row)) + (a_prime_bit c 1080 row)) + (a_prime_bit c 1400 row)) - (c_prime_bit c 120 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2710_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2710 c row ↔ constraint_2710 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2711 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 121 row) + (a_prime_bit c 441 row)) + (a_prime_bit c 761 row)) + (a_prime_bit c 1081 row)) + (a_prime_bit c 1401 row)) - (c_prime_bit c 121 row)) * (((((((a_prime_bit c 121 row) + (a_prime_bit c 441 row)) + (a_prime_bit c 761 row)) + (a_prime_bit c 1081 row)) + (a_prime_bit c 1401 row)) - (c_prime_bit c 121 row)) - 2)) * (((((((a_prime_bit c 121 row) + (a_prime_bit c 441 row)) + (a_prime_bit c 761 row)) + (a_prime_bit c 1081 row)) + (a_prime_bit c 1401 row)) - (c_prime_bit c 121 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2711_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2711 c row ↔ constraint_2711 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2712 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 122 row) + (a_prime_bit c 442 row)) + (a_prime_bit c 762 row)) + (a_prime_bit c 1082 row)) + (a_prime_bit c 1402 row)) - (c_prime_bit c 122 row)) * (((((((a_prime_bit c 122 row) + (a_prime_bit c 442 row)) + (a_prime_bit c 762 row)) + (a_prime_bit c 1082 row)) + (a_prime_bit c 1402 row)) - (c_prime_bit c 122 row)) - 2)) * (((((((a_prime_bit c 122 row) + (a_prime_bit c 442 row)) + (a_prime_bit c 762 row)) + (a_prime_bit c 1082 row)) + (a_prime_bit c 1402 row)) - (c_prime_bit c 122 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2712_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2712 c row ↔ constraint_2712 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2713 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 123 row) + (a_prime_bit c 443 row)) + (a_prime_bit c 763 row)) + (a_prime_bit c 1083 row)) + (a_prime_bit c 1403 row)) - (c_prime_bit c 123 row)) * (((((((a_prime_bit c 123 row) + (a_prime_bit c 443 row)) + (a_prime_bit c 763 row)) + (a_prime_bit c 1083 row)) + (a_prime_bit c 1403 row)) - (c_prime_bit c 123 row)) - 2)) * (((((((a_prime_bit c 123 row) + (a_prime_bit c 443 row)) + (a_prime_bit c 763 row)) + (a_prime_bit c 1083 row)) + (a_prime_bit c 1403 row)) - (c_prime_bit c 123 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2713_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2713 c row ↔ constraint_2713 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2714 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 124 row) + (a_prime_bit c 444 row)) + (a_prime_bit c 764 row)) + (a_prime_bit c 1084 row)) + (a_prime_bit c 1404 row)) - (c_prime_bit c 124 row)) * (((((((a_prime_bit c 124 row) + (a_prime_bit c 444 row)) + (a_prime_bit c 764 row)) + (a_prime_bit c 1084 row)) + (a_prime_bit c 1404 row)) - (c_prime_bit c 124 row)) - 2)) * (((((((a_prime_bit c 124 row) + (a_prime_bit c 444 row)) + (a_prime_bit c 764 row)) + (a_prime_bit c 1084 row)) + (a_prime_bit c 1404 row)) - (c_prime_bit c 124 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2714_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2714 c row ↔ constraint_2714 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2715 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 125 row) + (a_prime_bit c 445 row)) + (a_prime_bit c 765 row)) + (a_prime_bit c 1085 row)) + (a_prime_bit c 1405 row)) - (c_prime_bit c 125 row)) * (((((((a_prime_bit c 125 row) + (a_prime_bit c 445 row)) + (a_prime_bit c 765 row)) + (a_prime_bit c 1085 row)) + (a_prime_bit c 1405 row)) - (c_prime_bit c 125 row)) - 2)) * (((((((a_prime_bit c 125 row) + (a_prime_bit c 445 row)) + (a_prime_bit c 765 row)) + (a_prime_bit c 1085 row)) + (a_prime_bit c 1405 row)) - (c_prime_bit c 125 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2715_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2715 c row ↔ constraint_2715 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2716 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 126 row) + (a_prime_bit c 446 row)) + (a_prime_bit c 766 row)) + (a_prime_bit c 1086 row)) + (a_prime_bit c 1406 row)) - (c_prime_bit c 126 row)) * (((((((a_prime_bit c 126 row) + (a_prime_bit c 446 row)) + (a_prime_bit c 766 row)) + (a_prime_bit c 1086 row)) + (a_prime_bit c 1406 row)) - (c_prime_bit c 126 row)) - 2)) * (((((((a_prime_bit c 126 row) + (a_prime_bit c 446 row)) + (a_prime_bit c 766 row)) + (a_prime_bit c 1086 row)) + (a_prime_bit c 1406 row)) - (c_prime_bit c 126 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2716_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2716 c row ↔ constraint_2716 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2717 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 127 row) + (a_prime_bit c 447 row)) + (a_prime_bit c 767 row)) + (a_prime_bit c 1087 row)) + (a_prime_bit c 1407 row)) - (c_prime_bit c 127 row)) * (((((((a_prime_bit c 127 row) + (a_prime_bit c 447 row)) + (a_prime_bit c 767 row)) + (a_prime_bit c 1087 row)) + (a_prime_bit c 1407 row)) - (c_prime_bit c 127 row)) - 2)) * (((((((a_prime_bit c 127 row) + (a_prime_bit c 447 row)) + (a_prime_bit c 767 row)) + (a_prime_bit c 1087 row)) + (a_prime_bit c 1407 row)) - (c_prime_bit c 127 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2717_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2717 c row ↔ constraint_2717 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2718 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 128 row) + (a_prime_bit c 448 row)) + (a_prime_bit c 768 row)) + (a_prime_bit c 1088 row)) + (a_prime_bit c 1408 row)) - (c_prime_bit c 128 row)) * (((((((a_prime_bit c 128 row) + (a_prime_bit c 448 row)) + (a_prime_bit c 768 row)) + (a_prime_bit c 1088 row)) + (a_prime_bit c 1408 row)) - (c_prime_bit c 128 row)) - 2)) * (((((((a_prime_bit c 128 row) + (a_prime_bit c 448 row)) + (a_prime_bit c 768 row)) + (a_prime_bit c 1088 row)) + (a_prime_bit c 1408 row)) - (c_prime_bit c 128 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2718_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2718 c row ↔ constraint_2718 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2719 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 129 row) + (a_prime_bit c 449 row)) + (a_prime_bit c 769 row)) + (a_prime_bit c 1089 row)) + (a_prime_bit c 1409 row)) - (c_prime_bit c 129 row)) * (((((((a_prime_bit c 129 row) + (a_prime_bit c 449 row)) + (a_prime_bit c 769 row)) + (a_prime_bit c 1089 row)) + (a_prime_bit c 1409 row)) - (c_prime_bit c 129 row)) - 2)) * (((((((a_prime_bit c 129 row) + (a_prime_bit c 449 row)) + (a_prime_bit c 769 row)) + (a_prime_bit c 1089 row)) + (a_prime_bit c 1409 row)) - (c_prime_bit c 129 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2719_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2719 c row ↔ constraint_2719 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2720 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 130 row) + (a_prime_bit c 450 row)) + (a_prime_bit c 770 row)) + (a_prime_bit c 1090 row)) + (a_prime_bit c 1410 row)) - (c_prime_bit c 130 row)) * (((((((a_prime_bit c 130 row) + (a_prime_bit c 450 row)) + (a_prime_bit c 770 row)) + (a_prime_bit c 1090 row)) + (a_prime_bit c 1410 row)) - (c_prime_bit c 130 row)) - 2)) * (((((((a_prime_bit c 130 row) + (a_prime_bit c 450 row)) + (a_prime_bit c 770 row)) + (a_prime_bit c 1090 row)) + (a_prime_bit c 1410 row)) - (c_prime_bit c 130 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2720_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2720 c row ↔ constraint_2720 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2721 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 131 row) + (a_prime_bit c 451 row)) + (a_prime_bit c 771 row)) + (a_prime_bit c 1091 row)) + (a_prime_bit c 1411 row)) - (c_prime_bit c 131 row)) * (((((((a_prime_bit c 131 row) + (a_prime_bit c 451 row)) + (a_prime_bit c 771 row)) + (a_prime_bit c 1091 row)) + (a_prime_bit c 1411 row)) - (c_prime_bit c 131 row)) - 2)) * (((((((a_prime_bit c 131 row) + (a_prime_bit c 451 row)) + (a_prime_bit c 771 row)) + (a_prime_bit c 1091 row)) + (a_prime_bit c 1411 row)) - (c_prime_bit c 131 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2721_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2721 c row ↔ constraint_2721 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2722 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 132 row) + (a_prime_bit c 452 row)) + (a_prime_bit c 772 row)) + (a_prime_bit c 1092 row)) + (a_prime_bit c 1412 row)) - (c_prime_bit c 132 row)) * (((((((a_prime_bit c 132 row) + (a_prime_bit c 452 row)) + (a_prime_bit c 772 row)) + (a_prime_bit c 1092 row)) + (a_prime_bit c 1412 row)) - (c_prime_bit c 132 row)) - 2)) * (((((((a_prime_bit c 132 row) + (a_prime_bit c 452 row)) + (a_prime_bit c 772 row)) + (a_prime_bit c 1092 row)) + (a_prime_bit c 1412 row)) - (c_prime_bit c 132 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2722_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2722 c row ↔ constraint_2722 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2723 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 133 row) + (a_prime_bit c 453 row)) + (a_prime_bit c 773 row)) + (a_prime_bit c 1093 row)) + (a_prime_bit c 1413 row)) - (c_prime_bit c 133 row)) * (((((((a_prime_bit c 133 row) + (a_prime_bit c 453 row)) + (a_prime_bit c 773 row)) + (a_prime_bit c 1093 row)) + (a_prime_bit c 1413 row)) - (c_prime_bit c 133 row)) - 2)) * (((((((a_prime_bit c 133 row) + (a_prime_bit c 453 row)) + (a_prime_bit c 773 row)) + (a_prime_bit c 1093 row)) + (a_prime_bit c 1413 row)) - (c_prime_bit c 133 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2723_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2723 c row ↔ constraint_2723 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2724 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 134 row) + (a_prime_bit c 454 row)) + (a_prime_bit c 774 row)) + (a_prime_bit c 1094 row)) + (a_prime_bit c 1414 row)) - (c_prime_bit c 134 row)) * (((((((a_prime_bit c 134 row) + (a_prime_bit c 454 row)) + (a_prime_bit c 774 row)) + (a_prime_bit c 1094 row)) + (a_prime_bit c 1414 row)) - (c_prime_bit c 134 row)) - 2)) * (((((((a_prime_bit c 134 row) + (a_prime_bit c 454 row)) + (a_prime_bit c 774 row)) + (a_prime_bit c 1094 row)) + (a_prime_bit c 1414 row)) - (c_prime_bit c 134 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2724_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2724 c row ↔ constraint_2724 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2725 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 135 row) + (a_prime_bit c 455 row)) + (a_prime_bit c 775 row)) + (a_prime_bit c 1095 row)) + (a_prime_bit c 1415 row)) - (c_prime_bit c 135 row)) * (((((((a_prime_bit c 135 row) + (a_prime_bit c 455 row)) + (a_prime_bit c 775 row)) + (a_prime_bit c 1095 row)) + (a_prime_bit c 1415 row)) - (c_prime_bit c 135 row)) - 2)) * (((((((a_prime_bit c 135 row) + (a_prime_bit c 455 row)) + (a_prime_bit c 775 row)) + (a_prime_bit c 1095 row)) + (a_prime_bit c 1415 row)) - (c_prime_bit c 135 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2725_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2725 c row ↔ constraint_2725 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2726 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 136 row) + (a_prime_bit c 456 row)) + (a_prime_bit c 776 row)) + (a_prime_bit c 1096 row)) + (a_prime_bit c 1416 row)) - (c_prime_bit c 136 row)) * (((((((a_prime_bit c 136 row) + (a_prime_bit c 456 row)) + (a_prime_bit c 776 row)) + (a_prime_bit c 1096 row)) + (a_prime_bit c 1416 row)) - (c_prime_bit c 136 row)) - 2)) * (((((((a_prime_bit c 136 row) + (a_prime_bit c 456 row)) + (a_prime_bit c 776 row)) + (a_prime_bit c 1096 row)) + (a_prime_bit c 1416 row)) - (c_prime_bit c 136 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2726_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2726 c row ↔ constraint_2726 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2727 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 137 row) + (a_prime_bit c 457 row)) + (a_prime_bit c 777 row)) + (a_prime_bit c 1097 row)) + (a_prime_bit c 1417 row)) - (c_prime_bit c 137 row)) * (((((((a_prime_bit c 137 row) + (a_prime_bit c 457 row)) + (a_prime_bit c 777 row)) + (a_prime_bit c 1097 row)) + (a_prime_bit c 1417 row)) - (c_prime_bit c 137 row)) - 2)) * (((((((a_prime_bit c 137 row) + (a_prime_bit c 457 row)) + (a_prime_bit c 777 row)) + (a_prime_bit c 1097 row)) + (a_prime_bit c 1417 row)) - (c_prime_bit c 137 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2727_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2727 c row ↔ constraint_2727 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2728 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 138 row) + (a_prime_bit c 458 row)) + (a_prime_bit c 778 row)) + (a_prime_bit c 1098 row)) + (a_prime_bit c 1418 row)) - (c_prime_bit c 138 row)) * (((((((a_prime_bit c 138 row) + (a_prime_bit c 458 row)) + (a_prime_bit c 778 row)) + (a_prime_bit c 1098 row)) + (a_prime_bit c 1418 row)) - (c_prime_bit c 138 row)) - 2)) * (((((((a_prime_bit c 138 row) + (a_prime_bit c 458 row)) + (a_prime_bit c 778 row)) + (a_prime_bit c 1098 row)) + (a_prime_bit c 1418 row)) - (c_prime_bit c 138 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2728_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2728 c row ↔ constraint_2728 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2729 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 139 row) + (a_prime_bit c 459 row)) + (a_prime_bit c 779 row)) + (a_prime_bit c 1099 row)) + (a_prime_bit c 1419 row)) - (c_prime_bit c 139 row)) * (((((((a_prime_bit c 139 row) + (a_prime_bit c 459 row)) + (a_prime_bit c 779 row)) + (a_prime_bit c 1099 row)) + (a_prime_bit c 1419 row)) - (c_prime_bit c 139 row)) - 2)) * (((((((a_prime_bit c 139 row) + (a_prime_bit c 459 row)) + (a_prime_bit c 779 row)) + (a_prime_bit c 1099 row)) + (a_prime_bit c 1419 row)) - (c_prime_bit c 139 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2729_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2729 c row ↔ constraint_2729 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2730 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 140 row) + (a_prime_bit c 460 row)) + (a_prime_bit c 780 row)) + (a_prime_bit c 1100 row)) + (a_prime_bit c 1420 row)) - (c_prime_bit c 140 row)) * (((((((a_prime_bit c 140 row) + (a_prime_bit c 460 row)) + (a_prime_bit c 780 row)) + (a_prime_bit c 1100 row)) + (a_prime_bit c 1420 row)) - (c_prime_bit c 140 row)) - 2)) * (((((((a_prime_bit c 140 row) + (a_prime_bit c 460 row)) + (a_prime_bit c 780 row)) + (a_prime_bit c 1100 row)) + (a_prime_bit c 1420 row)) - (c_prime_bit c 140 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2730_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2730 c row ↔ constraint_2730 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2731 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 141 row) + (a_prime_bit c 461 row)) + (a_prime_bit c 781 row)) + (a_prime_bit c 1101 row)) + (a_prime_bit c 1421 row)) - (c_prime_bit c 141 row)) * (((((((a_prime_bit c 141 row) + (a_prime_bit c 461 row)) + (a_prime_bit c 781 row)) + (a_prime_bit c 1101 row)) + (a_prime_bit c 1421 row)) - (c_prime_bit c 141 row)) - 2)) * (((((((a_prime_bit c 141 row) + (a_prime_bit c 461 row)) + (a_prime_bit c 781 row)) + (a_prime_bit c 1101 row)) + (a_prime_bit c 1421 row)) - (c_prime_bit c 141 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2731_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2731 c row ↔ constraint_2731 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2732 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 142 row) + (a_prime_bit c 462 row)) + (a_prime_bit c 782 row)) + (a_prime_bit c 1102 row)) + (a_prime_bit c 1422 row)) - (c_prime_bit c 142 row)) * (((((((a_prime_bit c 142 row) + (a_prime_bit c 462 row)) + (a_prime_bit c 782 row)) + (a_prime_bit c 1102 row)) + (a_prime_bit c 1422 row)) - (c_prime_bit c 142 row)) - 2)) * (((((((a_prime_bit c 142 row) + (a_prime_bit c 462 row)) + (a_prime_bit c 782 row)) + (a_prime_bit c 1102 row)) + (a_prime_bit c 1422 row)) - (c_prime_bit c 142 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2732_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2732 c row ↔ constraint_2732 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2733 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 143 row) + (a_prime_bit c 463 row)) + (a_prime_bit c 783 row)) + (a_prime_bit c 1103 row)) + (a_prime_bit c 1423 row)) - (c_prime_bit c 143 row)) * (((((((a_prime_bit c 143 row) + (a_prime_bit c 463 row)) + (a_prime_bit c 783 row)) + (a_prime_bit c 1103 row)) + (a_prime_bit c 1423 row)) - (c_prime_bit c 143 row)) - 2)) * (((((((a_prime_bit c 143 row) + (a_prime_bit c 463 row)) + (a_prime_bit c 783 row)) + (a_prime_bit c 1103 row)) + (a_prime_bit c 1423 row)) - (c_prime_bit c 143 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2733_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2733 c row ↔ constraint_2733 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2734 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 144 row) + (a_prime_bit c 464 row)) + (a_prime_bit c 784 row)) + (a_prime_bit c 1104 row)) + (a_prime_bit c 1424 row)) - (c_prime_bit c 144 row)) * (((((((a_prime_bit c 144 row) + (a_prime_bit c 464 row)) + (a_prime_bit c 784 row)) + (a_prime_bit c 1104 row)) + (a_prime_bit c 1424 row)) - (c_prime_bit c 144 row)) - 2)) * (((((((a_prime_bit c 144 row) + (a_prime_bit c 464 row)) + (a_prime_bit c 784 row)) + (a_prime_bit c 1104 row)) + (a_prime_bit c 1424 row)) - (c_prime_bit c 144 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2734_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2734 c row ↔ constraint_2734 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2735 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 145 row) + (a_prime_bit c 465 row)) + (a_prime_bit c 785 row)) + (a_prime_bit c 1105 row)) + (a_prime_bit c 1425 row)) - (c_prime_bit c 145 row)) * (((((((a_prime_bit c 145 row) + (a_prime_bit c 465 row)) + (a_prime_bit c 785 row)) + (a_prime_bit c 1105 row)) + (a_prime_bit c 1425 row)) - (c_prime_bit c 145 row)) - 2)) * (((((((a_prime_bit c 145 row) + (a_prime_bit c 465 row)) + (a_prime_bit c 785 row)) + (a_prime_bit c 1105 row)) + (a_prime_bit c 1425 row)) - (c_prime_bit c 145 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2735_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2735 c row ↔ constraint_2735 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2736 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 146 row) + (a_prime_bit c 466 row)) + (a_prime_bit c 786 row)) + (a_prime_bit c 1106 row)) + (a_prime_bit c 1426 row)) - (c_prime_bit c 146 row)) * (((((((a_prime_bit c 146 row) + (a_prime_bit c 466 row)) + (a_prime_bit c 786 row)) + (a_prime_bit c 1106 row)) + (a_prime_bit c 1426 row)) - (c_prime_bit c 146 row)) - 2)) * (((((((a_prime_bit c 146 row) + (a_prime_bit c 466 row)) + (a_prime_bit c 786 row)) + (a_prime_bit c 1106 row)) + (a_prime_bit c 1426 row)) - (c_prime_bit c 146 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2736_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2736 c row ↔ constraint_2736 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2737 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 147 row) + (a_prime_bit c 467 row)) + (a_prime_bit c 787 row)) + (a_prime_bit c 1107 row)) + (a_prime_bit c 1427 row)) - (c_prime_bit c 147 row)) * (((((((a_prime_bit c 147 row) + (a_prime_bit c 467 row)) + (a_prime_bit c 787 row)) + (a_prime_bit c 1107 row)) + (a_prime_bit c 1427 row)) - (c_prime_bit c 147 row)) - 2)) * (((((((a_prime_bit c 147 row) + (a_prime_bit c 467 row)) + (a_prime_bit c 787 row)) + (a_prime_bit c 1107 row)) + (a_prime_bit c 1427 row)) - (c_prime_bit c 147 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2737_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2737 c row ↔ constraint_2737 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2738 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 148 row) + (a_prime_bit c 468 row)) + (a_prime_bit c 788 row)) + (a_prime_bit c 1108 row)) + (a_prime_bit c 1428 row)) - (c_prime_bit c 148 row)) * (((((((a_prime_bit c 148 row) + (a_prime_bit c 468 row)) + (a_prime_bit c 788 row)) + (a_prime_bit c 1108 row)) + (a_prime_bit c 1428 row)) - (c_prime_bit c 148 row)) - 2)) * (((((((a_prime_bit c 148 row) + (a_prime_bit c 468 row)) + (a_prime_bit c 788 row)) + (a_prime_bit c 1108 row)) + (a_prime_bit c 1428 row)) - (c_prime_bit c 148 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2738_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2738 c row ↔ constraint_2738 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2739 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 149 row) + (a_prime_bit c 469 row)) + (a_prime_bit c 789 row)) + (a_prime_bit c 1109 row)) + (a_prime_bit c 1429 row)) - (c_prime_bit c 149 row)) * (((((((a_prime_bit c 149 row) + (a_prime_bit c 469 row)) + (a_prime_bit c 789 row)) + (a_prime_bit c 1109 row)) + (a_prime_bit c 1429 row)) - (c_prime_bit c 149 row)) - 2)) * (((((((a_prime_bit c 149 row) + (a_prime_bit c 469 row)) + (a_prime_bit c 789 row)) + (a_prime_bit c 1109 row)) + (a_prime_bit c 1429 row)) - (c_prime_bit c 149 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2739_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2739 c row ↔ constraint_2739 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2740 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 150 row) + (a_prime_bit c 470 row)) + (a_prime_bit c 790 row)) + (a_prime_bit c 1110 row)) + (a_prime_bit c 1430 row)) - (c_prime_bit c 150 row)) * (((((((a_prime_bit c 150 row) + (a_prime_bit c 470 row)) + (a_prime_bit c 790 row)) + (a_prime_bit c 1110 row)) + (a_prime_bit c 1430 row)) - (c_prime_bit c 150 row)) - 2)) * (((((((a_prime_bit c 150 row) + (a_prime_bit c 470 row)) + (a_prime_bit c 790 row)) + (a_prime_bit c 1110 row)) + (a_prime_bit c 1430 row)) - (c_prime_bit c 150 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2740_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2740 c row ↔ constraint_2740 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2741 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 151 row) + (a_prime_bit c 471 row)) + (a_prime_bit c 791 row)) + (a_prime_bit c 1111 row)) + (a_prime_bit c 1431 row)) - (c_prime_bit c 151 row)) * (((((((a_prime_bit c 151 row) + (a_prime_bit c 471 row)) + (a_prime_bit c 791 row)) + (a_prime_bit c 1111 row)) + (a_prime_bit c 1431 row)) - (c_prime_bit c 151 row)) - 2)) * (((((((a_prime_bit c 151 row) + (a_prime_bit c 471 row)) + (a_prime_bit c 791 row)) + (a_prime_bit c 1111 row)) + (a_prime_bit c 1431 row)) - (c_prime_bit c 151 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2741_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2741 c row ↔ constraint_2741 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2742 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 152 row) + (a_prime_bit c 472 row)) + (a_prime_bit c 792 row)) + (a_prime_bit c 1112 row)) + (a_prime_bit c 1432 row)) - (c_prime_bit c 152 row)) * (((((((a_prime_bit c 152 row) + (a_prime_bit c 472 row)) + (a_prime_bit c 792 row)) + (a_prime_bit c 1112 row)) + (a_prime_bit c 1432 row)) - (c_prime_bit c 152 row)) - 2)) * (((((((a_prime_bit c 152 row) + (a_prime_bit c 472 row)) + (a_prime_bit c 792 row)) + (a_prime_bit c 1112 row)) + (a_prime_bit c 1432 row)) - (c_prime_bit c 152 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2742_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2742 c row ↔ constraint_2742 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2743 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 153 row) + (a_prime_bit c 473 row)) + (a_prime_bit c 793 row)) + (a_prime_bit c 1113 row)) + (a_prime_bit c 1433 row)) - (c_prime_bit c 153 row)) * (((((((a_prime_bit c 153 row) + (a_prime_bit c 473 row)) + (a_prime_bit c 793 row)) + (a_prime_bit c 1113 row)) + (a_prime_bit c 1433 row)) - (c_prime_bit c 153 row)) - 2)) * (((((((a_prime_bit c 153 row) + (a_prime_bit c 473 row)) + (a_prime_bit c 793 row)) + (a_prime_bit c 1113 row)) + (a_prime_bit c 1433 row)) - (c_prime_bit c 153 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2743_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2743 c row ↔ constraint_2743 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2744 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 154 row) + (a_prime_bit c 474 row)) + (a_prime_bit c 794 row)) + (a_prime_bit c 1114 row)) + (a_prime_bit c 1434 row)) - (c_prime_bit c 154 row)) * (((((((a_prime_bit c 154 row) + (a_prime_bit c 474 row)) + (a_prime_bit c 794 row)) + (a_prime_bit c 1114 row)) + (a_prime_bit c 1434 row)) - (c_prime_bit c 154 row)) - 2)) * (((((((a_prime_bit c 154 row) + (a_prime_bit c 474 row)) + (a_prime_bit c 794 row)) + (a_prime_bit c 1114 row)) + (a_prime_bit c 1434 row)) - (c_prime_bit c 154 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2744_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2744 c row ↔ constraint_2744 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2745 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 155 row) + (a_prime_bit c 475 row)) + (a_prime_bit c 795 row)) + (a_prime_bit c 1115 row)) + (a_prime_bit c 1435 row)) - (c_prime_bit c 155 row)) * (((((((a_prime_bit c 155 row) + (a_prime_bit c 475 row)) + (a_prime_bit c 795 row)) + (a_prime_bit c 1115 row)) + (a_prime_bit c 1435 row)) - (c_prime_bit c 155 row)) - 2)) * (((((((a_prime_bit c 155 row) + (a_prime_bit c 475 row)) + (a_prime_bit c 795 row)) + (a_prime_bit c 1115 row)) + (a_prime_bit c 1435 row)) - (c_prime_bit c 155 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2745_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2745 c row ↔ constraint_2745 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2746 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 156 row) + (a_prime_bit c 476 row)) + (a_prime_bit c 796 row)) + (a_prime_bit c 1116 row)) + (a_prime_bit c 1436 row)) - (c_prime_bit c 156 row)) * (((((((a_prime_bit c 156 row) + (a_prime_bit c 476 row)) + (a_prime_bit c 796 row)) + (a_prime_bit c 1116 row)) + (a_prime_bit c 1436 row)) - (c_prime_bit c 156 row)) - 2)) * (((((((a_prime_bit c 156 row) + (a_prime_bit c 476 row)) + (a_prime_bit c 796 row)) + (a_prime_bit c 1116 row)) + (a_prime_bit c 1436 row)) - (c_prime_bit c 156 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2746_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2746 c row ↔ constraint_2746 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2747 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 157 row) + (a_prime_bit c 477 row)) + (a_prime_bit c 797 row)) + (a_prime_bit c 1117 row)) + (a_prime_bit c 1437 row)) - (c_prime_bit c 157 row)) * (((((((a_prime_bit c 157 row) + (a_prime_bit c 477 row)) + (a_prime_bit c 797 row)) + (a_prime_bit c 1117 row)) + (a_prime_bit c 1437 row)) - (c_prime_bit c 157 row)) - 2)) * (((((((a_prime_bit c 157 row) + (a_prime_bit c 477 row)) + (a_prime_bit c 797 row)) + (a_prime_bit c 1117 row)) + (a_prime_bit c 1437 row)) - (c_prime_bit c 157 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2747_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2747 c row ↔ constraint_2747 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2748 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 158 row) + (a_prime_bit c 478 row)) + (a_prime_bit c 798 row)) + (a_prime_bit c 1118 row)) + (a_prime_bit c 1438 row)) - (c_prime_bit c 158 row)) * (((((((a_prime_bit c 158 row) + (a_prime_bit c 478 row)) + (a_prime_bit c 798 row)) + (a_prime_bit c 1118 row)) + (a_prime_bit c 1438 row)) - (c_prime_bit c 158 row)) - 2)) * (((((((a_prime_bit c 158 row) + (a_prime_bit c 478 row)) + (a_prime_bit c 798 row)) + (a_prime_bit c 1118 row)) + (a_prime_bit c 1438 row)) - (c_prime_bit c 158 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2748_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2748 c row ↔ constraint_2748 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2749 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 159 row) + (a_prime_bit c 479 row)) + (a_prime_bit c 799 row)) + (a_prime_bit c 1119 row)) + (a_prime_bit c 1439 row)) - (c_prime_bit c 159 row)) * (((((((a_prime_bit c 159 row) + (a_prime_bit c 479 row)) + (a_prime_bit c 799 row)) + (a_prime_bit c 1119 row)) + (a_prime_bit c 1439 row)) - (c_prime_bit c 159 row)) - 2)) * (((((((a_prime_bit c 159 row) + (a_prime_bit c 479 row)) + (a_prime_bit c 799 row)) + (a_prime_bit c 1119 row)) + (a_prime_bit c 1439 row)) - (c_prime_bit c 159 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2749_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2749 c row ↔ constraint_2749 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2750 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 160 row) + (a_prime_bit c 480 row)) + (a_prime_bit c 800 row)) + (a_prime_bit c 1120 row)) + (a_prime_bit c 1440 row)) - (c_prime_bit c 160 row)) * (((((((a_prime_bit c 160 row) + (a_prime_bit c 480 row)) + (a_prime_bit c 800 row)) + (a_prime_bit c 1120 row)) + (a_prime_bit c 1440 row)) - (c_prime_bit c 160 row)) - 2)) * (((((((a_prime_bit c 160 row) + (a_prime_bit c 480 row)) + (a_prime_bit c 800 row)) + (a_prime_bit c 1120 row)) + (a_prime_bit c 1440 row)) - (c_prime_bit c 160 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2750_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2750 c row ↔ constraint_2750 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2751 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 161 row) + (a_prime_bit c 481 row)) + (a_prime_bit c 801 row)) + (a_prime_bit c 1121 row)) + (a_prime_bit c 1441 row)) - (c_prime_bit c 161 row)) * (((((((a_prime_bit c 161 row) + (a_prime_bit c 481 row)) + (a_prime_bit c 801 row)) + (a_prime_bit c 1121 row)) + (a_prime_bit c 1441 row)) - (c_prime_bit c 161 row)) - 2)) * (((((((a_prime_bit c 161 row) + (a_prime_bit c 481 row)) + (a_prime_bit c 801 row)) + (a_prime_bit c 1121 row)) + (a_prime_bit c 1441 row)) - (c_prime_bit c 161 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2751_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2751 c row ↔ constraint_2751 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2752 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 162 row) + (a_prime_bit c 482 row)) + (a_prime_bit c 802 row)) + (a_prime_bit c 1122 row)) + (a_prime_bit c 1442 row)) - (c_prime_bit c 162 row)) * (((((((a_prime_bit c 162 row) + (a_prime_bit c 482 row)) + (a_prime_bit c 802 row)) + (a_prime_bit c 1122 row)) + (a_prime_bit c 1442 row)) - (c_prime_bit c 162 row)) - 2)) * (((((((a_prime_bit c 162 row) + (a_prime_bit c 482 row)) + (a_prime_bit c 802 row)) + (a_prime_bit c 1122 row)) + (a_prime_bit c 1442 row)) - (c_prime_bit c 162 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2752_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2752 c row ↔ constraint_2752 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2753 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 163 row) + (a_prime_bit c 483 row)) + (a_prime_bit c 803 row)) + (a_prime_bit c 1123 row)) + (a_prime_bit c 1443 row)) - (c_prime_bit c 163 row)) * (((((((a_prime_bit c 163 row) + (a_prime_bit c 483 row)) + (a_prime_bit c 803 row)) + (a_prime_bit c 1123 row)) + (a_prime_bit c 1443 row)) - (c_prime_bit c 163 row)) - 2)) * (((((((a_prime_bit c 163 row) + (a_prime_bit c 483 row)) + (a_prime_bit c 803 row)) + (a_prime_bit c 1123 row)) + (a_prime_bit c 1443 row)) - (c_prime_bit c 163 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2753_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2753 c row ↔ constraint_2753 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2754 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 164 row) + (a_prime_bit c 484 row)) + (a_prime_bit c 804 row)) + (a_prime_bit c 1124 row)) + (a_prime_bit c 1444 row)) - (c_prime_bit c 164 row)) * (((((((a_prime_bit c 164 row) + (a_prime_bit c 484 row)) + (a_prime_bit c 804 row)) + (a_prime_bit c 1124 row)) + (a_prime_bit c 1444 row)) - (c_prime_bit c 164 row)) - 2)) * (((((((a_prime_bit c 164 row) + (a_prime_bit c 484 row)) + (a_prime_bit c 804 row)) + (a_prime_bit c 1124 row)) + (a_prime_bit c 1444 row)) - (c_prime_bit c 164 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2754_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2754 c row ↔ constraint_2754 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2755 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 165 row) + (a_prime_bit c 485 row)) + (a_prime_bit c 805 row)) + (a_prime_bit c 1125 row)) + (a_prime_bit c 1445 row)) - (c_prime_bit c 165 row)) * (((((((a_prime_bit c 165 row) + (a_prime_bit c 485 row)) + (a_prime_bit c 805 row)) + (a_prime_bit c 1125 row)) + (a_prime_bit c 1445 row)) - (c_prime_bit c 165 row)) - 2)) * (((((((a_prime_bit c 165 row) + (a_prime_bit c 485 row)) + (a_prime_bit c 805 row)) + (a_prime_bit c 1125 row)) + (a_prime_bit c 1445 row)) - (c_prime_bit c 165 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2755_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2755 c row ↔ constraint_2755 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2756 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 166 row) + (a_prime_bit c 486 row)) + (a_prime_bit c 806 row)) + (a_prime_bit c 1126 row)) + (a_prime_bit c 1446 row)) - (c_prime_bit c 166 row)) * (((((((a_prime_bit c 166 row) + (a_prime_bit c 486 row)) + (a_prime_bit c 806 row)) + (a_prime_bit c 1126 row)) + (a_prime_bit c 1446 row)) - (c_prime_bit c 166 row)) - 2)) * (((((((a_prime_bit c 166 row) + (a_prime_bit c 486 row)) + (a_prime_bit c 806 row)) + (a_prime_bit c 1126 row)) + (a_prime_bit c 1446 row)) - (c_prime_bit c 166 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2756_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2756 c row ↔ constraint_2756 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2757 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 167 row) + (a_prime_bit c 487 row)) + (a_prime_bit c 807 row)) + (a_prime_bit c 1127 row)) + (a_prime_bit c 1447 row)) - (c_prime_bit c 167 row)) * (((((((a_prime_bit c 167 row) + (a_prime_bit c 487 row)) + (a_prime_bit c 807 row)) + (a_prime_bit c 1127 row)) + (a_prime_bit c 1447 row)) - (c_prime_bit c 167 row)) - 2)) * (((((((a_prime_bit c 167 row) + (a_prime_bit c 487 row)) + (a_prime_bit c 807 row)) + (a_prime_bit c 1127 row)) + (a_prime_bit c 1447 row)) - (c_prime_bit c 167 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2757_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2757 c row ↔ constraint_2757 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2758 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 168 row) + (a_prime_bit c 488 row)) + (a_prime_bit c 808 row)) + (a_prime_bit c 1128 row)) + (a_prime_bit c 1448 row)) - (c_prime_bit c 168 row)) * (((((((a_prime_bit c 168 row) + (a_prime_bit c 488 row)) + (a_prime_bit c 808 row)) + (a_prime_bit c 1128 row)) + (a_prime_bit c 1448 row)) - (c_prime_bit c 168 row)) - 2)) * (((((((a_prime_bit c 168 row) + (a_prime_bit c 488 row)) + (a_prime_bit c 808 row)) + (a_prime_bit c 1128 row)) + (a_prime_bit c 1448 row)) - (c_prime_bit c 168 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2758_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2758 c row ↔ constraint_2758 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2759 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 169 row) + (a_prime_bit c 489 row)) + (a_prime_bit c 809 row)) + (a_prime_bit c 1129 row)) + (a_prime_bit c 1449 row)) - (c_prime_bit c 169 row)) * (((((((a_prime_bit c 169 row) + (a_prime_bit c 489 row)) + (a_prime_bit c 809 row)) + (a_prime_bit c 1129 row)) + (a_prime_bit c 1449 row)) - (c_prime_bit c 169 row)) - 2)) * (((((((a_prime_bit c 169 row) + (a_prime_bit c 489 row)) + (a_prime_bit c 809 row)) + (a_prime_bit c 1129 row)) + (a_prime_bit c 1449 row)) - (c_prime_bit c 169 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2759_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2759 c row ↔ constraint_2759 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2760 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 170 row) + (a_prime_bit c 490 row)) + (a_prime_bit c 810 row)) + (a_prime_bit c 1130 row)) + (a_prime_bit c 1450 row)) - (c_prime_bit c 170 row)) * (((((((a_prime_bit c 170 row) + (a_prime_bit c 490 row)) + (a_prime_bit c 810 row)) + (a_prime_bit c 1130 row)) + (a_prime_bit c 1450 row)) - (c_prime_bit c 170 row)) - 2)) * (((((((a_prime_bit c 170 row) + (a_prime_bit c 490 row)) + (a_prime_bit c 810 row)) + (a_prime_bit c 1130 row)) + (a_prime_bit c 1450 row)) - (c_prime_bit c 170 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2760_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2760 c row ↔ constraint_2760 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2761 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 171 row) + (a_prime_bit c 491 row)) + (a_prime_bit c 811 row)) + (a_prime_bit c 1131 row)) + (a_prime_bit c 1451 row)) - (c_prime_bit c 171 row)) * (((((((a_prime_bit c 171 row) + (a_prime_bit c 491 row)) + (a_prime_bit c 811 row)) + (a_prime_bit c 1131 row)) + (a_prime_bit c 1451 row)) - (c_prime_bit c 171 row)) - 2)) * (((((((a_prime_bit c 171 row) + (a_prime_bit c 491 row)) + (a_prime_bit c 811 row)) + (a_prime_bit c 1131 row)) + (a_prime_bit c 1451 row)) - (c_prime_bit c 171 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2761_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2761 c row ↔ constraint_2761 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2762 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 172 row) + (a_prime_bit c 492 row)) + (a_prime_bit c 812 row)) + (a_prime_bit c 1132 row)) + (a_prime_bit c 1452 row)) - (c_prime_bit c 172 row)) * (((((((a_prime_bit c 172 row) + (a_prime_bit c 492 row)) + (a_prime_bit c 812 row)) + (a_prime_bit c 1132 row)) + (a_prime_bit c 1452 row)) - (c_prime_bit c 172 row)) - 2)) * (((((((a_prime_bit c 172 row) + (a_prime_bit c 492 row)) + (a_prime_bit c 812 row)) + (a_prime_bit c 1132 row)) + (a_prime_bit c 1452 row)) - (c_prime_bit c 172 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2762_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2762 c row ↔ constraint_2762 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2763 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 173 row) + (a_prime_bit c 493 row)) + (a_prime_bit c 813 row)) + (a_prime_bit c 1133 row)) + (a_prime_bit c 1453 row)) - (c_prime_bit c 173 row)) * (((((((a_prime_bit c 173 row) + (a_prime_bit c 493 row)) + (a_prime_bit c 813 row)) + (a_prime_bit c 1133 row)) + (a_prime_bit c 1453 row)) - (c_prime_bit c 173 row)) - 2)) * (((((((a_prime_bit c 173 row) + (a_prime_bit c 493 row)) + (a_prime_bit c 813 row)) + (a_prime_bit c 1133 row)) + (a_prime_bit c 1453 row)) - (c_prime_bit c 173 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2763_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2763 c row ↔ constraint_2763 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2764 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 174 row) + (a_prime_bit c 494 row)) + (a_prime_bit c 814 row)) + (a_prime_bit c 1134 row)) + (a_prime_bit c 1454 row)) - (c_prime_bit c 174 row)) * (((((((a_prime_bit c 174 row) + (a_prime_bit c 494 row)) + (a_prime_bit c 814 row)) + (a_prime_bit c 1134 row)) + (a_prime_bit c 1454 row)) - (c_prime_bit c 174 row)) - 2)) * (((((((a_prime_bit c 174 row) + (a_prime_bit c 494 row)) + (a_prime_bit c 814 row)) + (a_prime_bit c 1134 row)) + (a_prime_bit c 1454 row)) - (c_prime_bit c 174 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2764_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2764 c row ↔ constraint_2764 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2765 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 175 row) + (a_prime_bit c 495 row)) + (a_prime_bit c 815 row)) + (a_prime_bit c 1135 row)) + (a_prime_bit c 1455 row)) - (c_prime_bit c 175 row)) * (((((((a_prime_bit c 175 row) + (a_prime_bit c 495 row)) + (a_prime_bit c 815 row)) + (a_prime_bit c 1135 row)) + (a_prime_bit c 1455 row)) - (c_prime_bit c 175 row)) - 2)) * (((((((a_prime_bit c 175 row) + (a_prime_bit c 495 row)) + (a_prime_bit c 815 row)) + (a_prime_bit c 1135 row)) + (a_prime_bit c 1455 row)) - (c_prime_bit c 175 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2765_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2765 c row ↔ constraint_2765 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2766 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 176 row) + (a_prime_bit c 496 row)) + (a_prime_bit c 816 row)) + (a_prime_bit c 1136 row)) + (a_prime_bit c 1456 row)) - (c_prime_bit c 176 row)) * (((((((a_prime_bit c 176 row) + (a_prime_bit c 496 row)) + (a_prime_bit c 816 row)) + (a_prime_bit c 1136 row)) + (a_prime_bit c 1456 row)) - (c_prime_bit c 176 row)) - 2)) * (((((((a_prime_bit c 176 row) + (a_prime_bit c 496 row)) + (a_prime_bit c 816 row)) + (a_prime_bit c 1136 row)) + (a_prime_bit c 1456 row)) - (c_prime_bit c 176 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2766_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2766 c row ↔ constraint_2766 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2767 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 177 row) + (a_prime_bit c 497 row)) + (a_prime_bit c 817 row)) + (a_prime_bit c 1137 row)) + (a_prime_bit c 1457 row)) - (c_prime_bit c 177 row)) * (((((((a_prime_bit c 177 row) + (a_prime_bit c 497 row)) + (a_prime_bit c 817 row)) + (a_prime_bit c 1137 row)) + (a_prime_bit c 1457 row)) - (c_prime_bit c 177 row)) - 2)) * (((((((a_prime_bit c 177 row) + (a_prime_bit c 497 row)) + (a_prime_bit c 817 row)) + (a_prime_bit c 1137 row)) + (a_prime_bit c 1457 row)) - (c_prime_bit c 177 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2767_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2767 c row ↔ constraint_2767 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2768 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 178 row) + (a_prime_bit c 498 row)) + (a_prime_bit c 818 row)) + (a_prime_bit c 1138 row)) + (a_prime_bit c 1458 row)) - (c_prime_bit c 178 row)) * (((((((a_prime_bit c 178 row) + (a_prime_bit c 498 row)) + (a_prime_bit c 818 row)) + (a_prime_bit c 1138 row)) + (a_prime_bit c 1458 row)) - (c_prime_bit c 178 row)) - 2)) * (((((((a_prime_bit c 178 row) + (a_prime_bit c 498 row)) + (a_prime_bit c 818 row)) + (a_prime_bit c 1138 row)) + (a_prime_bit c 1458 row)) - (c_prime_bit c 178 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2768_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2768 c row ↔ constraint_2768 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2769 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 179 row) + (a_prime_bit c 499 row)) + (a_prime_bit c 819 row)) + (a_prime_bit c 1139 row)) + (a_prime_bit c 1459 row)) - (c_prime_bit c 179 row)) * (((((((a_prime_bit c 179 row) + (a_prime_bit c 499 row)) + (a_prime_bit c 819 row)) + (a_prime_bit c 1139 row)) + (a_prime_bit c 1459 row)) - (c_prime_bit c 179 row)) - 2)) * (((((((a_prime_bit c 179 row) + (a_prime_bit c 499 row)) + (a_prime_bit c 819 row)) + (a_prime_bit c 1139 row)) + (a_prime_bit c 1459 row)) - (c_prime_bit c 179 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2769_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2769 c row ↔ constraint_2769 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2770 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 180 row) + (a_prime_bit c 500 row)) + (a_prime_bit c 820 row)) + (a_prime_bit c 1140 row)) + (a_prime_bit c 1460 row)) - (c_prime_bit c 180 row)) * (((((((a_prime_bit c 180 row) + (a_prime_bit c 500 row)) + (a_prime_bit c 820 row)) + (a_prime_bit c 1140 row)) + (a_prime_bit c 1460 row)) - (c_prime_bit c 180 row)) - 2)) * (((((((a_prime_bit c 180 row) + (a_prime_bit c 500 row)) + (a_prime_bit c 820 row)) + (a_prime_bit c 1140 row)) + (a_prime_bit c 1460 row)) - (c_prime_bit c 180 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2770_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2770 c row ↔ constraint_2770 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2771 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 181 row) + (a_prime_bit c 501 row)) + (a_prime_bit c 821 row)) + (a_prime_bit c 1141 row)) + (a_prime_bit c 1461 row)) - (c_prime_bit c 181 row)) * (((((((a_prime_bit c 181 row) + (a_prime_bit c 501 row)) + (a_prime_bit c 821 row)) + (a_prime_bit c 1141 row)) + (a_prime_bit c 1461 row)) - (c_prime_bit c 181 row)) - 2)) * (((((((a_prime_bit c 181 row) + (a_prime_bit c 501 row)) + (a_prime_bit c 821 row)) + (a_prime_bit c 1141 row)) + (a_prime_bit c 1461 row)) - (c_prime_bit c 181 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2771_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2771 c row ↔ constraint_2771 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2772 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 182 row) + (a_prime_bit c 502 row)) + (a_prime_bit c 822 row)) + (a_prime_bit c 1142 row)) + (a_prime_bit c 1462 row)) - (c_prime_bit c 182 row)) * (((((((a_prime_bit c 182 row) + (a_prime_bit c 502 row)) + (a_prime_bit c 822 row)) + (a_prime_bit c 1142 row)) + (a_prime_bit c 1462 row)) - (c_prime_bit c 182 row)) - 2)) * (((((((a_prime_bit c 182 row) + (a_prime_bit c 502 row)) + (a_prime_bit c 822 row)) + (a_prime_bit c 1142 row)) + (a_prime_bit c 1462 row)) - (c_prime_bit c 182 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2772_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2772 c row ↔ constraint_2772 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2773 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 183 row) + (a_prime_bit c 503 row)) + (a_prime_bit c 823 row)) + (a_prime_bit c 1143 row)) + (a_prime_bit c 1463 row)) - (c_prime_bit c 183 row)) * (((((((a_prime_bit c 183 row) + (a_prime_bit c 503 row)) + (a_prime_bit c 823 row)) + (a_prime_bit c 1143 row)) + (a_prime_bit c 1463 row)) - (c_prime_bit c 183 row)) - 2)) * (((((((a_prime_bit c 183 row) + (a_prime_bit c 503 row)) + (a_prime_bit c 823 row)) + (a_prime_bit c 1143 row)) + (a_prime_bit c 1463 row)) - (c_prime_bit c 183 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2773_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2773 c row ↔ constraint_2773 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2774 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 184 row) + (a_prime_bit c 504 row)) + (a_prime_bit c 824 row)) + (a_prime_bit c 1144 row)) + (a_prime_bit c 1464 row)) - (c_prime_bit c 184 row)) * (((((((a_prime_bit c 184 row) + (a_prime_bit c 504 row)) + (a_prime_bit c 824 row)) + (a_prime_bit c 1144 row)) + (a_prime_bit c 1464 row)) - (c_prime_bit c 184 row)) - 2)) * (((((((a_prime_bit c 184 row) + (a_prime_bit c 504 row)) + (a_prime_bit c 824 row)) + (a_prime_bit c 1144 row)) + (a_prime_bit c 1464 row)) - (c_prime_bit c 184 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2774_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2774 c row ↔ constraint_2774 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2775 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 185 row) + (a_prime_bit c 505 row)) + (a_prime_bit c 825 row)) + (a_prime_bit c 1145 row)) + (a_prime_bit c 1465 row)) - (c_prime_bit c 185 row)) * (((((((a_prime_bit c 185 row) + (a_prime_bit c 505 row)) + (a_prime_bit c 825 row)) + (a_prime_bit c 1145 row)) + (a_prime_bit c 1465 row)) - (c_prime_bit c 185 row)) - 2)) * (((((((a_prime_bit c 185 row) + (a_prime_bit c 505 row)) + (a_prime_bit c 825 row)) + (a_prime_bit c 1145 row)) + (a_prime_bit c 1465 row)) - (c_prime_bit c 185 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2775_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2775 c row ↔ constraint_2775 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2776 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 186 row) + (a_prime_bit c 506 row)) + (a_prime_bit c 826 row)) + (a_prime_bit c 1146 row)) + (a_prime_bit c 1466 row)) - (c_prime_bit c 186 row)) * (((((((a_prime_bit c 186 row) + (a_prime_bit c 506 row)) + (a_prime_bit c 826 row)) + (a_prime_bit c 1146 row)) + (a_prime_bit c 1466 row)) - (c_prime_bit c 186 row)) - 2)) * (((((((a_prime_bit c 186 row) + (a_prime_bit c 506 row)) + (a_prime_bit c 826 row)) + (a_prime_bit c 1146 row)) + (a_prime_bit c 1466 row)) - (c_prime_bit c 186 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2776_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2776 c row ↔ constraint_2776 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2777 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 187 row) + (a_prime_bit c 507 row)) + (a_prime_bit c 827 row)) + (a_prime_bit c 1147 row)) + (a_prime_bit c 1467 row)) - (c_prime_bit c 187 row)) * (((((((a_prime_bit c 187 row) + (a_prime_bit c 507 row)) + (a_prime_bit c 827 row)) + (a_prime_bit c 1147 row)) + (a_prime_bit c 1467 row)) - (c_prime_bit c 187 row)) - 2)) * (((((((a_prime_bit c 187 row) + (a_prime_bit c 507 row)) + (a_prime_bit c 827 row)) + (a_prime_bit c 1147 row)) + (a_prime_bit c 1467 row)) - (c_prime_bit c 187 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2777_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2777 c row ↔ constraint_2777 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2778 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 188 row) + (a_prime_bit c 508 row)) + (a_prime_bit c 828 row)) + (a_prime_bit c 1148 row)) + (a_prime_bit c 1468 row)) - (c_prime_bit c 188 row)) * (((((((a_prime_bit c 188 row) + (a_prime_bit c 508 row)) + (a_prime_bit c 828 row)) + (a_prime_bit c 1148 row)) + (a_prime_bit c 1468 row)) - (c_prime_bit c 188 row)) - 2)) * (((((((a_prime_bit c 188 row) + (a_prime_bit c 508 row)) + (a_prime_bit c 828 row)) + (a_prime_bit c 1148 row)) + (a_prime_bit c 1468 row)) - (c_prime_bit c 188 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2778_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2778 c row ↔ constraint_2778 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2779 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 189 row) + (a_prime_bit c 509 row)) + (a_prime_bit c 829 row)) + (a_prime_bit c 1149 row)) + (a_prime_bit c 1469 row)) - (c_prime_bit c 189 row)) * (((((((a_prime_bit c 189 row) + (a_prime_bit c 509 row)) + (a_prime_bit c 829 row)) + (a_prime_bit c 1149 row)) + (a_prime_bit c 1469 row)) - (c_prime_bit c 189 row)) - 2)) * (((((((a_prime_bit c 189 row) + (a_prime_bit c 509 row)) + (a_prime_bit c 829 row)) + (a_prime_bit c 1149 row)) + (a_prime_bit c 1469 row)) - (c_prime_bit c 189 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2779_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2779 c row ↔ constraint_2779 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2780 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 190 row) + (a_prime_bit c 510 row)) + (a_prime_bit c 830 row)) + (a_prime_bit c 1150 row)) + (a_prime_bit c 1470 row)) - (c_prime_bit c 190 row)) * (((((((a_prime_bit c 190 row) + (a_prime_bit c 510 row)) + (a_prime_bit c 830 row)) + (a_prime_bit c 1150 row)) + (a_prime_bit c 1470 row)) - (c_prime_bit c 190 row)) - 2)) * (((((((a_prime_bit c 190 row) + (a_prime_bit c 510 row)) + (a_prime_bit c 830 row)) + (a_prime_bit c 1150 row)) + (a_prime_bit c 1470 row)) - (c_prime_bit c 190 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2780_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2780 c row ↔ constraint_2780 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2781 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 191 row) + (a_prime_bit c 511 row)) + (a_prime_bit c 831 row)) + (a_prime_bit c 1151 row)) + (a_prime_bit c 1471 row)) - (c_prime_bit c 191 row)) * (((((((a_prime_bit c 191 row) + (a_prime_bit c 511 row)) + (a_prime_bit c 831 row)) + (a_prime_bit c 1151 row)) + (a_prime_bit c 1471 row)) - (c_prime_bit c 191 row)) - 2)) * (((((((a_prime_bit c 191 row) + (a_prime_bit c 511 row)) + (a_prime_bit c 831 row)) + (a_prime_bit c 1151 row)) + (a_prime_bit c 1471 row)) - (c_prime_bit c 191 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2781_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2781 c row ↔ constraint_2781 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2782 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 192 row) + (a_prime_bit c 512 row)) + (a_prime_bit c 832 row)) + (a_prime_bit c 1152 row)) + (a_prime_bit c 1472 row)) - (c_prime_bit c 192 row)) * (((((((a_prime_bit c 192 row) + (a_prime_bit c 512 row)) + (a_prime_bit c 832 row)) + (a_prime_bit c 1152 row)) + (a_prime_bit c 1472 row)) - (c_prime_bit c 192 row)) - 2)) * (((((((a_prime_bit c 192 row) + (a_prime_bit c 512 row)) + (a_prime_bit c 832 row)) + (a_prime_bit c 1152 row)) + (a_prime_bit c 1472 row)) - (c_prime_bit c 192 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2782_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2782 c row ↔ constraint_2782 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2783 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 193 row) + (a_prime_bit c 513 row)) + (a_prime_bit c 833 row)) + (a_prime_bit c 1153 row)) + (a_prime_bit c 1473 row)) - (c_prime_bit c 193 row)) * (((((((a_prime_bit c 193 row) + (a_prime_bit c 513 row)) + (a_prime_bit c 833 row)) + (a_prime_bit c 1153 row)) + (a_prime_bit c 1473 row)) - (c_prime_bit c 193 row)) - 2)) * (((((((a_prime_bit c 193 row) + (a_prime_bit c 513 row)) + (a_prime_bit c 833 row)) + (a_prime_bit c 1153 row)) + (a_prime_bit c 1473 row)) - (c_prime_bit c 193 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2783_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2783 c row ↔ constraint_2783 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2784 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 194 row) + (a_prime_bit c 514 row)) + (a_prime_bit c 834 row)) + (a_prime_bit c 1154 row)) + (a_prime_bit c 1474 row)) - (c_prime_bit c 194 row)) * (((((((a_prime_bit c 194 row) + (a_prime_bit c 514 row)) + (a_prime_bit c 834 row)) + (a_prime_bit c 1154 row)) + (a_prime_bit c 1474 row)) - (c_prime_bit c 194 row)) - 2)) * (((((((a_prime_bit c 194 row) + (a_prime_bit c 514 row)) + (a_prime_bit c 834 row)) + (a_prime_bit c 1154 row)) + (a_prime_bit c 1474 row)) - (c_prime_bit c 194 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2784_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2784 c row ↔ constraint_2784 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2785 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 195 row) + (a_prime_bit c 515 row)) + (a_prime_bit c 835 row)) + (a_prime_bit c 1155 row)) + (a_prime_bit c 1475 row)) - (c_prime_bit c 195 row)) * (((((((a_prime_bit c 195 row) + (a_prime_bit c 515 row)) + (a_prime_bit c 835 row)) + (a_prime_bit c 1155 row)) + (a_prime_bit c 1475 row)) - (c_prime_bit c 195 row)) - 2)) * (((((((a_prime_bit c 195 row) + (a_prime_bit c 515 row)) + (a_prime_bit c 835 row)) + (a_prime_bit c 1155 row)) + (a_prime_bit c 1475 row)) - (c_prime_bit c 195 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2785_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2785 c row ↔ constraint_2785 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2786 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 196 row) + (a_prime_bit c 516 row)) + (a_prime_bit c 836 row)) + (a_prime_bit c 1156 row)) + (a_prime_bit c 1476 row)) - (c_prime_bit c 196 row)) * (((((((a_prime_bit c 196 row) + (a_prime_bit c 516 row)) + (a_prime_bit c 836 row)) + (a_prime_bit c 1156 row)) + (a_prime_bit c 1476 row)) - (c_prime_bit c 196 row)) - 2)) * (((((((a_prime_bit c 196 row) + (a_prime_bit c 516 row)) + (a_prime_bit c 836 row)) + (a_prime_bit c 1156 row)) + (a_prime_bit c 1476 row)) - (c_prime_bit c 196 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2786_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2786 c row ↔ constraint_2786 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2787 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 197 row) + (a_prime_bit c 517 row)) + (a_prime_bit c 837 row)) + (a_prime_bit c 1157 row)) + (a_prime_bit c 1477 row)) - (c_prime_bit c 197 row)) * (((((((a_prime_bit c 197 row) + (a_prime_bit c 517 row)) + (a_prime_bit c 837 row)) + (a_prime_bit c 1157 row)) + (a_prime_bit c 1477 row)) - (c_prime_bit c 197 row)) - 2)) * (((((((a_prime_bit c 197 row) + (a_prime_bit c 517 row)) + (a_prime_bit c 837 row)) + (a_prime_bit c 1157 row)) + (a_prime_bit c 1477 row)) - (c_prime_bit c 197 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2787_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2787 c row ↔ constraint_2787 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2788 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 198 row) + (a_prime_bit c 518 row)) + (a_prime_bit c 838 row)) + (a_prime_bit c 1158 row)) + (a_prime_bit c 1478 row)) - (c_prime_bit c 198 row)) * (((((((a_prime_bit c 198 row) + (a_prime_bit c 518 row)) + (a_prime_bit c 838 row)) + (a_prime_bit c 1158 row)) + (a_prime_bit c 1478 row)) - (c_prime_bit c 198 row)) - 2)) * (((((((a_prime_bit c 198 row) + (a_prime_bit c 518 row)) + (a_prime_bit c 838 row)) + (a_prime_bit c 1158 row)) + (a_prime_bit c 1478 row)) - (c_prime_bit c 198 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2788_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2788 c row ↔ constraint_2788 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2789 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 199 row) + (a_prime_bit c 519 row)) + (a_prime_bit c 839 row)) + (a_prime_bit c 1159 row)) + (a_prime_bit c 1479 row)) - (c_prime_bit c 199 row)) * (((((((a_prime_bit c 199 row) + (a_prime_bit c 519 row)) + (a_prime_bit c 839 row)) + (a_prime_bit c 1159 row)) + (a_prime_bit c 1479 row)) - (c_prime_bit c 199 row)) - 2)) * (((((((a_prime_bit c 199 row) + (a_prime_bit c 519 row)) + (a_prime_bit c 839 row)) + (a_prime_bit c 1159 row)) + (a_prime_bit c 1479 row)) - (c_prime_bit c 199 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2789_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2789 c row ↔ constraint_2789 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2790 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 200 row) + (a_prime_bit c 520 row)) + (a_prime_bit c 840 row)) + (a_prime_bit c 1160 row)) + (a_prime_bit c 1480 row)) - (c_prime_bit c 200 row)) * (((((((a_prime_bit c 200 row) + (a_prime_bit c 520 row)) + (a_prime_bit c 840 row)) + (a_prime_bit c 1160 row)) + (a_prime_bit c 1480 row)) - (c_prime_bit c 200 row)) - 2)) * (((((((a_prime_bit c 200 row) + (a_prime_bit c 520 row)) + (a_prime_bit c 840 row)) + (a_prime_bit c 1160 row)) + (a_prime_bit c 1480 row)) - (c_prime_bit c 200 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2790_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2790 c row ↔ constraint_2790 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2791 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 201 row) + (a_prime_bit c 521 row)) + (a_prime_bit c 841 row)) + (a_prime_bit c 1161 row)) + (a_prime_bit c 1481 row)) - (c_prime_bit c 201 row)) * (((((((a_prime_bit c 201 row) + (a_prime_bit c 521 row)) + (a_prime_bit c 841 row)) + (a_prime_bit c 1161 row)) + (a_prime_bit c 1481 row)) - (c_prime_bit c 201 row)) - 2)) * (((((((a_prime_bit c 201 row) + (a_prime_bit c 521 row)) + (a_prime_bit c 841 row)) + (a_prime_bit c 1161 row)) + (a_prime_bit c 1481 row)) - (c_prime_bit c 201 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2791_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2791 c row ↔ constraint_2791 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2792 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 202 row) + (a_prime_bit c 522 row)) + (a_prime_bit c 842 row)) + (a_prime_bit c 1162 row)) + (a_prime_bit c 1482 row)) - (c_prime_bit c 202 row)) * (((((((a_prime_bit c 202 row) + (a_prime_bit c 522 row)) + (a_prime_bit c 842 row)) + (a_prime_bit c 1162 row)) + (a_prime_bit c 1482 row)) - (c_prime_bit c 202 row)) - 2)) * (((((((a_prime_bit c 202 row) + (a_prime_bit c 522 row)) + (a_prime_bit c 842 row)) + (a_prime_bit c 1162 row)) + (a_prime_bit c 1482 row)) - (c_prime_bit c 202 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2792_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2792 c row ↔ constraint_2792 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2793 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 203 row) + (a_prime_bit c 523 row)) + (a_prime_bit c 843 row)) + (a_prime_bit c 1163 row)) + (a_prime_bit c 1483 row)) - (c_prime_bit c 203 row)) * (((((((a_prime_bit c 203 row) + (a_prime_bit c 523 row)) + (a_prime_bit c 843 row)) + (a_prime_bit c 1163 row)) + (a_prime_bit c 1483 row)) - (c_prime_bit c 203 row)) - 2)) * (((((((a_prime_bit c 203 row) + (a_prime_bit c 523 row)) + (a_prime_bit c 843 row)) + (a_prime_bit c 1163 row)) + (a_prime_bit c 1483 row)) - (c_prime_bit c 203 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2793_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2793 c row ↔ constraint_2793 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2794 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 204 row) + (a_prime_bit c 524 row)) + (a_prime_bit c 844 row)) + (a_prime_bit c 1164 row)) + (a_prime_bit c 1484 row)) - (c_prime_bit c 204 row)) * (((((((a_prime_bit c 204 row) + (a_prime_bit c 524 row)) + (a_prime_bit c 844 row)) + (a_prime_bit c 1164 row)) + (a_prime_bit c 1484 row)) - (c_prime_bit c 204 row)) - 2)) * (((((((a_prime_bit c 204 row) + (a_prime_bit c 524 row)) + (a_prime_bit c 844 row)) + (a_prime_bit c 1164 row)) + (a_prime_bit c 1484 row)) - (c_prime_bit c 204 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2794_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2794 c row ↔ constraint_2794 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2795 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 205 row) + (a_prime_bit c 525 row)) + (a_prime_bit c 845 row)) + (a_prime_bit c 1165 row)) + (a_prime_bit c 1485 row)) - (c_prime_bit c 205 row)) * (((((((a_prime_bit c 205 row) + (a_prime_bit c 525 row)) + (a_prime_bit c 845 row)) + (a_prime_bit c 1165 row)) + (a_prime_bit c 1485 row)) - (c_prime_bit c 205 row)) - 2)) * (((((((a_prime_bit c 205 row) + (a_prime_bit c 525 row)) + (a_prime_bit c 845 row)) + (a_prime_bit c 1165 row)) + (a_prime_bit c 1485 row)) - (c_prime_bit c 205 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2795_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2795 c row ↔ constraint_2795 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2796 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 206 row) + (a_prime_bit c 526 row)) + (a_prime_bit c 846 row)) + (a_prime_bit c 1166 row)) + (a_prime_bit c 1486 row)) - (c_prime_bit c 206 row)) * (((((((a_prime_bit c 206 row) + (a_prime_bit c 526 row)) + (a_prime_bit c 846 row)) + (a_prime_bit c 1166 row)) + (a_prime_bit c 1486 row)) - (c_prime_bit c 206 row)) - 2)) * (((((((a_prime_bit c 206 row) + (a_prime_bit c 526 row)) + (a_prime_bit c 846 row)) + (a_prime_bit c 1166 row)) + (a_prime_bit c 1486 row)) - (c_prime_bit c 206 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2796_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2796 c row ↔ constraint_2796 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2797 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 207 row) + (a_prime_bit c 527 row)) + (a_prime_bit c 847 row)) + (a_prime_bit c 1167 row)) + (a_prime_bit c 1487 row)) - (c_prime_bit c 207 row)) * (((((((a_prime_bit c 207 row) + (a_prime_bit c 527 row)) + (a_prime_bit c 847 row)) + (a_prime_bit c 1167 row)) + (a_prime_bit c 1487 row)) - (c_prime_bit c 207 row)) - 2)) * (((((((a_prime_bit c 207 row) + (a_prime_bit c 527 row)) + (a_prime_bit c 847 row)) + (a_prime_bit c 1167 row)) + (a_prime_bit c 1487 row)) - (c_prime_bit c 207 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2797_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2797 c row ↔ constraint_2797 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2798 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 208 row) + (a_prime_bit c 528 row)) + (a_prime_bit c 848 row)) + (a_prime_bit c 1168 row)) + (a_prime_bit c 1488 row)) - (c_prime_bit c 208 row)) * (((((((a_prime_bit c 208 row) + (a_prime_bit c 528 row)) + (a_prime_bit c 848 row)) + (a_prime_bit c 1168 row)) + (a_prime_bit c 1488 row)) - (c_prime_bit c 208 row)) - 2)) * (((((((a_prime_bit c 208 row) + (a_prime_bit c 528 row)) + (a_prime_bit c 848 row)) + (a_prime_bit c 1168 row)) + (a_prime_bit c 1488 row)) - (c_prime_bit c 208 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2798_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2798 c row ↔ constraint_2798 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2799 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 209 row) + (a_prime_bit c 529 row)) + (a_prime_bit c 849 row)) + (a_prime_bit c 1169 row)) + (a_prime_bit c 1489 row)) - (c_prime_bit c 209 row)) * (((((((a_prime_bit c 209 row) + (a_prime_bit c 529 row)) + (a_prime_bit c 849 row)) + (a_prime_bit c 1169 row)) + (a_prime_bit c 1489 row)) - (c_prime_bit c 209 row)) - 2)) * (((((((a_prime_bit c 209 row) + (a_prime_bit c 529 row)) + (a_prime_bit c 849 row)) + (a_prime_bit c 1169 row)) + (a_prime_bit c 1489 row)) - (c_prime_bit c 209 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2799_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2799 c row ↔ constraint_2799 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2800 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 210 row) + (a_prime_bit c 530 row)) + (a_prime_bit c 850 row)) + (a_prime_bit c 1170 row)) + (a_prime_bit c 1490 row)) - (c_prime_bit c 210 row)) * (((((((a_prime_bit c 210 row) + (a_prime_bit c 530 row)) + (a_prime_bit c 850 row)) + (a_prime_bit c 1170 row)) + (a_prime_bit c 1490 row)) - (c_prime_bit c 210 row)) - 2)) * (((((((a_prime_bit c 210 row) + (a_prime_bit c 530 row)) + (a_prime_bit c 850 row)) + (a_prime_bit c 1170 row)) + (a_prime_bit c 1490 row)) - (c_prime_bit c 210 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2800_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2800 c row ↔ constraint_2800 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2801 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 211 row) + (a_prime_bit c 531 row)) + (a_prime_bit c 851 row)) + (a_prime_bit c 1171 row)) + (a_prime_bit c 1491 row)) - (c_prime_bit c 211 row)) * (((((((a_prime_bit c 211 row) + (a_prime_bit c 531 row)) + (a_prime_bit c 851 row)) + (a_prime_bit c 1171 row)) + (a_prime_bit c 1491 row)) - (c_prime_bit c 211 row)) - 2)) * (((((((a_prime_bit c 211 row) + (a_prime_bit c 531 row)) + (a_prime_bit c 851 row)) + (a_prime_bit c 1171 row)) + (a_prime_bit c 1491 row)) - (c_prime_bit c 211 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2801_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2801 c row ↔ constraint_2801 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2802 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 212 row) + (a_prime_bit c 532 row)) + (a_prime_bit c 852 row)) + (a_prime_bit c 1172 row)) + (a_prime_bit c 1492 row)) - (c_prime_bit c 212 row)) * (((((((a_prime_bit c 212 row) + (a_prime_bit c 532 row)) + (a_prime_bit c 852 row)) + (a_prime_bit c 1172 row)) + (a_prime_bit c 1492 row)) - (c_prime_bit c 212 row)) - 2)) * (((((((a_prime_bit c 212 row) + (a_prime_bit c 532 row)) + (a_prime_bit c 852 row)) + (a_prime_bit c 1172 row)) + (a_prime_bit c 1492 row)) - (c_prime_bit c 212 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2802_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2802 c row ↔ constraint_2802 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2803 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 213 row) + (a_prime_bit c 533 row)) + (a_prime_bit c 853 row)) + (a_prime_bit c 1173 row)) + (a_prime_bit c 1493 row)) - (c_prime_bit c 213 row)) * (((((((a_prime_bit c 213 row) + (a_prime_bit c 533 row)) + (a_prime_bit c 853 row)) + (a_prime_bit c 1173 row)) + (a_prime_bit c 1493 row)) - (c_prime_bit c 213 row)) - 2)) * (((((((a_prime_bit c 213 row) + (a_prime_bit c 533 row)) + (a_prime_bit c 853 row)) + (a_prime_bit c 1173 row)) + (a_prime_bit c 1493 row)) - (c_prime_bit c 213 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2803_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2803 c row ↔ constraint_2803 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2804 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 214 row) + (a_prime_bit c 534 row)) + (a_prime_bit c 854 row)) + (a_prime_bit c 1174 row)) + (a_prime_bit c 1494 row)) - (c_prime_bit c 214 row)) * (((((((a_prime_bit c 214 row) + (a_prime_bit c 534 row)) + (a_prime_bit c 854 row)) + (a_prime_bit c 1174 row)) + (a_prime_bit c 1494 row)) - (c_prime_bit c 214 row)) - 2)) * (((((((a_prime_bit c 214 row) + (a_prime_bit c 534 row)) + (a_prime_bit c 854 row)) + (a_prime_bit c 1174 row)) + (a_prime_bit c 1494 row)) - (c_prime_bit c 214 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2804_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2804 c row ↔ constraint_2804 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2805 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 215 row) + (a_prime_bit c 535 row)) + (a_prime_bit c 855 row)) + (a_prime_bit c 1175 row)) + (a_prime_bit c 1495 row)) - (c_prime_bit c 215 row)) * (((((((a_prime_bit c 215 row) + (a_prime_bit c 535 row)) + (a_prime_bit c 855 row)) + (a_prime_bit c 1175 row)) + (a_prime_bit c 1495 row)) - (c_prime_bit c 215 row)) - 2)) * (((((((a_prime_bit c 215 row) + (a_prime_bit c 535 row)) + (a_prime_bit c 855 row)) + (a_prime_bit c 1175 row)) + (a_prime_bit c 1495 row)) - (c_prime_bit c 215 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2805_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2805 c row ↔ constraint_2805 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2806 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 216 row) + (a_prime_bit c 536 row)) + (a_prime_bit c 856 row)) + (a_prime_bit c 1176 row)) + (a_prime_bit c 1496 row)) - (c_prime_bit c 216 row)) * (((((((a_prime_bit c 216 row) + (a_prime_bit c 536 row)) + (a_prime_bit c 856 row)) + (a_prime_bit c 1176 row)) + (a_prime_bit c 1496 row)) - (c_prime_bit c 216 row)) - 2)) * (((((((a_prime_bit c 216 row) + (a_prime_bit c 536 row)) + (a_prime_bit c 856 row)) + (a_prime_bit c 1176 row)) + (a_prime_bit c 1496 row)) - (c_prime_bit c 216 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2806_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2806 c row ↔ constraint_2806 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2807 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 217 row) + (a_prime_bit c 537 row)) + (a_prime_bit c 857 row)) + (a_prime_bit c 1177 row)) + (a_prime_bit c 1497 row)) - (c_prime_bit c 217 row)) * (((((((a_prime_bit c 217 row) + (a_prime_bit c 537 row)) + (a_prime_bit c 857 row)) + (a_prime_bit c 1177 row)) + (a_prime_bit c 1497 row)) - (c_prime_bit c 217 row)) - 2)) * (((((((a_prime_bit c 217 row) + (a_prime_bit c 537 row)) + (a_prime_bit c 857 row)) + (a_prime_bit c 1177 row)) + (a_prime_bit c 1497 row)) - (c_prime_bit c 217 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2807_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2807 c row ↔ constraint_2807 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2808 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 218 row) + (a_prime_bit c 538 row)) + (a_prime_bit c 858 row)) + (a_prime_bit c 1178 row)) + (a_prime_bit c 1498 row)) - (c_prime_bit c 218 row)) * (((((((a_prime_bit c 218 row) + (a_prime_bit c 538 row)) + (a_prime_bit c 858 row)) + (a_prime_bit c 1178 row)) + (a_prime_bit c 1498 row)) - (c_prime_bit c 218 row)) - 2)) * (((((((a_prime_bit c 218 row) + (a_prime_bit c 538 row)) + (a_prime_bit c 858 row)) + (a_prime_bit c 1178 row)) + (a_prime_bit c 1498 row)) - (c_prime_bit c 218 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2808_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2808 c row ↔ constraint_2808 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2809 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 219 row) + (a_prime_bit c 539 row)) + (a_prime_bit c 859 row)) + (a_prime_bit c 1179 row)) + (a_prime_bit c 1499 row)) - (c_prime_bit c 219 row)) * (((((((a_prime_bit c 219 row) + (a_prime_bit c 539 row)) + (a_prime_bit c 859 row)) + (a_prime_bit c 1179 row)) + (a_prime_bit c 1499 row)) - (c_prime_bit c 219 row)) - 2)) * (((((((a_prime_bit c 219 row) + (a_prime_bit c 539 row)) + (a_prime_bit c 859 row)) + (a_prime_bit c 1179 row)) + (a_prime_bit c 1499 row)) - (c_prime_bit c 219 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2809_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2809 c row ↔ constraint_2809 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2810 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 220 row) + (a_prime_bit c 540 row)) + (a_prime_bit c 860 row)) + (a_prime_bit c 1180 row)) + (a_prime_bit c 1500 row)) - (c_prime_bit c 220 row)) * (((((((a_prime_bit c 220 row) + (a_prime_bit c 540 row)) + (a_prime_bit c 860 row)) + (a_prime_bit c 1180 row)) + (a_prime_bit c 1500 row)) - (c_prime_bit c 220 row)) - 2)) * (((((((a_prime_bit c 220 row) + (a_prime_bit c 540 row)) + (a_prime_bit c 860 row)) + (a_prime_bit c 1180 row)) + (a_prime_bit c 1500 row)) - (c_prime_bit c 220 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2810_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2810 c row ↔ constraint_2810 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2811 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 221 row) + (a_prime_bit c 541 row)) + (a_prime_bit c 861 row)) + (a_prime_bit c 1181 row)) + (a_prime_bit c 1501 row)) - (c_prime_bit c 221 row)) * (((((((a_prime_bit c 221 row) + (a_prime_bit c 541 row)) + (a_prime_bit c 861 row)) + (a_prime_bit c 1181 row)) + (a_prime_bit c 1501 row)) - (c_prime_bit c 221 row)) - 2)) * (((((((a_prime_bit c 221 row) + (a_prime_bit c 541 row)) + (a_prime_bit c 861 row)) + (a_prime_bit c 1181 row)) + (a_prime_bit c 1501 row)) - (c_prime_bit c 221 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2811_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2811 c row ↔ constraint_2811 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2812 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 222 row) + (a_prime_bit c 542 row)) + (a_prime_bit c 862 row)) + (a_prime_bit c 1182 row)) + (a_prime_bit c 1502 row)) - (c_prime_bit c 222 row)) * (((((((a_prime_bit c 222 row) + (a_prime_bit c 542 row)) + (a_prime_bit c 862 row)) + (a_prime_bit c 1182 row)) + (a_prime_bit c 1502 row)) - (c_prime_bit c 222 row)) - 2)) * (((((((a_prime_bit c 222 row) + (a_prime_bit c 542 row)) + (a_prime_bit c 862 row)) + (a_prime_bit c 1182 row)) + (a_prime_bit c 1502 row)) - (c_prime_bit c 222 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2812_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2812 c row ↔ constraint_2812 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2813 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 223 row) + (a_prime_bit c 543 row)) + (a_prime_bit c 863 row)) + (a_prime_bit c 1183 row)) + (a_prime_bit c 1503 row)) - (c_prime_bit c 223 row)) * (((((((a_prime_bit c 223 row) + (a_prime_bit c 543 row)) + (a_prime_bit c 863 row)) + (a_prime_bit c 1183 row)) + (a_prime_bit c 1503 row)) - (c_prime_bit c 223 row)) - 2)) * (((((((a_prime_bit c 223 row) + (a_prime_bit c 543 row)) + (a_prime_bit c 863 row)) + (a_prime_bit c 1183 row)) + (a_prime_bit c 1503 row)) - (c_prime_bit c 223 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2813_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2813 c row ↔ constraint_2813 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2814 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 224 row) + (a_prime_bit c 544 row)) + (a_prime_bit c 864 row)) + (a_prime_bit c 1184 row)) + (a_prime_bit c 1504 row)) - (c_prime_bit c 224 row)) * (((((((a_prime_bit c 224 row) + (a_prime_bit c 544 row)) + (a_prime_bit c 864 row)) + (a_prime_bit c 1184 row)) + (a_prime_bit c 1504 row)) - (c_prime_bit c 224 row)) - 2)) * (((((((a_prime_bit c 224 row) + (a_prime_bit c 544 row)) + (a_prime_bit c 864 row)) + (a_prime_bit c 1184 row)) + (a_prime_bit c 1504 row)) - (c_prime_bit c 224 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2814_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2814 c row ↔ constraint_2814 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2815 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 225 row) + (a_prime_bit c 545 row)) + (a_prime_bit c 865 row)) + (a_prime_bit c 1185 row)) + (a_prime_bit c 1505 row)) - (c_prime_bit c 225 row)) * (((((((a_prime_bit c 225 row) + (a_prime_bit c 545 row)) + (a_prime_bit c 865 row)) + (a_prime_bit c 1185 row)) + (a_prime_bit c 1505 row)) - (c_prime_bit c 225 row)) - 2)) * (((((((a_prime_bit c 225 row) + (a_prime_bit c 545 row)) + (a_prime_bit c 865 row)) + (a_prime_bit c 1185 row)) + (a_prime_bit c 1505 row)) - (c_prime_bit c 225 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2815_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2815 c row ↔ constraint_2815 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2816 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 226 row) + (a_prime_bit c 546 row)) + (a_prime_bit c 866 row)) + (a_prime_bit c 1186 row)) + (a_prime_bit c 1506 row)) - (c_prime_bit c 226 row)) * (((((((a_prime_bit c 226 row) + (a_prime_bit c 546 row)) + (a_prime_bit c 866 row)) + (a_prime_bit c 1186 row)) + (a_prime_bit c 1506 row)) - (c_prime_bit c 226 row)) - 2)) * (((((((a_prime_bit c 226 row) + (a_prime_bit c 546 row)) + (a_prime_bit c 866 row)) + (a_prime_bit c 1186 row)) + (a_prime_bit c 1506 row)) - (c_prime_bit c 226 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2816_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2816 c row ↔ constraint_2816 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2817 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 227 row) + (a_prime_bit c 547 row)) + (a_prime_bit c 867 row)) + (a_prime_bit c 1187 row)) + (a_prime_bit c 1507 row)) - (c_prime_bit c 227 row)) * (((((((a_prime_bit c 227 row) + (a_prime_bit c 547 row)) + (a_prime_bit c 867 row)) + (a_prime_bit c 1187 row)) + (a_prime_bit c 1507 row)) - (c_prime_bit c 227 row)) - 2)) * (((((((a_prime_bit c 227 row) + (a_prime_bit c 547 row)) + (a_prime_bit c 867 row)) + (a_prime_bit c 1187 row)) + (a_prime_bit c 1507 row)) - (c_prime_bit c 227 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2817_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2817 c row ↔ constraint_2817 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2818 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 228 row) + (a_prime_bit c 548 row)) + (a_prime_bit c 868 row)) + (a_prime_bit c 1188 row)) + (a_prime_bit c 1508 row)) - (c_prime_bit c 228 row)) * (((((((a_prime_bit c 228 row) + (a_prime_bit c 548 row)) + (a_prime_bit c 868 row)) + (a_prime_bit c 1188 row)) + (a_prime_bit c 1508 row)) - (c_prime_bit c 228 row)) - 2)) * (((((((a_prime_bit c 228 row) + (a_prime_bit c 548 row)) + (a_prime_bit c 868 row)) + (a_prime_bit c 1188 row)) + (a_prime_bit c 1508 row)) - (c_prime_bit c 228 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2818_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2818 c row ↔ constraint_2818 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2819 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 229 row) + (a_prime_bit c 549 row)) + (a_prime_bit c 869 row)) + (a_prime_bit c 1189 row)) + (a_prime_bit c 1509 row)) - (c_prime_bit c 229 row)) * (((((((a_prime_bit c 229 row) + (a_prime_bit c 549 row)) + (a_prime_bit c 869 row)) + (a_prime_bit c 1189 row)) + (a_prime_bit c 1509 row)) - (c_prime_bit c 229 row)) - 2)) * (((((((a_prime_bit c 229 row) + (a_prime_bit c 549 row)) + (a_prime_bit c 869 row)) + (a_prime_bit c 1189 row)) + (a_prime_bit c 1509 row)) - (c_prime_bit c 229 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2819_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2819 c row ↔ constraint_2819 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2820 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 230 row) + (a_prime_bit c 550 row)) + (a_prime_bit c 870 row)) + (a_prime_bit c 1190 row)) + (a_prime_bit c 1510 row)) - (c_prime_bit c 230 row)) * (((((((a_prime_bit c 230 row) + (a_prime_bit c 550 row)) + (a_prime_bit c 870 row)) + (a_prime_bit c 1190 row)) + (a_prime_bit c 1510 row)) - (c_prime_bit c 230 row)) - 2)) * (((((((a_prime_bit c 230 row) + (a_prime_bit c 550 row)) + (a_prime_bit c 870 row)) + (a_prime_bit c 1190 row)) + (a_prime_bit c 1510 row)) - (c_prime_bit c 230 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2820_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2820 c row ↔ constraint_2820 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2821 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 231 row) + (a_prime_bit c 551 row)) + (a_prime_bit c 871 row)) + (a_prime_bit c 1191 row)) + (a_prime_bit c 1511 row)) - (c_prime_bit c 231 row)) * (((((((a_prime_bit c 231 row) + (a_prime_bit c 551 row)) + (a_prime_bit c 871 row)) + (a_prime_bit c 1191 row)) + (a_prime_bit c 1511 row)) - (c_prime_bit c 231 row)) - 2)) * (((((((a_prime_bit c 231 row) + (a_prime_bit c 551 row)) + (a_prime_bit c 871 row)) + (a_prime_bit c 1191 row)) + (a_prime_bit c 1511 row)) - (c_prime_bit c 231 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2821_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2821 c row ↔ constraint_2821 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2822 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 232 row) + (a_prime_bit c 552 row)) + (a_prime_bit c 872 row)) + (a_prime_bit c 1192 row)) + (a_prime_bit c 1512 row)) - (c_prime_bit c 232 row)) * (((((((a_prime_bit c 232 row) + (a_prime_bit c 552 row)) + (a_prime_bit c 872 row)) + (a_prime_bit c 1192 row)) + (a_prime_bit c 1512 row)) - (c_prime_bit c 232 row)) - 2)) * (((((((a_prime_bit c 232 row) + (a_prime_bit c 552 row)) + (a_prime_bit c 872 row)) + (a_prime_bit c 1192 row)) + (a_prime_bit c 1512 row)) - (c_prime_bit c 232 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2822_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2822 c row ↔ constraint_2822 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2823 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 233 row) + (a_prime_bit c 553 row)) + (a_prime_bit c 873 row)) + (a_prime_bit c 1193 row)) + (a_prime_bit c 1513 row)) - (c_prime_bit c 233 row)) * (((((((a_prime_bit c 233 row) + (a_prime_bit c 553 row)) + (a_prime_bit c 873 row)) + (a_prime_bit c 1193 row)) + (a_prime_bit c 1513 row)) - (c_prime_bit c 233 row)) - 2)) * (((((((a_prime_bit c 233 row) + (a_prime_bit c 553 row)) + (a_prime_bit c 873 row)) + (a_prime_bit c 1193 row)) + (a_prime_bit c 1513 row)) - (c_prime_bit c 233 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2823_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2823 c row ↔ constraint_2823 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2824 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 234 row) + (a_prime_bit c 554 row)) + (a_prime_bit c 874 row)) + (a_prime_bit c 1194 row)) + (a_prime_bit c 1514 row)) - (c_prime_bit c 234 row)) * (((((((a_prime_bit c 234 row) + (a_prime_bit c 554 row)) + (a_prime_bit c 874 row)) + (a_prime_bit c 1194 row)) + (a_prime_bit c 1514 row)) - (c_prime_bit c 234 row)) - 2)) * (((((((a_prime_bit c 234 row) + (a_prime_bit c 554 row)) + (a_prime_bit c 874 row)) + (a_prime_bit c 1194 row)) + (a_prime_bit c 1514 row)) - (c_prime_bit c 234 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2824_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2824 c row ↔ constraint_2824 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2825 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 235 row) + (a_prime_bit c 555 row)) + (a_prime_bit c 875 row)) + (a_prime_bit c 1195 row)) + (a_prime_bit c 1515 row)) - (c_prime_bit c 235 row)) * (((((((a_prime_bit c 235 row) + (a_prime_bit c 555 row)) + (a_prime_bit c 875 row)) + (a_prime_bit c 1195 row)) + (a_prime_bit c 1515 row)) - (c_prime_bit c 235 row)) - 2)) * (((((((a_prime_bit c 235 row) + (a_prime_bit c 555 row)) + (a_prime_bit c 875 row)) + (a_prime_bit c 1195 row)) + (a_prime_bit c 1515 row)) - (c_prime_bit c 235 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2825_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2825 c row ↔ constraint_2825 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2826 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 236 row) + (a_prime_bit c 556 row)) + (a_prime_bit c 876 row)) + (a_prime_bit c 1196 row)) + (a_prime_bit c 1516 row)) - (c_prime_bit c 236 row)) * (((((((a_prime_bit c 236 row) + (a_prime_bit c 556 row)) + (a_prime_bit c 876 row)) + (a_prime_bit c 1196 row)) + (a_prime_bit c 1516 row)) - (c_prime_bit c 236 row)) - 2)) * (((((((a_prime_bit c 236 row) + (a_prime_bit c 556 row)) + (a_prime_bit c 876 row)) + (a_prime_bit c 1196 row)) + (a_prime_bit c 1516 row)) - (c_prime_bit c 236 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2826_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2826 c row ↔ constraint_2826 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2827 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 237 row) + (a_prime_bit c 557 row)) + (a_prime_bit c 877 row)) + (a_prime_bit c 1197 row)) + (a_prime_bit c 1517 row)) - (c_prime_bit c 237 row)) * (((((((a_prime_bit c 237 row) + (a_prime_bit c 557 row)) + (a_prime_bit c 877 row)) + (a_prime_bit c 1197 row)) + (a_prime_bit c 1517 row)) - (c_prime_bit c 237 row)) - 2)) * (((((((a_prime_bit c 237 row) + (a_prime_bit c 557 row)) + (a_prime_bit c 877 row)) + (a_prime_bit c 1197 row)) + (a_prime_bit c 1517 row)) - (c_prime_bit c 237 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2827_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2827 c row ↔ constraint_2827 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2828 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 238 row) + (a_prime_bit c 558 row)) + (a_prime_bit c 878 row)) + (a_prime_bit c 1198 row)) + (a_prime_bit c 1518 row)) - (c_prime_bit c 238 row)) * (((((((a_prime_bit c 238 row) + (a_prime_bit c 558 row)) + (a_prime_bit c 878 row)) + (a_prime_bit c 1198 row)) + (a_prime_bit c 1518 row)) - (c_prime_bit c 238 row)) - 2)) * (((((((a_prime_bit c 238 row) + (a_prime_bit c 558 row)) + (a_prime_bit c 878 row)) + (a_prime_bit c 1198 row)) + (a_prime_bit c 1518 row)) - (c_prime_bit c 238 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2828_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2828 c row ↔ constraint_2828 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2829 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 239 row) + (a_prime_bit c 559 row)) + (a_prime_bit c 879 row)) + (a_prime_bit c 1199 row)) + (a_prime_bit c 1519 row)) - (c_prime_bit c 239 row)) * (((((((a_prime_bit c 239 row) + (a_prime_bit c 559 row)) + (a_prime_bit c 879 row)) + (a_prime_bit c 1199 row)) + (a_prime_bit c 1519 row)) - (c_prime_bit c 239 row)) - 2)) * (((((((a_prime_bit c 239 row) + (a_prime_bit c 559 row)) + (a_prime_bit c 879 row)) + (a_prime_bit c 1199 row)) + (a_prime_bit c 1519 row)) - (c_prime_bit c 239 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2829_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2829 c row ↔ constraint_2829 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2830 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 240 row) + (a_prime_bit c 560 row)) + (a_prime_bit c 880 row)) + (a_prime_bit c 1200 row)) + (a_prime_bit c 1520 row)) - (c_prime_bit c 240 row)) * (((((((a_prime_bit c 240 row) + (a_prime_bit c 560 row)) + (a_prime_bit c 880 row)) + (a_prime_bit c 1200 row)) + (a_prime_bit c 1520 row)) - (c_prime_bit c 240 row)) - 2)) * (((((((a_prime_bit c 240 row) + (a_prime_bit c 560 row)) + (a_prime_bit c 880 row)) + (a_prime_bit c 1200 row)) + (a_prime_bit c 1520 row)) - (c_prime_bit c 240 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2830_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2830 c row ↔ constraint_2830 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2831 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 241 row) + (a_prime_bit c 561 row)) + (a_prime_bit c 881 row)) + (a_prime_bit c 1201 row)) + (a_prime_bit c 1521 row)) - (c_prime_bit c 241 row)) * (((((((a_prime_bit c 241 row) + (a_prime_bit c 561 row)) + (a_prime_bit c 881 row)) + (a_prime_bit c 1201 row)) + (a_prime_bit c 1521 row)) - (c_prime_bit c 241 row)) - 2)) * (((((((a_prime_bit c 241 row) + (a_prime_bit c 561 row)) + (a_prime_bit c 881 row)) + (a_prime_bit c 1201 row)) + (a_prime_bit c 1521 row)) - (c_prime_bit c 241 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2831_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2831 c row ↔ constraint_2831 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2832 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 242 row) + (a_prime_bit c 562 row)) + (a_prime_bit c 882 row)) + (a_prime_bit c 1202 row)) + (a_prime_bit c 1522 row)) - (c_prime_bit c 242 row)) * (((((((a_prime_bit c 242 row) + (a_prime_bit c 562 row)) + (a_prime_bit c 882 row)) + (a_prime_bit c 1202 row)) + (a_prime_bit c 1522 row)) - (c_prime_bit c 242 row)) - 2)) * (((((((a_prime_bit c 242 row) + (a_prime_bit c 562 row)) + (a_prime_bit c 882 row)) + (a_prime_bit c 1202 row)) + (a_prime_bit c 1522 row)) - (c_prime_bit c 242 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2832_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2832 c row ↔ constraint_2832 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2833 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 243 row) + (a_prime_bit c 563 row)) + (a_prime_bit c 883 row)) + (a_prime_bit c 1203 row)) + (a_prime_bit c 1523 row)) - (c_prime_bit c 243 row)) * (((((((a_prime_bit c 243 row) + (a_prime_bit c 563 row)) + (a_prime_bit c 883 row)) + (a_prime_bit c 1203 row)) + (a_prime_bit c 1523 row)) - (c_prime_bit c 243 row)) - 2)) * (((((((a_prime_bit c 243 row) + (a_prime_bit c 563 row)) + (a_prime_bit c 883 row)) + (a_prime_bit c 1203 row)) + (a_prime_bit c 1523 row)) - (c_prime_bit c 243 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2833_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2833 c row ↔ constraint_2833 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2834 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 244 row) + (a_prime_bit c 564 row)) + (a_prime_bit c 884 row)) + (a_prime_bit c 1204 row)) + (a_prime_bit c 1524 row)) - (c_prime_bit c 244 row)) * (((((((a_prime_bit c 244 row) + (a_prime_bit c 564 row)) + (a_prime_bit c 884 row)) + (a_prime_bit c 1204 row)) + (a_prime_bit c 1524 row)) - (c_prime_bit c 244 row)) - 2)) * (((((((a_prime_bit c 244 row) + (a_prime_bit c 564 row)) + (a_prime_bit c 884 row)) + (a_prime_bit c 1204 row)) + (a_prime_bit c 1524 row)) - (c_prime_bit c 244 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2834_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2834 c row ↔ constraint_2834 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2835 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 245 row) + (a_prime_bit c 565 row)) + (a_prime_bit c 885 row)) + (a_prime_bit c 1205 row)) + (a_prime_bit c 1525 row)) - (c_prime_bit c 245 row)) * (((((((a_prime_bit c 245 row) + (a_prime_bit c 565 row)) + (a_prime_bit c 885 row)) + (a_prime_bit c 1205 row)) + (a_prime_bit c 1525 row)) - (c_prime_bit c 245 row)) - 2)) * (((((((a_prime_bit c 245 row) + (a_prime_bit c 565 row)) + (a_prime_bit c 885 row)) + (a_prime_bit c 1205 row)) + (a_prime_bit c 1525 row)) - (c_prime_bit c 245 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2835_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2835 c row ↔ constraint_2835 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2836 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 246 row) + (a_prime_bit c 566 row)) + (a_prime_bit c 886 row)) + (a_prime_bit c 1206 row)) + (a_prime_bit c 1526 row)) - (c_prime_bit c 246 row)) * (((((((a_prime_bit c 246 row) + (a_prime_bit c 566 row)) + (a_prime_bit c 886 row)) + (a_prime_bit c 1206 row)) + (a_prime_bit c 1526 row)) - (c_prime_bit c 246 row)) - 2)) * (((((((a_prime_bit c 246 row) + (a_prime_bit c 566 row)) + (a_prime_bit c 886 row)) + (a_prime_bit c 1206 row)) + (a_prime_bit c 1526 row)) - (c_prime_bit c 246 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2836_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2836 c row ↔ constraint_2836 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2837 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 247 row) + (a_prime_bit c 567 row)) + (a_prime_bit c 887 row)) + (a_prime_bit c 1207 row)) + (a_prime_bit c 1527 row)) - (c_prime_bit c 247 row)) * (((((((a_prime_bit c 247 row) + (a_prime_bit c 567 row)) + (a_prime_bit c 887 row)) + (a_prime_bit c 1207 row)) + (a_prime_bit c 1527 row)) - (c_prime_bit c 247 row)) - 2)) * (((((((a_prime_bit c 247 row) + (a_prime_bit c 567 row)) + (a_prime_bit c 887 row)) + (a_prime_bit c 1207 row)) + (a_prime_bit c 1527 row)) - (c_prime_bit c 247 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2837_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2837 c row ↔ constraint_2837 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2838 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 248 row) + (a_prime_bit c 568 row)) + (a_prime_bit c 888 row)) + (a_prime_bit c 1208 row)) + (a_prime_bit c 1528 row)) - (c_prime_bit c 248 row)) * (((((((a_prime_bit c 248 row) + (a_prime_bit c 568 row)) + (a_prime_bit c 888 row)) + (a_prime_bit c 1208 row)) + (a_prime_bit c 1528 row)) - (c_prime_bit c 248 row)) - 2)) * (((((((a_prime_bit c 248 row) + (a_prime_bit c 568 row)) + (a_prime_bit c 888 row)) + (a_prime_bit c 1208 row)) + (a_prime_bit c 1528 row)) - (c_prime_bit c 248 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2838_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2838 c row ↔ constraint_2838 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2839 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 249 row) + (a_prime_bit c 569 row)) + (a_prime_bit c 889 row)) + (a_prime_bit c 1209 row)) + (a_prime_bit c 1529 row)) - (c_prime_bit c 249 row)) * (((((((a_prime_bit c 249 row) + (a_prime_bit c 569 row)) + (a_prime_bit c 889 row)) + (a_prime_bit c 1209 row)) + (a_prime_bit c 1529 row)) - (c_prime_bit c 249 row)) - 2)) * (((((((a_prime_bit c 249 row) + (a_prime_bit c 569 row)) + (a_prime_bit c 889 row)) + (a_prime_bit c 1209 row)) + (a_prime_bit c 1529 row)) - (c_prime_bit c 249 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2839_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2839 c row ↔ constraint_2839 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2840 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 250 row) + (a_prime_bit c 570 row)) + (a_prime_bit c 890 row)) + (a_prime_bit c 1210 row)) + (a_prime_bit c 1530 row)) - (c_prime_bit c 250 row)) * (((((((a_prime_bit c 250 row) + (a_prime_bit c 570 row)) + (a_prime_bit c 890 row)) + (a_prime_bit c 1210 row)) + (a_prime_bit c 1530 row)) - (c_prime_bit c 250 row)) - 2)) * (((((((a_prime_bit c 250 row) + (a_prime_bit c 570 row)) + (a_prime_bit c 890 row)) + (a_prime_bit c 1210 row)) + (a_prime_bit c 1530 row)) - (c_prime_bit c 250 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2840_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2840 c row ↔ constraint_2840 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2841 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 251 row) + (a_prime_bit c 571 row)) + (a_prime_bit c 891 row)) + (a_prime_bit c 1211 row)) + (a_prime_bit c 1531 row)) - (c_prime_bit c 251 row)) * (((((((a_prime_bit c 251 row) + (a_prime_bit c 571 row)) + (a_prime_bit c 891 row)) + (a_prime_bit c 1211 row)) + (a_prime_bit c 1531 row)) - (c_prime_bit c 251 row)) - 2)) * (((((((a_prime_bit c 251 row) + (a_prime_bit c 571 row)) + (a_prime_bit c 891 row)) + (a_prime_bit c 1211 row)) + (a_prime_bit c 1531 row)) - (c_prime_bit c 251 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2841_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2841 c row ↔ constraint_2841 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2842 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 252 row) + (a_prime_bit c 572 row)) + (a_prime_bit c 892 row)) + (a_prime_bit c 1212 row)) + (a_prime_bit c 1532 row)) - (c_prime_bit c 252 row)) * (((((((a_prime_bit c 252 row) + (a_prime_bit c 572 row)) + (a_prime_bit c 892 row)) + (a_prime_bit c 1212 row)) + (a_prime_bit c 1532 row)) - (c_prime_bit c 252 row)) - 2)) * (((((((a_prime_bit c 252 row) + (a_prime_bit c 572 row)) + (a_prime_bit c 892 row)) + (a_prime_bit c 1212 row)) + (a_prime_bit c 1532 row)) - (c_prime_bit c 252 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2842_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2842 c row ↔ constraint_2842 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2843 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 253 row) + (a_prime_bit c 573 row)) + (a_prime_bit c 893 row)) + (a_prime_bit c 1213 row)) + (a_prime_bit c 1533 row)) - (c_prime_bit c 253 row)) * (((((((a_prime_bit c 253 row) + (a_prime_bit c 573 row)) + (a_prime_bit c 893 row)) + (a_prime_bit c 1213 row)) + (a_prime_bit c 1533 row)) - (c_prime_bit c 253 row)) - 2)) * (((((((a_prime_bit c 253 row) + (a_prime_bit c 573 row)) + (a_prime_bit c 893 row)) + (a_prime_bit c 1213 row)) + (a_prime_bit c 1533 row)) - (c_prime_bit c 253 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2843_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2843 c row ↔ constraint_2843 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2844 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 254 row) + (a_prime_bit c 574 row)) + (a_prime_bit c 894 row)) + (a_prime_bit c 1214 row)) + (a_prime_bit c 1534 row)) - (c_prime_bit c 254 row)) * (((((((a_prime_bit c 254 row) + (a_prime_bit c 574 row)) + (a_prime_bit c 894 row)) + (a_prime_bit c 1214 row)) + (a_prime_bit c 1534 row)) - (c_prime_bit c 254 row)) - 2)) * (((((((a_prime_bit c 254 row) + (a_prime_bit c 574 row)) + (a_prime_bit c 894 row)) + (a_prime_bit c 1214 row)) + (a_prime_bit c 1534 row)) - (c_prime_bit c 254 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2844_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2844 c row ↔ constraint_2844 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2845 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 255 row) + (a_prime_bit c 575 row)) + (a_prime_bit c 895 row)) + (a_prime_bit c 1215 row)) + (a_prime_bit c 1535 row)) - (c_prime_bit c 255 row)) * (((((((a_prime_bit c 255 row) + (a_prime_bit c 575 row)) + (a_prime_bit c 895 row)) + (a_prime_bit c 1215 row)) + (a_prime_bit c 1535 row)) - (c_prime_bit c 255 row)) - 2)) * (((((((a_prime_bit c 255 row) + (a_prime_bit c 575 row)) + (a_prime_bit c 895 row)) + (a_prime_bit c 1215 row)) + (a_prime_bit c 1535 row)) - (c_prime_bit c 255 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2845_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2845 c row ↔ constraint_2845 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2846 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 256 row) + (a_prime_bit c 576 row)) + (a_prime_bit c 896 row)) + (a_prime_bit c 1216 row)) + (a_prime_bit c 1536 row)) - (c_prime_bit c 256 row)) * (((((((a_prime_bit c 256 row) + (a_prime_bit c 576 row)) + (a_prime_bit c 896 row)) + (a_prime_bit c 1216 row)) + (a_prime_bit c 1536 row)) - (c_prime_bit c 256 row)) - 2)) * (((((((a_prime_bit c 256 row) + (a_prime_bit c 576 row)) + (a_prime_bit c 896 row)) + (a_prime_bit c 1216 row)) + (a_prime_bit c 1536 row)) - (c_prime_bit c 256 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2846_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2846 c row ↔ constraint_2846 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2847 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 257 row) + (a_prime_bit c 577 row)) + (a_prime_bit c 897 row)) + (a_prime_bit c 1217 row)) + (a_prime_bit c 1537 row)) - (c_prime_bit c 257 row)) * (((((((a_prime_bit c 257 row) + (a_prime_bit c 577 row)) + (a_prime_bit c 897 row)) + (a_prime_bit c 1217 row)) + (a_prime_bit c 1537 row)) - (c_prime_bit c 257 row)) - 2)) * (((((((a_prime_bit c 257 row) + (a_prime_bit c 577 row)) + (a_prime_bit c 897 row)) + (a_prime_bit c 1217 row)) + (a_prime_bit c 1537 row)) - (c_prime_bit c 257 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2847_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2847 c row ↔ constraint_2847 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2848 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 258 row) + (a_prime_bit c 578 row)) + (a_prime_bit c 898 row)) + (a_prime_bit c 1218 row)) + (a_prime_bit c 1538 row)) - (c_prime_bit c 258 row)) * (((((((a_prime_bit c 258 row) + (a_prime_bit c 578 row)) + (a_prime_bit c 898 row)) + (a_prime_bit c 1218 row)) + (a_prime_bit c 1538 row)) - (c_prime_bit c 258 row)) - 2)) * (((((((a_prime_bit c 258 row) + (a_prime_bit c 578 row)) + (a_prime_bit c 898 row)) + (a_prime_bit c 1218 row)) + (a_prime_bit c 1538 row)) - (c_prime_bit c 258 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2848_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2848 c row ↔ constraint_2848 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2849 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 259 row) + (a_prime_bit c 579 row)) + (a_prime_bit c 899 row)) + (a_prime_bit c 1219 row)) + (a_prime_bit c 1539 row)) - (c_prime_bit c 259 row)) * (((((((a_prime_bit c 259 row) + (a_prime_bit c 579 row)) + (a_prime_bit c 899 row)) + (a_prime_bit c 1219 row)) + (a_prime_bit c 1539 row)) - (c_prime_bit c 259 row)) - 2)) * (((((((a_prime_bit c 259 row) + (a_prime_bit c 579 row)) + (a_prime_bit c 899 row)) + (a_prime_bit c 1219 row)) + (a_prime_bit c 1539 row)) - (c_prime_bit c 259 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2849_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2849 c row ↔ constraint_2849 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2850 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 260 row) + (a_prime_bit c 580 row)) + (a_prime_bit c 900 row)) + (a_prime_bit c 1220 row)) + (a_prime_bit c 1540 row)) - (c_prime_bit c 260 row)) * (((((((a_prime_bit c 260 row) + (a_prime_bit c 580 row)) + (a_prime_bit c 900 row)) + (a_prime_bit c 1220 row)) + (a_prime_bit c 1540 row)) - (c_prime_bit c 260 row)) - 2)) * (((((((a_prime_bit c 260 row) + (a_prime_bit c 580 row)) + (a_prime_bit c 900 row)) + (a_prime_bit c 1220 row)) + (a_prime_bit c 1540 row)) - (c_prime_bit c 260 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2850_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2850 c row ↔ constraint_2850 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2851 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 261 row) + (a_prime_bit c 581 row)) + (a_prime_bit c 901 row)) + (a_prime_bit c 1221 row)) + (a_prime_bit c 1541 row)) - (c_prime_bit c 261 row)) * (((((((a_prime_bit c 261 row) + (a_prime_bit c 581 row)) + (a_prime_bit c 901 row)) + (a_prime_bit c 1221 row)) + (a_prime_bit c 1541 row)) - (c_prime_bit c 261 row)) - 2)) * (((((((a_prime_bit c 261 row) + (a_prime_bit c 581 row)) + (a_prime_bit c 901 row)) + (a_prime_bit c 1221 row)) + (a_prime_bit c 1541 row)) - (c_prime_bit c 261 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2851_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2851 c row ↔ constraint_2851 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2852 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 262 row) + (a_prime_bit c 582 row)) + (a_prime_bit c 902 row)) + (a_prime_bit c 1222 row)) + (a_prime_bit c 1542 row)) - (c_prime_bit c 262 row)) * (((((((a_prime_bit c 262 row) + (a_prime_bit c 582 row)) + (a_prime_bit c 902 row)) + (a_prime_bit c 1222 row)) + (a_prime_bit c 1542 row)) - (c_prime_bit c 262 row)) - 2)) * (((((((a_prime_bit c 262 row) + (a_prime_bit c 582 row)) + (a_prime_bit c 902 row)) + (a_prime_bit c 1222 row)) + (a_prime_bit c 1542 row)) - (c_prime_bit c 262 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2852_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2852 c row ↔ constraint_2852 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2853 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 263 row) + (a_prime_bit c 583 row)) + (a_prime_bit c 903 row)) + (a_prime_bit c 1223 row)) + (a_prime_bit c 1543 row)) - (c_prime_bit c 263 row)) * (((((((a_prime_bit c 263 row) + (a_prime_bit c 583 row)) + (a_prime_bit c 903 row)) + (a_prime_bit c 1223 row)) + (a_prime_bit c 1543 row)) - (c_prime_bit c 263 row)) - 2)) * (((((((a_prime_bit c 263 row) + (a_prime_bit c 583 row)) + (a_prime_bit c 903 row)) + (a_prime_bit c 1223 row)) + (a_prime_bit c 1543 row)) - (c_prime_bit c 263 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2853_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2853 c row ↔ constraint_2853 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2854 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 264 row) + (a_prime_bit c 584 row)) + (a_prime_bit c 904 row)) + (a_prime_bit c 1224 row)) + (a_prime_bit c 1544 row)) - (c_prime_bit c 264 row)) * (((((((a_prime_bit c 264 row) + (a_prime_bit c 584 row)) + (a_prime_bit c 904 row)) + (a_prime_bit c 1224 row)) + (a_prime_bit c 1544 row)) - (c_prime_bit c 264 row)) - 2)) * (((((((a_prime_bit c 264 row) + (a_prime_bit c 584 row)) + (a_prime_bit c 904 row)) + (a_prime_bit c 1224 row)) + (a_prime_bit c 1544 row)) - (c_prime_bit c 264 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2854_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2854 c row ↔ constraint_2854 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2855 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 265 row) + (a_prime_bit c 585 row)) + (a_prime_bit c 905 row)) + (a_prime_bit c 1225 row)) + (a_prime_bit c 1545 row)) - (c_prime_bit c 265 row)) * (((((((a_prime_bit c 265 row) + (a_prime_bit c 585 row)) + (a_prime_bit c 905 row)) + (a_prime_bit c 1225 row)) + (a_prime_bit c 1545 row)) - (c_prime_bit c 265 row)) - 2)) * (((((((a_prime_bit c 265 row) + (a_prime_bit c 585 row)) + (a_prime_bit c 905 row)) + (a_prime_bit c 1225 row)) + (a_prime_bit c 1545 row)) - (c_prime_bit c 265 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2855_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2855 c row ↔ constraint_2855 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2856 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 266 row) + (a_prime_bit c 586 row)) + (a_prime_bit c 906 row)) + (a_prime_bit c 1226 row)) + (a_prime_bit c 1546 row)) - (c_prime_bit c 266 row)) * (((((((a_prime_bit c 266 row) + (a_prime_bit c 586 row)) + (a_prime_bit c 906 row)) + (a_prime_bit c 1226 row)) + (a_prime_bit c 1546 row)) - (c_prime_bit c 266 row)) - 2)) * (((((((a_prime_bit c 266 row) + (a_prime_bit c 586 row)) + (a_prime_bit c 906 row)) + (a_prime_bit c 1226 row)) + (a_prime_bit c 1546 row)) - (c_prime_bit c 266 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2856_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2856 c row ↔ constraint_2856 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2857 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 267 row) + (a_prime_bit c 587 row)) + (a_prime_bit c 907 row)) + (a_prime_bit c 1227 row)) + (a_prime_bit c 1547 row)) - (c_prime_bit c 267 row)) * (((((((a_prime_bit c 267 row) + (a_prime_bit c 587 row)) + (a_prime_bit c 907 row)) + (a_prime_bit c 1227 row)) + (a_prime_bit c 1547 row)) - (c_prime_bit c 267 row)) - 2)) * (((((((a_prime_bit c 267 row) + (a_prime_bit c 587 row)) + (a_prime_bit c 907 row)) + (a_prime_bit c 1227 row)) + (a_prime_bit c 1547 row)) - (c_prime_bit c 267 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2857_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2857 c row ↔ constraint_2857 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2858 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 268 row) + (a_prime_bit c 588 row)) + (a_prime_bit c 908 row)) + (a_prime_bit c 1228 row)) + (a_prime_bit c 1548 row)) - (c_prime_bit c 268 row)) * (((((((a_prime_bit c 268 row) + (a_prime_bit c 588 row)) + (a_prime_bit c 908 row)) + (a_prime_bit c 1228 row)) + (a_prime_bit c 1548 row)) - (c_prime_bit c 268 row)) - 2)) * (((((((a_prime_bit c 268 row) + (a_prime_bit c 588 row)) + (a_prime_bit c 908 row)) + (a_prime_bit c 1228 row)) + (a_prime_bit c 1548 row)) - (c_prime_bit c 268 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2858_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2858 c row ↔ constraint_2858 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2859 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 269 row) + (a_prime_bit c 589 row)) + (a_prime_bit c 909 row)) + (a_prime_bit c 1229 row)) + (a_prime_bit c 1549 row)) - (c_prime_bit c 269 row)) * (((((((a_prime_bit c 269 row) + (a_prime_bit c 589 row)) + (a_prime_bit c 909 row)) + (a_prime_bit c 1229 row)) + (a_prime_bit c 1549 row)) - (c_prime_bit c 269 row)) - 2)) * (((((((a_prime_bit c 269 row) + (a_prime_bit c 589 row)) + (a_prime_bit c 909 row)) + (a_prime_bit c 1229 row)) + (a_prime_bit c 1549 row)) - (c_prime_bit c 269 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2859_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2859 c row ↔ constraint_2859 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2860 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 270 row) + (a_prime_bit c 590 row)) + (a_prime_bit c 910 row)) + (a_prime_bit c 1230 row)) + (a_prime_bit c 1550 row)) - (c_prime_bit c 270 row)) * (((((((a_prime_bit c 270 row) + (a_prime_bit c 590 row)) + (a_prime_bit c 910 row)) + (a_prime_bit c 1230 row)) + (a_prime_bit c 1550 row)) - (c_prime_bit c 270 row)) - 2)) * (((((((a_prime_bit c 270 row) + (a_prime_bit c 590 row)) + (a_prime_bit c 910 row)) + (a_prime_bit c 1230 row)) + (a_prime_bit c 1550 row)) - (c_prime_bit c 270 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2860_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2860 c row ↔ constraint_2860 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2861 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 271 row) + (a_prime_bit c 591 row)) + (a_prime_bit c 911 row)) + (a_prime_bit c 1231 row)) + (a_prime_bit c 1551 row)) - (c_prime_bit c 271 row)) * (((((((a_prime_bit c 271 row) + (a_prime_bit c 591 row)) + (a_prime_bit c 911 row)) + (a_prime_bit c 1231 row)) + (a_prime_bit c 1551 row)) - (c_prime_bit c 271 row)) - 2)) * (((((((a_prime_bit c 271 row) + (a_prime_bit c 591 row)) + (a_prime_bit c 911 row)) + (a_prime_bit c 1231 row)) + (a_prime_bit c 1551 row)) - (c_prime_bit c 271 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2861_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2861 c row ↔ constraint_2861 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2862 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 272 row) + (a_prime_bit c 592 row)) + (a_prime_bit c 912 row)) + (a_prime_bit c 1232 row)) + (a_prime_bit c 1552 row)) - (c_prime_bit c 272 row)) * (((((((a_prime_bit c 272 row) + (a_prime_bit c 592 row)) + (a_prime_bit c 912 row)) + (a_prime_bit c 1232 row)) + (a_prime_bit c 1552 row)) - (c_prime_bit c 272 row)) - 2)) * (((((((a_prime_bit c 272 row) + (a_prime_bit c 592 row)) + (a_prime_bit c 912 row)) + (a_prime_bit c 1232 row)) + (a_prime_bit c 1552 row)) - (c_prime_bit c 272 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2862_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2862 c row ↔ constraint_2862 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2863 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 273 row) + (a_prime_bit c 593 row)) + (a_prime_bit c 913 row)) + (a_prime_bit c 1233 row)) + (a_prime_bit c 1553 row)) - (c_prime_bit c 273 row)) * (((((((a_prime_bit c 273 row) + (a_prime_bit c 593 row)) + (a_prime_bit c 913 row)) + (a_prime_bit c 1233 row)) + (a_prime_bit c 1553 row)) - (c_prime_bit c 273 row)) - 2)) * (((((((a_prime_bit c 273 row) + (a_prime_bit c 593 row)) + (a_prime_bit c 913 row)) + (a_prime_bit c 1233 row)) + (a_prime_bit c 1553 row)) - (c_prime_bit c 273 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2863_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2863 c row ↔ constraint_2863 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2864 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 274 row) + (a_prime_bit c 594 row)) + (a_prime_bit c 914 row)) + (a_prime_bit c 1234 row)) + (a_prime_bit c 1554 row)) - (c_prime_bit c 274 row)) * (((((((a_prime_bit c 274 row) + (a_prime_bit c 594 row)) + (a_prime_bit c 914 row)) + (a_prime_bit c 1234 row)) + (a_prime_bit c 1554 row)) - (c_prime_bit c 274 row)) - 2)) * (((((((a_prime_bit c 274 row) + (a_prime_bit c 594 row)) + (a_prime_bit c 914 row)) + (a_prime_bit c 1234 row)) + (a_prime_bit c 1554 row)) - (c_prime_bit c 274 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2864_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2864 c row ↔ constraint_2864 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2865 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 275 row) + (a_prime_bit c 595 row)) + (a_prime_bit c 915 row)) + (a_prime_bit c 1235 row)) + (a_prime_bit c 1555 row)) - (c_prime_bit c 275 row)) * (((((((a_prime_bit c 275 row) + (a_prime_bit c 595 row)) + (a_prime_bit c 915 row)) + (a_prime_bit c 1235 row)) + (a_prime_bit c 1555 row)) - (c_prime_bit c 275 row)) - 2)) * (((((((a_prime_bit c 275 row) + (a_prime_bit c 595 row)) + (a_prime_bit c 915 row)) + (a_prime_bit c 1235 row)) + (a_prime_bit c 1555 row)) - (c_prime_bit c 275 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2865_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2865 c row ↔ constraint_2865 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2866 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 276 row) + (a_prime_bit c 596 row)) + (a_prime_bit c 916 row)) + (a_prime_bit c 1236 row)) + (a_prime_bit c 1556 row)) - (c_prime_bit c 276 row)) * (((((((a_prime_bit c 276 row) + (a_prime_bit c 596 row)) + (a_prime_bit c 916 row)) + (a_prime_bit c 1236 row)) + (a_prime_bit c 1556 row)) - (c_prime_bit c 276 row)) - 2)) * (((((((a_prime_bit c 276 row) + (a_prime_bit c 596 row)) + (a_prime_bit c 916 row)) + (a_prime_bit c 1236 row)) + (a_prime_bit c 1556 row)) - (c_prime_bit c 276 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2866_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2866 c row ↔ constraint_2866 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2867 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 277 row) + (a_prime_bit c 597 row)) + (a_prime_bit c 917 row)) + (a_prime_bit c 1237 row)) + (a_prime_bit c 1557 row)) - (c_prime_bit c 277 row)) * (((((((a_prime_bit c 277 row) + (a_prime_bit c 597 row)) + (a_prime_bit c 917 row)) + (a_prime_bit c 1237 row)) + (a_prime_bit c 1557 row)) - (c_prime_bit c 277 row)) - 2)) * (((((((a_prime_bit c 277 row) + (a_prime_bit c 597 row)) + (a_prime_bit c 917 row)) + (a_prime_bit c 1237 row)) + (a_prime_bit c 1557 row)) - (c_prime_bit c 277 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2867_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2867 c row ↔ constraint_2867 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2868 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 278 row) + (a_prime_bit c 598 row)) + (a_prime_bit c 918 row)) + (a_prime_bit c 1238 row)) + (a_prime_bit c 1558 row)) - (c_prime_bit c 278 row)) * (((((((a_prime_bit c 278 row) + (a_prime_bit c 598 row)) + (a_prime_bit c 918 row)) + (a_prime_bit c 1238 row)) + (a_prime_bit c 1558 row)) - (c_prime_bit c 278 row)) - 2)) * (((((((a_prime_bit c 278 row) + (a_prime_bit c 598 row)) + (a_prime_bit c 918 row)) + (a_prime_bit c 1238 row)) + (a_prime_bit c 1558 row)) - (c_prime_bit c 278 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2868_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2868 c row ↔ constraint_2868 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2869 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 279 row) + (a_prime_bit c 599 row)) + (a_prime_bit c 919 row)) + (a_prime_bit c 1239 row)) + (a_prime_bit c 1559 row)) - (c_prime_bit c 279 row)) * (((((((a_prime_bit c 279 row) + (a_prime_bit c 599 row)) + (a_prime_bit c 919 row)) + (a_prime_bit c 1239 row)) + (a_prime_bit c 1559 row)) - (c_prime_bit c 279 row)) - 2)) * (((((((a_prime_bit c 279 row) + (a_prime_bit c 599 row)) + (a_prime_bit c 919 row)) + (a_prime_bit c 1239 row)) + (a_prime_bit c 1559 row)) - (c_prime_bit c 279 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2869_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2869 c row ↔ constraint_2869 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2870 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 280 row) + (a_prime_bit c 600 row)) + (a_prime_bit c 920 row)) + (a_prime_bit c 1240 row)) + (a_prime_bit c 1560 row)) - (c_prime_bit c 280 row)) * (((((((a_prime_bit c 280 row) + (a_prime_bit c 600 row)) + (a_prime_bit c 920 row)) + (a_prime_bit c 1240 row)) + (a_prime_bit c 1560 row)) - (c_prime_bit c 280 row)) - 2)) * (((((((a_prime_bit c 280 row) + (a_prime_bit c 600 row)) + (a_prime_bit c 920 row)) + (a_prime_bit c 1240 row)) + (a_prime_bit c 1560 row)) - (c_prime_bit c 280 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2870_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2870 c row ↔ constraint_2870 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2871 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 281 row) + (a_prime_bit c 601 row)) + (a_prime_bit c 921 row)) + (a_prime_bit c 1241 row)) + (a_prime_bit c 1561 row)) - (c_prime_bit c 281 row)) * (((((((a_prime_bit c 281 row) + (a_prime_bit c 601 row)) + (a_prime_bit c 921 row)) + (a_prime_bit c 1241 row)) + (a_prime_bit c 1561 row)) - (c_prime_bit c 281 row)) - 2)) * (((((((a_prime_bit c 281 row) + (a_prime_bit c 601 row)) + (a_prime_bit c 921 row)) + (a_prime_bit c 1241 row)) + (a_prime_bit c 1561 row)) - (c_prime_bit c 281 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2871_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2871 c row ↔ constraint_2871 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2872 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 282 row) + (a_prime_bit c 602 row)) + (a_prime_bit c 922 row)) + (a_prime_bit c 1242 row)) + (a_prime_bit c 1562 row)) - (c_prime_bit c 282 row)) * (((((((a_prime_bit c 282 row) + (a_prime_bit c 602 row)) + (a_prime_bit c 922 row)) + (a_prime_bit c 1242 row)) + (a_prime_bit c 1562 row)) - (c_prime_bit c 282 row)) - 2)) * (((((((a_prime_bit c 282 row) + (a_prime_bit c 602 row)) + (a_prime_bit c 922 row)) + (a_prime_bit c 1242 row)) + (a_prime_bit c 1562 row)) - (c_prime_bit c 282 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2872_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2872 c row ↔ constraint_2872 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2873 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 283 row) + (a_prime_bit c 603 row)) + (a_prime_bit c 923 row)) + (a_prime_bit c 1243 row)) + (a_prime_bit c 1563 row)) - (c_prime_bit c 283 row)) * (((((((a_prime_bit c 283 row) + (a_prime_bit c 603 row)) + (a_prime_bit c 923 row)) + (a_prime_bit c 1243 row)) + (a_prime_bit c 1563 row)) - (c_prime_bit c 283 row)) - 2)) * (((((((a_prime_bit c 283 row) + (a_prime_bit c 603 row)) + (a_prime_bit c 923 row)) + (a_prime_bit c 1243 row)) + (a_prime_bit c 1563 row)) - (c_prime_bit c 283 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2873_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2873 c row ↔ constraint_2873 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2874 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 284 row) + (a_prime_bit c 604 row)) + (a_prime_bit c 924 row)) + (a_prime_bit c 1244 row)) + (a_prime_bit c 1564 row)) - (c_prime_bit c 284 row)) * (((((((a_prime_bit c 284 row) + (a_prime_bit c 604 row)) + (a_prime_bit c 924 row)) + (a_prime_bit c 1244 row)) + (a_prime_bit c 1564 row)) - (c_prime_bit c 284 row)) - 2)) * (((((((a_prime_bit c 284 row) + (a_prime_bit c 604 row)) + (a_prime_bit c 924 row)) + (a_prime_bit c 1244 row)) + (a_prime_bit c 1564 row)) - (c_prime_bit c 284 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2874_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2874 c row ↔ constraint_2874 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2875 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 285 row) + (a_prime_bit c 605 row)) + (a_prime_bit c 925 row)) + (a_prime_bit c 1245 row)) + (a_prime_bit c 1565 row)) - (c_prime_bit c 285 row)) * (((((((a_prime_bit c 285 row) + (a_prime_bit c 605 row)) + (a_prime_bit c 925 row)) + (a_prime_bit c 1245 row)) + (a_prime_bit c 1565 row)) - (c_prime_bit c 285 row)) - 2)) * (((((((a_prime_bit c 285 row) + (a_prime_bit c 605 row)) + (a_prime_bit c 925 row)) + (a_prime_bit c 1245 row)) + (a_prime_bit c 1565 row)) - (c_prime_bit c 285 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2875_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2875 c row ↔ constraint_2875 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2876 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 286 row) + (a_prime_bit c 606 row)) + (a_prime_bit c 926 row)) + (a_prime_bit c 1246 row)) + (a_prime_bit c 1566 row)) - (c_prime_bit c 286 row)) * (((((((a_prime_bit c 286 row) + (a_prime_bit c 606 row)) + (a_prime_bit c 926 row)) + (a_prime_bit c 1246 row)) + (a_prime_bit c 1566 row)) - (c_prime_bit c 286 row)) - 2)) * (((((((a_prime_bit c 286 row) + (a_prime_bit c 606 row)) + (a_prime_bit c 926 row)) + (a_prime_bit c 1246 row)) + (a_prime_bit c 1566 row)) - (c_prime_bit c 286 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2876_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2876 c row ↔ constraint_2876 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2877 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 287 row) + (a_prime_bit c 607 row)) + (a_prime_bit c 927 row)) + (a_prime_bit c 1247 row)) + (a_prime_bit c 1567 row)) - (c_prime_bit c 287 row)) * (((((((a_prime_bit c 287 row) + (a_prime_bit c 607 row)) + (a_prime_bit c 927 row)) + (a_prime_bit c 1247 row)) + (a_prime_bit c 1567 row)) - (c_prime_bit c 287 row)) - 2)) * (((((((a_prime_bit c 287 row) + (a_prime_bit c 607 row)) + (a_prime_bit c 927 row)) + (a_prime_bit c 1247 row)) + (a_prime_bit c 1567 row)) - (c_prime_bit c 287 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2877_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2877 c row ↔ constraint_2877 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2878 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 288 row) + (a_prime_bit c 608 row)) + (a_prime_bit c 928 row)) + (a_prime_bit c 1248 row)) + (a_prime_bit c 1568 row)) - (c_prime_bit c 288 row)) * (((((((a_prime_bit c 288 row) + (a_prime_bit c 608 row)) + (a_prime_bit c 928 row)) + (a_prime_bit c 1248 row)) + (a_prime_bit c 1568 row)) - (c_prime_bit c 288 row)) - 2)) * (((((((a_prime_bit c 288 row) + (a_prime_bit c 608 row)) + (a_prime_bit c 928 row)) + (a_prime_bit c 1248 row)) + (a_prime_bit c 1568 row)) - (c_prime_bit c 288 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2878_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2878 c row ↔ constraint_2878 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2879 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 289 row) + (a_prime_bit c 609 row)) + (a_prime_bit c 929 row)) + (a_prime_bit c 1249 row)) + (a_prime_bit c 1569 row)) - (c_prime_bit c 289 row)) * (((((((a_prime_bit c 289 row) + (a_prime_bit c 609 row)) + (a_prime_bit c 929 row)) + (a_prime_bit c 1249 row)) + (a_prime_bit c 1569 row)) - (c_prime_bit c 289 row)) - 2)) * (((((((a_prime_bit c 289 row) + (a_prime_bit c 609 row)) + (a_prime_bit c 929 row)) + (a_prime_bit c 1249 row)) + (a_prime_bit c 1569 row)) - (c_prime_bit c 289 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2879_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2879 c row ↔ constraint_2879 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2880 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 290 row) + (a_prime_bit c 610 row)) + (a_prime_bit c 930 row)) + (a_prime_bit c 1250 row)) + (a_prime_bit c 1570 row)) - (c_prime_bit c 290 row)) * (((((((a_prime_bit c 290 row) + (a_prime_bit c 610 row)) + (a_prime_bit c 930 row)) + (a_prime_bit c 1250 row)) + (a_prime_bit c 1570 row)) - (c_prime_bit c 290 row)) - 2)) * (((((((a_prime_bit c 290 row) + (a_prime_bit c 610 row)) + (a_prime_bit c 930 row)) + (a_prime_bit c 1250 row)) + (a_prime_bit c 1570 row)) - (c_prime_bit c 290 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2880_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2880 c row ↔ constraint_2880 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2881 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 291 row) + (a_prime_bit c 611 row)) + (a_prime_bit c 931 row)) + (a_prime_bit c 1251 row)) + (a_prime_bit c 1571 row)) - (c_prime_bit c 291 row)) * (((((((a_prime_bit c 291 row) + (a_prime_bit c 611 row)) + (a_prime_bit c 931 row)) + (a_prime_bit c 1251 row)) + (a_prime_bit c 1571 row)) - (c_prime_bit c 291 row)) - 2)) * (((((((a_prime_bit c 291 row) + (a_prime_bit c 611 row)) + (a_prime_bit c 931 row)) + (a_prime_bit c 1251 row)) + (a_prime_bit c 1571 row)) - (c_prime_bit c 291 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2881_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2881 c row ↔ constraint_2881 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2882 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 292 row) + (a_prime_bit c 612 row)) + (a_prime_bit c 932 row)) + (a_prime_bit c 1252 row)) + (a_prime_bit c 1572 row)) - (c_prime_bit c 292 row)) * (((((((a_prime_bit c 292 row) + (a_prime_bit c 612 row)) + (a_prime_bit c 932 row)) + (a_prime_bit c 1252 row)) + (a_prime_bit c 1572 row)) - (c_prime_bit c 292 row)) - 2)) * (((((((a_prime_bit c 292 row) + (a_prime_bit c 612 row)) + (a_prime_bit c 932 row)) + (a_prime_bit c 1252 row)) + (a_prime_bit c 1572 row)) - (c_prime_bit c 292 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2882_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2882 c row ↔ constraint_2882 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2883 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 293 row) + (a_prime_bit c 613 row)) + (a_prime_bit c 933 row)) + (a_prime_bit c 1253 row)) + (a_prime_bit c 1573 row)) - (c_prime_bit c 293 row)) * (((((((a_prime_bit c 293 row) + (a_prime_bit c 613 row)) + (a_prime_bit c 933 row)) + (a_prime_bit c 1253 row)) + (a_prime_bit c 1573 row)) - (c_prime_bit c 293 row)) - 2)) * (((((((a_prime_bit c 293 row) + (a_prime_bit c 613 row)) + (a_prime_bit c 933 row)) + (a_prime_bit c 1253 row)) + (a_prime_bit c 1573 row)) - (c_prime_bit c 293 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2883_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2883 c row ↔ constraint_2883 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2884 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 294 row) + (a_prime_bit c 614 row)) + (a_prime_bit c 934 row)) + (a_prime_bit c 1254 row)) + (a_prime_bit c 1574 row)) - (c_prime_bit c 294 row)) * (((((((a_prime_bit c 294 row) + (a_prime_bit c 614 row)) + (a_prime_bit c 934 row)) + (a_prime_bit c 1254 row)) + (a_prime_bit c 1574 row)) - (c_prime_bit c 294 row)) - 2)) * (((((((a_prime_bit c 294 row) + (a_prime_bit c 614 row)) + (a_prime_bit c 934 row)) + (a_prime_bit c 1254 row)) + (a_prime_bit c 1574 row)) - (c_prime_bit c 294 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2884_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2884 c row ↔ constraint_2884 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2885 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 295 row) + (a_prime_bit c 615 row)) + (a_prime_bit c 935 row)) + (a_prime_bit c 1255 row)) + (a_prime_bit c 1575 row)) - (c_prime_bit c 295 row)) * (((((((a_prime_bit c 295 row) + (a_prime_bit c 615 row)) + (a_prime_bit c 935 row)) + (a_prime_bit c 1255 row)) + (a_prime_bit c 1575 row)) - (c_prime_bit c 295 row)) - 2)) * (((((((a_prime_bit c 295 row) + (a_prime_bit c 615 row)) + (a_prime_bit c 935 row)) + (a_prime_bit c 1255 row)) + (a_prime_bit c 1575 row)) - (c_prime_bit c 295 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2885_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2885 c row ↔ constraint_2885 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2886 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 296 row) + (a_prime_bit c 616 row)) + (a_prime_bit c 936 row)) + (a_prime_bit c 1256 row)) + (a_prime_bit c 1576 row)) - (c_prime_bit c 296 row)) * (((((((a_prime_bit c 296 row) + (a_prime_bit c 616 row)) + (a_prime_bit c 936 row)) + (a_prime_bit c 1256 row)) + (a_prime_bit c 1576 row)) - (c_prime_bit c 296 row)) - 2)) * (((((((a_prime_bit c 296 row) + (a_prime_bit c 616 row)) + (a_prime_bit c 936 row)) + (a_prime_bit c 1256 row)) + (a_prime_bit c 1576 row)) - (c_prime_bit c 296 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2886_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2886 c row ↔ constraint_2886 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2887 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 297 row) + (a_prime_bit c 617 row)) + (a_prime_bit c 937 row)) + (a_prime_bit c 1257 row)) + (a_prime_bit c 1577 row)) - (c_prime_bit c 297 row)) * (((((((a_prime_bit c 297 row) + (a_prime_bit c 617 row)) + (a_prime_bit c 937 row)) + (a_prime_bit c 1257 row)) + (a_prime_bit c 1577 row)) - (c_prime_bit c 297 row)) - 2)) * (((((((a_prime_bit c 297 row) + (a_prime_bit c 617 row)) + (a_prime_bit c 937 row)) + (a_prime_bit c 1257 row)) + (a_prime_bit c 1577 row)) - (c_prime_bit c 297 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2887_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2887 c row ↔ constraint_2887 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2888 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 298 row) + (a_prime_bit c 618 row)) + (a_prime_bit c 938 row)) + (a_prime_bit c 1258 row)) + (a_prime_bit c 1578 row)) - (c_prime_bit c 298 row)) * (((((((a_prime_bit c 298 row) + (a_prime_bit c 618 row)) + (a_prime_bit c 938 row)) + (a_prime_bit c 1258 row)) + (a_prime_bit c 1578 row)) - (c_prime_bit c 298 row)) - 2)) * (((((((a_prime_bit c 298 row) + (a_prime_bit c 618 row)) + (a_prime_bit c 938 row)) + (a_prime_bit c 1258 row)) + (a_prime_bit c 1578 row)) - (c_prime_bit c 298 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2888_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2888 c row ↔ constraint_2888 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2889 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 299 row) + (a_prime_bit c 619 row)) + (a_prime_bit c 939 row)) + (a_prime_bit c 1259 row)) + (a_prime_bit c 1579 row)) - (c_prime_bit c 299 row)) * (((((((a_prime_bit c 299 row) + (a_prime_bit c 619 row)) + (a_prime_bit c 939 row)) + (a_prime_bit c 1259 row)) + (a_prime_bit c 1579 row)) - (c_prime_bit c 299 row)) - 2)) * (((((((a_prime_bit c 299 row) + (a_prime_bit c 619 row)) + (a_prime_bit c 939 row)) + (a_prime_bit c 1259 row)) + (a_prime_bit c 1579 row)) - (c_prime_bit c 299 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2889_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2889 c row ↔ constraint_2889 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2890 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 300 row) + (a_prime_bit c 620 row)) + (a_prime_bit c 940 row)) + (a_prime_bit c 1260 row)) + (a_prime_bit c 1580 row)) - (c_prime_bit c 300 row)) * (((((((a_prime_bit c 300 row) + (a_prime_bit c 620 row)) + (a_prime_bit c 940 row)) + (a_prime_bit c 1260 row)) + (a_prime_bit c 1580 row)) - (c_prime_bit c 300 row)) - 2)) * (((((((a_prime_bit c 300 row) + (a_prime_bit c 620 row)) + (a_prime_bit c 940 row)) + (a_prime_bit c 1260 row)) + (a_prime_bit c 1580 row)) - (c_prime_bit c 300 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2890_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2890 c row ↔ constraint_2890 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2891 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 301 row) + (a_prime_bit c 621 row)) + (a_prime_bit c 941 row)) + (a_prime_bit c 1261 row)) + (a_prime_bit c 1581 row)) - (c_prime_bit c 301 row)) * (((((((a_prime_bit c 301 row) + (a_prime_bit c 621 row)) + (a_prime_bit c 941 row)) + (a_prime_bit c 1261 row)) + (a_prime_bit c 1581 row)) - (c_prime_bit c 301 row)) - 2)) * (((((((a_prime_bit c 301 row) + (a_prime_bit c 621 row)) + (a_prime_bit c 941 row)) + (a_prime_bit c 1261 row)) + (a_prime_bit c 1581 row)) - (c_prime_bit c 301 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2891_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2891 c row ↔ constraint_2891 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2892 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 302 row) + (a_prime_bit c 622 row)) + (a_prime_bit c 942 row)) + (a_prime_bit c 1262 row)) + (a_prime_bit c 1582 row)) - (c_prime_bit c 302 row)) * (((((((a_prime_bit c 302 row) + (a_prime_bit c 622 row)) + (a_prime_bit c 942 row)) + (a_prime_bit c 1262 row)) + (a_prime_bit c 1582 row)) - (c_prime_bit c 302 row)) - 2)) * (((((((a_prime_bit c 302 row) + (a_prime_bit c 622 row)) + (a_prime_bit c 942 row)) + (a_prime_bit c 1262 row)) + (a_prime_bit c 1582 row)) - (c_prime_bit c 302 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2892_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2892 c row ↔ constraint_2892 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2893 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 303 row) + (a_prime_bit c 623 row)) + (a_prime_bit c 943 row)) + (a_prime_bit c 1263 row)) + (a_prime_bit c 1583 row)) - (c_prime_bit c 303 row)) * (((((((a_prime_bit c 303 row) + (a_prime_bit c 623 row)) + (a_prime_bit c 943 row)) + (a_prime_bit c 1263 row)) + (a_prime_bit c 1583 row)) - (c_prime_bit c 303 row)) - 2)) * (((((((a_prime_bit c 303 row) + (a_prime_bit c 623 row)) + (a_prime_bit c 943 row)) + (a_prime_bit c 1263 row)) + (a_prime_bit c 1583 row)) - (c_prime_bit c 303 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2893_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2893 c row ↔ constraint_2893 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2894 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 304 row) + (a_prime_bit c 624 row)) + (a_prime_bit c 944 row)) + (a_prime_bit c 1264 row)) + (a_prime_bit c 1584 row)) - (c_prime_bit c 304 row)) * (((((((a_prime_bit c 304 row) + (a_prime_bit c 624 row)) + (a_prime_bit c 944 row)) + (a_prime_bit c 1264 row)) + (a_prime_bit c 1584 row)) - (c_prime_bit c 304 row)) - 2)) * (((((((a_prime_bit c 304 row) + (a_prime_bit c 624 row)) + (a_prime_bit c 944 row)) + (a_prime_bit c 1264 row)) + (a_prime_bit c 1584 row)) - (c_prime_bit c 304 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2894_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2894 c row ↔ constraint_2894 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2895 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 305 row) + (a_prime_bit c 625 row)) + (a_prime_bit c 945 row)) + (a_prime_bit c 1265 row)) + (a_prime_bit c 1585 row)) - (c_prime_bit c 305 row)) * (((((((a_prime_bit c 305 row) + (a_prime_bit c 625 row)) + (a_prime_bit c 945 row)) + (a_prime_bit c 1265 row)) + (a_prime_bit c 1585 row)) - (c_prime_bit c 305 row)) - 2)) * (((((((a_prime_bit c 305 row) + (a_prime_bit c 625 row)) + (a_prime_bit c 945 row)) + (a_prime_bit c 1265 row)) + (a_prime_bit c 1585 row)) - (c_prime_bit c 305 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2895_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2895 c row ↔ constraint_2895 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2896 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 306 row) + (a_prime_bit c 626 row)) + (a_prime_bit c 946 row)) + (a_prime_bit c 1266 row)) + (a_prime_bit c 1586 row)) - (c_prime_bit c 306 row)) * (((((((a_prime_bit c 306 row) + (a_prime_bit c 626 row)) + (a_prime_bit c 946 row)) + (a_prime_bit c 1266 row)) + (a_prime_bit c 1586 row)) - (c_prime_bit c 306 row)) - 2)) * (((((((a_prime_bit c 306 row) + (a_prime_bit c 626 row)) + (a_prime_bit c 946 row)) + (a_prime_bit c 1266 row)) + (a_prime_bit c 1586 row)) - (c_prime_bit c 306 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2896_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2896 c row ↔ constraint_2896 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2897 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 307 row) + (a_prime_bit c 627 row)) + (a_prime_bit c 947 row)) + (a_prime_bit c 1267 row)) + (a_prime_bit c 1587 row)) - (c_prime_bit c 307 row)) * (((((((a_prime_bit c 307 row) + (a_prime_bit c 627 row)) + (a_prime_bit c 947 row)) + (a_prime_bit c 1267 row)) + (a_prime_bit c 1587 row)) - (c_prime_bit c 307 row)) - 2)) * (((((((a_prime_bit c 307 row) + (a_prime_bit c 627 row)) + (a_prime_bit c 947 row)) + (a_prime_bit c 1267 row)) + (a_prime_bit c 1587 row)) - (c_prime_bit c 307 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2897_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2897 c row ↔ constraint_2897 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2898 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 308 row) + (a_prime_bit c 628 row)) + (a_prime_bit c 948 row)) + (a_prime_bit c 1268 row)) + (a_prime_bit c 1588 row)) - (c_prime_bit c 308 row)) * (((((((a_prime_bit c 308 row) + (a_prime_bit c 628 row)) + (a_prime_bit c 948 row)) + (a_prime_bit c 1268 row)) + (a_prime_bit c 1588 row)) - (c_prime_bit c 308 row)) - 2)) * (((((((a_prime_bit c 308 row) + (a_prime_bit c 628 row)) + (a_prime_bit c 948 row)) + (a_prime_bit c 1268 row)) + (a_prime_bit c 1588 row)) - (c_prime_bit c 308 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2898_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2898 c row ↔ constraint_2898 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2899 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 309 row) + (a_prime_bit c 629 row)) + (a_prime_bit c 949 row)) + (a_prime_bit c 1269 row)) + (a_prime_bit c 1589 row)) - (c_prime_bit c 309 row)) * (((((((a_prime_bit c 309 row) + (a_prime_bit c 629 row)) + (a_prime_bit c 949 row)) + (a_prime_bit c 1269 row)) + (a_prime_bit c 1589 row)) - (c_prime_bit c 309 row)) - 2)) * (((((((a_prime_bit c 309 row) + (a_prime_bit c 629 row)) + (a_prime_bit c 949 row)) + (a_prime_bit c 1269 row)) + (a_prime_bit c 1589 row)) - (c_prime_bit c 309 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2899_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2899 c row ↔ constraint_2899 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2900 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 310 row) + (a_prime_bit c 630 row)) + (a_prime_bit c 950 row)) + (a_prime_bit c 1270 row)) + (a_prime_bit c 1590 row)) - (c_prime_bit c 310 row)) * (((((((a_prime_bit c 310 row) + (a_prime_bit c 630 row)) + (a_prime_bit c 950 row)) + (a_prime_bit c 1270 row)) + (a_prime_bit c 1590 row)) - (c_prime_bit c 310 row)) - 2)) * (((((((a_prime_bit c 310 row) + (a_prime_bit c 630 row)) + (a_prime_bit c 950 row)) + (a_prime_bit c 1270 row)) + (a_prime_bit c 1590 row)) - (c_prime_bit c 310 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2900_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2900 c row ↔ constraint_2900 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2901 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 311 row) + (a_prime_bit c 631 row)) + (a_prime_bit c 951 row)) + (a_prime_bit c 1271 row)) + (a_prime_bit c 1591 row)) - (c_prime_bit c 311 row)) * (((((((a_prime_bit c 311 row) + (a_prime_bit c 631 row)) + (a_prime_bit c 951 row)) + (a_prime_bit c 1271 row)) + (a_prime_bit c 1591 row)) - (c_prime_bit c 311 row)) - 2)) * (((((((a_prime_bit c 311 row) + (a_prime_bit c 631 row)) + (a_prime_bit c 951 row)) + (a_prime_bit c 1271 row)) + (a_prime_bit c 1591 row)) - (c_prime_bit c 311 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2901_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2901 c row ↔ constraint_2901 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2902 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 312 row) + (a_prime_bit c 632 row)) + (a_prime_bit c 952 row)) + (a_prime_bit c 1272 row)) + (a_prime_bit c 1592 row)) - (c_prime_bit c 312 row)) * (((((((a_prime_bit c 312 row) + (a_prime_bit c 632 row)) + (a_prime_bit c 952 row)) + (a_prime_bit c 1272 row)) + (a_prime_bit c 1592 row)) - (c_prime_bit c 312 row)) - 2)) * (((((((a_prime_bit c 312 row) + (a_prime_bit c 632 row)) + (a_prime_bit c 952 row)) + (a_prime_bit c 1272 row)) + (a_prime_bit c 1592 row)) - (c_prime_bit c 312 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2902_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2902 c row ↔ constraint_2902 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2903 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 313 row) + (a_prime_bit c 633 row)) + (a_prime_bit c 953 row)) + (a_prime_bit c 1273 row)) + (a_prime_bit c 1593 row)) - (c_prime_bit c 313 row)) * (((((((a_prime_bit c 313 row) + (a_prime_bit c 633 row)) + (a_prime_bit c 953 row)) + (a_prime_bit c 1273 row)) + (a_prime_bit c 1593 row)) - (c_prime_bit c 313 row)) - 2)) * (((((((a_prime_bit c 313 row) + (a_prime_bit c 633 row)) + (a_prime_bit c 953 row)) + (a_prime_bit c 1273 row)) + (a_prime_bit c 1593 row)) - (c_prime_bit c 313 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2903_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2903 c row ↔ constraint_2903 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2904 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 314 row) + (a_prime_bit c 634 row)) + (a_prime_bit c 954 row)) + (a_prime_bit c 1274 row)) + (a_prime_bit c 1594 row)) - (c_prime_bit c 314 row)) * (((((((a_prime_bit c 314 row) + (a_prime_bit c 634 row)) + (a_prime_bit c 954 row)) + (a_prime_bit c 1274 row)) + (a_prime_bit c 1594 row)) - (c_prime_bit c 314 row)) - 2)) * (((((((a_prime_bit c 314 row) + (a_prime_bit c 634 row)) + (a_prime_bit c 954 row)) + (a_prime_bit c 1274 row)) + (a_prime_bit c 1594 row)) - (c_prime_bit c 314 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2904_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2904 c row ↔ constraint_2904 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2905 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 315 row) + (a_prime_bit c 635 row)) + (a_prime_bit c 955 row)) + (a_prime_bit c 1275 row)) + (a_prime_bit c 1595 row)) - (c_prime_bit c 315 row)) * (((((((a_prime_bit c 315 row) + (a_prime_bit c 635 row)) + (a_prime_bit c 955 row)) + (a_prime_bit c 1275 row)) + (a_prime_bit c 1595 row)) - (c_prime_bit c 315 row)) - 2)) * (((((((a_prime_bit c 315 row) + (a_prime_bit c 635 row)) + (a_prime_bit c 955 row)) + (a_prime_bit c 1275 row)) + (a_prime_bit c 1595 row)) - (c_prime_bit c 315 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2905_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2905 c row ↔ constraint_2905 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2906 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 316 row) + (a_prime_bit c 636 row)) + (a_prime_bit c 956 row)) + (a_prime_bit c 1276 row)) + (a_prime_bit c 1596 row)) - (c_prime_bit c 316 row)) * (((((((a_prime_bit c 316 row) + (a_prime_bit c 636 row)) + (a_prime_bit c 956 row)) + (a_prime_bit c 1276 row)) + (a_prime_bit c 1596 row)) - (c_prime_bit c 316 row)) - 2)) * (((((((a_prime_bit c 316 row) + (a_prime_bit c 636 row)) + (a_prime_bit c 956 row)) + (a_prime_bit c 1276 row)) + (a_prime_bit c 1596 row)) - (c_prime_bit c 316 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2906_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2906 c row ↔ constraint_2906 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2907 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 317 row) + (a_prime_bit c 637 row)) + (a_prime_bit c 957 row)) + (a_prime_bit c 1277 row)) + (a_prime_bit c 1597 row)) - (c_prime_bit c 317 row)) * (((((((a_prime_bit c 317 row) + (a_prime_bit c 637 row)) + (a_prime_bit c 957 row)) + (a_prime_bit c 1277 row)) + (a_prime_bit c 1597 row)) - (c_prime_bit c 317 row)) - 2)) * (((((((a_prime_bit c 317 row) + (a_prime_bit c 637 row)) + (a_prime_bit c 957 row)) + (a_prime_bit c 1277 row)) + (a_prime_bit c 1597 row)) - (c_prime_bit c 317 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2907_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2907 c row ↔ constraint_2907 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2908 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 318 row) + (a_prime_bit c 638 row)) + (a_prime_bit c 958 row)) + (a_prime_bit c 1278 row)) + (a_prime_bit c 1598 row)) - (c_prime_bit c 318 row)) * (((((((a_prime_bit c 318 row) + (a_prime_bit c 638 row)) + (a_prime_bit c 958 row)) + (a_prime_bit c 1278 row)) + (a_prime_bit c 1598 row)) - (c_prime_bit c 318 row)) - 2)) * (((((((a_prime_bit c 318 row) + (a_prime_bit c 638 row)) + (a_prime_bit c 958 row)) + (a_prime_bit c 1278 row)) + (a_prime_bit c 1598 row)) - (c_prime_bit c 318 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2908_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2908 c row ↔ constraint_2908 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2909 (c : C F ExtF) (row : ℕ) : Prop :=
    ((((((((a_prime_bit c 319 row) + (a_prime_bit c 639 row)) + (a_prime_bit c 959 row)) + (a_prime_bit c 1279 row)) + (a_prime_bit c 1599 row)) - (c_prime_bit c 319 row)) * (((((((a_prime_bit c 319 row) + (a_prime_bit c 639 row)) + (a_prime_bit c 959 row)) + (a_prime_bit c 1279 row)) + (a_prime_bit c 1599 row)) - (c_prime_bit c 319 row)) - 2)) * (((((((a_prime_bit c 319 row) + (a_prime_bit c 639 row)) + (a_prime_bit c 959 row)) + (a_prime_bit c 1279 row)) + (a_prime_bit c 1599 row)) - (c_prime_bit c 319 row)) - 4)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2909_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2909 c row ↔ constraint_2909 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
