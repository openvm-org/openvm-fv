import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## θ linking constraints: a → a_prime via c_prime -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2490 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1508 row) * ((a_prime_bit c 1508 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2490_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2490 c row ↔ constraint_2490 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2491 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1509 row) * ((a_prime_bit c 1509 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2491_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2491 c row ↔ constraint_2491 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2492 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1510 row) * ((a_prime_bit c 1510 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2492_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2492 c row ↔ constraint_2492 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2493 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1511 row) * ((a_prime_bit c 1511 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2493_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2493 c row ↔ constraint_2493 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2494 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1512 row) * ((a_prime_bit c 1512 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2494_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2494 c row ↔ constraint_2494 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2495 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1513 row) * ((a_prime_bit c 1513 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2495_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2495 c row ↔ constraint_2495 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2496 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1514 row) * ((a_prime_bit c 1514 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2496_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2496 c row ↔ constraint_2496 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2497 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1515 row) * ((a_prime_bit c 1515 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2497_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2497 c row ↔ constraint_2497 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2498 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1516 row) * ((a_prime_bit c 1516 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2498_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2498 c row ↔ constraint_2498 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2499 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1517 row) * ((a_prime_bit c 1517 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2499_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2499 c row ↔ constraint_2499 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2500 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1518 row) * ((a_prime_bit c 1518 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2500_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2500 c row ↔ constraint_2500 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2501 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1519 row) * ((a_prime_bit c 1519 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2501_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2501 c row ↔ constraint_2501 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2502 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1520 row) * ((a_prime_bit c 1520 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2502_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2502 c row ↔ constraint_2502 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2503 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1521 row) * ((a_prime_bit c 1521 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2503_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2503 c row ↔ constraint_2503 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2504 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1522 row) * ((a_prime_bit c 1522 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2504_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2504 c row ↔ constraint_2504 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2505 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1523 row) * ((a_prime_bit c 1523 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2505_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2505 c row ↔ constraint_2505 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2506 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1524 row) * ((a_prime_bit c 1524 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2506_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2506 c row ↔ constraint_2506 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2507 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1525 row) * ((a_prime_bit c 1525 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2507_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2507 c row ↔ constraint_2507 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2508 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1526 row) * ((a_prime_bit c 1526 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2508_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2508 c row ↔ constraint_2508 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2509 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1527 row) * ((a_prime_bit c 1527 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2509_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2509 c row ↔ constraint_2509 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2510 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1528 row) * ((a_prime_bit c 1528 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2510_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2510 c row ↔ constraint_2510 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2511 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1529 row) * ((a_prime_bit c 1529 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2511_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2511 c row ↔ constraint_2511 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2512 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1530 row) * ((a_prime_bit c 1530 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2512_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2512 c row ↔ constraint_2512 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2513 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1531 row) * ((a_prime_bit c 1531 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2513_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2513 c row ↔ constraint_2513 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2514 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1532 row) * ((a_prime_bit c 1532 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2514_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2514 c row ↔ constraint_2514 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2515 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1533 row) * ((a_prime_bit c 1533 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2515_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2515 c row ↔ constraint_2515 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2516 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1534 row) * ((a_prime_bit c 1534 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2516_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2516 c row ↔ constraint_2516 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2517 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1535 row) * ((a_prime_bit c 1535 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2517_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2517 c row ↔ constraint_2517 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2518 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 417 737 2337 217 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2518_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2518 c row ↔ constraint_2518 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2519 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 433 753 2353 218 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2519_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2519 c row ↔ constraint_2519 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2520 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 449 769 2369 219 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2520_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2520 c row ↔ constraint_2520 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2521 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 465 785 2385 220 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2521_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2521 c row ↔ constraint_2521 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2522 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1536 row) * ((a_prime_bit c 1536 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2522_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2522 c row ↔ constraint_2522 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2523 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1537 row) * ((a_prime_bit c 1537 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2523_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2523 c row ↔ constraint_2523 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2524 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1538 row) * ((a_prime_bit c 1538 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2524_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2524 c row ↔ constraint_2524 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2525 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1539 row) * ((a_prime_bit c 1539 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2525_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2525 c row ↔ constraint_2525 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2526 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1540 row) * ((a_prime_bit c 1540 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2526_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2526 c row ↔ constraint_2526 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2527 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1541 row) * ((a_prime_bit c 1541 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2527_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2527 c row ↔ constraint_2527 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2528 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1542 row) * ((a_prime_bit c 1542 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2528_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2528 c row ↔ constraint_2528 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2529 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1543 row) * ((a_prime_bit c 1543 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2529_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2529 c row ↔ constraint_2529 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2530 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1544 row) * ((a_prime_bit c 1544 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2530_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2530 c row ↔ constraint_2530 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2531 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1545 row) * ((a_prime_bit c 1545 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2531_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2531 c row ↔ constraint_2531 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2532 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1546 row) * ((a_prime_bit c 1546 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2532_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2532 c row ↔ constraint_2532 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2533 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1547 row) * ((a_prime_bit c 1547 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2533_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2533 c row ↔ constraint_2533 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2534 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1548 row) * ((a_prime_bit c 1548 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2534_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2534 c row ↔ constraint_2534 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2535 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1549 row) * ((a_prime_bit c 1549 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2535_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2535 c row ↔ constraint_2535 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2536 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1550 row) * ((a_prime_bit c 1550 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2536_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2536 c row ↔ constraint_2536 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2537 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1551 row) * ((a_prime_bit c 1551 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2537_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2537 c row ↔ constraint_2537 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2538 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1552 row) * ((a_prime_bit c 1552 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2538_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2538 c row ↔ constraint_2538 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2539 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1553 row) * ((a_prime_bit c 1553 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2539_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2539 c row ↔ constraint_2539 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2540 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1554 row) * ((a_prime_bit c 1554 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2540_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2540 c row ↔ constraint_2540 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2541 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1555 row) * ((a_prime_bit c 1555 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2541_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2541 c row ↔ constraint_2541 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2542 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1556 row) * ((a_prime_bit c 1556 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2542_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2542 c row ↔ constraint_2542 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2543 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1557 row) * ((a_prime_bit c 1557 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2543_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2543 c row ↔ constraint_2543 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2544 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1558 row) * ((a_prime_bit c 1558 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2544_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2544 c row ↔ constraint_2544 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2545 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1559 row) * ((a_prime_bit c 1559 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2545_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2545 c row ↔ constraint_2545 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2546 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1560 row) * ((a_prime_bit c 1560 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2546_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2546 c row ↔ constraint_2546 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2547 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1561 row) * ((a_prime_bit c 1561 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2547_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2547 c row ↔ constraint_2547 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2548 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1562 row) * ((a_prime_bit c 1562 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2548_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2548 c row ↔ constraint_2548 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2549 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1563 row) * ((a_prime_bit c 1563 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2549_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2549 c row ↔ constraint_2549 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2550 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1564 row) * ((a_prime_bit c 1564 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2550_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2550 c row ↔ constraint_2550 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2551 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1565 row) * ((a_prime_bit c 1565 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2551_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2551 c row ↔ constraint_2551 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2552 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1566 row) * ((a_prime_bit c 1566 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2552_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2552 c row ↔ constraint_2552 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2553 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1567 row) * ((a_prime_bit c 1567 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2553_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2553 c row ↔ constraint_2553 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2554 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1568 row) * ((a_prime_bit c 1568 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2554_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2554 c row ↔ constraint_2554 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2555 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1569 row) * ((a_prime_bit c 1569 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2555_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2555 c row ↔ constraint_2555 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2556 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1570 row) * ((a_prime_bit c 1570 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2556_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2556 c row ↔ constraint_2556 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2557 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1571 row) * ((a_prime_bit c 1571 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2557_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2557 c row ↔ constraint_2557 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2558 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1572 row) * ((a_prime_bit c 1572 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2558_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2558 c row ↔ constraint_2558 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2559 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1573 row) * ((a_prime_bit c 1573 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2559_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2559 c row ↔ constraint_2559 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2560 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1574 row) * ((a_prime_bit c 1574 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2560_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2560 c row ↔ constraint_2560 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2561 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1575 row) * ((a_prime_bit c 1575 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2561_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2561 c row ↔ constraint_2561 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2562 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1576 row) * ((a_prime_bit c 1576 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2562_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2562 c row ↔ constraint_2562 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2563 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1577 row) * ((a_prime_bit c 1577 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2563_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2563 c row ↔ constraint_2563 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2564 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1578 row) * ((a_prime_bit c 1578 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2564_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2564 c row ↔ constraint_2564 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2565 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1579 row) * ((a_prime_bit c 1579 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2565_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2565 c row ↔ constraint_2565 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2566 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1580 row) * ((a_prime_bit c 1580 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2566_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2566 c row ↔ constraint_2566 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2567 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1581 row) * ((a_prime_bit c 1581 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2567_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2567 c row ↔ constraint_2567 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2568 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1582 row) * ((a_prime_bit c 1582 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2568_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2568 c row ↔ constraint_2568 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2569 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1583 row) * ((a_prime_bit c 1583 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2569_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2569 c row ↔ constraint_2569 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2570 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1584 row) * ((a_prime_bit c 1584 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2570_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2570 c row ↔ constraint_2570 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2571 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1585 row) * ((a_prime_bit c 1585 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2571_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2571 c row ↔ constraint_2571 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2572 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1586 row) * ((a_prime_bit c 1586 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2572_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2572 c row ↔ constraint_2572 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2573 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1587 row) * ((a_prime_bit c 1587 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2573_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2573 c row ↔ constraint_2573 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2574 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1588 row) * ((a_prime_bit c 1588 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2574_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2574 c row ↔ constraint_2574 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2575 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1589 row) * ((a_prime_bit c 1589 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2575_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2575 c row ↔ constraint_2575 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2576 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1590 row) * ((a_prime_bit c 1590 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2576_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2576 c row ↔ constraint_2576 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2577 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1591 row) * ((a_prime_bit c 1591 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2577_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2577 c row ↔ constraint_2577 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2578 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1592 row) * ((a_prime_bit c 1592 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2578_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2578 c row ↔ constraint_2578 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2579 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1593 row) * ((a_prime_bit c 1593 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2579_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2579 c row ↔ constraint_2579 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2580 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1594 row) * ((a_prime_bit c 1594 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2580_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2580 c row ↔ constraint_2580 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2581 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1595 row) * ((a_prime_bit c 1595 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2581_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2581 c row ↔ constraint_2581 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2582 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1596 row) * ((a_prime_bit c 1596 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2582_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2582 c row ↔ constraint_2582 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2583 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1597 row) * ((a_prime_bit c 1597 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2583_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2583 c row ↔ constraint_2583 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2584 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1598 row) * ((a_prime_bit c 1598 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2584_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2584 c row ↔ constraint_2584 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2585 (c : C F ExtF) (row : ℕ) : Prop :=
    ((a_prime_bit c 1599 row) * ((a_prime_bit c 1599 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2585_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2585 c row ↔ constraint_2585 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2586 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 481 801 2401 221 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2586_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2586 c row ↔ constraint_2586 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2587 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 497 817 2417 222 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2587_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2587 c row ↔ constraint_2587 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2588 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 513 833 2433 223 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2588_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2588 c row ↔ constraint_2588 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_2589 (c : C F ExtF) (row : ℕ) : Prop :=
    KeccakfPermAir.extraction.xor3_recompose16_eq c 529 849 2449 224 row

  @[KeccakfPermAir_air_simplification]
  lemma constraint_2589_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_2589 c row ↔ constraint_2589 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
