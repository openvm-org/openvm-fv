import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## θ parity-prime computation constraints -/

section constraint_simplification
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_570 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 128 row) - (((((c_bit c 128 row) + (c_bit c 64 row)) - ((c_bit c 128 row) * ((c_bit c 64 row) + (c_bit c 64 row)))) + (c_bit c 255 row)) - ((((c_bit c 128 row) + (c_bit c 64 row)) - ((c_bit c 128 row) * ((c_bit c 64 row) + (c_bit c 64 row)))) * ((c_bit c 255 row) + (c_bit c 255 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_570_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_570 c row ↔ constraint_570 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_571 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 129 row) - (((((c_bit c 129 row) + (c_bit c 65 row)) - ((c_bit c 129 row) * ((c_bit c 65 row) + (c_bit c 65 row)))) + (c_bit c 192 row)) - ((((c_bit c 129 row) + (c_bit c 65 row)) - ((c_bit c 129 row) * ((c_bit c 65 row) + (c_bit c 65 row)))) * ((c_bit c 192 row) + (c_bit c 192 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_571_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_571 c row ↔ constraint_571 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_572 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 130 row) - (((((c_bit c 130 row) + (c_bit c 66 row)) - ((c_bit c 130 row) * ((c_bit c 66 row) + (c_bit c 66 row)))) + (c_bit c 193 row)) - ((((c_bit c 130 row) + (c_bit c 66 row)) - ((c_bit c 130 row) * ((c_bit c 66 row) + (c_bit c 66 row)))) * ((c_bit c 193 row) + (c_bit c 193 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_572_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_572 c row ↔ constraint_572 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_573 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 131 row) - (((((c_bit c 131 row) + (c_bit c 67 row)) - ((c_bit c 131 row) * ((c_bit c 67 row) + (c_bit c 67 row)))) + (c_bit c 194 row)) - ((((c_bit c 131 row) + (c_bit c 67 row)) - ((c_bit c 131 row) * ((c_bit c 67 row) + (c_bit c 67 row)))) * ((c_bit c 194 row) + (c_bit c 194 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_573_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_573 c row ↔ constraint_573 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_574 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 132 row) - (((((c_bit c 132 row) + (c_bit c 68 row)) - ((c_bit c 132 row) * ((c_bit c 68 row) + (c_bit c 68 row)))) + (c_bit c 195 row)) - ((((c_bit c 132 row) + (c_bit c 68 row)) - ((c_bit c 132 row) * ((c_bit c 68 row) + (c_bit c 68 row)))) * ((c_bit c 195 row) + (c_bit c 195 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_574_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_574 c row ↔ constraint_574 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_575 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 133 row) - (((((c_bit c 133 row) + (c_bit c 69 row)) - ((c_bit c 133 row) * ((c_bit c 69 row) + (c_bit c 69 row)))) + (c_bit c 196 row)) - ((((c_bit c 133 row) + (c_bit c 69 row)) - ((c_bit c 133 row) * ((c_bit c 69 row) + (c_bit c 69 row)))) * ((c_bit c 196 row) + (c_bit c 196 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_575_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_575 c row ↔ constraint_575 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_576 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 134 row) - (((((c_bit c 134 row) + (c_bit c 70 row)) - ((c_bit c 134 row) * ((c_bit c 70 row) + (c_bit c 70 row)))) + (c_bit c 197 row)) - ((((c_bit c 134 row) + (c_bit c 70 row)) - ((c_bit c 134 row) * ((c_bit c 70 row) + (c_bit c 70 row)))) * ((c_bit c 197 row) + (c_bit c 197 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_576_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_576 c row ↔ constraint_576 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_577 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 135 row) - (((((c_bit c 135 row) + (c_bit c 71 row)) - ((c_bit c 135 row) * ((c_bit c 71 row) + (c_bit c 71 row)))) + (c_bit c 198 row)) - ((((c_bit c 135 row) + (c_bit c 71 row)) - ((c_bit c 135 row) * ((c_bit c 71 row) + (c_bit c 71 row)))) * ((c_bit c 198 row) + (c_bit c 198 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_577_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_577 c row ↔ constraint_577 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_578 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 136 row) - (((((c_bit c 136 row) + (c_bit c 72 row)) - ((c_bit c 136 row) * ((c_bit c 72 row) + (c_bit c 72 row)))) + (c_bit c 199 row)) - ((((c_bit c 136 row) + (c_bit c 72 row)) - ((c_bit c 136 row) * ((c_bit c 72 row) + (c_bit c 72 row)))) * ((c_bit c 199 row) + (c_bit c 199 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_578_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_578 c row ↔ constraint_578 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_579 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 137 row) - (((((c_bit c 137 row) + (c_bit c 73 row)) - ((c_bit c 137 row) * ((c_bit c 73 row) + (c_bit c 73 row)))) + (c_bit c 200 row)) - ((((c_bit c 137 row) + (c_bit c 73 row)) - ((c_bit c 137 row) * ((c_bit c 73 row) + (c_bit c 73 row)))) * ((c_bit c 200 row) + (c_bit c 200 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_579_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_579 c row ↔ constraint_579 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_580 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 138 row) - (((((c_bit c 138 row) + (c_bit c 74 row)) - ((c_bit c 138 row) * ((c_bit c 74 row) + (c_bit c 74 row)))) + (c_bit c 201 row)) - ((((c_bit c 138 row) + (c_bit c 74 row)) - ((c_bit c 138 row) * ((c_bit c 74 row) + (c_bit c 74 row)))) * ((c_bit c 201 row) + (c_bit c 201 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_580_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_580 c row ↔ constraint_580 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_581 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 139 row) - (((((c_bit c 139 row) + (c_bit c 75 row)) - ((c_bit c 139 row) * ((c_bit c 75 row) + (c_bit c 75 row)))) + (c_bit c 202 row)) - ((((c_bit c 139 row) + (c_bit c 75 row)) - ((c_bit c 139 row) * ((c_bit c 75 row) + (c_bit c 75 row)))) * ((c_bit c 202 row) + (c_bit c 202 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_581_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_581 c row ↔ constraint_581 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_582 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 140 row) - (((((c_bit c 140 row) + (c_bit c 76 row)) - ((c_bit c 140 row) * ((c_bit c 76 row) + (c_bit c 76 row)))) + (c_bit c 203 row)) - ((((c_bit c 140 row) + (c_bit c 76 row)) - ((c_bit c 140 row) * ((c_bit c 76 row) + (c_bit c 76 row)))) * ((c_bit c 203 row) + (c_bit c 203 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_582_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_582 c row ↔ constraint_582 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_583 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 141 row) - (((((c_bit c 141 row) + (c_bit c 77 row)) - ((c_bit c 141 row) * ((c_bit c 77 row) + (c_bit c 77 row)))) + (c_bit c 204 row)) - ((((c_bit c 141 row) + (c_bit c 77 row)) - ((c_bit c 141 row) * ((c_bit c 77 row) + (c_bit c 77 row)))) * ((c_bit c 204 row) + (c_bit c 204 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_583_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_583 c row ↔ constraint_583 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_584 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 142 row) - (((((c_bit c 142 row) + (c_bit c 78 row)) - ((c_bit c 142 row) * ((c_bit c 78 row) + (c_bit c 78 row)))) + (c_bit c 205 row)) - ((((c_bit c 142 row) + (c_bit c 78 row)) - ((c_bit c 142 row) * ((c_bit c 78 row) + (c_bit c 78 row)))) * ((c_bit c 205 row) + (c_bit c 205 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_584_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_584 c row ↔ constraint_584 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_585 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 143 row) - (((((c_bit c 143 row) + (c_bit c 79 row)) - ((c_bit c 143 row) * ((c_bit c 79 row) + (c_bit c 79 row)))) + (c_bit c 206 row)) - ((((c_bit c 143 row) + (c_bit c 79 row)) - ((c_bit c 143 row) * ((c_bit c 79 row) + (c_bit c 79 row)))) * ((c_bit c 206 row) + (c_bit c 206 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_585_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_585 c row ↔ constraint_585 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_586 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 144 row) - (((((c_bit c 144 row) + (c_bit c 80 row)) - ((c_bit c 144 row) * ((c_bit c 80 row) + (c_bit c 80 row)))) + (c_bit c 207 row)) - ((((c_bit c 144 row) + (c_bit c 80 row)) - ((c_bit c 144 row) * ((c_bit c 80 row) + (c_bit c 80 row)))) * ((c_bit c 207 row) + (c_bit c 207 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_586_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_586 c row ↔ constraint_586 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_587 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 145 row) - (((((c_bit c 145 row) + (c_bit c 81 row)) - ((c_bit c 145 row) * ((c_bit c 81 row) + (c_bit c 81 row)))) + (c_bit c 208 row)) - ((((c_bit c 145 row) + (c_bit c 81 row)) - ((c_bit c 145 row) * ((c_bit c 81 row) + (c_bit c 81 row)))) * ((c_bit c 208 row) + (c_bit c 208 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_587_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_587 c row ↔ constraint_587 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_588 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 146 row) - (((((c_bit c 146 row) + (c_bit c 82 row)) - ((c_bit c 146 row) * ((c_bit c 82 row) + (c_bit c 82 row)))) + (c_bit c 209 row)) - ((((c_bit c 146 row) + (c_bit c 82 row)) - ((c_bit c 146 row) * ((c_bit c 82 row) + (c_bit c 82 row)))) * ((c_bit c 209 row) + (c_bit c 209 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_588_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_588 c row ↔ constraint_588 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_589 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 147 row) - (((((c_bit c 147 row) + (c_bit c 83 row)) - ((c_bit c 147 row) * ((c_bit c 83 row) + (c_bit c 83 row)))) + (c_bit c 210 row)) - ((((c_bit c 147 row) + (c_bit c 83 row)) - ((c_bit c 147 row) * ((c_bit c 83 row) + (c_bit c 83 row)))) * ((c_bit c 210 row) + (c_bit c 210 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_589_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_589 c row ↔ constraint_589 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_590 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 148 row) - (((((c_bit c 148 row) + (c_bit c 84 row)) - ((c_bit c 148 row) * ((c_bit c 84 row) + (c_bit c 84 row)))) + (c_bit c 211 row)) - ((((c_bit c 148 row) + (c_bit c 84 row)) - ((c_bit c 148 row) * ((c_bit c 84 row) + (c_bit c 84 row)))) * ((c_bit c 211 row) + (c_bit c 211 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_590_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_590 c row ↔ constraint_590 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_591 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 149 row) - (((((c_bit c 149 row) + (c_bit c 85 row)) - ((c_bit c 149 row) * ((c_bit c 85 row) + (c_bit c 85 row)))) + (c_bit c 212 row)) - ((((c_bit c 149 row) + (c_bit c 85 row)) - ((c_bit c 149 row) * ((c_bit c 85 row) + (c_bit c 85 row)))) * ((c_bit c 212 row) + (c_bit c 212 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_591_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_591 c row ↔ constraint_591 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_592 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 150 row) - (((((c_bit c 150 row) + (c_bit c 86 row)) - ((c_bit c 150 row) * ((c_bit c 86 row) + (c_bit c 86 row)))) + (c_bit c 213 row)) - ((((c_bit c 150 row) + (c_bit c 86 row)) - ((c_bit c 150 row) * ((c_bit c 86 row) + (c_bit c 86 row)))) * ((c_bit c 213 row) + (c_bit c 213 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_592_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_592 c row ↔ constraint_592 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_593 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 151 row) - (((((c_bit c 151 row) + (c_bit c 87 row)) - ((c_bit c 151 row) * ((c_bit c 87 row) + (c_bit c 87 row)))) + (c_bit c 214 row)) - ((((c_bit c 151 row) + (c_bit c 87 row)) - ((c_bit c 151 row) * ((c_bit c 87 row) + (c_bit c 87 row)))) * ((c_bit c 214 row) + (c_bit c 214 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_593_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_593 c row ↔ constraint_593 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_594 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 152 row) - (((((c_bit c 152 row) + (c_bit c 88 row)) - ((c_bit c 152 row) * ((c_bit c 88 row) + (c_bit c 88 row)))) + (c_bit c 215 row)) - ((((c_bit c 152 row) + (c_bit c 88 row)) - ((c_bit c 152 row) * ((c_bit c 88 row) + (c_bit c 88 row)))) * ((c_bit c 215 row) + (c_bit c 215 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_594_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_594 c row ↔ constraint_594 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_595 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 153 row) - (((((c_bit c 153 row) + (c_bit c 89 row)) - ((c_bit c 153 row) * ((c_bit c 89 row) + (c_bit c 89 row)))) + (c_bit c 216 row)) - ((((c_bit c 153 row) + (c_bit c 89 row)) - ((c_bit c 153 row) * ((c_bit c 89 row) + (c_bit c 89 row)))) * ((c_bit c 216 row) + (c_bit c 216 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_595_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_595 c row ↔ constraint_595 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_596 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 154 row) - (((((c_bit c 154 row) + (c_bit c 90 row)) - ((c_bit c 154 row) * ((c_bit c 90 row) + (c_bit c 90 row)))) + (c_bit c 217 row)) - ((((c_bit c 154 row) + (c_bit c 90 row)) - ((c_bit c 154 row) * ((c_bit c 90 row) + (c_bit c 90 row)))) * ((c_bit c 217 row) + (c_bit c 217 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_596_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_596 c row ↔ constraint_596 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_597 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 155 row) - (((((c_bit c 155 row) + (c_bit c 91 row)) - ((c_bit c 155 row) * ((c_bit c 91 row) + (c_bit c 91 row)))) + (c_bit c 218 row)) - ((((c_bit c 155 row) + (c_bit c 91 row)) - ((c_bit c 155 row) * ((c_bit c 91 row) + (c_bit c 91 row)))) * ((c_bit c 218 row) + (c_bit c 218 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_597_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_597 c row ↔ constraint_597 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_598 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 156 row) - (((((c_bit c 156 row) + (c_bit c 92 row)) - ((c_bit c 156 row) * ((c_bit c 92 row) + (c_bit c 92 row)))) + (c_bit c 219 row)) - ((((c_bit c 156 row) + (c_bit c 92 row)) - ((c_bit c 156 row) * ((c_bit c 92 row) + (c_bit c 92 row)))) * ((c_bit c 219 row) + (c_bit c 219 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_598_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_598 c row ↔ constraint_598 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_599 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 157 row) - (((((c_bit c 157 row) + (c_bit c 93 row)) - ((c_bit c 157 row) * ((c_bit c 93 row) + (c_bit c 93 row)))) + (c_bit c 220 row)) - ((((c_bit c 157 row) + (c_bit c 93 row)) - ((c_bit c 157 row) * ((c_bit c 93 row) + (c_bit c 93 row)))) * ((c_bit c 220 row) + (c_bit c 220 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_599_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_599 c row ↔ constraint_599 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_600 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 158 row) - (((((c_bit c 158 row) + (c_bit c 94 row)) - ((c_bit c 158 row) * ((c_bit c 94 row) + (c_bit c 94 row)))) + (c_bit c 221 row)) - ((((c_bit c 158 row) + (c_bit c 94 row)) - ((c_bit c 158 row) * ((c_bit c 94 row) + (c_bit c 94 row)))) * ((c_bit c 221 row) + (c_bit c 221 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_600_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_600 c row ↔ constraint_600 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_601 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 159 row) - (((((c_bit c 159 row) + (c_bit c 95 row)) - ((c_bit c 159 row) * ((c_bit c 95 row) + (c_bit c 95 row)))) + (c_bit c 222 row)) - ((((c_bit c 159 row) + (c_bit c 95 row)) - ((c_bit c 159 row) * ((c_bit c 95 row) + (c_bit c 95 row)))) * ((c_bit c 222 row) + (c_bit c 222 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_601_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_601 c row ↔ constraint_601 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_602 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 160 row) - (((((c_bit c 160 row) + (c_bit c 96 row)) - ((c_bit c 160 row) * ((c_bit c 96 row) + (c_bit c 96 row)))) + (c_bit c 223 row)) - ((((c_bit c 160 row) + (c_bit c 96 row)) - ((c_bit c 160 row) * ((c_bit c 96 row) + (c_bit c 96 row)))) * ((c_bit c 223 row) + (c_bit c 223 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_602_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_602 c row ↔ constraint_602 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_603 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 161 row) - (((((c_bit c 161 row) + (c_bit c 97 row)) - ((c_bit c 161 row) * ((c_bit c 97 row) + (c_bit c 97 row)))) + (c_bit c 224 row)) - ((((c_bit c 161 row) + (c_bit c 97 row)) - ((c_bit c 161 row) * ((c_bit c 97 row) + (c_bit c 97 row)))) * ((c_bit c 224 row) + (c_bit c 224 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_603_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_603 c row ↔ constraint_603 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_604 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 162 row) - (((((c_bit c 162 row) + (c_bit c 98 row)) - ((c_bit c 162 row) * ((c_bit c 98 row) + (c_bit c 98 row)))) + (c_bit c 225 row)) - ((((c_bit c 162 row) + (c_bit c 98 row)) - ((c_bit c 162 row) * ((c_bit c 98 row) + (c_bit c 98 row)))) * ((c_bit c 225 row) + (c_bit c 225 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_604_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_604 c row ↔ constraint_604 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_605 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 163 row) - (((((c_bit c 163 row) + (c_bit c 99 row)) - ((c_bit c 163 row) * ((c_bit c 99 row) + (c_bit c 99 row)))) + (c_bit c 226 row)) - ((((c_bit c 163 row) + (c_bit c 99 row)) - ((c_bit c 163 row) * ((c_bit c 99 row) + (c_bit c 99 row)))) * ((c_bit c 226 row) + (c_bit c 226 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_605_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_605 c row ↔ constraint_605 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_606 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 164 row) - (((((c_bit c 164 row) + (c_bit c 100 row)) - ((c_bit c 164 row) * ((c_bit c 100 row) + (c_bit c 100 row)))) + (c_bit c 227 row)) - ((((c_bit c 164 row) + (c_bit c 100 row)) - ((c_bit c 164 row) * ((c_bit c 100 row) + (c_bit c 100 row)))) * ((c_bit c 227 row) + (c_bit c 227 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_606_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_606 c row ↔ constraint_606 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_607 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 165 row) - (((((c_bit c 165 row) + (c_bit c 101 row)) - ((c_bit c 165 row) * ((c_bit c 101 row) + (c_bit c 101 row)))) + (c_bit c 228 row)) - ((((c_bit c 165 row) + (c_bit c 101 row)) - ((c_bit c 165 row) * ((c_bit c 101 row) + (c_bit c 101 row)))) * ((c_bit c 228 row) + (c_bit c 228 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_607_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_607 c row ↔ constraint_607 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_608 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 166 row) - (((((c_bit c 166 row) + (c_bit c 102 row)) - ((c_bit c 166 row) * ((c_bit c 102 row) + (c_bit c 102 row)))) + (c_bit c 229 row)) - ((((c_bit c 166 row) + (c_bit c 102 row)) - ((c_bit c 166 row) * ((c_bit c 102 row) + (c_bit c 102 row)))) * ((c_bit c 229 row) + (c_bit c 229 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_608_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_608 c row ↔ constraint_608 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_609 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 167 row) - (((((c_bit c 167 row) + (c_bit c 103 row)) - ((c_bit c 167 row) * ((c_bit c 103 row) + (c_bit c 103 row)))) + (c_bit c 230 row)) - ((((c_bit c 167 row) + (c_bit c 103 row)) - ((c_bit c 167 row) * ((c_bit c 103 row) + (c_bit c 103 row)))) * ((c_bit c 230 row) + (c_bit c 230 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_609_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_609 c row ↔ constraint_609 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_610 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 168 row) - (((((c_bit c 168 row) + (c_bit c 104 row)) - ((c_bit c 168 row) * ((c_bit c 104 row) + (c_bit c 104 row)))) + (c_bit c 231 row)) - ((((c_bit c 168 row) + (c_bit c 104 row)) - ((c_bit c 168 row) * ((c_bit c 104 row) + (c_bit c 104 row)))) * ((c_bit c 231 row) + (c_bit c 231 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_610_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_610 c row ↔ constraint_610 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_611 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 169 row) - (((((c_bit c 169 row) + (c_bit c 105 row)) - ((c_bit c 169 row) * ((c_bit c 105 row) + (c_bit c 105 row)))) + (c_bit c 232 row)) - ((((c_bit c 169 row) + (c_bit c 105 row)) - ((c_bit c 169 row) * ((c_bit c 105 row) + (c_bit c 105 row)))) * ((c_bit c 232 row) + (c_bit c 232 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_611_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_611 c row ↔ constraint_611 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_612 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 170 row) - (((((c_bit c 170 row) + (c_bit c 106 row)) - ((c_bit c 170 row) * ((c_bit c 106 row) + (c_bit c 106 row)))) + (c_bit c 233 row)) - ((((c_bit c 170 row) + (c_bit c 106 row)) - ((c_bit c 170 row) * ((c_bit c 106 row) + (c_bit c 106 row)))) * ((c_bit c 233 row) + (c_bit c 233 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_612_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_612 c row ↔ constraint_612 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_613 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 171 row) - (((((c_bit c 171 row) + (c_bit c 107 row)) - ((c_bit c 171 row) * ((c_bit c 107 row) + (c_bit c 107 row)))) + (c_bit c 234 row)) - ((((c_bit c 171 row) + (c_bit c 107 row)) - ((c_bit c 171 row) * ((c_bit c 107 row) + (c_bit c 107 row)))) * ((c_bit c 234 row) + (c_bit c 234 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_613_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_613 c row ↔ constraint_613 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_614 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 172 row) - (((((c_bit c 172 row) + (c_bit c 108 row)) - ((c_bit c 172 row) * ((c_bit c 108 row) + (c_bit c 108 row)))) + (c_bit c 235 row)) - ((((c_bit c 172 row) + (c_bit c 108 row)) - ((c_bit c 172 row) * ((c_bit c 108 row) + (c_bit c 108 row)))) * ((c_bit c 235 row) + (c_bit c 235 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_614_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_614 c row ↔ constraint_614 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_615 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 173 row) - (((((c_bit c 173 row) + (c_bit c 109 row)) - ((c_bit c 173 row) * ((c_bit c 109 row) + (c_bit c 109 row)))) + (c_bit c 236 row)) - ((((c_bit c 173 row) + (c_bit c 109 row)) - ((c_bit c 173 row) * ((c_bit c 109 row) + (c_bit c 109 row)))) * ((c_bit c 236 row) + (c_bit c 236 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_615_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_615 c row ↔ constraint_615 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_616 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 174 row) - (((((c_bit c 174 row) + (c_bit c 110 row)) - ((c_bit c 174 row) * ((c_bit c 110 row) + (c_bit c 110 row)))) + (c_bit c 237 row)) - ((((c_bit c 174 row) + (c_bit c 110 row)) - ((c_bit c 174 row) * ((c_bit c 110 row) + (c_bit c 110 row)))) * ((c_bit c 237 row) + (c_bit c 237 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_616_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_616 c row ↔ constraint_616 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_617 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 175 row) - (((((c_bit c 175 row) + (c_bit c 111 row)) - ((c_bit c 175 row) * ((c_bit c 111 row) + (c_bit c 111 row)))) + (c_bit c 238 row)) - ((((c_bit c 175 row) + (c_bit c 111 row)) - ((c_bit c 175 row) * ((c_bit c 111 row) + (c_bit c 111 row)))) * ((c_bit c 238 row) + (c_bit c 238 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_617_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_617 c row ↔ constraint_617 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_618 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 176 row) - (((((c_bit c 176 row) + (c_bit c 112 row)) - ((c_bit c 176 row) * ((c_bit c 112 row) + (c_bit c 112 row)))) + (c_bit c 239 row)) - ((((c_bit c 176 row) + (c_bit c 112 row)) - ((c_bit c 176 row) * ((c_bit c 112 row) + (c_bit c 112 row)))) * ((c_bit c 239 row) + (c_bit c 239 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_618_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_618 c row ↔ constraint_618 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_619 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 177 row) - (((((c_bit c 177 row) + (c_bit c 113 row)) - ((c_bit c 177 row) * ((c_bit c 113 row) + (c_bit c 113 row)))) + (c_bit c 240 row)) - ((((c_bit c 177 row) + (c_bit c 113 row)) - ((c_bit c 177 row) * ((c_bit c 113 row) + (c_bit c 113 row)))) * ((c_bit c 240 row) + (c_bit c 240 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_619_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_619 c row ↔ constraint_619 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_620 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 178 row) - (((((c_bit c 178 row) + (c_bit c 114 row)) - ((c_bit c 178 row) * ((c_bit c 114 row) + (c_bit c 114 row)))) + (c_bit c 241 row)) - ((((c_bit c 178 row) + (c_bit c 114 row)) - ((c_bit c 178 row) * ((c_bit c 114 row) + (c_bit c 114 row)))) * ((c_bit c 241 row) + (c_bit c 241 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_620_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_620 c row ↔ constraint_620 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_621 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 179 row) - (((((c_bit c 179 row) + (c_bit c 115 row)) - ((c_bit c 179 row) * ((c_bit c 115 row) + (c_bit c 115 row)))) + (c_bit c 242 row)) - ((((c_bit c 179 row) + (c_bit c 115 row)) - ((c_bit c 179 row) * ((c_bit c 115 row) + (c_bit c 115 row)))) * ((c_bit c 242 row) + (c_bit c 242 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_621_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_621 c row ↔ constraint_621 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_622 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 180 row) - (((((c_bit c 180 row) + (c_bit c 116 row)) - ((c_bit c 180 row) * ((c_bit c 116 row) + (c_bit c 116 row)))) + (c_bit c 243 row)) - ((((c_bit c 180 row) + (c_bit c 116 row)) - ((c_bit c 180 row) * ((c_bit c 116 row) + (c_bit c 116 row)))) * ((c_bit c 243 row) + (c_bit c 243 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_622_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_622 c row ↔ constraint_622 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_623 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 181 row) - (((((c_bit c 181 row) + (c_bit c 117 row)) - ((c_bit c 181 row) * ((c_bit c 117 row) + (c_bit c 117 row)))) + (c_bit c 244 row)) - ((((c_bit c 181 row) + (c_bit c 117 row)) - ((c_bit c 181 row) * ((c_bit c 117 row) + (c_bit c 117 row)))) * ((c_bit c 244 row) + (c_bit c 244 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_623_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_623 c row ↔ constraint_623 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_624 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 182 row) - (((((c_bit c 182 row) + (c_bit c 118 row)) - ((c_bit c 182 row) * ((c_bit c 118 row) + (c_bit c 118 row)))) + (c_bit c 245 row)) - ((((c_bit c 182 row) + (c_bit c 118 row)) - ((c_bit c 182 row) * ((c_bit c 118 row) + (c_bit c 118 row)))) * ((c_bit c 245 row) + (c_bit c 245 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_624_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_624 c row ↔ constraint_624 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_625 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 183 row) - (((((c_bit c 183 row) + (c_bit c 119 row)) - ((c_bit c 183 row) * ((c_bit c 119 row) + (c_bit c 119 row)))) + (c_bit c 246 row)) - ((((c_bit c 183 row) + (c_bit c 119 row)) - ((c_bit c 183 row) * ((c_bit c 119 row) + (c_bit c 119 row)))) * ((c_bit c 246 row) + (c_bit c 246 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_625_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_625 c row ↔ constraint_625 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_626 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 184 row) - (((((c_bit c 184 row) + (c_bit c 120 row)) - ((c_bit c 184 row) * ((c_bit c 120 row) + (c_bit c 120 row)))) + (c_bit c 247 row)) - ((((c_bit c 184 row) + (c_bit c 120 row)) - ((c_bit c 184 row) * ((c_bit c 120 row) + (c_bit c 120 row)))) * ((c_bit c 247 row) + (c_bit c 247 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_626_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_626 c row ↔ constraint_626 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_627 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 185 row) - (((((c_bit c 185 row) + (c_bit c 121 row)) - ((c_bit c 185 row) * ((c_bit c 121 row) + (c_bit c 121 row)))) + (c_bit c 248 row)) - ((((c_bit c 185 row) + (c_bit c 121 row)) - ((c_bit c 185 row) * ((c_bit c 121 row) + (c_bit c 121 row)))) * ((c_bit c 248 row) + (c_bit c 248 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_627_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_627 c row ↔ constraint_627 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_628 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 186 row) - (((((c_bit c 186 row) + (c_bit c 122 row)) - ((c_bit c 186 row) * ((c_bit c 122 row) + (c_bit c 122 row)))) + (c_bit c 249 row)) - ((((c_bit c 186 row) + (c_bit c 122 row)) - ((c_bit c 186 row) * ((c_bit c 122 row) + (c_bit c 122 row)))) * ((c_bit c 249 row) + (c_bit c 249 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_628_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_628 c row ↔ constraint_628 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_629 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 187 row) - (((((c_bit c 187 row) + (c_bit c 123 row)) - ((c_bit c 187 row) * ((c_bit c 123 row) + (c_bit c 123 row)))) + (c_bit c 250 row)) - ((((c_bit c 187 row) + (c_bit c 123 row)) - ((c_bit c 187 row) * ((c_bit c 123 row) + (c_bit c 123 row)))) * ((c_bit c 250 row) + (c_bit c 250 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_629_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_629 c row ↔ constraint_629 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_630 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 188 row) - (((((c_bit c 188 row) + (c_bit c 124 row)) - ((c_bit c 188 row) * ((c_bit c 124 row) + (c_bit c 124 row)))) + (c_bit c 251 row)) - ((((c_bit c 188 row) + (c_bit c 124 row)) - ((c_bit c 188 row) * ((c_bit c 124 row) + (c_bit c 124 row)))) * ((c_bit c 251 row) + (c_bit c 251 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_630_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_630 c row ↔ constraint_630 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_631 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 189 row) - (((((c_bit c 189 row) + (c_bit c 125 row)) - ((c_bit c 189 row) * ((c_bit c 125 row) + (c_bit c 125 row)))) + (c_bit c 252 row)) - ((((c_bit c 189 row) + (c_bit c 125 row)) - ((c_bit c 189 row) * ((c_bit c 125 row) + (c_bit c 125 row)))) * ((c_bit c 252 row) + (c_bit c 252 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_631_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_631 c row ↔ constraint_631 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_632 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 190 row) - (((((c_bit c 190 row) + (c_bit c 126 row)) - ((c_bit c 190 row) * ((c_bit c 126 row) + (c_bit c 126 row)))) + (c_bit c 253 row)) - ((((c_bit c 190 row) + (c_bit c 126 row)) - ((c_bit c 190 row) * ((c_bit c 126 row) + (c_bit c 126 row)))) * ((c_bit c 253 row) + (c_bit c 253 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_632_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_632 c row ↔ constraint_632 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_633 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 191 row) - (((((c_bit c 191 row) + (c_bit c 127 row)) - ((c_bit c 191 row) * ((c_bit c 127 row) + (c_bit c 127 row)))) + (c_bit c 254 row)) - ((((c_bit c 191 row) + (c_bit c 127 row)) - ((c_bit c 191 row) * ((c_bit c 127 row) + (c_bit c 127 row)))) * ((c_bit c 254 row) + (c_bit c 254 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_633_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_633 c row ↔ constraint_633 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_634 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 192 row) * ((c_bit c 192 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_634_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_634 c row ↔ constraint_634 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_635 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 193 row) * ((c_bit c 193 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_635_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_635 c row ↔ constraint_635 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_636 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 194 row) * ((c_bit c 194 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_636_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_636 c row ↔ constraint_636 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_637 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 195 row) * ((c_bit c 195 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_637_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_637 c row ↔ constraint_637 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_638 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 196 row) * ((c_bit c 196 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_638_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_638 c row ↔ constraint_638 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_639 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 197 row) * ((c_bit c 197 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_639_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_639 c row ↔ constraint_639 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_640 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 198 row) * ((c_bit c 198 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_640_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_640 c row ↔ constraint_640 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_641 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 199 row) * ((c_bit c 199 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_641_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_641 c row ↔ constraint_641 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_642 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 200 row) * ((c_bit c 200 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_642_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_642 c row ↔ constraint_642 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_643 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 201 row) * ((c_bit c 201 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_643_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_643 c row ↔ constraint_643 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_644 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 202 row) * ((c_bit c 202 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_644_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_644 c row ↔ constraint_644 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_645 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 203 row) * ((c_bit c 203 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_645_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_645 c row ↔ constraint_645 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_646 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 204 row) * ((c_bit c 204 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_646_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_646 c row ↔ constraint_646 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_647 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 205 row) * ((c_bit c 205 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_647_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_647 c row ↔ constraint_647 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_648 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 206 row) * ((c_bit c 206 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_648_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_648 c row ↔ constraint_648 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_649 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 207 row) * ((c_bit c 207 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_649_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_649 c row ↔ constraint_649 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_650 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 208 row) * ((c_bit c 208 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_650_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_650 c row ↔ constraint_650 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_651 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 209 row) * ((c_bit c 209 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_651_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_651 c row ↔ constraint_651 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_652 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 210 row) * ((c_bit c 210 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_652_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_652 c row ↔ constraint_652 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_653 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 211 row) * ((c_bit c 211 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_653_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_653 c row ↔ constraint_653 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_654 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 212 row) * ((c_bit c 212 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_654_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_654 c row ↔ constraint_654 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_655 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 213 row) * ((c_bit c 213 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_655_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_655 c row ↔ constraint_655 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_656 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 214 row) * ((c_bit c 214 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_656_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_656 c row ↔ constraint_656 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_657 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 215 row) * ((c_bit c 215 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_657_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_657 c row ↔ constraint_657 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_658 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 216 row) * ((c_bit c 216 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_658_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_658 c row ↔ constraint_658 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_659 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 217 row) * ((c_bit c 217 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_659_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_659 c row ↔ constraint_659 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_660 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 218 row) * ((c_bit c 218 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_660_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_660 c row ↔ constraint_660 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_661 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 219 row) * ((c_bit c 219 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_661_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_661 c row ↔ constraint_661 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_662 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 220 row) * ((c_bit c 220 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_662_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_662 c row ↔ constraint_662 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_663 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 221 row) * ((c_bit c 221 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_663_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_663 c row ↔ constraint_663 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_664 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 222 row) * ((c_bit c 222 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_664_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_664 c row ↔ constraint_664 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_665 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 223 row) * ((c_bit c 223 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_665_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_665 c row ↔ constraint_665 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_666 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 224 row) * ((c_bit c 224 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_666_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_666 c row ↔ constraint_666 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_667 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 225 row) * ((c_bit c 225 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_667_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_667 c row ↔ constraint_667 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_668 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 226 row) * ((c_bit c 226 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_668_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_668 c row ↔ constraint_668 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_669 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 227 row) * ((c_bit c 227 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_669_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_669 c row ↔ constraint_669 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_670 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 228 row) * ((c_bit c 228 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_670_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_670 c row ↔ constraint_670 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_671 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 229 row) * ((c_bit c 229 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_671_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_671 c row ↔ constraint_671 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_672 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 230 row) * ((c_bit c 230 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_672_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_672 c row ↔ constraint_672 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_673 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 231 row) * ((c_bit c 231 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_673_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_673 c row ↔ constraint_673 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_674 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 232 row) * ((c_bit c 232 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_674_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_674 c row ↔ constraint_674 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_675 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 233 row) * ((c_bit c 233 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_675_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_675 c row ↔ constraint_675 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_676 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 234 row) * ((c_bit c 234 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_676_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_676 c row ↔ constraint_676 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_677 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 235 row) * ((c_bit c 235 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_677_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_677 c row ↔ constraint_677 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_678 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 236 row) * ((c_bit c 236 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_678_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_678 c row ↔ constraint_678 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_679 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 237 row) * ((c_bit c 237 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_679_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_679 c row ↔ constraint_679 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_680 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 238 row) * ((c_bit c 238 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_680_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_680 c row ↔ constraint_680 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_681 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 239 row) * ((c_bit c 239 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_681_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_681 c row ↔ constraint_681 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_682 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 240 row) * ((c_bit c 240 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_682_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_682 c row ↔ constraint_682 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_683 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 241 row) * ((c_bit c 241 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_683_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_683 c row ↔ constraint_683 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_684 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 242 row) * ((c_bit c 242 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_684_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_684 c row ↔ constraint_684 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_685 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 243 row) * ((c_bit c 243 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_685_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_685 c row ↔ constraint_685 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_686 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 244 row) * ((c_bit c 244 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_686_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_686 c row ↔ constraint_686 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_687 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 245 row) * ((c_bit c 245 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_687_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_687 c row ↔ constraint_687 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_688 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 246 row) * ((c_bit c 246 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_688_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_688 c row ↔ constraint_688 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_689 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 247 row) * ((c_bit c 247 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_689_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_689 c row ↔ constraint_689 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_690 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 248 row) * ((c_bit c 248 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_690_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_690 c row ↔ constraint_690 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_691 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 249 row) * ((c_bit c 249 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_691_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_691 c row ↔ constraint_691 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_692 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 250 row) * ((c_bit c 250 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_692_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_692 c row ↔ constraint_692 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_693 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 251 row) * ((c_bit c 251 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_693_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_693 c row ↔ constraint_693 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_694 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 252 row) * ((c_bit c 252 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_694_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_694 c row ↔ constraint_694 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_695 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 253 row) * ((c_bit c 253 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_695_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_695 c row ↔ constraint_695 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_696 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 254 row) * ((c_bit c 254 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_696_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_696 c row ↔ constraint_696 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_697 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 255 row) * ((c_bit c 255 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_697_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_697 c row ↔ constraint_697 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_698 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 192 row) - (((((c_bit c 192 row) + (c_bit c 128 row)) - ((c_bit c 192 row) * ((c_bit c 128 row) + (c_bit c 128 row)))) + (c_bit c 319 row)) - ((((c_bit c 192 row) + (c_bit c 128 row)) - ((c_bit c 192 row) * ((c_bit c 128 row) + (c_bit c 128 row)))) * ((c_bit c 319 row) + (c_bit c 319 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_698_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_698 c row ↔ constraint_698 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_699 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 193 row) - (((((c_bit c 193 row) + (c_bit c 129 row)) - ((c_bit c 193 row) * ((c_bit c 129 row) + (c_bit c 129 row)))) + (c_bit c 256 row)) - ((((c_bit c 193 row) + (c_bit c 129 row)) - ((c_bit c 193 row) * ((c_bit c 129 row) + (c_bit c 129 row)))) * ((c_bit c 256 row) + (c_bit c 256 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_699_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_699 c row ↔ constraint_699 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_700 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 194 row) - (((((c_bit c 194 row) + (c_bit c 130 row)) - ((c_bit c 194 row) * ((c_bit c 130 row) + (c_bit c 130 row)))) + (c_bit c 257 row)) - ((((c_bit c 194 row) + (c_bit c 130 row)) - ((c_bit c 194 row) * ((c_bit c 130 row) + (c_bit c 130 row)))) * ((c_bit c 257 row) + (c_bit c 257 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_700_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_700 c row ↔ constraint_700 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_701 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 195 row) - (((((c_bit c 195 row) + (c_bit c 131 row)) - ((c_bit c 195 row) * ((c_bit c 131 row) + (c_bit c 131 row)))) + (c_bit c 258 row)) - ((((c_bit c 195 row) + (c_bit c 131 row)) - ((c_bit c 195 row) * ((c_bit c 131 row) + (c_bit c 131 row)))) * ((c_bit c 258 row) + (c_bit c 258 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_701_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_701 c row ↔ constraint_701 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_702 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 196 row) - (((((c_bit c 196 row) + (c_bit c 132 row)) - ((c_bit c 196 row) * ((c_bit c 132 row) + (c_bit c 132 row)))) + (c_bit c 259 row)) - ((((c_bit c 196 row) + (c_bit c 132 row)) - ((c_bit c 196 row) * ((c_bit c 132 row) + (c_bit c 132 row)))) * ((c_bit c 259 row) + (c_bit c 259 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_702_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_702 c row ↔ constraint_702 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_703 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 197 row) - (((((c_bit c 197 row) + (c_bit c 133 row)) - ((c_bit c 197 row) * ((c_bit c 133 row) + (c_bit c 133 row)))) + (c_bit c 260 row)) - ((((c_bit c 197 row) + (c_bit c 133 row)) - ((c_bit c 197 row) * ((c_bit c 133 row) + (c_bit c 133 row)))) * ((c_bit c 260 row) + (c_bit c 260 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_703_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_703 c row ↔ constraint_703 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_704 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 198 row) - (((((c_bit c 198 row) + (c_bit c 134 row)) - ((c_bit c 198 row) * ((c_bit c 134 row) + (c_bit c 134 row)))) + (c_bit c 261 row)) - ((((c_bit c 198 row) + (c_bit c 134 row)) - ((c_bit c 198 row) * ((c_bit c 134 row) + (c_bit c 134 row)))) * ((c_bit c 261 row) + (c_bit c 261 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_704_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_704 c row ↔ constraint_704 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_705 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 199 row) - (((((c_bit c 199 row) + (c_bit c 135 row)) - ((c_bit c 199 row) * ((c_bit c 135 row) + (c_bit c 135 row)))) + (c_bit c 262 row)) - ((((c_bit c 199 row) + (c_bit c 135 row)) - ((c_bit c 199 row) * ((c_bit c 135 row) + (c_bit c 135 row)))) * ((c_bit c 262 row) + (c_bit c 262 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_705_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_705 c row ↔ constraint_705 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_706 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 200 row) - (((((c_bit c 200 row) + (c_bit c 136 row)) - ((c_bit c 200 row) * ((c_bit c 136 row) + (c_bit c 136 row)))) + (c_bit c 263 row)) - ((((c_bit c 200 row) + (c_bit c 136 row)) - ((c_bit c 200 row) * ((c_bit c 136 row) + (c_bit c 136 row)))) * ((c_bit c 263 row) + (c_bit c 263 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_706_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_706 c row ↔ constraint_706 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_707 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 201 row) - (((((c_bit c 201 row) + (c_bit c 137 row)) - ((c_bit c 201 row) * ((c_bit c 137 row) + (c_bit c 137 row)))) + (c_bit c 264 row)) - ((((c_bit c 201 row) + (c_bit c 137 row)) - ((c_bit c 201 row) * ((c_bit c 137 row) + (c_bit c 137 row)))) * ((c_bit c 264 row) + (c_bit c 264 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_707_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_707 c row ↔ constraint_707 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_708 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 202 row) - (((((c_bit c 202 row) + (c_bit c 138 row)) - ((c_bit c 202 row) * ((c_bit c 138 row) + (c_bit c 138 row)))) + (c_bit c 265 row)) - ((((c_bit c 202 row) + (c_bit c 138 row)) - ((c_bit c 202 row) * ((c_bit c 138 row) + (c_bit c 138 row)))) * ((c_bit c 265 row) + (c_bit c 265 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_708_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_708 c row ↔ constraint_708 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_709 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 203 row) - (((((c_bit c 203 row) + (c_bit c 139 row)) - ((c_bit c 203 row) * ((c_bit c 139 row) + (c_bit c 139 row)))) + (c_bit c 266 row)) - ((((c_bit c 203 row) + (c_bit c 139 row)) - ((c_bit c 203 row) * ((c_bit c 139 row) + (c_bit c 139 row)))) * ((c_bit c 266 row) + (c_bit c 266 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_709_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_709 c row ↔ constraint_709 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_710 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 204 row) - (((((c_bit c 204 row) + (c_bit c 140 row)) - ((c_bit c 204 row) * ((c_bit c 140 row) + (c_bit c 140 row)))) + (c_bit c 267 row)) - ((((c_bit c 204 row) + (c_bit c 140 row)) - ((c_bit c 204 row) * ((c_bit c 140 row) + (c_bit c 140 row)))) * ((c_bit c 267 row) + (c_bit c 267 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_710_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_710 c row ↔ constraint_710 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_711 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 205 row) - (((((c_bit c 205 row) + (c_bit c 141 row)) - ((c_bit c 205 row) * ((c_bit c 141 row) + (c_bit c 141 row)))) + (c_bit c 268 row)) - ((((c_bit c 205 row) + (c_bit c 141 row)) - ((c_bit c 205 row) * ((c_bit c 141 row) + (c_bit c 141 row)))) * ((c_bit c 268 row) + (c_bit c 268 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_711_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_711 c row ↔ constraint_711 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_712 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 206 row) - (((((c_bit c 206 row) + (c_bit c 142 row)) - ((c_bit c 206 row) * ((c_bit c 142 row) + (c_bit c 142 row)))) + (c_bit c 269 row)) - ((((c_bit c 206 row) + (c_bit c 142 row)) - ((c_bit c 206 row) * ((c_bit c 142 row) + (c_bit c 142 row)))) * ((c_bit c 269 row) + (c_bit c 269 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_712_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_712 c row ↔ constraint_712 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_713 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 207 row) - (((((c_bit c 207 row) + (c_bit c 143 row)) - ((c_bit c 207 row) * ((c_bit c 143 row) + (c_bit c 143 row)))) + (c_bit c 270 row)) - ((((c_bit c 207 row) + (c_bit c 143 row)) - ((c_bit c 207 row) * ((c_bit c 143 row) + (c_bit c 143 row)))) * ((c_bit c 270 row) + (c_bit c 270 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_713_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_713 c row ↔ constraint_713 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_714 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 208 row) - (((((c_bit c 208 row) + (c_bit c 144 row)) - ((c_bit c 208 row) * ((c_bit c 144 row) + (c_bit c 144 row)))) + (c_bit c 271 row)) - ((((c_bit c 208 row) + (c_bit c 144 row)) - ((c_bit c 208 row) * ((c_bit c 144 row) + (c_bit c 144 row)))) * ((c_bit c 271 row) + (c_bit c 271 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_714_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_714 c row ↔ constraint_714 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_715 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 209 row) - (((((c_bit c 209 row) + (c_bit c 145 row)) - ((c_bit c 209 row) * ((c_bit c 145 row) + (c_bit c 145 row)))) + (c_bit c 272 row)) - ((((c_bit c 209 row) + (c_bit c 145 row)) - ((c_bit c 209 row) * ((c_bit c 145 row) + (c_bit c 145 row)))) * ((c_bit c 272 row) + (c_bit c 272 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_715_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_715 c row ↔ constraint_715 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_716 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 210 row) - (((((c_bit c 210 row) + (c_bit c 146 row)) - ((c_bit c 210 row) * ((c_bit c 146 row) + (c_bit c 146 row)))) + (c_bit c 273 row)) - ((((c_bit c 210 row) + (c_bit c 146 row)) - ((c_bit c 210 row) * ((c_bit c 146 row) + (c_bit c 146 row)))) * ((c_bit c 273 row) + (c_bit c 273 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_716_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_716 c row ↔ constraint_716 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_717 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 211 row) - (((((c_bit c 211 row) + (c_bit c 147 row)) - ((c_bit c 211 row) * ((c_bit c 147 row) + (c_bit c 147 row)))) + (c_bit c 274 row)) - ((((c_bit c 211 row) + (c_bit c 147 row)) - ((c_bit c 211 row) * ((c_bit c 147 row) + (c_bit c 147 row)))) * ((c_bit c 274 row) + (c_bit c 274 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_717_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_717 c row ↔ constraint_717 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_718 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 212 row) - (((((c_bit c 212 row) + (c_bit c 148 row)) - ((c_bit c 212 row) * ((c_bit c 148 row) + (c_bit c 148 row)))) + (c_bit c 275 row)) - ((((c_bit c 212 row) + (c_bit c 148 row)) - ((c_bit c 212 row) * ((c_bit c 148 row) + (c_bit c 148 row)))) * ((c_bit c 275 row) + (c_bit c 275 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_718_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_718 c row ↔ constraint_718 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_719 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 213 row) - (((((c_bit c 213 row) + (c_bit c 149 row)) - ((c_bit c 213 row) * ((c_bit c 149 row) + (c_bit c 149 row)))) + (c_bit c 276 row)) - ((((c_bit c 213 row) + (c_bit c 149 row)) - ((c_bit c 213 row) * ((c_bit c 149 row) + (c_bit c 149 row)))) * ((c_bit c 276 row) + (c_bit c 276 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_719_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_719 c row ↔ constraint_719 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_720 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 214 row) - (((((c_bit c 214 row) + (c_bit c 150 row)) - ((c_bit c 214 row) * ((c_bit c 150 row) + (c_bit c 150 row)))) + (c_bit c 277 row)) - ((((c_bit c 214 row) + (c_bit c 150 row)) - ((c_bit c 214 row) * ((c_bit c 150 row) + (c_bit c 150 row)))) * ((c_bit c 277 row) + (c_bit c 277 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_720_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_720 c row ↔ constraint_720 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_721 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 215 row) - (((((c_bit c 215 row) + (c_bit c 151 row)) - ((c_bit c 215 row) * ((c_bit c 151 row) + (c_bit c 151 row)))) + (c_bit c 278 row)) - ((((c_bit c 215 row) + (c_bit c 151 row)) - ((c_bit c 215 row) * ((c_bit c 151 row) + (c_bit c 151 row)))) * ((c_bit c 278 row) + (c_bit c 278 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_721_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_721 c row ↔ constraint_721 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_722 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 216 row) - (((((c_bit c 216 row) + (c_bit c 152 row)) - ((c_bit c 216 row) * ((c_bit c 152 row) + (c_bit c 152 row)))) + (c_bit c 279 row)) - ((((c_bit c 216 row) + (c_bit c 152 row)) - ((c_bit c 216 row) * ((c_bit c 152 row) + (c_bit c 152 row)))) * ((c_bit c 279 row) + (c_bit c 279 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_722_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_722 c row ↔ constraint_722 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_723 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 217 row) - (((((c_bit c 217 row) + (c_bit c 153 row)) - ((c_bit c 217 row) * ((c_bit c 153 row) + (c_bit c 153 row)))) + (c_bit c 280 row)) - ((((c_bit c 217 row) + (c_bit c 153 row)) - ((c_bit c 217 row) * ((c_bit c 153 row) + (c_bit c 153 row)))) * ((c_bit c 280 row) + (c_bit c 280 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_723_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_723 c row ↔ constraint_723 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_724 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 218 row) - (((((c_bit c 218 row) + (c_bit c 154 row)) - ((c_bit c 218 row) * ((c_bit c 154 row) + (c_bit c 154 row)))) + (c_bit c 281 row)) - ((((c_bit c 218 row) + (c_bit c 154 row)) - ((c_bit c 218 row) * ((c_bit c 154 row) + (c_bit c 154 row)))) * ((c_bit c 281 row) + (c_bit c 281 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_724_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_724 c row ↔ constraint_724 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_725 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 219 row) - (((((c_bit c 219 row) + (c_bit c 155 row)) - ((c_bit c 219 row) * ((c_bit c 155 row) + (c_bit c 155 row)))) + (c_bit c 282 row)) - ((((c_bit c 219 row) + (c_bit c 155 row)) - ((c_bit c 219 row) * ((c_bit c 155 row) + (c_bit c 155 row)))) * ((c_bit c 282 row) + (c_bit c 282 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_725_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_725 c row ↔ constraint_725 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_726 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 220 row) - (((((c_bit c 220 row) + (c_bit c 156 row)) - ((c_bit c 220 row) * ((c_bit c 156 row) + (c_bit c 156 row)))) + (c_bit c 283 row)) - ((((c_bit c 220 row) + (c_bit c 156 row)) - ((c_bit c 220 row) * ((c_bit c 156 row) + (c_bit c 156 row)))) * ((c_bit c 283 row) + (c_bit c 283 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_726_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_726 c row ↔ constraint_726 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_727 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 221 row) - (((((c_bit c 221 row) + (c_bit c 157 row)) - ((c_bit c 221 row) * ((c_bit c 157 row) + (c_bit c 157 row)))) + (c_bit c 284 row)) - ((((c_bit c 221 row) + (c_bit c 157 row)) - ((c_bit c 221 row) * ((c_bit c 157 row) + (c_bit c 157 row)))) * ((c_bit c 284 row) + (c_bit c 284 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_727_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_727 c row ↔ constraint_727 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_728 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 222 row) - (((((c_bit c 222 row) + (c_bit c 158 row)) - ((c_bit c 222 row) * ((c_bit c 158 row) + (c_bit c 158 row)))) + (c_bit c 285 row)) - ((((c_bit c 222 row) + (c_bit c 158 row)) - ((c_bit c 222 row) * ((c_bit c 158 row) + (c_bit c 158 row)))) * ((c_bit c 285 row) + (c_bit c 285 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_728_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_728 c row ↔ constraint_728 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_729 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 223 row) - (((((c_bit c 223 row) + (c_bit c 159 row)) - ((c_bit c 223 row) * ((c_bit c 159 row) + (c_bit c 159 row)))) + (c_bit c 286 row)) - ((((c_bit c 223 row) + (c_bit c 159 row)) - ((c_bit c 223 row) * ((c_bit c 159 row) + (c_bit c 159 row)))) * ((c_bit c 286 row) + (c_bit c 286 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_729_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_729 c row ↔ constraint_729 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_730 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 224 row) - (((((c_bit c 224 row) + (c_bit c 160 row)) - ((c_bit c 224 row) * ((c_bit c 160 row) + (c_bit c 160 row)))) + (c_bit c 287 row)) - ((((c_bit c 224 row) + (c_bit c 160 row)) - ((c_bit c 224 row) * ((c_bit c 160 row) + (c_bit c 160 row)))) * ((c_bit c 287 row) + (c_bit c 287 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_730_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_730 c row ↔ constraint_730 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_731 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 225 row) - (((((c_bit c 225 row) + (c_bit c 161 row)) - ((c_bit c 225 row) * ((c_bit c 161 row) + (c_bit c 161 row)))) + (c_bit c 288 row)) - ((((c_bit c 225 row) + (c_bit c 161 row)) - ((c_bit c 225 row) * ((c_bit c 161 row) + (c_bit c 161 row)))) * ((c_bit c 288 row) + (c_bit c 288 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_731_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_731 c row ↔ constraint_731 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_732 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 226 row) - (((((c_bit c 226 row) + (c_bit c 162 row)) - ((c_bit c 226 row) * ((c_bit c 162 row) + (c_bit c 162 row)))) + (c_bit c 289 row)) - ((((c_bit c 226 row) + (c_bit c 162 row)) - ((c_bit c 226 row) * ((c_bit c 162 row) + (c_bit c 162 row)))) * ((c_bit c 289 row) + (c_bit c 289 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_732_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_732 c row ↔ constraint_732 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_733 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 227 row) - (((((c_bit c 227 row) + (c_bit c 163 row)) - ((c_bit c 227 row) * ((c_bit c 163 row) + (c_bit c 163 row)))) + (c_bit c 290 row)) - ((((c_bit c 227 row) + (c_bit c 163 row)) - ((c_bit c 227 row) * ((c_bit c 163 row) + (c_bit c 163 row)))) * ((c_bit c 290 row) + (c_bit c 290 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_733_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_733 c row ↔ constraint_733 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_734 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 228 row) - (((((c_bit c 228 row) + (c_bit c 164 row)) - ((c_bit c 228 row) * ((c_bit c 164 row) + (c_bit c 164 row)))) + (c_bit c 291 row)) - ((((c_bit c 228 row) + (c_bit c 164 row)) - ((c_bit c 228 row) * ((c_bit c 164 row) + (c_bit c 164 row)))) * ((c_bit c 291 row) + (c_bit c 291 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_734_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_734 c row ↔ constraint_734 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_735 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 229 row) - (((((c_bit c 229 row) + (c_bit c 165 row)) - ((c_bit c 229 row) * ((c_bit c 165 row) + (c_bit c 165 row)))) + (c_bit c 292 row)) - ((((c_bit c 229 row) + (c_bit c 165 row)) - ((c_bit c 229 row) * ((c_bit c 165 row) + (c_bit c 165 row)))) * ((c_bit c 292 row) + (c_bit c 292 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_735_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_735 c row ↔ constraint_735 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_736 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 230 row) - (((((c_bit c 230 row) + (c_bit c 166 row)) - ((c_bit c 230 row) * ((c_bit c 166 row) + (c_bit c 166 row)))) + (c_bit c 293 row)) - ((((c_bit c 230 row) + (c_bit c 166 row)) - ((c_bit c 230 row) * ((c_bit c 166 row) + (c_bit c 166 row)))) * ((c_bit c 293 row) + (c_bit c 293 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_736_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_736 c row ↔ constraint_736 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_737 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 231 row) - (((((c_bit c 231 row) + (c_bit c 167 row)) - ((c_bit c 231 row) * ((c_bit c 167 row) + (c_bit c 167 row)))) + (c_bit c 294 row)) - ((((c_bit c 231 row) + (c_bit c 167 row)) - ((c_bit c 231 row) * ((c_bit c 167 row) + (c_bit c 167 row)))) * ((c_bit c 294 row) + (c_bit c 294 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_737_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_737 c row ↔ constraint_737 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_738 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 232 row) - (((((c_bit c 232 row) + (c_bit c 168 row)) - ((c_bit c 232 row) * ((c_bit c 168 row) + (c_bit c 168 row)))) + (c_bit c 295 row)) - ((((c_bit c 232 row) + (c_bit c 168 row)) - ((c_bit c 232 row) * ((c_bit c 168 row) + (c_bit c 168 row)))) * ((c_bit c 295 row) + (c_bit c 295 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_738_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_738 c row ↔ constraint_738 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_739 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 233 row) - (((((c_bit c 233 row) + (c_bit c 169 row)) - ((c_bit c 233 row) * ((c_bit c 169 row) + (c_bit c 169 row)))) + (c_bit c 296 row)) - ((((c_bit c 233 row) + (c_bit c 169 row)) - ((c_bit c 233 row) * ((c_bit c 169 row) + (c_bit c 169 row)))) * ((c_bit c 296 row) + (c_bit c 296 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_739_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_739 c row ↔ constraint_739 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_740 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 234 row) - (((((c_bit c 234 row) + (c_bit c 170 row)) - ((c_bit c 234 row) * ((c_bit c 170 row) + (c_bit c 170 row)))) + (c_bit c 297 row)) - ((((c_bit c 234 row) + (c_bit c 170 row)) - ((c_bit c 234 row) * ((c_bit c 170 row) + (c_bit c 170 row)))) * ((c_bit c 297 row) + (c_bit c 297 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_740_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_740 c row ↔ constraint_740 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_741 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 235 row) - (((((c_bit c 235 row) + (c_bit c 171 row)) - ((c_bit c 235 row) * ((c_bit c 171 row) + (c_bit c 171 row)))) + (c_bit c 298 row)) - ((((c_bit c 235 row) + (c_bit c 171 row)) - ((c_bit c 235 row) * ((c_bit c 171 row) + (c_bit c 171 row)))) * ((c_bit c 298 row) + (c_bit c 298 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_741_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_741 c row ↔ constraint_741 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_742 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 236 row) - (((((c_bit c 236 row) + (c_bit c 172 row)) - ((c_bit c 236 row) * ((c_bit c 172 row) + (c_bit c 172 row)))) + (c_bit c 299 row)) - ((((c_bit c 236 row) + (c_bit c 172 row)) - ((c_bit c 236 row) * ((c_bit c 172 row) + (c_bit c 172 row)))) * ((c_bit c 299 row) + (c_bit c 299 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_742_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_742 c row ↔ constraint_742 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_743 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 237 row) - (((((c_bit c 237 row) + (c_bit c 173 row)) - ((c_bit c 237 row) * ((c_bit c 173 row) + (c_bit c 173 row)))) + (c_bit c 300 row)) - ((((c_bit c 237 row) + (c_bit c 173 row)) - ((c_bit c 237 row) * ((c_bit c 173 row) + (c_bit c 173 row)))) * ((c_bit c 300 row) + (c_bit c 300 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_743_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_743 c row ↔ constraint_743 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_744 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 238 row) - (((((c_bit c 238 row) + (c_bit c 174 row)) - ((c_bit c 238 row) * ((c_bit c 174 row) + (c_bit c 174 row)))) + (c_bit c 301 row)) - ((((c_bit c 238 row) + (c_bit c 174 row)) - ((c_bit c 238 row) * ((c_bit c 174 row) + (c_bit c 174 row)))) * ((c_bit c 301 row) + (c_bit c 301 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_744_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_744 c row ↔ constraint_744 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_745 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 239 row) - (((((c_bit c 239 row) + (c_bit c 175 row)) - ((c_bit c 239 row) * ((c_bit c 175 row) + (c_bit c 175 row)))) + (c_bit c 302 row)) - ((((c_bit c 239 row) + (c_bit c 175 row)) - ((c_bit c 239 row) * ((c_bit c 175 row) + (c_bit c 175 row)))) * ((c_bit c 302 row) + (c_bit c 302 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_745_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_745 c row ↔ constraint_745 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_746 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 240 row) - (((((c_bit c 240 row) + (c_bit c 176 row)) - ((c_bit c 240 row) * ((c_bit c 176 row) + (c_bit c 176 row)))) + (c_bit c 303 row)) - ((((c_bit c 240 row) + (c_bit c 176 row)) - ((c_bit c 240 row) * ((c_bit c 176 row) + (c_bit c 176 row)))) * ((c_bit c 303 row) + (c_bit c 303 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_746_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_746 c row ↔ constraint_746 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_747 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 241 row) - (((((c_bit c 241 row) + (c_bit c 177 row)) - ((c_bit c 241 row) * ((c_bit c 177 row) + (c_bit c 177 row)))) + (c_bit c 304 row)) - ((((c_bit c 241 row) + (c_bit c 177 row)) - ((c_bit c 241 row) * ((c_bit c 177 row) + (c_bit c 177 row)))) * ((c_bit c 304 row) + (c_bit c 304 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_747_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_747 c row ↔ constraint_747 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_748 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 242 row) - (((((c_bit c 242 row) + (c_bit c 178 row)) - ((c_bit c 242 row) * ((c_bit c 178 row) + (c_bit c 178 row)))) + (c_bit c 305 row)) - ((((c_bit c 242 row) + (c_bit c 178 row)) - ((c_bit c 242 row) * ((c_bit c 178 row) + (c_bit c 178 row)))) * ((c_bit c 305 row) + (c_bit c 305 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_748_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_748 c row ↔ constraint_748 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_749 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 243 row) - (((((c_bit c 243 row) + (c_bit c 179 row)) - ((c_bit c 243 row) * ((c_bit c 179 row) + (c_bit c 179 row)))) + (c_bit c 306 row)) - ((((c_bit c 243 row) + (c_bit c 179 row)) - ((c_bit c 243 row) * ((c_bit c 179 row) + (c_bit c 179 row)))) * ((c_bit c 306 row) + (c_bit c 306 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_749_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_749 c row ↔ constraint_749 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_750 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 244 row) - (((((c_bit c 244 row) + (c_bit c 180 row)) - ((c_bit c 244 row) * ((c_bit c 180 row) + (c_bit c 180 row)))) + (c_bit c 307 row)) - ((((c_bit c 244 row) + (c_bit c 180 row)) - ((c_bit c 244 row) * ((c_bit c 180 row) + (c_bit c 180 row)))) * ((c_bit c 307 row) + (c_bit c 307 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_750_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_750 c row ↔ constraint_750 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_751 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 245 row) - (((((c_bit c 245 row) + (c_bit c 181 row)) - ((c_bit c 245 row) * ((c_bit c 181 row) + (c_bit c 181 row)))) + (c_bit c 308 row)) - ((((c_bit c 245 row) + (c_bit c 181 row)) - ((c_bit c 245 row) * ((c_bit c 181 row) + (c_bit c 181 row)))) * ((c_bit c 308 row) + (c_bit c 308 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_751_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_751 c row ↔ constraint_751 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_752 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 246 row) - (((((c_bit c 246 row) + (c_bit c 182 row)) - ((c_bit c 246 row) * ((c_bit c 182 row) + (c_bit c 182 row)))) + (c_bit c 309 row)) - ((((c_bit c 246 row) + (c_bit c 182 row)) - ((c_bit c 246 row) * ((c_bit c 182 row) + (c_bit c 182 row)))) * ((c_bit c 309 row) + (c_bit c 309 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_752_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_752 c row ↔ constraint_752 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_753 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 247 row) - (((((c_bit c 247 row) + (c_bit c 183 row)) - ((c_bit c 247 row) * ((c_bit c 183 row) + (c_bit c 183 row)))) + (c_bit c 310 row)) - ((((c_bit c 247 row) + (c_bit c 183 row)) - ((c_bit c 247 row) * ((c_bit c 183 row) + (c_bit c 183 row)))) * ((c_bit c 310 row) + (c_bit c 310 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_753_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_753 c row ↔ constraint_753 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_754 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 248 row) - (((((c_bit c 248 row) + (c_bit c 184 row)) - ((c_bit c 248 row) * ((c_bit c 184 row) + (c_bit c 184 row)))) + (c_bit c 311 row)) - ((((c_bit c 248 row) + (c_bit c 184 row)) - ((c_bit c 248 row) * ((c_bit c 184 row) + (c_bit c 184 row)))) * ((c_bit c 311 row) + (c_bit c 311 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_754_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_754 c row ↔ constraint_754 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_755 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 249 row) - (((((c_bit c 249 row) + (c_bit c 185 row)) - ((c_bit c 249 row) * ((c_bit c 185 row) + (c_bit c 185 row)))) + (c_bit c 312 row)) - ((((c_bit c 249 row) + (c_bit c 185 row)) - ((c_bit c 249 row) * ((c_bit c 185 row) + (c_bit c 185 row)))) * ((c_bit c 312 row) + (c_bit c 312 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_755_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_755 c row ↔ constraint_755 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_756 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 250 row) - (((((c_bit c 250 row) + (c_bit c 186 row)) - ((c_bit c 250 row) * ((c_bit c 186 row) + (c_bit c 186 row)))) + (c_bit c 313 row)) - ((((c_bit c 250 row) + (c_bit c 186 row)) - ((c_bit c 250 row) * ((c_bit c 186 row) + (c_bit c 186 row)))) * ((c_bit c 313 row) + (c_bit c 313 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_756_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_756 c row ↔ constraint_756 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_757 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 251 row) - (((((c_bit c 251 row) + (c_bit c 187 row)) - ((c_bit c 251 row) * ((c_bit c 187 row) + (c_bit c 187 row)))) + (c_bit c 314 row)) - ((((c_bit c 251 row) + (c_bit c 187 row)) - ((c_bit c 251 row) * ((c_bit c 187 row) + (c_bit c 187 row)))) * ((c_bit c 314 row) + (c_bit c 314 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_757_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_757 c row ↔ constraint_757 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_758 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 252 row) - (((((c_bit c 252 row) + (c_bit c 188 row)) - ((c_bit c 252 row) * ((c_bit c 188 row) + (c_bit c 188 row)))) + (c_bit c 315 row)) - ((((c_bit c 252 row) + (c_bit c 188 row)) - ((c_bit c 252 row) * ((c_bit c 188 row) + (c_bit c 188 row)))) * ((c_bit c 315 row) + (c_bit c 315 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_758_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_758 c row ↔ constraint_758 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_759 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 253 row) - (((((c_bit c 253 row) + (c_bit c 189 row)) - ((c_bit c 253 row) * ((c_bit c 189 row) + (c_bit c 189 row)))) + (c_bit c 316 row)) - ((((c_bit c 253 row) + (c_bit c 189 row)) - ((c_bit c 253 row) * ((c_bit c 189 row) + (c_bit c 189 row)))) * ((c_bit c 316 row) + (c_bit c 316 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_759_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_759 c row ↔ constraint_759 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_760 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 254 row) - (((((c_bit c 254 row) + (c_bit c 190 row)) - ((c_bit c 254 row) * ((c_bit c 190 row) + (c_bit c 190 row)))) + (c_bit c 317 row)) - ((((c_bit c 254 row) + (c_bit c 190 row)) - ((c_bit c 254 row) * ((c_bit c 190 row) + (c_bit c 190 row)))) * ((c_bit c 317 row) + (c_bit c 317 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_760_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_760 c row ↔ constraint_760 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_761 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 255 row) - (((((c_bit c 255 row) + (c_bit c 191 row)) - ((c_bit c 255 row) * ((c_bit c 191 row) + (c_bit c 191 row)))) + (c_bit c 318 row)) - ((((c_bit c 255 row) + (c_bit c 191 row)) - ((c_bit c 255 row) * ((c_bit c 191 row) + (c_bit c 191 row)))) * ((c_bit c 318 row) + (c_bit c 318 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_761_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_761 c row ↔ constraint_761 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_762 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 256 row) * ((c_bit c 256 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_762_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_762 c row ↔ constraint_762 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_763 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 257 row) * ((c_bit c 257 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_763_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_763 c row ↔ constraint_763 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_764 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 258 row) * ((c_bit c 258 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_764_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_764 c row ↔ constraint_764 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_765 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 259 row) * ((c_bit c 259 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_765_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_765 c row ↔ constraint_765 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_766 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 260 row) * ((c_bit c 260 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_766_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_766 c row ↔ constraint_766 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_767 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 261 row) * ((c_bit c 261 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_767_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_767 c row ↔ constraint_767 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_768 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 262 row) * ((c_bit c 262 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_768_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_768 c row ↔ constraint_768 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_769 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 263 row) * ((c_bit c 263 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_769_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_769 c row ↔ constraint_769 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_770 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 264 row) * ((c_bit c 264 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_770_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_770 c row ↔ constraint_770 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_771 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 265 row) * ((c_bit c 265 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_771_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_771 c row ↔ constraint_771 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_772 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 266 row) * ((c_bit c 266 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_772_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_772 c row ↔ constraint_772 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_773 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 267 row) * ((c_bit c 267 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_773_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_773 c row ↔ constraint_773 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_774 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 268 row) * ((c_bit c 268 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_774_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_774 c row ↔ constraint_774 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_775 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 269 row) * ((c_bit c 269 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_775_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_775 c row ↔ constraint_775 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_776 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 270 row) * ((c_bit c 270 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_776_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_776 c row ↔ constraint_776 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_777 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 271 row) * ((c_bit c 271 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_777_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_777 c row ↔ constraint_777 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_778 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 272 row) * ((c_bit c 272 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_778_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_778 c row ↔ constraint_778 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_779 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 273 row) * ((c_bit c 273 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_779_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_779 c row ↔ constraint_779 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_780 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 274 row) * ((c_bit c 274 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_780_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_780 c row ↔ constraint_780 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_781 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 275 row) * ((c_bit c 275 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_781_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_781 c row ↔ constraint_781 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_782 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 276 row) * ((c_bit c 276 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_782_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_782 c row ↔ constraint_782 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_783 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 277 row) * ((c_bit c 277 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_783_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_783 c row ↔ constraint_783 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_784 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 278 row) * ((c_bit c 278 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_784_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_784 c row ↔ constraint_784 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_785 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 279 row) * ((c_bit c 279 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_785_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_785 c row ↔ constraint_785 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_786 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 280 row) * ((c_bit c 280 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_786_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_786 c row ↔ constraint_786 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_787 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 281 row) * ((c_bit c 281 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_787_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_787 c row ↔ constraint_787 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_788 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 282 row) * ((c_bit c 282 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_788_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_788 c row ↔ constraint_788 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_789 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 283 row) * ((c_bit c 283 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_789_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_789 c row ↔ constraint_789 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_790 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 284 row) * ((c_bit c 284 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_790_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_790 c row ↔ constraint_790 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_791 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 285 row) * ((c_bit c 285 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_791_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_791 c row ↔ constraint_791 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_792 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 286 row) * ((c_bit c 286 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_792_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_792 c row ↔ constraint_792 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_793 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 287 row) * ((c_bit c 287 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_793_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_793 c row ↔ constraint_793 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_794 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 288 row) * ((c_bit c 288 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_794_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_794 c row ↔ constraint_794 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_795 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 289 row) * ((c_bit c 289 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_795_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_795 c row ↔ constraint_795 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_796 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 290 row) * ((c_bit c 290 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_796_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_796 c row ↔ constraint_796 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_797 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 291 row) * ((c_bit c 291 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_797_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_797 c row ↔ constraint_797 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_798 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 292 row) * ((c_bit c 292 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_798_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_798 c row ↔ constraint_798 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_799 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 293 row) * ((c_bit c 293 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_799_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_799 c row ↔ constraint_799 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_800 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 294 row) * ((c_bit c 294 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_800_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_800 c row ↔ constraint_800 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_801 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 295 row) * ((c_bit c 295 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_801_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_801 c row ↔ constraint_801 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_802 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 296 row) * ((c_bit c 296 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_802_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_802 c row ↔ constraint_802 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_803 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 297 row) * ((c_bit c 297 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_803_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_803 c row ↔ constraint_803 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_804 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 298 row) * ((c_bit c 298 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_804_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_804 c row ↔ constraint_804 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_805 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 299 row) * ((c_bit c 299 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_805_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_805 c row ↔ constraint_805 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_806 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 300 row) * ((c_bit c 300 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_806_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_806 c row ↔ constraint_806 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_807 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 301 row) * ((c_bit c 301 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_807_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_807 c row ↔ constraint_807 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_808 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 302 row) * ((c_bit c 302 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_808_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_808 c row ↔ constraint_808 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_809 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 303 row) * ((c_bit c 303 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_809_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_809 c row ↔ constraint_809 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_810 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 304 row) * ((c_bit c 304 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_810_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_810 c row ↔ constraint_810 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_811 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 305 row) * ((c_bit c 305 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_811_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_811 c row ↔ constraint_811 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_812 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 306 row) * ((c_bit c 306 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_812_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_812 c row ↔ constraint_812 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_813 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 307 row) * ((c_bit c 307 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_813_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_813 c row ↔ constraint_813 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_814 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 308 row) * ((c_bit c 308 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_814_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_814 c row ↔ constraint_814 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_815 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 309 row) * ((c_bit c 309 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_815_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_815 c row ↔ constraint_815 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_816 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 310 row) * ((c_bit c 310 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_816_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_816 c row ↔ constraint_816 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_817 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 311 row) * ((c_bit c 311 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_817_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_817 c row ↔ constraint_817 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_818 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 312 row) * ((c_bit c 312 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_818_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_818 c row ↔ constraint_818 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_819 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 313 row) * ((c_bit c 313 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_819_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_819 c row ↔ constraint_819 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_820 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 314 row) * ((c_bit c 314 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_820_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_820 c row ↔ constraint_820 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_821 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 315 row) * ((c_bit c 315 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_821_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_821 c row ↔ constraint_821 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_822 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 316 row) * ((c_bit c 316 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_822_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_822 c row ↔ constraint_822 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_823 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 317 row) * ((c_bit c 317 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_823_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_823 c row ↔ constraint_823 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_824 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 318 row) * ((c_bit c 318 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_824_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_824 c row ↔ constraint_824 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_825 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_bit c 319 row) * ((c_bit c 319 row) - 1)) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_825_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_825 c row ↔ constraint_825 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_826 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 256 row) - (((((c_bit c 256 row) + (c_bit c 192 row)) - ((c_bit c 256 row) * ((c_bit c 192 row) + (c_bit c 192 row)))) + (c_bit c 63 row)) - ((((c_bit c 256 row) + (c_bit c 192 row)) - ((c_bit c 256 row) * ((c_bit c 192 row) + (c_bit c 192 row)))) * ((c_bit c 63 row) + (c_bit c 63 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_826_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_826 c row ↔ constraint_826 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_827 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 257 row) - (((((c_bit c 257 row) + (c_bit c 193 row)) - ((c_bit c 257 row) * ((c_bit c 193 row) + (c_bit c 193 row)))) + (c_bit c 0 row)) - ((((c_bit c 257 row) + (c_bit c 193 row)) - ((c_bit c 257 row) * ((c_bit c 193 row) + (c_bit c 193 row)))) * ((c_bit c 0 row) + (c_bit c 0 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_827_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_827 c row ↔ constraint_827 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_828 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 258 row) - (((((c_bit c 258 row) + (c_bit c 194 row)) - ((c_bit c 258 row) * ((c_bit c 194 row) + (c_bit c 194 row)))) + (c_bit c 1 row)) - ((((c_bit c 258 row) + (c_bit c 194 row)) - ((c_bit c 258 row) * ((c_bit c 194 row) + (c_bit c 194 row)))) * ((c_bit c 1 row) + (c_bit c 1 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_828_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_828 c row ↔ constraint_828 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_829 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 259 row) - (((((c_bit c 259 row) + (c_bit c 195 row)) - ((c_bit c 259 row) * ((c_bit c 195 row) + (c_bit c 195 row)))) + (c_bit c 2 row)) - ((((c_bit c 259 row) + (c_bit c 195 row)) - ((c_bit c 259 row) * ((c_bit c 195 row) + (c_bit c 195 row)))) * ((c_bit c 2 row) + (c_bit c 2 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_829_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_829 c row ↔ constraint_829 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_830 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 260 row) - (((((c_bit c 260 row) + (c_bit c 196 row)) - ((c_bit c 260 row) * ((c_bit c 196 row) + (c_bit c 196 row)))) + (c_bit c 3 row)) - ((((c_bit c 260 row) + (c_bit c 196 row)) - ((c_bit c 260 row) * ((c_bit c 196 row) + (c_bit c 196 row)))) * ((c_bit c 3 row) + (c_bit c 3 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_830_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_830 c row ↔ constraint_830 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_831 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 261 row) - (((((c_bit c 261 row) + (c_bit c 197 row)) - ((c_bit c 261 row) * ((c_bit c 197 row) + (c_bit c 197 row)))) + (c_bit c 4 row)) - ((((c_bit c 261 row) + (c_bit c 197 row)) - ((c_bit c 261 row) * ((c_bit c 197 row) + (c_bit c 197 row)))) * ((c_bit c 4 row) + (c_bit c 4 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_831_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_831 c row ↔ constraint_831 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_832 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 262 row) - (((((c_bit c 262 row) + (c_bit c 198 row)) - ((c_bit c 262 row) * ((c_bit c 198 row) + (c_bit c 198 row)))) + (c_bit c 5 row)) - ((((c_bit c 262 row) + (c_bit c 198 row)) - ((c_bit c 262 row) * ((c_bit c 198 row) + (c_bit c 198 row)))) * ((c_bit c 5 row) + (c_bit c 5 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_832_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_832 c row ↔ constraint_832 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_833 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 263 row) - (((((c_bit c 263 row) + (c_bit c 199 row)) - ((c_bit c 263 row) * ((c_bit c 199 row) + (c_bit c 199 row)))) + (c_bit c 6 row)) - ((((c_bit c 263 row) + (c_bit c 199 row)) - ((c_bit c 263 row) * ((c_bit c 199 row) + (c_bit c 199 row)))) * ((c_bit c 6 row) + (c_bit c 6 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_833_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_833 c row ↔ constraint_833 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_834 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 264 row) - (((((c_bit c 264 row) + (c_bit c 200 row)) - ((c_bit c 264 row) * ((c_bit c 200 row) + (c_bit c 200 row)))) + (c_bit c 7 row)) - ((((c_bit c 264 row) + (c_bit c 200 row)) - ((c_bit c 264 row) * ((c_bit c 200 row) + (c_bit c 200 row)))) * ((c_bit c 7 row) + (c_bit c 7 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_834_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_834 c row ↔ constraint_834 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_835 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 265 row) - (((((c_bit c 265 row) + (c_bit c 201 row)) - ((c_bit c 265 row) * ((c_bit c 201 row) + (c_bit c 201 row)))) + (c_bit c 8 row)) - ((((c_bit c 265 row) + (c_bit c 201 row)) - ((c_bit c 265 row) * ((c_bit c 201 row) + (c_bit c 201 row)))) * ((c_bit c 8 row) + (c_bit c 8 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_835_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_835 c row ↔ constraint_835 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_836 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 266 row) - (((((c_bit c 266 row) + (c_bit c 202 row)) - ((c_bit c 266 row) * ((c_bit c 202 row) + (c_bit c 202 row)))) + (c_bit c 9 row)) - ((((c_bit c 266 row) + (c_bit c 202 row)) - ((c_bit c 266 row) * ((c_bit c 202 row) + (c_bit c 202 row)))) * ((c_bit c 9 row) + (c_bit c 9 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_836_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_836 c row ↔ constraint_836 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_837 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 267 row) - (((((c_bit c 267 row) + (c_bit c 203 row)) - ((c_bit c 267 row) * ((c_bit c 203 row) + (c_bit c 203 row)))) + (c_bit c 10 row)) - ((((c_bit c 267 row) + (c_bit c 203 row)) - ((c_bit c 267 row) * ((c_bit c 203 row) + (c_bit c 203 row)))) * ((c_bit c 10 row) + (c_bit c 10 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_837_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_837 c row ↔ constraint_837 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_838 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 268 row) - (((((c_bit c 268 row) + (c_bit c 204 row)) - ((c_bit c 268 row) * ((c_bit c 204 row) + (c_bit c 204 row)))) + (c_bit c 11 row)) - ((((c_bit c 268 row) + (c_bit c 204 row)) - ((c_bit c 268 row) * ((c_bit c 204 row) + (c_bit c 204 row)))) * ((c_bit c 11 row) + (c_bit c 11 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_838_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_838 c row ↔ constraint_838 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_839 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 269 row) - (((((c_bit c 269 row) + (c_bit c 205 row)) - ((c_bit c 269 row) * ((c_bit c 205 row) + (c_bit c 205 row)))) + (c_bit c 12 row)) - ((((c_bit c 269 row) + (c_bit c 205 row)) - ((c_bit c 269 row) * ((c_bit c 205 row) + (c_bit c 205 row)))) * ((c_bit c 12 row) + (c_bit c 12 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_839_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_839 c row ↔ constraint_839 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_840 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 270 row) - (((((c_bit c 270 row) + (c_bit c 206 row)) - ((c_bit c 270 row) * ((c_bit c 206 row) + (c_bit c 206 row)))) + (c_bit c 13 row)) - ((((c_bit c 270 row) + (c_bit c 206 row)) - ((c_bit c 270 row) * ((c_bit c 206 row) + (c_bit c 206 row)))) * ((c_bit c 13 row) + (c_bit c 13 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_840_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_840 c row ↔ constraint_840 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_841 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 271 row) - (((((c_bit c 271 row) + (c_bit c 207 row)) - ((c_bit c 271 row) * ((c_bit c 207 row) + (c_bit c 207 row)))) + (c_bit c 14 row)) - ((((c_bit c 271 row) + (c_bit c 207 row)) - ((c_bit c 271 row) * ((c_bit c 207 row) + (c_bit c 207 row)))) * ((c_bit c 14 row) + (c_bit c 14 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_841_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_841 c row ↔ constraint_841 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_842 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 272 row) - (((((c_bit c 272 row) + (c_bit c 208 row)) - ((c_bit c 272 row) * ((c_bit c 208 row) + (c_bit c 208 row)))) + (c_bit c 15 row)) - ((((c_bit c 272 row) + (c_bit c 208 row)) - ((c_bit c 272 row) * ((c_bit c 208 row) + (c_bit c 208 row)))) * ((c_bit c 15 row) + (c_bit c 15 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_842_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_842 c row ↔ constraint_842 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_843 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 273 row) - (((((c_bit c 273 row) + (c_bit c 209 row)) - ((c_bit c 273 row) * ((c_bit c 209 row) + (c_bit c 209 row)))) + (c_bit c 16 row)) - ((((c_bit c 273 row) + (c_bit c 209 row)) - ((c_bit c 273 row) * ((c_bit c 209 row) + (c_bit c 209 row)))) * ((c_bit c 16 row) + (c_bit c 16 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_843_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_843 c row ↔ constraint_843 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_844 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 274 row) - (((((c_bit c 274 row) + (c_bit c 210 row)) - ((c_bit c 274 row) * ((c_bit c 210 row) + (c_bit c 210 row)))) + (c_bit c 17 row)) - ((((c_bit c 274 row) + (c_bit c 210 row)) - ((c_bit c 274 row) * ((c_bit c 210 row) + (c_bit c 210 row)))) * ((c_bit c 17 row) + (c_bit c 17 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_844_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_844 c row ↔ constraint_844 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_845 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 275 row) - (((((c_bit c 275 row) + (c_bit c 211 row)) - ((c_bit c 275 row) * ((c_bit c 211 row) + (c_bit c 211 row)))) + (c_bit c 18 row)) - ((((c_bit c 275 row) + (c_bit c 211 row)) - ((c_bit c 275 row) * ((c_bit c 211 row) + (c_bit c 211 row)))) * ((c_bit c 18 row) + (c_bit c 18 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_845_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_845 c row ↔ constraint_845 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_846 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 276 row) - (((((c_bit c 276 row) + (c_bit c 212 row)) - ((c_bit c 276 row) * ((c_bit c 212 row) + (c_bit c 212 row)))) + (c_bit c 19 row)) - ((((c_bit c 276 row) + (c_bit c 212 row)) - ((c_bit c 276 row) * ((c_bit c 212 row) + (c_bit c 212 row)))) * ((c_bit c 19 row) + (c_bit c 19 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_846_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_846 c row ↔ constraint_846 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_847 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 277 row) - (((((c_bit c 277 row) + (c_bit c 213 row)) - ((c_bit c 277 row) * ((c_bit c 213 row) + (c_bit c 213 row)))) + (c_bit c 20 row)) - ((((c_bit c 277 row) + (c_bit c 213 row)) - ((c_bit c 277 row) * ((c_bit c 213 row) + (c_bit c 213 row)))) * ((c_bit c 20 row) + (c_bit c 20 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_847_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_847 c row ↔ constraint_847 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_848 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 278 row) - (((((c_bit c 278 row) + (c_bit c 214 row)) - ((c_bit c 278 row) * ((c_bit c 214 row) + (c_bit c 214 row)))) + (c_bit c 21 row)) - ((((c_bit c 278 row) + (c_bit c 214 row)) - ((c_bit c 278 row) * ((c_bit c 214 row) + (c_bit c 214 row)))) * ((c_bit c 21 row) + (c_bit c 21 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_848_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_848 c row ↔ constraint_848 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_849 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 279 row) - (((((c_bit c 279 row) + (c_bit c 215 row)) - ((c_bit c 279 row) * ((c_bit c 215 row) + (c_bit c 215 row)))) + (c_bit c 22 row)) - ((((c_bit c 279 row) + (c_bit c 215 row)) - ((c_bit c 279 row) * ((c_bit c 215 row) + (c_bit c 215 row)))) * ((c_bit c 22 row) + (c_bit c 22 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_849_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_849 c row ↔ constraint_849 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_850 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 280 row) - (((((c_bit c 280 row) + (c_bit c 216 row)) - ((c_bit c 280 row) * ((c_bit c 216 row) + (c_bit c 216 row)))) + (c_bit c 23 row)) - ((((c_bit c 280 row) + (c_bit c 216 row)) - ((c_bit c 280 row) * ((c_bit c 216 row) + (c_bit c 216 row)))) * ((c_bit c 23 row) + (c_bit c 23 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_850_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_850 c row ↔ constraint_850 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_851 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 281 row) - (((((c_bit c 281 row) + (c_bit c 217 row)) - ((c_bit c 281 row) * ((c_bit c 217 row) + (c_bit c 217 row)))) + (c_bit c 24 row)) - ((((c_bit c 281 row) + (c_bit c 217 row)) - ((c_bit c 281 row) * ((c_bit c 217 row) + (c_bit c 217 row)))) * ((c_bit c 24 row) + (c_bit c 24 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_851_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_851 c row ↔ constraint_851 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_852 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 282 row) - (((((c_bit c 282 row) + (c_bit c 218 row)) - ((c_bit c 282 row) * ((c_bit c 218 row) + (c_bit c 218 row)))) + (c_bit c 25 row)) - ((((c_bit c 282 row) + (c_bit c 218 row)) - ((c_bit c 282 row) * ((c_bit c 218 row) + (c_bit c 218 row)))) * ((c_bit c 25 row) + (c_bit c 25 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_852_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_852 c row ↔ constraint_852 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_853 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 283 row) - (((((c_bit c 283 row) + (c_bit c 219 row)) - ((c_bit c 283 row) * ((c_bit c 219 row) + (c_bit c 219 row)))) + (c_bit c 26 row)) - ((((c_bit c 283 row) + (c_bit c 219 row)) - ((c_bit c 283 row) * ((c_bit c 219 row) + (c_bit c 219 row)))) * ((c_bit c 26 row) + (c_bit c 26 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_853_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_853 c row ↔ constraint_853 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_854 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 284 row) - (((((c_bit c 284 row) + (c_bit c 220 row)) - ((c_bit c 284 row) * ((c_bit c 220 row) + (c_bit c 220 row)))) + (c_bit c 27 row)) - ((((c_bit c 284 row) + (c_bit c 220 row)) - ((c_bit c 284 row) * ((c_bit c 220 row) + (c_bit c 220 row)))) * ((c_bit c 27 row) + (c_bit c 27 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_854_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_854 c row ↔ constraint_854 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_855 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 285 row) - (((((c_bit c 285 row) + (c_bit c 221 row)) - ((c_bit c 285 row) * ((c_bit c 221 row) + (c_bit c 221 row)))) + (c_bit c 28 row)) - ((((c_bit c 285 row) + (c_bit c 221 row)) - ((c_bit c 285 row) * ((c_bit c 221 row) + (c_bit c 221 row)))) * ((c_bit c 28 row) + (c_bit c 28 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_855_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_855 c row ↔ constraint_855 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_856 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 286 row) - (((((c_bit c 286 row) + (c_bit c 222 row)) - ((c_bit c 286 row) * ((c_bit c 222 row) + (c_bit c 222 row)))) + (c_bit c 29 row)) - ((((c_bit c 286 row) + (c_bit c 222 row)) - ((c_bit c 286 row) * ((c_bit c 222 row) + (c_bit c 222 row)))) * ((c_bit c 29 row) + (c_bit c 29 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_856_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_856 c row ↔ constraint_856 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_857 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 287 row) - (((((c_bit c 287 row) + (c_bit c 223 row)) - ((c_bit c 287 row) * ((c_bit c 223 row) + (c_bit c 223 row)))) + (c_bit c 30 row)) - ((((c_bit c 287 row) + (c_bit c 223 row)) - ((c_bit c 287 row) * ((c_bit c 223 row) + (c_bit c 223 row)))) * ((c_bit c 30 row) + (c_bit c 30 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_857_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_857 c row ↔ constraint_857 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_858 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 288 row) - (((((c_bit c 288 row) + (c_bit c 224 row)) - ((c_bit c 288 row) * ((c_bit c 224 row) + (c_bit c 224 row)))) + (c_bit c 31 row)) - ((((c_bit c 288 row) + (c_bit c 224 row)) - ((c_bit c 288 row) * ((c_bit c 224 row) + (c_bit c 224 row)))) * ((c_bit c 31 row) + (c_bit c 31 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_858_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_858 c row ↔ constraint_858 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_859 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 289 row) - (((((c_bit c 289 row) + (c_bit c 225 row)) - ((c_bit c 289 row) * ((c_bit c 225 row) + (c_bit c 225 row)))) + (c_bit c 32 row)) - ((((c_bit c 289 row) + (c_bit c 225 row)) - ((c_bit c 289 row) * ((c_bit c 225 row) + (c_bit c 225 row)))) * ((c_bit c 32 row) + (c_bit c 32 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_859_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_859 c row ↔ constraint_859 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_860 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 290 row) - (((((c_bit c 290 row) + (c_bit c 226 row)) - ((c_bit c 290 row) * ((c_bit c 226 row) + (c_bit c 226 row)))) + (c_bit c 33 row)) - ((((c_bit c 290 row) + (c_bit c 226 row)) - ((c_bit c 290 row) * ((c_bit c 226 row) + (c_bit c 226 row)))) * ((c_bit c 33 row) + (c_bit c 33 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_860_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_860 c row ↔ constraint_860 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_861 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 291 row) - (((((c_bit c 291 row) + (c_bit c 227 row)) - ((c_bit c 291 row) * ((c_bit c 227 row) + (c_bit c 227 row)))) + (c_bit c 34 row)) - ((((c_bit c 291 row) + (c_bit c 227 row)) - ((c_bit c 291 row) * ((c_bit c 227 row) + (c_bit c 227 row)))) * ((c_bit c 34 row) + (c_bit c 34 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_861_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_861 c row ↔ constraint_861 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_862 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 292 row) - (((((c_bit c 292 row) + (c_bit c 228 row)) - ((c_bit c 292 row) * ((c_bit c 228 row) + (c_bit c 228 row)))) + (c_bit c 35 row)) - ((((c_bit c 292 row) + (c_bit c 228 row)) - ((c_bit c 292 row) * ((c_bit c 228 row) + (c_bit c 228 row)))) * ((c_bit c 35 row) + (c_bit c 35 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_862_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_862 c row ↔ constraint_862 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_863 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 293 row) - (((((c_bit c 293 row) + (c_bit c 229 row)) - ((c_bit c 293 row) * ((c_bit c 229 row) + (c_bit c 229 row)))) + (c_bit c 36 row)) - ((((c_bit c 293 row) + (c_bit c 229 row)) - ((c_bit c 293 row) * ((c_bit c 229 row) + (c_bit c 229 row)))) * ((c_bit c 36 row) + (c_bit c 36 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_863_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_863 c row ↔ constraint_863 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_864 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 294 row) - (((((c_bit c 294 row) + (c_bit c 230 row)) - ((c_bit c 294 row) * ((c_bit c 230 row) + (c_bit c 230 row)))) + (c_bit c 37 row)) - ((((c_bit c 294 row) + (c_bit c 230 row)) - ((c_bit c 294 row) * ((c_bit c 230 row) + (c_bit c 230 row)))) * ((c_bit c 37 row) + (c_bit c 37 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_864_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_864 c row ↔ constraint_864 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_865 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 295 row) - (((((c_bit c 295 row) + (c_bit c 231 row)) - ((c_bit c 295 row) * ((c_bit c 231 row) + (c_bit c 231 row)))) + (c_bit c 38 row)) - ((((c_bit c 295 row) + (c_bit c 231 row)) - ((c_bit c 295 row) * ((c_bit c 231 row) + (c_bit c 231 row)))) * ((c_bit c 38 row) + (c_bit c 38 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_865_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_865 c row ↔ constraint_865 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_866 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 296 row) - (((((c_bit c 296 row) + (c_bit c 232 row)) - ((c_bit c 296 row) * ((c_bit c 232 row) + (c_bit c 232 row)))) + (c_bit c 39 row)) - ((((c_bit c 296 row) + (c_bit c 232 row)) - ((c_bit c 296 row) * ((c_bit c 232 row) + (c_bit c 232 row)))) * ((c_bit c 39 row) + (c_bit c 39 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_866_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_866 c row ↔ constraint_866 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_867 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 297 row) - (((((c_bit c 297 row) + (c_bit c 233 row)) - ((c_bit c 297 row) * ((c_bit c 233 row) + (c_bit c 233 row)))) + (c_bit c 40 row)) - ((((c_bit c 297 row) + (c_bit c 233 row)) - ((c_bit c 297 row) * ((c_bit c 233 row) + (c_bit c 233 row)))) * ((c_bit c 40 row) + (c_bit c 40 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_867_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_867 c row ↔ constraint_867 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_868 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 298 row) - (((((c_bit c 298 row) + (c_bit c 234 row)) - ((c_bit c 298 row) * ((c_bit c 234 row) + (c_bit c 234 row)))) + (c_bit c 41 row)) - ((((c_bit c 298 row) + (c_bit c 234 row)) - ((c_bit c 298 row) * ((c_bit c 234 row) + (c_bit c 234 row)))) * ((c_bit c 41 row) + (c_bit c 41 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_868_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_868 c row ↔ constraint_868 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_869 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 299 row) - (((((c_bit c 299 row) + (c_bit c 235 row)) - ((c_bit c 299 row) * ((c_bit c 235 row) + (c_bit c 235 row)))) + (c_bit c 42 row)) - ((((c_bit c 299 row) + (c_bit c 235 row)) - ((c_bit c 299 row) * ((c_bit c 235 row) + (c_bit c 235 row)))) * ((c_bit c 42 row) + (c_bit c 42 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_869_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_869 c row ↔ constraint_869 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_870 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 300 row) - (((((c_bit c 300 row) + (c_bit c 236 row)) - ((c_bit c 300 row) * ((c_bit c 236 row) + (c_bit c 236 row)))) + (c_bit c 43 row)) - ((((c_bit c 300 row) + (c_bit c 236 row)) - ((c_bit c 300 row) * ((c_bit c 236 row) + (c_bit c 236 row)))) * ((c_bit c 43 row) + (c_bit c 43 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_870_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_870 c row ↔ constraint_870 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_871 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 301 row) - (((((c_bit c 301 row) + (c_bit c 237 row)) - ((c_bit c 301 row) * ((c_bit c 237 row) + (c_bit c 237 row)))) + (c_bit c 44 row)) - ((((c_bit c 301 row) + (c_bit c 237 row)) - ((c_bit c 301 row) * ((c_bit c 237 row) + (c_bit c 237 row)))) * ((c_bit c 44 row) + (c_bit c 44 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_871_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_871 c row ↔ constraint_871 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_872 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 302 row) - (((((c_bit c 302 row) + (c_bit c 238 row)) - ((c_bit c 302 row) * ((c_bit c 238 row) + (c_bit c 238 row)))) + (c_bit c 45 row)) - ((((c_bit c 302 row) + (c_bit c 238 row)) - ((c_bit c 302 row) * ((c_bit c 238 row) + (c_bit c 238 row)))) * ((c_bit c 45 row) + (c_bit c 45 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_872_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_872 c row ↔ constraint_872 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_873 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 303 row) - (((((c_bit c 303 row) + (c_bit c 239 row)) - ((c_bit c 303 row) * ((c_bit c 239 row) + (c_bit c 239 row)))) + (c_bit c 46 row)) - ((((c_bit c 303 row) + (c_bit c 239 row)) - ((c_bit c 303 row) * ((c_bit c 239 row) + (c_bit c 239 row)))) * ((c_bit c 46 row) + (c_bit c 46 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_873_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_873 c row ↔ constraint_873 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_874 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 304 row) - (((((c_bit c 304 row) + (c_bit c 240 row)) - ((c_bit c 304 row) * ((c_bit c 240 row) + (c_bit c 240 row)))) + (c_bit c 47 row)) - ((((c_bit c 304 row) + (c_bit c 240 row)) - ((c_bit c 304 row) * ((c_bit c 240 row) + (c_bit c 240 row)))) * ((c_bit c 47 row) + (c_bit c 47 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_874_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_874 c row ↔ constraint_874 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_875 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 305 row) - (((((c_bit c 305 row) + (c_bit c 241 row)) - ((c_bit c 305 row) * ((c_bit c 241 row) + (c_bit c 241 row)))) + (c_bit c 48 row)) - ((((c_bit c 305 row) + (c_bit c 241 row)) - ((c_bit c 305 row) * ((c_bit c 241 row) + (c_bit c 241 row)))) * ((c_bit c 48 row) + (c_bit c 48 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_875_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_875 c row ↔ constraint_875 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_876 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 306 row) - (((((c_bit c 306 row) + (c_bit c 242 row)) - ((c_bit c 306 row) * ((c_bit c 242 row) + (c_bit c 242 row)))) + (c_bit c 49 row)) - ((((c_bit c 306 row) + (c_bit c 242 row)) - ((c_bit c 306 row) * ((c_bit c 242 row) + (c_bit c 242 row)))) * ((c_bit c 49 row) + (c_bit c 49 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_876_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_876 c row ↔ constraint_876 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_877 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 307 row) - (((((c_bit c 307 row) + (c_bit c 243 row)) - ((c_bit c 307 row) * ((c_bit c 243 row) + (c_bit c 243 row)))) + (c_bit c 50 row)) - ((((c_bit c 307 row) + (c_bit c 243 row)) - ((c_bit c 307 row) * ((c_bit c 243 row) + (c_bit c 243 row)))) * ((c_bit c 50 row) + (c_bit c 50 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_877_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_877 c row ↔ constraint_877 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_878 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 308 row) - (((((c_bit c 308 row) + (c_bit c 244 row)) - ((c_bit c 308 row) * ((c_bit c 244 row) + (c_bit c 244 row)))) + (c_bit c 51 row)) - ((((c_bit c 308 row) + (c_bit c 244 row)) - ((c_bit c 308 row) * ((c_bit c 244 row) + (c_bit c 244 row)))) * ((c_bit c 51 row) + (c_bit c 51 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_878_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_878 c row ↔ constraint_878 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_879 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 309 row) - (((((c_bit c 309 row) + (c_bit c 245 row)) - ((c_bit c 309 row) * ((c_bit c 245 row) + (c_bit c 245 row)))) + (c_bit c 52 row)) - ((((c_bit c 309 row) + (c_bit c 245 row)) - ((c_bit c 309 row) * ((c_bit c 245 row) + (c_bit c 245 row)))) * ((c_bit c 52 row) + (c_bit c 52 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_879_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_879 c row ↔ constraint_879 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_880 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 310 row) - (((((c_bit c 310 row) + (c_bit c 246 row)) - ((c_bit c 310 row) * ((c_bit c 246 row) + (c_bit c 246 row)))) + (c_bit c 53 row)) - ((((c_bit c 310 row) + (c_bit c 246 row)) - ((c_bit c 310 row) * ((c_bit c 246 row) + (c_bit c 246 row)))) * ((c_bit c 53 row) + (c_bit c 53 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_880_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_880 c row ↔ constraint_880 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_881 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 311 row) - (((((c_bit c 311 row) + (c_bit c 247 row)) - ((c_bit c 311 row) * ((c_bit c 247 row) + (c_bit c 247 row)))) + (c_bit c 54 row)) - ((((c_bit c 311 row) + (c_bit c 247 row)) - ((c_bit c 311 row) * ((c_bit c 247 row) + (c_bit c 247 row)))) * ((c_bit c 54 row) + (c_bit c 54 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_881_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_881 c row ↔ constraint_881 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_882 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 312 row) - (((((c_bit c 312 row) + (c_bit c 248 row)) - ((c_bit c 312 row) * ((c_bit c 248 row) + (c_bit c 248 row)))) + (c_bit c 55 row)) - ((((c_bit c 312 row) + (c_bit c 248 row)) - ((c_bit c 312 row) * ((c_bit c 248 row) + (c_bit c 248 row)))) * ((c_bit c 55 row) + (c_bit c 55 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_882_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_882 c row ↔ constraint_882 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_883 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 313 row) - (((((c_bit c 313 row) + (c_bit c 249 row)) - ((c_bit c 313 row) * ((c_bit c 249 row) + (c_bit c 249 row)))) + (c_bit c 56 row)) - ((((c_bit c 313 row) + (c_bit c 249 row)) - ((c_bit c 313 row) * ((c_bit c 249 row) + (c_bit c 249 row)))) * ((c_bit c 56 row) + (c_bit c 56 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_883_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_883 c row ↔ constraint_883 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_884 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 314 row) - (((((c_bit c 314 row) + (c_bit c 250 row)) - ((c_bit c 314 row) * ((c_bit c 250 row) + (c_bit c 250 row)))) + (c_bit c 57 row)) - ((((c_bit c 314 row) + (c_bit c 250 row)) - ((c_bit c 314 row) * ((c_bit c 250 row) + (c_bit c 250 row)))) * ((c_bit c 57 row) + (c_bit c 57 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_884_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_884 c row ↔ constraint_884 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_885 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 315 row) - (((((c_bit c 315 row) + (c_bit c 251 row)) - ((c_bit c 315 row) * ((c_bit c 251 row) + (c_bit c 251 row)))) + (c_bit c 58 row)) - ((((c_bit c 315 row) + (c_bit c 251 row)) - ((c_bit c 315 row) * ((c_bit c 251 row) + (c_bit c 251 row)))) * ((c_bit c 58 row) + (c_bit c 58 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_885_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_885 c row ↔ constraint_885 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_886 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 316 row) - (((((c_bit c 316 row) + (c_bit c 252 row)) - ((c_bit c 316 row) * ((c_bit c 252 row) + (c_bit c 252 row)))) + (c_bit c 59 row)) - ((((c_bit c 316 row) + (c_bit c 252 row)) - ((c_bit c 316 row) * ((c_bit c 252 row) + (c_bit c 252 row)))) * ((c_bit c 59 row) + (c_bit c 59 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_886_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_886 c row ↔ constraint_886 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_887 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 317 row) - (((((c_bit c 317 row) + (c_bit c 253 row)) - ((c_bit c 317 row) * ((c_bit c 253 row) + (c_bit c 253 row)))) + (c_bit c 60 row)) - ((((c_bit c 317 row) + (c_bit c 253 row)) - ((c_bit c 317 row) * ((c_bit c 253 row) + (c_bit c 253 row)))) * ((c_bit c 60 row) + (c_bit c 60 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_887_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_887 c row ↔ constraint_887 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_888 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 318 row) - (((((c_bit c 318 row) + (c_bit c 254 row)) - ((c_bit c 318 row) * ((c_bit c 254 row) + (c_bit c 254 row)))) + (c_bit c 61 row)) - ((((c_bit c 318 row) + (c_bit c 254 row)) - ((c_bit c 318 row) * ((c_bit c 254 row) + (c_bit c 254 row)))) * ((c_bit c 61 row) + (c_bit c 61 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_888_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_888 c row ↔ constraint_888 c row := by
    rfl

  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constraint_889 (c : C F ExtF) (row : ℕ) : Prop :=
    ((c_prime_bit c 319 row) - (((((c_bit c 319 row) + (c_bit c 255 row)) - ((c_bit c 319 row) * ((c_bit c 255 row) + (c_bit c 255 row)))) + (c_bit c 62 row)) - ((((c_bit c 319 row) + (c_bit c 255 row)) - ((c_bit c 319 row) * ((c_bit c 255 row) + (c_bit c 255 row)))) * ((c_bit c 62 row) + (c_bit c 62 row))))) = 0

  @[KeccakfPermAir_air_simplification]
  lemma constraint_889_of_extraction
    (c : C F ExtF) (row : ℕ)
  : KeccakfPermAir.extraction.constraint_889 c row ↔ constraint_889 c row := by
    rfl

end constraint_simplification

end KeccakfPermAir.constraints
