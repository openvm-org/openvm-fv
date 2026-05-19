import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Extraction.KeccakfPermAir

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## Bus-7 Row Definition (Keccak State Bus)

Each row contributes two bus entries (pre-state and post-state), gated by
`export_flag`. The multiplicity is `-(export_flag)`.
-/

section bus_definition
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  /-- Pre-state bus payload: [0, timestamp, preimage[0], ..., preimage[99]] -/
  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def keccakStateBus_pre_entry (c : C F ExtF) (row : ℕ) : F × List F :=
    (-(export_flag c row),
     [0,
      timestamp c row,
      preimage c 0 row, preimage c 1 row, preimage c 2 row, preimage c 3 row,
      preimage c 4 row, preimage c 5 row, preimage c 6 row, preimage c 7 row,
      preimage c 8 row, preimage c 9 row, preimage c 10 row, preimage c 11 row,
      preimage c 12 row, preimage c 13 row, preimage c 14 row, preimage c 15 row,
      preimage c 16 row, preimage c 17 row, preimage c 18 row, preimage c 19 row,
      preimage c 20 row, preimage c 21 row, preimage c 22 row, preimage c 23 row,
      preimage c 24 row, preimage c 25 row, preimage c 26 row, preimage c 27 row,
      preimage c 28 row, preimage c 29 row, preimage c 30 row, preimage c 31 row,
      preimage c 32 row, preimage c 33 row, preimage c 34 row, preimage c 35 row,
      preimage c 36 row, preimage c 37 row, preimage c 38 row, preimage c 39 row,
      preimage c 40 row, preimage c 41 row, preimage c 42 row, preimage c 43 row,
      preimage c 44 row, preimage c 45 row, preimage c 46 row, preimage c 47 row,
      preimage c 48 row, preimage c 49 row, preimage c 50 row, preimage c 51 row,
      preimage c 52 row, preimage c 53 row, preimage c 54 row, preimage c 55 row,
      preimage c 56 row, preimage c 57 row, preimage c 58 row, preimage c 59 row,
      preimage c 60 row, preimage c 61 row, preimage c 62 row, preimage c 63 row,
      preimage c 64 row, preimage c 65 row, preimage c 66 row, preimage c 67 row,
      preimage c 68 row, preimage c 69 row, preimage c 70 row, preimage c 71 row,
      preimage c 72 row, preimage c 73 row, preimage c 74 row, preimage c 75 row,
      preimage c 76 row, preimage c 77 row, preimage c 78 row, preimage c 79 row,
      preimage c 80 row, preimage c 81 row, preimage c 82 row, preimage c 83 row,
      preimage c 84 row, preimage c 85 row, preimage c 86 row, preimage c 87 row,
      preimage c 88 row, preimage c 89 row, preimage c 90 row, preimage c 91 row,
      preimage c 92 row, preimage c 93 row, preimage c 94 row, preimage c 95 row,
      preimage c 96 row, preimage c 97 row, preimage c 98 row, preimage c 99 row])

  /-- Post-state bus payload: [1, timestamp, a_ppp_00_limb[0..3], a_prime_prime[4..99]] -/
  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def keccakStateBus_post_entry (c : C F ExtF) (row : ℕ) : F × List F :=
    (-(export_flag c row),
     [1,
      timestamp c row,
      a_ppp_00_limb c 0 row, a_ppp_00_limb c 1 row,
      a_ppp_00_limb c 2 row, a_ppp_00_limb c 3 row,
      a_prime_prime c 4 row, a_prime_prime c 5 row,
      a_prime_prime c 6 row, a_prime_prime c 7 row,
      a_prime_prime c 8 row, a_prime_prime c 9 row,
      a_prime_prime c 10 row, a_prime_prime c 11 row,
      a_prime_prime c 12 row, a_prime_prime c 13 row,
      a_prime_prime c 14 row, a_prime_prime c 15 row,
      a_prime_prime c 16 row, a_prime_prime c 17 row,
      a_prime_prime c 18 row, a_prime_prime c 19 row,
      a_prime_prime c 20 row, a_prime_prime c 21 row,
      a_prime_prime c 22 row, a_prime_prime c 23 row,
      a_prime_prime c 24 row, a_prime_prime c 25 row,
      a_prime_prime c 26 row, a_prime_prime c 27 row,
      a_prime_prime c 28 row, a_prime_prime c 29 row,
      a_prime_prime c 30 row, a_prime_prime c 31 row,
      a_prime_prime c 32 row, a_prime_prime c 33 row,
      a_prime_prime c 34 row, a_prime_prime c 35 row,
      a_prime_prime c 36 row, a_prime_prime c 37 row,
      a_prime_prime c 38 row, a_prime_prime c 39 row,
      a_prime_prime c 40 row, a_prime_prime c 41 row,
      a_prime_prime c 42 row, a_prime_prime c 43 row,
      a_prime_prime c 44 row, a_prime_prime c 45 row,
      a_prime_prime c 46 row, a_prime_prime c 47 row,
      a_prime_prime c 48 row, a_prime_prime c 49 row,
      a_prime_prime c 50 row, a_prime_prime c 51 row,
      a_prime_prime c 52 row, a_prime_prime c 53 row,
      a_prime_prime c 54 row, a_prime_prime c 55 row,
      a_prime_prime c 56 row, a_prime_prime c 57 row,
      a_prime_prime c 58 row, a_prime_prime c 59 row,
      a_prime_prime c 60 row, a_prime_prime c 61 row,
      a_prime_prime c 62 row, a_prime_prime c 63 row,
      a_prime_prime c 64 row, a_prime_prime c 65 row,
      a_prime_prime c 66 row, a_prime_prime c 67 row,
      a_prime_prime c 68 row, a_prime_prime c 69 row,
      a_prime_prime c 70 row, a_prime_prime c 71 row,
      a_prime_prime c 72 row, a_prime_prime c 73 row,
      a_prime_prime c 74 row, a_prime_prime c 75 row,
      a_prime_prime c 76 row, a_prime_prime c 77 row,
      a_prime_prime c 78 row, a_prime_prime c 79 row,
      a_prime_prime c 80 row, a_prime_prime c 81 row,
      a_prime_prime c 82 row, a_prime_prime c 83 row,
      a_prime_prime c 84 row, a_prime_prime c 85 row,
      a_prime_prime c 86 row, a_prime_prime c 87 row,
      a_prime_prime c 88 row, a_prime_prime c 89 row,
      a_prime_prime c 90 row, a_prime_prime c 91 row,
      a_prime_prime c 92 row, a_prime_prime c 93 row,
      a_prime_prime c 94 row, a_prime_prime c 95 row,
      a_prime_prime c 96 row, a_prime_prime c 97 row,
      a_prime_prime c 98 row, a_prime_prime c 99 row])

  /-- Full bus-7 row: pre-state + post-state entries. -/
  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def bus_7Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
    [keccakStateBus_pre_entry c row, keccakStateBus_post_entry c row]

  /-- Simplified constrain_interactions: bus 7 is the only bus. -/
  @[KeccakfPermAir_constraint_and_interaction_simplification]
  def constrain_interactions (c : C F ExtF) : Prop :=
    Circuit.buses c = fun index =>
      if index = 7 then (List.range (Circuit.last_row c + 1)).flatMap (bus_7Bus_row c)
      else []

end bus_definition

/-! ## Bus Bridge Lemma

The extraction's `constrain_interactions` and the simplified `constrain_interactions`
are definitionally equal because all column abbreviations are `abbrev` (reducible).
This lemma extracts bus index 7 from the function extensionality in the hypothesis.
-/

section bus_bridge
  variable {F ExtF : Type} [Field F] [Field ExtF]

  /-- The extraction's constrain_interactions implies bus 7 uses our semantic bus_7Bus_row.
      Uses `air.1` (the `Raw_KeccakfPermAir`) which has the `Circuit` instance. -/
  lemma constrain_keccakState_interactions
      (air : Valid_KeccakfPermAir F ExtF)
      (h : KeccakfPermAir.extraction.constrain_interactions air.1)
    : air.1.buses 7 = (List.range (air.1.last_row + 1)).flatMap (bus_7Bus_row air.1) := by
    unfold KeccakfPermAir.extraction.constrain_interactions at h
    exact congrFun h 7

end bus_bridge

end KeccakfPermAir.constraints
