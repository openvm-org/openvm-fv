import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

namespace MemoryDummAir_1.extraction

-- def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
--   (((Circuit.permutation c (column := 0) (row := row) (rotation := 0)) * ((((((0 + (1 * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)))) + ((1 * (Circuit.challenge c (index := 1))) * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)))) + (((1 * (Circuit.challenge c (index := 1))) * (Circuit.challenge c (index := 1))) * (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)))) + ((((1 * (Circuit.challenge c (index := 1))) * (Circuit.challenge c (index := 1))) * (Circuit.challenge c (index := 1))) * (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)))) + (((((1 * (Circuit.challenge c (index := 1))) * (Circuit.challenge c (index := 1))) * (Circuit.challenge c (index := 1))) * (Circuit.challenge c (index := 1))) * 2)) + (Circuit.challenge c (index := 0)))) - (0 + (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)))) = 0

-- def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
--   ((((Circuit.permutation c (column := 1) (row := row) (rotation := 1)) - (Circuit.permutation c (column := 1) (row := row) (rotation := 0))) - (0 + (Circuit.permutation c (column := 0) (row := row) (rotation := 1)))) * (Circuit.isTransitionRow c row)) = 0

-- def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
--   (((Circuit.permutation c (column := 1) (row := row) (rotation := 0)) - (0 + (Circuit.permutation c (column := 0) (row := row) (rotation := 0)))) * (Circuit.isFirstRow c row)) = 0

-- def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
--   (((Circuit.permutation c (column := 1) (row := row) (rotation := 0)) - (Circuitc.exposed c (index := 0))) * (Circuit.isLastRow c row)) = 0

def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.buses c = λ index =>
    if index = 1 then ([].append ((List.range (Circuit.last_row c + 1)).map (λ row => ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)),[(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))]))))
    else []

end MemoryDummAir_1.extraction
