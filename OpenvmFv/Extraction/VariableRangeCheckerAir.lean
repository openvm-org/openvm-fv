import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr VariableRangeCheckerAir_air_simplification
register_simp_attr VariableRangeCheckerAir_constraint_and_interaction_simplification

namespace VariableRangeCheckerAir.extraction

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isFirstRow c row) * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isFirstRow c row) * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isFirstRow c row) * ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isTransitionRow c row) * (((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))) * (((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))) - 1))) = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isTransitionRow c row) * ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) * ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) - ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + 1)))) = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isTransitionRow c row) * ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 1)) - ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * (1 + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) - (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))))))) = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isTransitionRow c row) * ((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0))) + 1) - ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) + (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 1))))) = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isLastRow c row) * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isLastRow c row) * ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - 18)) = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isLastRow c row) * (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))) = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 4 then (List.range (Circuit.last_row c + 1)).flatMap (λ row => [(-((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))), [(Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)), (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))])])
    else []

end VariableRangeCheckerAir.extraction
