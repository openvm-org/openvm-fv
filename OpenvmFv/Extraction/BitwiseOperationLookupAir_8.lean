import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr BitwiseOperationLookupAir_8_air_simplification
register_simp_attr BitwiseOperationLookupAir_8_constraint_and_interaction_simplification

namespace BitwiseOperationLookupAir_8.extraction

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) - 1)) = 0

  @[simp]
  def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isTransitionRow c row) * ((((((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)) + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 1)) * 2)) + ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 1)) * 4)) + ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 1)) * 8)) + ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 1)) * 16)) + ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 1)) * 32)) + ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 1)) * 64)) + ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 1)) * 128)) * 256) + ((((((((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 1)) + ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 1)) * 2)) + ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 1)) * 4)) + ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 1)) * 8)) + ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 1)) * 16)) + ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 1)) * 32)) + ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 1)) * 64)) + ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 1)) * 128))) - ((((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)) * 256) + ((((((((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)))) - 1)) = 0

  @[simp]
  def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isFirstRow c row) * ((((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)) * 256) + ((((((((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)))) = 0

  @[simp]
  def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.isLastRow c row) * (((((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)) * 256) + ((((((((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128))) - 65535)) = 0

  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.buses c = λ index =>
      if index = 9 then (List.range (Circuit.last_row c + 1)).flatMap (λ row => [(-((Circuit.main c (id := 0) (column := 16) (row := row) (rotation := 0))), [((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)), ((((((((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)), 0, 0]), (-((Circuit.main c (id := 0) (column := 17) (row := row) (rotation := 0))), [((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) * 128)), ((((((((Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)) * 128)), ((((((((((Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 8) (row := row) (rotation := 0)))) + ((((Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 9) (row := row) (rotation := 0)))) * 2)) + ((((Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 2) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 10) (row := row) (rotation := 0)))) * 4)) + ((((Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 3) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 11) (row := row) (rotation := 0)))) * 8)) + ((((Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 4) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 12) (row := row) (rotation := 0)))) * 16)) + ((((Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 5) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 13) (row := row) (rotation := 0)))) * 32)) + ((((Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 6) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 14) (row := row) (rotation := 0)))) * 64)) + ((((Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0)) + (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0))) - ((2 * (Circuit.main c (id := 0) (column := 7) (row := row) (rotation := 0))) * (Circuit.main c (id := 0) (column := 15) (row := row) (rotation := 0)))) * 128)), 1])])
      else []

end BitwiseOperationLookupAir_8.extraction
