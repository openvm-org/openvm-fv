import LeanZKCircuit.OpenVM.Circuit
import OpenvmFv.Tactic.AssignColumn
import OpenvmFv.Tactic.RewriteColumnOfIsValid
import OpenvmFv.Tactic.SubcircuitIsValidOfIsValid

-- Note this is with NUM_LIMBS=4, LIMB_BITS=8

structure BaseAluCoreAir (F : Type) (ExtF : Type) where
  buses: (index: ℕ) -> List (F × List F)
  challenge: (index: ℕ) -> ExtF
  exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
  main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
  preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
  public_values: (index: ℕ) -> F
  last_row: ℕ

  a_0 (row : ℕ) (rotation : ℕ) : F
  a_1 (row : ℕ) (rotation : ℕ) : F
  a_2 (row : ℕ) (rotation : ℕ) : F
  a_3 (row : ℕ) (rotation : ℕ) : F
  b_0 (row : ℕ) (rotation : ℕ) : F
  b_1 (row : ℕ) (rotation : ℕ) : F
  b_2 (row : ℕ) (rotation : ℕ) : F
  b_3 (row : ℕ) (rotation : ℕ) : F
  c_0 (row : ℕ) (rotation : ℕ) : F
  c_1 (row : ℕ) (rotation : ℕ) : F
  c_2 (row : ℕ) (rotation : ℕ) : F
  c_3 (row : ℕ) (rotation : ℕ) : F
  opcode_add_flag (row : ℕ) (rotation : ℕ) : F
  opcode_sub_flag (row : ℕ) (rotation : ℕ) : F
  opcode_xor_flag (row : ℕ) (rotation : ℕ) : F
  opcode_or_flag (row : ℕ) (rotation : ℕ) : F
  opcode_and_flag (row : ℕ) (rotation : ℕ) : F

instance [Field F] [Field ExtF] : Circuit F ExtF BaseAluCoreAir where
  buses := BaseAluCoreAir.buses
  challenge := BaseAluCoreAir.challenge
  exposed := BaseAluCoreAir.exposed
  main := BaseAluCoreAir.main
  permutation := BaseAluCoreAir.permutation
  preprocessed := BaseAluCoreAir.preprocessed
  public_values := BaseAluCoreAir.public_values
  last_row := BaseAluCoreAir.last_row


#assign_column "BaseAluCoreAir" 0 "a_0"
#assign_column "BaseAluCoreAir" 1 "a_1"
#assign_column "BaseAluCoreAir" 2 "a_2"
#assign_column "BaseAluCoreAir" 3 "a_3"
#assign_column "BaseAluCoreAir" 4 "b_0"
#assign_column "BaseAluCoreAir" 5 "b_1"
#assign_column "BaseAluCoreAir" 6 "b_2"
#assign_column "BaseAluCoreAir" 7 "b_3"
#assign_column "BaseAluCoreAir" 8 "c_0"
#assign_column "BaseAluCoreAir" 9 "c_1"
#assign_column "BaseAluCoreAir" 10 "c_2"
#assign_column "BaseAluCoreAir" 11 "c_3"
#assign_column "BaseAluCoreAir" 12 "opcode_add_flag"
#assign_column "BaseAluCoreAir" 13 "opcode_sub_flag"
#assign_column "BaseAluCoreAir" 14 "opcode_xor_flag"
#assign_column "BaseAluCoreAir" 15 "opcode_or_flag"
#assign_column "BaseAluCoreAir" 16 "opcode_and_flag"

def BaseAluCoreAir.isValid [Field F] [Field ExtF]
  (c : BaseAluCoreAir F ExtF) : Prop :=
    true ∧
    ∀ row rotation,
      c.col_0 row rotation ∧
      c.col_1 row rotation ∧
      c.col_2 row rotation ∧
      c.col_3 row rotation ∧
      c.col_4 row rotation ∧
      c.col_5 row rotation ∧
      c.col_6 row rotation ∧
      c.col_7 row rotation ∧
      c.col_8 row rotation ∧
      c.col_9 row rotation ∧
      c.col_10 row rotation ∧
      c.col_11 row rotation ∧
      c.col_12 row rotation ∧
      c.col_13 row rotation ∧
      c.col_14 row rotation ∧
      c.col_15 row rotation ∧
      c.col_16 row rotation ∧
      true

#rewrite_column_of_isValid "BaseAluCoreAir" 0 "a_0"
#rewrite_column_of_isValid "BaseAluCoreAir" 1 "a_1"
#rewrite_column_of_isValid "BaseAluCoreAir" 2 "a_2"
#rewrite_column_of_isValid "BaseAluCoreAir" 3 "a_3"
#rewrite_column_of_isValid "BaseAluCoreAir" 4 "b_0"
#rewrite_column_of_isValid "BaseAluCoreAir" 5 "b_1"
#rewrite_column_of_isValid "BaseAluCoreAir" 6 "b_2"
#rewrite_column_of_isValid "BaseAluCoreAir" 7 "b_3"
#rewrite_column_of_isValid "BaseAluCoreAir" 8 "c_0"
#rewrite_column_of_isValid "BaseAluCoreAir" 9 "c_1"
#rewrite_column_of_isValid "BaseAluCoreAir" 10 "c_2"
#rewrite_column_of_isValid "BaseAluCoreAir" 11 "c_3"
#rewrite_column_of_isValid "BaseAluCoreAir" 12 "opcode_add_flag"
#rewrite_column_of_isValid "BaseAluCoreAir" 13 "opcode_sub_flag"
#rewrite_column_of_isValid "BaseAluCoreAir" 14 "opcode_xor_flag"
#rewrite_column_of_isValid "BaseAluCoreAir" 15 "opcode_or_flag"
#rewrite_column_of_isValid "BaseAluCoreAir" 16 "opcode_and_flag"

abbrev Valid_BaseAluCoreAir (F : Type) [Field F] (ExtF : Type) [Field ExtF] := { c: BaseAluCoreAir F ExtF // c.isValid }
abbrev Valid_BaseAluCoreAir.main [Field F] [Field ExtF] (c: Valid_BaseAluCoreAir F ExtF) (id column row rotation : ℕ) := c.1.main id column row rotation
