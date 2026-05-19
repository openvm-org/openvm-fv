import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

/-!
# XorinVmAir Column Definitions

Manual AIR definition for XorinVmAir (914 main trace columns).
The standard `#define_air` macro hits Lean's recursion depth limit with this many
columns, so we define the raw structure, Circuit instance, validity predicate,
and Valid abbreviation by hand.

The column-assignment validity uses a universally quantified form instead of a
914-fold conjunction, which avoids deep recursion in proofs and type-checking.
-/

-- Subair: generic column accessor wrapping 914 main-trace columns
structure Raw_XorinVmAirCols (F : Type) where
  columns (column : ℕ) (row : ℕ) (rotation : ℕ) : F

def Raw_XorinVmAirCols.isValid {F} (_c : Raw_XorinVmAirCols F) : Prop := True

abbrev Valid_XorinVmAirCols (F : Type) :=
  { c : Raw_XorinVmAirCols F // c.isValid }

abbrev Valid_XorinVmAirCols.columns {F}
  (c : Valid_XorinVmAirCols F) :=
  c.1.columns

-- Raw AIR structure
structure Raw_XorinVmAir (F : Type) (ExtF : Type) where
  buses (index : ℕ) : List (F × List F)
  challenge (index : ℕ) : ExtF
  exposed (index : ℕ) : ExtF
  main (id : ℕ) (column : ℕ) (row : ℕ) (rotation : ℕ) : F
  permutation (column : ℕ) (row : ℕ) (rotation : ℕ) : ExtF
  preprocessed (column : ℕ) (row : ℕ) (rotation : ℕ) : F
  public_values (index : ℕ) : F
  last_row : ℕ
  main_cols : Raw_XorinVmAirCols F

-- Circuit instance for Raw_XorinVmAir
instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF (Raw_XorinVmAir) where
  buses := Raw_XorinVmAir.buses
  challenge := Raw_XorinVmAir.challenge
  exposed := Raw_XorinVmAir.exposed
  main := Raw_XorinVmAir.main
  permutation := Raw_XorinVmAir.permutation
  preprocessed := Raw_XorinVmAir.preprocessed
  public_values := Raw_XorinVmAir.public_values
  last_row := Raw_XorinVmAir.last_row

-- Validity: subair is valid and all 914 main-trace columns route through main_cols
def Raw_XorinVmAir.isValid {F ExtF}
  (c : Raw_XorinVmAir F ExtF)
: Prop :=
  c.main_cols.isValid ∧
  (∀ col row rotation, col < 914 →
    c.main (id := 0) (column := col) (row := row) (rotation := rotation) =
    c.main_cols.columns (column := col) (row := row) (rotation := rotation))

-- Valid AIR abbreviation (subtype of Raw with isValid proof)
abbrev Valid_XorinVmAir (F : Type) (ExtF : Type) :=
  { c : Raw_XorinVmAir F ExtF // c.isValid }

-- Projections for Valid_XorinVmAir
abbrev Valid_XorinVmAir.buses {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.buses
abbrev Valid_XorinVmAir.challenge {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.challenge
abbrev Valid_XorinVmAir.exposed {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.exposed
abbrev Valid_XorinVmAir.main {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.main
abbrev Valid_XorinVmAir.permutation {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.permutation
abbrev Valid_XorinVmAir.preprocessed {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.preprocessed
abbrev Valid_XorinVmAir.public_values {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.public_values
abbrev Valid_XorinVmAir.last_row {F ExtF} (c : Valid_XorinVmAir F ExtF) := c.1.last_row

def Valid_XorinVmAir.main_cols {F ExtF}
  (c : Valid_XorinVmAir F ExtF)
: Valid_XorinVmAirCols F := ⟨
  c.1.main_cols,
  c.2.1
⟩

-- Circuit instance for Valid_XorinVmAir
instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF (Valid_XorinVmAir) where
  buses := Valid_XorinVmAir.buses
  challenge := Valid_XorinVmAir.challenge
  exposed := Valid_XorinVmAir.exposed
  main := Valid_XorinVmAir.main
  permutation := Valid_XorinVmAir.permutation
  preprocessed := Valid_XorinVmAir.preprocessed
  public_values := Valid_XorinVmAir.public_values
  last_row := Valid_XorinVmAir.last_row
