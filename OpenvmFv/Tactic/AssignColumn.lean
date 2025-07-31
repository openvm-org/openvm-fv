import Mathlib

import OpenvmFv.Tactic.SubcircuitIsValidOfIsValid
import OpenvmFv.Tactic.RewriteColumnOfIsValid

open Lean Parser
set_option hygiene false in
elab "#assign_column" circuit:str col:num member:str : command => do
  let circuit_type : String := s!"{circuit.getString} F ExtF"
  -- logInfo m!"Circuit type: {circuit_type}"
  let .ok circuit_type_stx := runParserCategory (← getEnv) `term circuit_type
    | throwError "Failed to parse the circuit type"
  let circuit_type_tstx : TSyntax `term := ⟨circuit_type_stx⟩

  let member_term : String := s!"c.{member.getString}"
  -- logInfo m!"Member term: {member_term}"
  let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
    | throwError "Failed to parse the member term"
  let member_term_tstx : TSyntax `term := ⟨member_term_stx⟩

  let col_num : String := s!"{col.getNat}"
  -- logInfo m!"Column number: {col_num}"
  let .ok col_num_stx := runParserCategory (← getEnv) `term col_num
    | throwError "Failed to parse the column number"
  let col_num_tstx : TSyntax `term := ⟨col_num_stx⟩

  let uniqueName := mkIdent (Name.mkStr2 circuit.getString s!"col_{col.getNat}")
  -- logInfo m!"Registering: {uniqueName.getId}"
  Lean.Elab.Command.elabCommand
    (←`(
      @[openvm_encapsulation]
      def $uniqueName
        (c: $circuit_type_tstx) (row : ℕ) (rotation : ℕ) : Prop :=
          c.main (id := 0) (column := $col_num_tstx) (row := row) (rotation := rotation) =
          $member_term_tstx (row := row) (rotation := rotation)
    ))


-- syntax column := "[" num "," str "]"
-- syntax subair := "SubAir[" str ":" str "width" ":=" num "]"
-- syntax columnEntry := "Column[" str "]"

syntax entry := orelse("Column[" str "]", "SubAir[" str ":" str "width" ":=" num "]")

-- def run_assign_column (circuitName: TSyntax `str) (head: TSyntax `column): Elab.Command.CommandElabM Unit := do
--   match head with
--     | `(column| [$col, $member]) => Lean.Elab.Command.elabCommand (←`(#assign_column $circuitName $col $member))
--     | _ => throwError "Nooooooooooooooooooo"



def isValid_subair (head: TSyntax `str): Elab.Command.CommandElabM (TSyntax `term) := do
  let member_term : String := s!"c.{head.getString}.isValid"
  let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
    | throwError "Failed to parse a subair for isValid"
  let member_term_tstx : TSyntax `term := ⟨member_term_stx⟩
  pure (member_term_tstx)

-- def run_rewrite_column_of_isValid (circuitName: TSyntax `str) (head: TSyntax `column): Elab.Command.CommandElabM Unit := do
--   match head with
--     | `(column| [$col, $member]) => Lean.Elab.Command.elabCommand (←`(#rewrite_column_of_isValid $circuitName $col $member))
--     | _ => throwError "Nooooooooooooooooooo"

def add_structure_field (struct_string: String) (subair: TSyntax `entry) : Elab.Command.CommandElabM String := do
  logInfo m!"{subair}"
  match subair with
    | `(entry| SubAir[$name:str : $typeName:str width := $_:num]) => return s!"{struct_string}\n        {name.getString} : {typeName.getString} F ExtF"
    | _ =>
      match subair with
        | `(entry| Column[$name]) => return s!"{struct_string}\n        {name.getString} (row: ℕ) (rotation: ℕ) : F"
        | _ => throwError "failed to add struct field"

-- def add_subair_width (width: ℕ) (subair: TSyntax `subair) : Elab.Command.CommandElabM ℕ := do
--   match subair with
--     | `(subair| SubAir[$_ : $_ width := $w]) => return width + w.getNat
--     | _ => throwError "failed to sum subair width"

def add_isValid_subair (subair: TSyntax `entry) (isValid_string: String) : Elab.Command.CommandElabM String := do
  match subair with
    | `(entry| SubAir[$name:str : $_:str width := $_:num]) => return s!"c.{name.getString}.isValid ∧ {isValid_string}"
    | _ => match subair with
      | `(entry| Column[$_]) => return isValid_string
      | _ => throwError "failed to add subair to isValid"

-- def add_isValid_column (column: TSyntax `column) (isValid_string: String) : Elab.Command.CommandElabM String := do
--   match column with
--     | `(column| [$pos, $_]) => return s!"c.col_{pos.getNat} row rotation ∧ {isValid_string}"
--     | _ => throwError "failed to add column to isValid"

def run_subcircuit_isValid_for_subair (circuit : String) (idx: ℕ) (subair: TSyntax `entry) : Elab.Command.CommandElabM Unit := do
  match subair with
    | `(entry| SubAir[$name:str : $_:str width := $_:num]) => run_subcircuit_isValid_of_isValid circuit idx name.getString
    | _ => match subair with
      | `(entry| Column[$_]) => pure ()
      | _ => throwError "failed to run subcircuit_isValid_of_isValid for subair"

def create_projection_lemma (circuit: String) (member: String) : Elab.Command.CommandElabM Unit := do
  let .ok lemma_stx := runParserCategory (← getEnv) `command s!"
    @[openvm_encapsulation] lemma {circuit}_{member}_project (c: {circuit} F ExtF) [Field F] [Field ExtF] :
      @Circuit.{member} F (by assumption) ExtF (by assumption) {circuit} _ c = c.{member} := rfl"
    | throwError "Failed to parse circuit type"
  let lemma_tstx: TSyntax `command := ⟨lemma_stx⟩

  logInfo m!"{lemma_tstx}"

  Lean.Elab.Command.elabCommand lemma_tstx

def define_valid_circuit (circuit: String) : Elab.Command.CommandElabM Unit := do
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit} (F : Type) (ExtF : Type) := {"{"} c: {circuit} F ExtF // c.isValid {"}"}"
    | throwError "Failed to parse valid circuit abbrev"
  logInfo m!"{abbrev_stx}"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩

  Lean.Elab.Command.elabCommand abbrev_tstx

def define_valid_circuit_members (circuit: String) : Elab.Command.CommandElabM Unit := do
  --buses
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.buses (c: Valid_{circuit} F ExtF) (index: ℕ) := c.1.buses index"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  --challenge
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.challenge (c: Valid_{circuit} F ExtF) (index: ℕ) := c.1.challenge index"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  --exposed
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.exposed (c: Valid_{circuit} F ExtF) (index: ℕ) := c.1.exposed index"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  -- main
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.main (c: Valid_{circuit} F ExtF) (id column row rotation: ℕ) := c.1.main id column row rotation"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  -- permutation
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.permutation (c: Valid_{circuit} F ExtF) (column row rotation: ℕ) := c.1.permutation column row rotation"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  --preprocessed
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.preprocessed (c: Valid_{circuit} F ExtF) (column row rotation: ℕ) := c.1.preprocessed column row rotation"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  --public_values
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.public_values (c: Valid_{circuit} F ExtF) (index: ℕ) := c.1.public_values index"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx
  --last_row
  let .ok abbrev_stx := runParserCategory (← getEnv) `command
    s!"abbrev Valid_{circuit}.last_row (c: Valid_{circuit} F ExtF) := c.1.last_row"
    | throwError "Failed to parse valid circuit member abbrev"
  let abbrev_tstx: TSyntax `command := ⟨abbrev_stx⟩
  Lean.Elab.Command.elabCommand abbrev_tstx

def define_valid_circuit_subair (circuit: String) (subair: TSyntax `entry) : Elab.Command.CommandElabM Unit := do
  match subair with
    | `(entry| SubAir[$name:str : $typeName:str width := $_:num]) =>
      let .ok def_stx := runParserCategory (← getEnv) `command
        s!"def Valid_{circuit}.{name.getString} (c: Valid_{circuit} F ExtF) : Valid_{typeName.getString} F ExtF := ⟨c.1.{name.getString}, c.1.subcircuit_{name.getString}_isValid_of_isValid c.2⟩"
        | throwError "Failed to parse valid circuit member validity def"
      logInfo m!"{def_stx}"
      let def_tstx: TSyntax `command := ⟨def_stx⟩
      Lean.Elab.Command.elabCommand def_tstx
    | _ => match subair with
      | `(entry| Column[$name]) =>
        let .ok def_stx := runParserCategory (← getEnv) `command
          s!"def Valid_{circuit}.{name.getString} (c: Valid_{circuit} F ExtF) (row rotation: ℕ) : F := c.1.{name.getString} row rotation"
          | throwError "Failed to parse valid circuit member validity def"
        logInfo m!"{def_stx}"
        let def_tstx: TSyntax `command := ⟨def_stx⟩
        Lean.Elab.Command.elabCommand def_tstx
      | _ => throwError "failed to run subcircuit_isValid_of_isValid for subair"

def prove_valid_circuit_column_assignment (circuit: String) (pos: ℕ) (member: String) : Elab.Command.CommandElabM Unit := do
    let index := transformIndex pos
    let .ok lemma_stx := runParserCategory (← getEnv) `command
      s!"@[openvm_encapsulation] lemma Valid_{circuit}.col_{pos} [Field F] [Field ExtF] (c : Valid_{circuit} F ExtF) (row rotation: ℕ) : c.main 0 {pos} row rotation = c.{member} row rotation := (c.2.2 row rotation){index}"
      | throwError "Failed to parse valid circuit column proof"
    logInfo m!"{lemma_stx}"
    let lemma_tstx: TSyntax `command := ⟨lemma_stx⟩
    Lean.Elab.Command.elabCommand lemma_tstx

def calculate_column_assignments (offset: ℕ) (entry : TSyntax `entry) : Elab.Command.CommandElabM (List (ℕ × String)) := do
  match entry with
    | `(entry| SubAir[$name:str : $_:str width := $w:num]) =>
      return (
          List.range w.getNat
        ).map λ index => (offset + index, s!"{name.getString}.main (id := 0) (column := {index})")
    | _ => match entry with
      | `(entry| Column[$name]) =>
      return [(offset, name.getString)]
      | _ => throwError "failed to parse subair"

def calculate_all_column_assignments (entries: TSyntaxArray `entry) : Elab.Command.CommandElabM (List (ℕ × String)) := do
  let assignments: ℕ × List (ℕ × String) := ←(entries.foldlM (λ (acc: ℕ × List (ℕ × String)) (x: TSyntax `entry) => do
    let assignments := ←(calculate_column_assignments acc.1 x)

    match x with
      | `(entry| SubAir[$_:str : $_:str width := $w:num]) =>
        return (acc.1 + w.getNat, acc.2.append assignments)
      | _ => match x with
        | `(entry| Column[$_]) =>
        return (acc.1 + 1, acc.2.append assignments)
        | _ => throwError ""
  ) (0, []))

  pure (assignments.2)

open Lean Parser
set_option hygiene false in
elab "#assign_columns" circuitName: str subairs: entry* : command => do

  let column_assignments : List (ℕ × String) := ←(calculate_all_column_assignments subairs)
  logInfo m!"{column_assignments}"

  -- Create struct
  let base_structure_string : String := s!"structure {circuitName.getString} (F: Type) (ExtF : Type) where
        buses: (index: ℕ) -> List (F × List F)
        challenge: (index: ℕ) -> ExtF
        exposed: (index: ℕ) -> ExtF -- TODO should this be ExtF?,
        main: (id: ℕ) -> (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
        permutation: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> ExtF
        preprocessed: (column: ℕ) -> (row: ℕ) -> (rotation: ℕ) -> F
        public_values: (index: ℕ) -> F
        last_row: ℕ"

  let structure_string: String := ←(Array.foldlM add_structure_field base_structure_string subairs)
  logInfo m!"{structure_string}"
  let .ok structure_command_stx := runParserCategory (← getEnv) `command structure_string
    | throwError "Failed to parse structure creation commmand"
  let structure_command_tstx : TSyntax `command := ⟨structure_command_stx⟩
  Lean.Elab.Command.elabCommand structure_command_tstx

  -- Create instance
  let instance_string : String := s!"instance [Field F] [Field ExtF] : Circuit F ExtF {circuitName.getString} where
      buses := {circuitName.getString}.buses
      challenge := {circuitName.getString}.challenge
      exposed := {circuitName.getString}.exposed
      main := {circuitName.getString}.main
      permutation := {circuitName.getString}.permutation
      preprocessed := {circuitName.getString}.preprocessed
      public_values := {circuitName.getString}.public_values
      last_row := {circuitName.getString}.last_row"
  logInfo m!"{instance_string}"

  let .ok instance_command_stx := runParserCategory (← getEnv) `command instance_string
    | throwError "Failed to parse instance creation commmand"
  let instance_command_tstx : TSyntax `command := ⟨instance_command_stx⟩
  Lean.Elab.Command.elabCommand instance_command_tstx

  create_projection_lemma circuitName.getString "buses"
  create_projection_lemma circuitName.getString "challenge"
  create_projection_lemma circuitName.getString "exposed"
  create_projection_lemma circuitName.getString "main"
  create_projection_lemma circuitName.getString "permutation"
  create_projection_lemma circuitName.getString "preprocessed"
  create_projection_lemma circuitName.getString "public_values"
  create_projection_lemma circuitName.getString "last_row"

  -- Assign columns of main trace to struct member columns and subair columns
  discard (column_assignments.mapM (λ assignment => do
    let col := assignment.1
    let member := assignment.2
    let circuit_type : String := s!"{circuitName.getString} F ExtF"
    logInfo m!"Circuit type: {circuit_type}"
    let .ok circuit_type_stx := runParserCategory (← getEnv) `term circuit_type
      | throwError "Failed to parse the circuit type"
    let circuit_type_tstx : TSyntax `term := ⟨circuit_type_stx⟩

    let member_term : String := s!"c.{member}"
    logInfo m!"Member term: {member_term}"
    let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
      | throwError "Failed to parse the member term"
    let member_term_tstx : TSyntax `term := ⟨member_term_stx⟩

    let col_num : String := s!"{col}"
    logInfo m!"Column number: {col_num}"
    let .ok col_num_stx := runParserCategory (← getEnv) `term col_num
      | throwError "Failed to parse the column number"
    let col_num_tstx : TSyntax `term := ⟨col_num_stx⟩

    let uniqueName := mkIdent (Name.mkStr2 circuitName.getString s!"col_{col}")
    logInfo m!"Registering: {uniqueName.getId}"
    Lean.Elab.Command.elabCommand
      (←`(
        @[openvm_encapsulation]
        def $uniqueName
          (c: $circuit_type_tstx) (row : ℕ) (rotation : ℕ) : Prop :=
            c.main (id := 0) (column := $col_num_tstx) (row := row) (rotation := rotation) =
            $member_term_tstx (row := row) (rotation := rotation)
      ))
  ))

  -- Create isValid operation
  let isValid_recursion: String := ←(Array.foldrM add_isValid_subair "true" subairs)
  logInfo m!"isValid_recursion: {isValid_recursion}"
  let .ok isValid_recursion_stx := runParserCategory (← getEnv) `term isValid_recursion
    | throwError "Failed to parse the isValid subair term"
  let isValid_recursion_tstx : TSyntax `term := ⟨isValid_recursion_stx⟩
  logInfo m!"IsValid recursion term: {isValid_recursion_tstx}"

  let circuit_type : String := s!"{circuitName.getString} F ExtF"
  logInfo m!"Circuit type: {circuit_type}"
  let .ok circuit_type_stx := runParserCategory (← getEnv) `term circuit_type
    | throwError "Failed to parse the circuit type"
  let circuit_type_tstx : TSyntax `term := ⟨circuit_type_stx⟩

  let column_assertions: String := --←(Array.foldrM add_isValid_column "true" columns)
    (List.range column_assignments.length).foldr (λ n acc => s!"c.col_{n} row rotation ∧ {acc}") "true"
  logInfo m!"column_assertions: {column_assertions}"
  let .ok column_assertions_stx := runParserCategory (← getEnv) `term column_assertions
    | throwError "Failed to create the isValid column assertions term"
  let column_assertions_tstx : TSyntax `term := ⟨column_assertions_stx⟩

  let isValid_name := mkIdent (Name.mkStr2 circuitName.getString "isValid")
  Lean.Elab.Command.elabCommand
    (←`(
      def $isValid_name
        (c : $circuit_type_tstx) : Prop :=
          ($isValid_recursion_tstx) ∧
          ∀ row rotation, $column_assertions_tstx
    ))

  -- Create subcircuit_X_isValid_of_isValid lemmas
  discard (
    (subairs.filter (λ subair: TSyntax `entry =>
        match subair with
          | `(entry| SubAir[$_:str : $_:str width := $_:num]) => true
          | _ => false
      )).mapIdxM λ idx subair =>
      run_subcircuit_isValid_for_subair circuitName.getString idx subair
  )

  -- create the Valid_Circuit abbrev
  define_valid_circuit circuitName.getString
  -- project the underlying circuit's base members out
  define_valid_circuit_members circuitName.getString
  -- project the subairs out as validated versions
  discard (subairs.mapM λ subair => define_valid_circuit_subair circuitName.getString subair)
  -- TODO project the custom columns out

  -- Create valid circuit instance
  let instance_string : String := s!"instance [Field F] [Field ExtF] : Circuit F ExtF Valid_{circuitName.getString} where
      buses := Valid_{circuitName.getString}.buses
      challenge := Valid_{circuitName.getString}.challenge
      exposed := Valid_{circuitName.getString}.exposed
      main := Valid_{circuitName.getString}.main
      permutation := Valid_{circuitName.getString}.permutation
      preprocessed := Valid_{circuitName.getString}.preprocessed
      public_values := Valid_{circuitName.getString}.public_values
      last_row := Valid_{circuitName.getString}.last_row"

  let .ok instance_command_stx := runParserCategory (← getEnv) `command instance_string
    | throwError "Failed to parse instance creation commmand"
  logInfo m!"{instance_command_stx}"
  let instance_command_tstx : TSyntax `command := ⟨instance_command_stx⟩
  Lean.Elab.Command.elabCommand instance_command_tstx

  create_projection_lemma s!"Valid_{circuitName.getString}" "buses"
  create_projection_lemma s!"Valid_{circuitName.getString}" "challenge"
  create_projection_lemma s!"Valid_{circuitName.getString}" "exposed"
  create_projection_lemma s!"Valid_{circuitName.getString}" "main"
  create_projection_lemma s!"Valid_{circuitName.getString}" "permutation"
  create_projection_lemma s!"Valid_{circuitName.getString}" "preprocessed"
  create_projection_lemma s!"Valid_{circuitName.getString}" "public_values"
  create_projection_lemma s!"Valid_{circuitName.getString}" "last_row"

  discard (column_assignments.mapM λ x => prove_valid_circuit_column_assignment circuitName.getString x.1 x.2)
