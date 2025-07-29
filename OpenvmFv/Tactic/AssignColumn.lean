import Mathlib

import OpenvmFv.Tactic.SubcircuitIsValidOfIsValid
import OpenvmFv.Tactic.RewriteColumnOfIsValid

open Lean Parser
set_option hygiene false in
elab "#assign_column" circuit:str col:num member:str : command => do
  let circuit_type : String := s!"{circuit.getString} F ExtF"
  logInfo m!"Circuit type: {circuit_type}"
  let .ok circuit_type_stx := runParserCategory (← getEnv) `term circuit_type
    | throwError "Failed to parse the circuit type"
  let circuit_type_tstx : TSyntax `term := ⟨circuit_type_stx⟩

  let member_term : String := s!"c.{member.getString}"
  logInfo m!"Member term: {member_term}"
  let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
    | throwError "Failed to parse the member term"
  let member_term_tstx : TSyntax `term := ⟨member_term_stx⟩

  let col_num : String := s!"{col.getNat}"
  logInfo m!"Column number: {col_num}"
  let .ok col_num_stx := runParserCategory (← getEnv) `term col_num
    | throwError "Failed to parse the column number"
  let col_num_tstx : TSyntax `term := ⟨col_num_stx⟩

  let uniqueName := mkIdent (Name.mkStr2 circuit.getString s!"col_{col.getNat}")
  logInfo m!"Registering: {uniqueName.getId}"
  Lean.Elab.Command.elabCommand
    (←`(
      @[openvm_encapsulation]
      def $uniqueName [Field F] [Field ExtF]
        (c: $circuit_type_tstx) (row : ℕ) (rotation : ℕ) : Prop :=
          c.main (id := 0) (column := $col_num_tstx) (row := row) (rotation := rotation) =
          $member_term_tstx (row := row) (rotation := rotation)
    ))


syntax column := "[" num "," str "]"
syntax subair := "SubAir[" str ":" str "]"

def run_assign_column (circuitName: TSyntax `str) (head: TSyntax `column): Elab.Command.CommandElabM Unit := do
  match head with
    | `(column| [$col, $member]) => Lean.Elab.Command.elabCommand (←`(#assign_column $circuitName $col $member))
    | _ => throwError "Nooooooooooooooooooo"



def isValid_subair (head: TSyntax `str): Elab.Command.CommandElabM (TSyntax `term) := do
  let member_term : String := s!"c.{head.getString}.isValid"
  let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
    | throwError "Failed to parse a subair for isValid"
  let member_term_tstx : TSyntax `term := ⟨member_term_stx⟩
  pure (member_term_tstx)

def run_rewrite_column_of_isValid (circuitName: TSyntax `str) (head: TSyntax `column): Elab.Command.CommandElabM Unit := do
  match head with
    | `(column| [$col, $member]) => Lean.Elab.Command.elabCommand (←`(#rewrite_column_of_isValid $circuitName $col $member))
    | _ => throwError "Nooooooooooooooooooo"

def add_structure_field (struct_string: String) (subair: TSyntax `subair) : Elab.Command.CommandElabM String := do
  match subair with
    | `(subair| SubAir[$name : $typeName]) => return s!"{struct_string}\n        {name.getString} : {typeName.getString} F ExtF"
    | _ => throwError "failed to add struct field"

def add_isValid_subair (subair: TSyntax `subair) (isValid_string: String) : Elab.Command.CommandElabM String := do
  match subair with
    | `(subair| SubAir[$name : $_]) => return s!"c.{name.getString}.isValid ∧ {isValid_string}"
    | _ => throwError "failed to add subair to isValid"

def add_isValid_column (column: TSyntax `column) (isValid_string: String) : Elab.Command.CommandElabM String := do
  match column with
    | `(column| [$pos, $_]) => return s!"c.col_{pos.getNat} row rotation ∧ {isValid_string}"
    | _ => throwError "failed to add column to isValid"

def run_subcircuit_isValid_for_subair (circuit : String) (idx: ℕ) (subair: TSyntax `subair) : Elab.Command.CommandElabM Unit := do
  match subair with
    | `(subair| SubAir[$name : $_]) => run_subcircuit_isValid_of_isValid circuit idx name.getString
    | _ => throwError "failed to run subcircuit_isValid_of_isValid for subair"

def create_projection_lemma (circuit: String) (member: String) : Elab.Command.CommandElabM Unit := do
  let .ok lemma_stx := runParserCategory (← getEnv) `command s!"
    @[openvm_encapsulation] lemma {circuit}_{member}_project [Field F] [Field ExtF] (c: {circuit} F ExtF) :
      @Circuit.{member} F (by assumption) ExtF (by assumption) {circuit} _ c = c.{member} := rfl"
    | throwError "Failed to parse circuit type"
  let lemma_tstx: TSyntax `command := ⟨lemma_stx⟩

  Lean.Elab.Command.elabCommand lemma_tstx

open Lean Parser
set_option hygiene false in
elab "#assign_columns" circuitName: str subairs: subair* columns: column+ : command => do
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
  match columns with
    | ⟨[]⟩ => pure ()
    | ⟨list⟩ => discard (list.mapM (run_assign_column circuitName))

  -- Create isValid operation
  let isValid_recursion: String := ←(Array.foldrM add_isValid_subair "true" subairs)
  logInfo m!"isValid_recursion: {isValid_recursion}"
  let .ok isValid_recursion_stx := runParserCategory (← getEnv) `term isValid_recursion
    | throwError "Failed to parse the isValid subair term"
  let isValid_recursion_tstx : TSyntax `term := ⟨isValid_recursion_stx⟩

  let column_assertions: String := ←(Array.foldrM add_isValid_column "true" columns)
  logInfo m!"column_assertions: {column_assertions}"
  let .ok column_assertions_stx := runParserCategory (← getEnv) `term column_assertions
    | throwError "Failed to create the isValid column assertions term"
  let column_assertions_tstx : TSyntax `term := ⟨column_assertions_stx⟩

  let isValid_name := mkIdent (Name.mkStr2 circuitName.getString "isValid")
  Lean.Elab.Command.elabCommand
    (←`(
      def $isValid_name [Field F] [Field ExtF]
        (c : VmAirWrapper_alu F ExtF) : Prop :=
          ($isValid_recursion_tstx) ∧
          ∀ row rotation, $column_assertions_tstx
    ))

  discard (
    subairs.mapIdxM λ idx subair =>
      run_subcircuit_isValid_for_subair circuitName.getString idx subair
  )

  match columns with
    | ⟨[]⟩ => pure ()
    | ⟨list⟩ => discard (list.mapM (run_rewrite_column_of_isValid circuitName))
