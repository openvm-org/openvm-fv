import Lean
import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.util

/-
REVIEW: `TSyntax term` is just `Term`.
-/

open Lean Parser
set_option hygiene false in
elab "#subcircuit_isValid_of_isValid" circuit:str col:num member:str : command => do
  let circuit_type : String := s!"{circuit.getString} F ExtF"
  -- logInfo m!"Circuit type: {circuit_type}"
  let .ok circuit_type_stx := runParserCategory (← getEnv) `term circuit_type
    | throwError "Failed to parse the circuit type"
  let circuit_type_tstx : Term := ⟨circuit_type_stx⟩

  let member_term : String := s!"c.{member.getString}"
  -- logInfo m!"Member term: {member_term}"
  let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
    | throwError "Failed to parse the member term"
  let member_term_tstx : Term := ⟨member_term_stx⟩

  let proof_member := transformIndex col.getNat
  let proof : String := s!"h.1{proof_member}"
  let .ok proof_stx := runParserCategory (← getEnv) `term proof
    | throwError "Failed to parse the proof"
  let proof_tstx : Term := ⟨proof_stx⟩

  let uniqueName := mkIdent (Name.mkStr2 circuit.getString s!"subcircuit_{member.getString}_isValid_of_isValid")
  -- logInfo m!"Registering: {uniqueName.getId}"
  Lean.Elab.Command.elabCommand
    (←`(
      @[openvm_encapsulation]
      lemma $uniqueName [Field F] [Field ExtF]
        (c: $circuit_type_tstx) (h: c.isValid) :
        ($member_term_tstx).isValid := by
          exact $proof_tstx
    ))

open Lean Parser
set_option hygiene false in -- stops the intermediate terms from having parameters inserted for unbound variables
def run_subcircuit_isValid_of_isValid (circuit:String) (col:ℕ) (member:String) : Elab.Command.CommandElabM Unit := do
  let circuit_type : String := s!"{circuit} F ExtF"
  -- logInfo m!"Circuit type: {circuit_type}"
  let .ok circuit_type_stx := runParserCategory (← getEnv) `term circuit_type
    | throwError "Failed to parse the circuit type"
  let circuit_type_tstx : Term := ⟨circuit_type_stx⟩

  let member_term : String := s!"c.{member}"
  -- logInfo m!"Member term: {member_term}"
  let .ok member_term_stx := runParserCategory (← getEnv) `term member_term
    | throwError "Failed to parse the member term"
  let member_term_tstx : Term := ⟨member_term_stx⟩

  let proof_member := transformIndex col
  let proof : String := s!"h.1{proof_member}"
  let .ok proof_stx := runParserCategory (← getEnv) `term proof
    | throwError "Failed to parse the proof"
  let proof_tstx : Term := ⟨proof_stx⟩

  let uniqueName := mkIdent (Name.mkStr2 circuit s!"subcircuit_{member}_isValid_of_isValid")
  -- logInfo m!"Registering: {uniqueName.getId}"
  Lean.Elab.Command.elabCommand
    (←`(
      @[openvm_encapsulation]
      lemma $uniqueName
        (c: $circuit_type_tstx) (h: c.isValid) :
        ($member_term_tstx).isValid := by
          exact $proof_tstx
    ))

open Lean Parser
set_option hygiene false in
/--
REVIEW: `discard` only needed to throw away the value from a monad (to obtain a `Unit` instead).
        `run_subcircuit_isValid_of_isValid` already gives a `Unit`.
-/
elab "#subcircuit_isValid_of_isValid1" circuit:str col:num member:str : command => do
  run_subcircuit_isValid_of_isValid circuit.getString col.getNat member.getString

-- @[openvm_encapsulation]
-- lemma BaseAluCoreAir.col_12_of_isValid [Field F] [Field ExtF]
--   (c : BaseAluCoreAir F ExtF) (row rotation : ℕ) (h : c.isValid) :
--   c.main (id := 0) (column := 12) (row := row) (rotation := rotation) =
--   c.opcode_add_flag (row := row) (rotation := rotation) := by
--     exact (h row rotation).2.2.2.2.2.2.2.2.2.2.2.2.1
