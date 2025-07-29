import Mathlib
import OpenvmFv.Tactic.Util

open Lean Parser
set_option hygiene false in
elab "#rewrite_column_of_isValid" circuit:str col:num member:str : command => do
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

  let proof_member := transformIndex col.getNat
  let proof : String := s!"(h.2 row rotation){proof_member}"
  let .ok proof_stx := runParserCategory (← getEnv) `term proof
    | throwError "Failed to parse the proof"
  let proof_tstx : TSyntax `term := ⟨proof_stx⟩

  let uniqueName := mkIdent (Name.mkStr2 circuit.getString s!"col_{col.getNat}_of_isValid")
  -- logInfo m!"Registering: {uniqueName.getId}"
  Lean.Elab.Command.elabCommand
    (←`(
      @[openvm_encapsulation]
      lemma $uniqueName [Field F] [Field ExtF]
        (c: $circuit_type_tstx) (row rotation : ℕ) (h: c.isValid) :
        c.main (id := 0) (column := $col_num_tstx) (row := row) (rotation := rotation) =
        $member_term_tstx (row := row) (rotation := rotation) := by
          exact $proof_tstx
    ))

-- @[openvm_encapsulation]
-- lemma BaseAluCoreAir.col_12_of_isValid [Field F] [Field ExtF]
--   (c : BaseAluCoreAir F ExtF) (row rotation : ℕ) (h : c.isValid) :
--   c.main (id := 0) (column := 12) (row := row) (rotation := rotation) =
--   c.opcode_add_flag (row := row) (rotation := rotation) := by
--     exact (h row rotation).2.2.2.2.2.2.2.2.2.2.2.2.1
