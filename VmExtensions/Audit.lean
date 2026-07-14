/-
  Axiom-footprint audit — CI gate (compile-to-check).

  This module is the in-build counterpart of the `leanprover/comparator`
  axiom-compliance check (see `ci/comparator/`). It kernel-collects the
  transitive axiom footprint of each top-level VmExtensions soundness theorem
  (via `Lean.collectAxioms`, the same routine backing `#print axioms`) and
  FAILS ELABORATION if any theorem depends on an axiom outside the permitted
  allowlist.

  The allowlist is exactly the three standard classical-logic axioms
  (`propext`, `Classical.choice`, `Quot.sound`). Crucially it EXCLUDES:
    * `sorryAx`               — injected by `sorry` / `admit`
    * `Lean.ofReduceBool`     — injected by `native_decide`
    * `Lean.trustCompiler`    — injected by `native_decide`
  so a regression that reintroduces any forbidden tactic (or an open hole) into
  a gated theorem's dependency graph breaks `lake build VmExtensions.Audit`,
  independently of the textual `scripts/check_hygiene.py` scan.

  CI runs `lake build VmExtensions.Audit`.
-/
import Lean
import VmExtensions.Soundness.Sha2MainAir_sha256.Soundness
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Block.Soundness
import VmExtensions.Soundness.XorinVmAir.Soundness
import VmExtensions.Soundness.Keccakf.Soundness

open Lean Elab Command

namespace VmExtensions.Audit

/-- Axioms a certified proof may depend on: the three standard classical-logic
    axioms and nothing else. Any other axiom — notably `sorryAx`,
    `Lean.ofReduceBool`, `Lean.trustCompiler` — is a gate failure. -/
def permittedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- `#audit_axioms t₁, t₂, …` collects each theorem's transitive axiom
    footprint and throws (failing the build) if any theorem depends on an axiom
    outside `permittedAxioms`. On success it logs each theorem's exact
    footprint so the audit is visible in the build log. -/
syntax (name := auditAxiomsCmd) "#audit_axioms " ident,+ : command

@[command_elab auditAxiomsCmd]
def elabAuditAxioms : CommandElab := fun stx => do
  match stx with
  | `(#audit_axioms $ids,*) => do
    let mut failures : Array (Name × Array Name) := #[]
    for id in ids.getElems do
      -- Fails the build if the name no longer resolves (e.g. a renamed theorem),
      -- which is itself a useful regression signal.
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let axs ← collectAxioms name
      let bad := axs.filter (fun a => !permittedAxioms.contains a)
      if bad.isEmpty then
        logInfo m!"✓ {name} — axioms: {axs.toList}"
      else
        failures := failures.push (name, bad)
    unless failures.isEmpty do
      let details := failures.toList.map fun (n, b) => m!"  • {n}: forbidden {b.toList}"
      throwError m!"AXIOM AUDIT FAILED — gated theorem(s) depend on non-permitted axioms:\n\
        {MessageData.joinSep details "\n"}\n\
        Permitted allowlist: {permittedAxioms}\n\
        (sorryAx ⇒ open hole; Lean.ofReduceBool/trustCompiler ⇒ compiled decide.)"
  | _ => throwUnsupportedSyntax

/-! ## Gated top-level soundness theorems

Each entry is an end-to-end soundness leaf of the wired-in `VmExtensions` build.
Adding a theorem here makes CI certify it is kernel-checkable with no forbidden
axioms. -/

-- SHA-256: opcode-level equivalence to the reference compression function, and
-- the underlying block-hasher soundness.
#audit_axioms
  VmExtensions.Sha2CompressOpcode.equiv_SHA256_COMPRESS,
  Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness

-- Xorin (Keccak sponge XOR-in): per-row essentials bundle.
#audit_axioms XorinVmAir.Soundness.ValidRows.essentials

-- Keccak-f permutation: the state-bus payload-trace equivalences (the wired-in
-- soundness surface; the full `keccakf_matches_spec` permutation theorem lives
-- in the not-yet-wired Round tree).
#audit_axioms
  Keccakf.Soundness.Concrete.opStateBusTrace_sends_eq_payloadTrace,
  Keccakf.Soundness.Concrete.permStateBusTrace_recvs_eq_payloadTrace

end VmExtensions.Audit
