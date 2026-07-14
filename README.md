# Formal verification of the OpenVM RISC-V zkVM

This repository contains an infrastructure for formal verification of OpenVM RISC-V chips in Lean (v4.26.0), together with Lean proofs that the OpenVM implementations of all 45 of the RISC-V RV32IM opcodes satisfy their RISC-V specifications, as per the [Official Lean RISC-V specification](https://github.com/opencompl/sail-riscv-lean). These are, specifically:
- all 27 opcodes related to the functionalities of the ALU: `ADD`, `ADDI`, `SUB`, `XOR`, `XORI`, `OR`, `ORI`, `AND`, `ANDI`, `SLT`, `SLTI`, `SLTU`, `SLTUI`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI`, `MUL`, `MULH`, `MULHU`, `MULHSU`, `DIV`, `DIVU`, `REM`, and `REMU`;
- all 10 opcodes related to handling of control flow: `AUIPC`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `JAL`, `JALR`, and `LUI`; and
- all 8 opcodes related to memory manipulation: `LW`, `LH`, `LHU`, `LB`, `LBU`, `SW`, `SH`, and `SB`.

## Precompile ("extension") chips

In addition to the RV32IM base, the [`VmExtensions`](VmExtensions) folder contains Lean proofs of soundness for several OpenVM precompile chips, each relating a chip's extracted AIR constraints to a reference specification of the primitive it implements:

- **Keccak-f[1600] permutation** — every enabled `KeccakfOpAir` row's decoded post-state equals `Keccak-f[1600]` applied to its decoded pre-state (with the expected program-counter and timestamp advance), together with the state-bus payload-trace equivalences that connect the opcode and permutation chips. Top-level theorem: `Keccakf.Soundness.keccakf_matches_spec`.
- **Keccak sponge XOR-in** (`XorinVmAir`) — the per-row well-formedness bundle `XorinVmAir.Soundness.ValidRows.essentials`.
- **SHA-256 compression** — one `compress` row's decoded output equals the reference `CryptoHash.SHA256.compressBlock` of its decoded input (`VmExtensions.Sha2CompressOpcode.equiv_SHA256_COMPRESS`), backed by the block-hasher soundness `Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness`.
- **SHA-512 compression** — the SHA-512 analogues `VmExtensions.Sha2CompressOpcode.equiv_SHA512_COMPRESS` and `Sha2BlockHasherVmAir_sha512.BlockSpec.sha2_block_soundness`.

Each of these is a soundness statement of the form "if a trace satisfies the chip's extracted constraints, then its decoded output matches the reference model." The constraint hypotheses bundle the raw extracted constraints of the chip; the reference models live in [`VmExtensions/Sha2`](VmExtensions/Sha2) and [`VmExtensions/Keccak`](VmExtensions/Keccak) and follow the corresponding public specifications:

- SHA-256 and SHA-512 follow [FIPS 180-4, *Secure Hash Standard*](https://csrc.nist.gov/pubs/fips/180-4/upd1/final);
- the Keccak-f[1600] permutation follows [FIPS 202, *SHA-3 Standard*](https://csrc.nist.gov/pubs/fips/202/final) (§3, the `KECCAK-p` permutations), originally specified in the [Keccak team reference](https://keccak.team/keccak.html).

As with the RISC-V proofs, the extraction and the reference models form the trusted frontend, and there is no separate completeness/satisfiability direction. These precompile chips are **not** covered by [REPORT.pdf](REPORT.pdf), which documents the RV32IM work only.

Every one of the top-level theorems above is certified to depend only on the three standard classical-logic axioms (`propext`, `Classical.choice`, `Quot.sound`) — with no `sorry` and no `native_decide`/`bv_decide` (which would inject `Lean.ofReduceBool`) — by three CI gates:

- [`scripts/check_hygiene.py`](scripts/check_hygiene.py): a fast textual scan forbidding `native_decide`/`bv_decide`/`sorry`/`admit` in the first-party sources (no build required);
- [`VmExtensions/Audit.lean`](VmExtensions/Audit.lean): an in-build `#audit_axioms` command that kernel-collects each listed theorem's transitive axiom footprint (via `Lean.collectAxioms`) and fails the build on any axiom outside the allowlist; and
- [`ci/comparator`](ci/comparator): an independent `leanprover/comparator` re-export and replay of the frozen statements against the same allowlist (defence-in-depth).

## Repository structure

This repository is structured as follows:
- the [`OpenvmFv/Fundamentals`](OpenvmFv/Fundamentals) folder contains a number of files that underpin the infrastructure:
  - [`BabyBear.lean`](OpenvmFv/Fundamentals/BabyBear.lean), for reasoning about the `BabyBear` finite field, which is used by OpenVM;
  - [`Core.lean`](OpenvmFv/Fundamentals/Core.lean), which contains useful lemmas about Lean lists, bit-vectors, and integers;
  - [`Execution.lean`](OpenvmFv/Fundamentals/Execution.lean), for simplifying reasoning about the Lean RISC-V specification;
  - [`Interaction.lean`](OpenvmFv/Fundamentals/Interaction.lean), for formalising general bus interactions;
  - [`Transpiler.lean`](OpenvmFv/Fundamentals/Transpiler.lean), in which we formalise the OpenVM transpiler from RISC-V instructions to native OpenVM instructions; and
  - [`U32.lean`](OpenvmFv/Fundamentals/U32.lean), for reasoning about 32-bit words.
- the [`OpenvmFv/Airs`](OpenvmFv/Airs) folder contains the formalisation of the structure of the relevant airs in a way that mirrors their Rust implementations;
- the [`OpenvmFv/Extraction`](OpenvmFv/Extraction) folder contains the constraints extracted from the OpenVM implementation for all of the relevant chips, in raw, unsimplified form;
- the [`OpenvmFv/Constraints`](OpenvmFv/Constraints) folder contains the constraints extracted from the OpenVM implementation for all of the relevant chips, simplified into human-readable form;
- the [`OpenvmFv/Spec`](OpenvmFv/Spec) folder contains the proofs that opcode constraints imply human-readable characterisations of their RISC-V intended behaviour; and
- the [`OpenvmFv/RV32D`](OpenvmFv/RV32D) folder contains a number of auxiliary functions that ease the reasoning about the Lean RISC-V specification, as well as the pure specifications for all of the RV32IM opcodes;
- the [`OpenvmFv/Equivalence/Equivalence.lean`](OpenvmFv/Equivalence/Equivalence.lean) file contains the proofs of equivalence between implemented opcode behaviour and the correspoding Lean RISC-V specification.
- the [`VmExtensions`](VmExtensions) folder is a separate lake package holding the precompile-chip proofs described above; it mirrors the layout of the RISC-V tree — [`Extraction`](VmExtensions/Extraction) (raw extracted constraints), [`Constraints`](VmExtensions/Constraints) (human-readable form), and [`Soundness`](VmExtensions/Soundness) (the per-chip soundness proofs) — alongside the reference models in [`Sha2`](VmExtensions/Sha2) and [`Keccak`](VmExtensions/Keccak).
- the [report](REPORT.pdf) file documents the RV32IM verification effort **only** — it does not cover the precompile chips in [`VmExtensions`](VmExtensions) — including detailed examples and a breakdown of the assumptions and caveats used.

## Building the proofs

Assuming that an installation of Lean's `lake` package manager is present on the system,
the infrastructure and all of the proofs can be built using:
```
lake update
lake exe cache get!
lake build
```
in the root folder of the repository, where the first two lines are in principle superfluous but allow
for a faster initial build. This builds the RISC-V (`OpenvmFv`) proofs.

The precompile proofs live in the separate `VmExtensions` lake package and are built independently:
```
cd VmExtensions
lake exe cache get!
lake build VmExtensions          # the precompile-chip proofs
lake build VmExtensions.Audit    # the axiom-footprint gate (fails on any non-allowlisted axiom)
```
The hygiene scan can be run from the repository root with `python3 scripts/check_hygiene.py`.
