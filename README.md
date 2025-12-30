# Formal verification of the OpenVM RISC-V zkVM

This repository contains an infrastructure for formal verification of OpenVM RISC-V chips in Lean (v4.26.0), together with Lean proofs that the OpenVM implementations of all 45 of the RISC-V RV32IM opcodes satisfy their RISC-V specifications, as per the [Official Lean RISC-V specification](https://github.com/opencompl/sail-riscv-lean). These are, specifically:
- all 27 opcodes related to the functionalities of the ALU: `ADD`, `ADDI`, `SUB`, `XOR`, `XORI`, `OR`, `ORI`, `AND`, `ANDI`, `SLT`, `SLTI`, `SLTU`, `SLTUI`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI`, `MUL`, `MULH`, `MULHU`, `MULHSU`, `DIV`, `DIVU`, `REM`, and `REMU`;
- all 10 opcodes related to handling of control flow: `AUIPC`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `JAL`, `JALR`, and `LUI`; and
- all 8 opcodes related to memory manipulation: `LW`, `LH`, `LHU`, `LB`, `LBU`, `SW`, `SH`, and `SB`.

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
- the [`OpenvmFv/Equivalence`](OpenvmFv/Equivalence) folder contains the proofs of equivalence between implemented opcode behaviour and the correspoding Lean RISC-V specification.
- the [report](REPORT.pdf) file contains the report of the verification effort, including detailed examples and breakdown of assumptions and caveats used.

## Building the proofs

Assuming that an installation of Lean's `lake` package manager is present on the system,
the infrastructure and all of the proofs can be built using:
```
lake update
lake exe cache get!
lake build
```
in the root folder of the repository, where the first two lines are in principle superfluous but allow
for a faster initial build.
