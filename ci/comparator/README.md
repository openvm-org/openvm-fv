# Comparator axiom-footprint gate

This directory wires the [`leanprover/comparator`](https://github.com/leanprover/comparator)
tool into the project as an **independent, kernel-level** certification that the
top-level VmExtensions soundness theorems are proved with only a permitted set
of axioms — in particular **without** `native_decide` (`Lean.ofReduceBool` /
`Lean.trustCompiler`) or any open hole (`sorryAx`).

It complements two other, always-on gates:

| Gate | Mechanism | Runs in CI |
|------|-----------|-----------|
| `scripts/check_hygiene.py` | textual scan for forbidden tactics / holes | always (seconds, no build) |
| `VmExtensions/Audit.lean`  | in-build `Lean.collectAxioms` allowlist check on the same theorems | always (`lake build VmExtensions.Audit`) |
| **this comparator gate**   | external re-export (`lean4export`) + sandboxed replay + statement-equality | always (`comparator` job) |

All three gate every push. The comparator adds an *independent* re-derivation
using a separate exporter/kernel, so a bug in Lean's own axiom bookkeeping cannot
hide a forbidden dependency. It is heavier (needs external binaries built from
source), so the `comparator` CI job first provisions them with
[`scripts/setup_comparator_toolchain.sh`](../../scripts/setup_comparator_toolchain.sh)
and then invokes [`scripts/run_comparator.sh`](../../scripts/run_comparator.sh).

## Layout

- `lakefile.toml` — an **isolated** lake package (`comparator-gate`) that
  `require`s `vm-extensions` by path. Isolated so that…
- `Challenge.lean` — the **frozen statement** of each gated theorem, stated with
  `sorry`. Living outside `VmExtensions/` keeps this `sorry` out of the
  `scripts/check_hygiene.py` scan.
- `Solution.lean` — the identically-named, identically-typed theorem whose proof
  **delegates to the real VmExtensions theorem**.
- `config.json` — comparator configuration (modules, theorem names, permitted
  axioms).

Currently gated:

- `ComparatorGate.sha2_block_soundness` — mirrors `Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness`
- `ComparatorGate.sha512_block_soundness` — mirrors `Sha2BlockHasherVmAir_sha512.BlockSpec.sha2_block_soundness`
- `ComparatorGate.keccakf_matches_spec` — mirrors `Keccakf.Soundness.keccakf_matches_spec`

Add more by copying a theorem's statement into both `Challenge.lean` and
`Solution.lean` (verbatim) and appending the name to `theorem_names`. When the
source theorems live in namespaces that reuse predicate names — as the SHA-256
and SHA-512 block-hasher bridges do (`blockCompressionSpec`, `rotation_consistent`,
…) — put each variant in its own `section` with section-scoped `open`s so the
frozen statements stay unambiguous.

## Required toolchain

The comparator needs three external binaries (none are vendored here).
[`scripts/setup_comparator_toolchain.sh`](../../scripts/setup_comparator_toolchain.sh)
builds them at pinned revisions and exports the paths below; run it before
`run_comparator.sh` (the CI job does this automatically):

1. **`comparator`** — built from <https://github.com/leanprover/comparator>
   (uses its own pinned Lean toolchain).
2. **`lean4export`** — built against **this repo's** Lean (`v4.26.0`); the export
   format is fixed by the exporter source, so only the toolchain has to match.
3. **`landrun`** — Landlock sandbox helper, built from the `main` branch with Go.
   Build from `main`, **not** a release: the tagged release assets fail to apply
   the Landlock ruleset ("permission denied") under comparator.

The script points comparator at them via `COMPARATOR_BIN`,
`COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_LANDRUN` (and `COMPARATOR_NANODA` only
if you set `"enable_nanoda": true`, which this gate does not).

## Running

```bash
scripts/setup_comparator_toolchain.sh   # provision comparator + lean4export + landrun (pinned)
scripts/run_comparator.sh               # build Challenge + Solution, then run the gate
```

`run_comparator.sh` wraps the comparator in `systemd-run --user`, which needs a
systemd user session; on a CI runner enable it with `loginctl enable-linger
"$USER"`. Set `COMPARATOR_NO_SANDBOX=1` to skip that outer wrapper — comparator
still sandboxes the rebuild internally via `landrun`. The CI `comparator` job
runs exactly this with `COMPARATOR_NO_SANDBOX=1`.

## What "pass" means

The gate passes iff, for every name in `theorem_names`, the `Solution` theorem
(a) proves a statement **definitionally equal** to the `Challenge` statement,
(b) is **accepted by the kernel** after re-export, and
(c) transitively depends on **no axiom outside** `permitted_axioms`
    (`propext`, `Quot.sound`, `Classical.choice`).

This gate runs in CI: the `comparator` job in
[`.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)
provisions the toolchain and runs it on every push and pull request, alongside
the in-build `VmExtensions/Audit.lean` check.
