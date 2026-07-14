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
| **this comparator gate**   | external re-export (`lean4export`) + sandboxed replay + statement-equality | when the comparator toolchain is available |

The first two are self-contained and gate every push. The comparator adds an
*independent* re-derivation using a separate exporter/kernel, so a bug in Lean's
own axiom bookkeeping cannot hide a forbidden dependency. It is heavier (needs
external binaries + a systemd user session) and is intended to run on a
GitHub-hosted runner or locally.

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

Currently gated: `ComparatorGate.sha2_block_soundness` (mirrors
`Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness`). Add more by
copying its statement into both `Challenge.lean` and `Solution.lean` (verbatim)
and appending the name to `theorem_names`.

## Required toolchain

The comparator needs three external binaries (none are vendored here):

1. **`comparator`** — build from <https://github.com/leanprover/comparator>.
2. **`landrun`** — Landlock sandbox helper, built from source.
3. **`lean4export`** — must match this repo's Lean (`v4.26.0`).

Point the runner at them via `PATH` or these env vars:
`COMPARATOR_BIN`, `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT`
(`COMPARATOR_NANODA` only if you set `"enable_nanoda": true`).

## Running

```bash
# builds Challenge + Solution, then runs the sandboxed comparator
scripts/run_comparator.sh
```

Sandboxing uses `systemd-run --user`, which needs a systemd user session; on a
CI runner enable it with `loginctl enable-linger "$USER"`. For local runs
without systemd you can set `COMPARATOR_NO_SANDBOX=1` (weaker isolation).

## What "pass" means

The gate passes iff, for every name in `theorem_names`, the `Solution` theorem
(a) proves a statement **definitionally equal** to the `Challenge` statement,
(b) is **accepted by the kernel** after re-export, and
(c) transitively depends on **no axiom outside** `permitted_axioms`
    (`propext`, `Quot.sound`, `Classical.choice`).

> Note: the binaries above are not present in this repository's build
> environment, so this gate has not been executed here. The Lean-side inputs
> (`Challenge`, `Solution`, `config.json`) build against the current tree, and
> `VmExtensions/Audit.lean` enforces (c) on every CI run in the meantime.
