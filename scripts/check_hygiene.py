#!/usr/bin/env python3
"""Fast, comment-aware hygiene scan for the openvm-fv proof tree.

Fails (exit 1) if any *real* (non-comment) occurrence of a forbidden token is
found in the scanned Lean sources:

  * ``native_decide`` / ``bv_decide`` -- the only tactics that inject
    ``Lean.ofReduceBool`` (+ ``Lean.trustCompiler``) into a theorem's axiom
    footprint, i.e. the ones that break canonical/kernel-checkable proofs.
  * ``sorry`` / ``admit`` -- open proof holes.

This is the cheap first line of defence in CI (no build required). The
authoritative axiom check is the comparator gate (see ci/comparator/), which
independently re-exports and kernel-checks the top-level theorems against an
axiom allowlist; this script just catches regressions in seconds and gives a
precise file:line for every offending site.

Comment handling: nested ``/- ... -/`` block comments and ``-- ...`` line
comments are stripped before matching, so tokens that only appear in prose
(e.g. "the file can still be used with `sorry`") do not trip the scan.

Usage:
    scripts/check_hygiene.py [ROOT ...]        # default: OpenvmFv VmExtensions

Exit status: 0 = clean, 1 = violations found, 2 = usage/IO error.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# token -> human category. Order defines report order.
FORBIDDEN = {
    "native_decide": "non-canonical tactic (ofReduceBool)",
    "bv_decide": "non-canonical tactic (ofReduceBool)",
    "sorry": "open proof hole",
    "admit": "open proof hole",
}

DEFAULT_ROOTS = ["OpenvmFv", "VmExtensions"]

# Never scan build artefacts / vendored dependencies. These live under `.lake`
# (mathlib/aesop/etc. carry their own `sorry`/`native_decide` in test files) and
# `.git`. We only police first-party sources.
EXCLUDED_DIRS = {".lake", ".git"}

# Shelved WIP: unfinished, unwired-into-the-build subtrees that are intentionally
# NOT gated yet. Files whose path contains any of these markers are reported as
# "excluded (shelved WIP)" and do NOT count as violations. Keep this list short
# and documented — everything here is a deliberate, visible exception, never a
# silent skip.
#
# Currently empty: the SHA-512 tree (Extraction/Constraints/Soundness) was
# un-shelved once it was wired into the VmExtensions root aggregate and its
# top-level soundness theorems (`equiv_SHA512_COMPRESS`,
# `Sha2BlockHasherVmAir_sha512.BlockSpec.sha2_block_soundness`) were certified
# axiom-clean by the audit gate — it is now policed like every other subtree.
SHELVED_WIP_MARKERS: tuple[str, ...] = ()

# \b treats '_' as a word char, so e.g. `my_native_decide` / `sorryAx` do NOT match.
TOKEN_RE = re.compile(r"\b(" + "|".join(map(re.escape, FORBIDDEN)) + r")\b")


def strip_comments(src: str) -> str:
    """Replace Lean comments with spaces, preserving line/column layout.

    Handles nested ``/- ... -/`` block comments (Lean allows nesting) and
    ``-- ...`` line comments. Newlines inside stripped regions are preserved so
    that line numbers of surviving code are unchanged. String literals are not
    interpreted; a forbidden token hidden inside a string after ``--`` on the
    same line is treated as a comment, which is acceptable for this check.
    """
    out = []
    i, n = 0, len(src)
    depth = 0  # block-comment nesting depth
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        # not currently in a block comment
        if c == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if c == "-" and nxt == "-":
            # line comment: blank until end of line
            j = src.find("\n", i)
            if j == -1:
                j = n
            out.append(" " * (j - i))
            i = j
            continue
        out.append(c)
        i += 1
    return "".join(out)


def scan_file(path: Path) -> list[tuple[int, str, str]]:
    """Return list of (lineno, token, source_line) violations in *path*."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as e:  # pragma: no cover
        print(f"error: cannot read {path}: {e}", file=sys.stderr)
        return []
    stripped = strip_comments(text)
    raw_lines = text.splitlines()
    hits = []
    for lineno, line in enumerate(stripped.splitlines(), start=1):
        for m in TOKEN_RE.finditer(line):
            raw = raw_lines[lineno - 1] if lineno - 1 < len(raw_lines) else line
            hits.append((lineno, m.group(1), raw.strip()))
    return hits


def main(argv: list[str]) -> int:
    roots = argv or DEFAULT_ROOTS
    repo = Path(__file__).resolve().parent.parent

    files: list[Path] = []
    for root in roots:
        base = (repo / root).resolve()
        if not base.exists():
            print(f"error: root not found: {root}", file=sys.stderr)
            return 2
        files.extend(
            p
            for p in sorted(base.rglob("*.lean"))
            if not (EXCLUDED_DIRS & set(p.relative_to(repo).parts))
        )

    # Partition off shelved WIP so it is visibly excluded, never silently skipped.
    shelved = [p for p in files if any(m in str(p) for m in SHELVED_WIP_MARKERS)]
    files = [p for p in files if p not in shelved]
    if shelved:
        print(f"note: {len(shelved)} shelved-WIP file(s) excluded from the gate "
              f"(markers: {', '.join(SHELVED_WIP_MARKERS)}) — e.g. {shelved[0].relative_to(repo)}\n")

    total = 0
    per_token: dict[str, int] = {t: 0 for t in FORBIDDEN}
    per_root: dict[str, int] = {}
    print(f"hygiene scan: {len(files)} Lean files under {', '.join(roots)}\n")

    for path in files:
        hits = scan_file(path)
        if not hits:
            continue
        rel = path.relative_to(repo)
        root0 = rel.parts[0]
        per_root[root0] = per_root.get(root0, 0) + len(hits)
        for lineno, token, raw in hits:
            per_token[token] += 1
            total += 1
            print(f"  {rel}:{lineno}: {token}  [{FORBIDDEN[token]}]")
            print(f"      | {raw}")

    print()
    if total == 0:
        print("OK: no forbidden tactics or open proof holes found.")
        return 0
    print("VIOLATIONS:")
    for t, c in per_token.items():
        if c:
            print(f"  {t}: {c}")
    print("by area:")
    for r, c in sorted(per_root.items()):
        print(f"  {r}: {c}")
    print(f"\nFAIL: {total} forbidden occurrence(s). Zero-tolerance policy.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
