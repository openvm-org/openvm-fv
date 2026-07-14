#!/usr/bin/env bash
# Run the leanprover/comparator axiom-footprint gate over ci/comparator/.
#
# The comparator independently re-exports the Challenge and Solution modules via
# lean4export and certifies, in a landrun sandbox, that each Solution theorem
# proves the same statement as its Challenge counterpart using only the axioms
# listed in ci/comparator/config.json's `permitted_axioms`.
#
# Required tools (provide via PATH or the COMPARATOR_* environment variables):
#   * comparator binary          -> $COMPARATOR_BIN            (default: `comparator` on PATH)
#   * landrun                    -> $COMPARATOR_LANDRUN        (built from github.com/leanprover/landrun)
#   * lean4export                -> $COMPARATOR_LEAN4EXPORT    (version-matched to this repo's Lean)
#   * nanoda_bin (optional)      -> $COMPARATOR_NANODA         (only if enable_nanoda: true)
#
# Sandboxing uses `systemd-run --user`, which requires a systemd user session
# (on CI: `loginctl enable-linger "$USER"`). Set COMPARATOR_NO_SANDBOX=1 to run
# the comparator directly without systemd-run (weaker isolation; for local dev).
#
# Usage: scripts/run_comparator.sh
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GATE_DIR="$REPO_ROOT/ci/comparator"
CONFIG="$GATE_DIR/config.json"

COMPARATOR_BIN="${COMPARATOR_BIN:-comparator}"

missing=0
need() {
  local name="$1" path="$2"
  if ! command -v "$path" >/dev/null 2>&1 && [ ! -x "$path" ]; then
    echo "ERROR: required tool '$name' not found (looked for: $path)." >&2
    missing=1
  fi
}
need "comparator" "$COMPARATOR_BIN"
[ -n "${COMPARATOR_LANDRUN:-}" ]     && need "landrun"     "$COMPARATOR_LANDRUN"
[ -n "${COMPARATOR_LEAN4EXPORT:-}" ] && need "lean4export" "$COMPARATOR_LEAN4EXPORT"
if [ "$missing" -ne 0 ]; then
  echo "See ci/comparator/README.md for how to obtain the comparator toolchain." >&2
  exit 2
fi

echo ">> Building Challenge + Solution (ci/comparator) ..."
( cd "$GATE_DIR" && lake exe cache get >/dev/null 2>&1 || true; cd "$GATE_DIR" && lake build )

echo ">> Running comparator on $CONFIG ..."
if [ "${COMPARATOR_NO_SANDBOX:-0}" = "1" ]; then
  ( cd "$GATE_DIR" && lake env "$COMPARATOR_BIN" "$CONFIG" )
else
  ( cd "$GATE_DIR" && systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
      -E PATH="$PATH" \
      ${COMPARATOR_LANDRUN:+-E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN"} \
      ${COMPARATOR_LEAN4EXPORT:+-E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT"} \
      ${COMPARATOR_NANODA:+-E COMPARATOR_NANODA="$COMPARATOR_NANODA"} \
      --working-directory "$GATE_DIR" -- \
      bash -c "lake env '$COMPARATOR_BIN' '$CONFIG'" )
fi
echo ">> Comparator gate passed."
