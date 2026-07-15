#!/usr/bin/env bash
# Provision the leanprover/comparator toolchain used by scripts/run_comparator.sh
# (and the "Comparator gate" CI job): the `comparator`, `lean4export`, and
# `landrun` binaries.
#
# Builds pinned revisions into $COMPARATOR_TOOLCHAIN_DIR (default
# ~/.comparator-toolchain) and prints the COMPARATOR_* env vars pointing at them.
# When run inside GitHub Actions ($GITHUB_ENV set) it also appends those vars to
# $GITHUB_ENV so subsequent steps inherit them.
#
# Requirements: git, elan/lake (a Lean install), curl. No Go toolchain is needed
# (landrun is fetched as a prebuilt release). Idempotent: each binary is built
# only if it is not already present in the toolchain dir.
#
# Pins can be overridden via the COMPARATOR_REV / LEAN4EXPORT_REV /
# LANDRUN_VERSION environment variables.
set -euo pipefail

COMPARATOR_REV="${COMPARATOR_REV:-07bc4ea40f2266dcb861820a2ec1fa3244ed307f}"
LEAN4EXPORT_REV="${LEAN4EXPORT_REV:-4e7915201d3f9f04470d9eae002fa695f7cdc589}"
# landrun: a pinned `main` commit (see the landrun note below).
LANDRUN_REV="${LANDRUN_REV:-5ed4a3db3a4ad930d577215c6b9abaa19df7f99f}"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# `lean4export` must be built against the SAME Lean toolchain as the project it
# exports (the vm-extensions / ci-comparator packages). Read it from the repo so
# the two never drift; the export FORMAT (3.1.0) is fixed by the exporter source.
TARGET_TOOLCHAIN="$(tr -d '[:space:]' < "$REPO_ROOT/lean-toolchain")"

DIR="${COMPARATOR_TOOLCHAIN_DIR:-$HOME/.comparator-toolchain}"
BIN="$DIR/bin"
SRC="$DIR/src"
mkdir -p "$BIN" "$SRC"

# --- comparator (leanprover/comparator; builds with its own pinned toolchain) --
if [ ! -x "$BIN/comparator" ]; then
  echo ">> building comparator @ $COMPARATOR_REV"
  rm -rf "$SRC/comparator"
  git clone https://github.com/leanprover/comparator.git "$SRC/comparator"
  git -C "$SRC/comparator" checkout -q "$COMPARATOR_REV"
  ( cd "$SRC/comparator" && lake build )
  cp "$SRC/comparator/.lake/build/bin/comparator" "$BIN/comparator"
fi

# --- lean4export (built against the target project's Lean toolchain) -----------
if [ ! -x "$BIN/lean4export" ]; then
  echo ">> building lean4export @ $LEAN4EXPORT_REV against $TARGET_TOOLCHAIN"
  rm -rf "$SRC/lean4export"
  git clone https://github.com/leanprover/lean4export.git "$SRC/lean4export"
  git -C "$SRC/lean4export" checkout -q "$LEAN4EXPORT_REV"
  echo "$TARGET_TOOLCHAIN" > "$SRC/lean4export/lean-toolchain"
  ( cd "$SRC/lean4export" && lake build )
  cp "$SRC/lean4export/.lake/build/bin/lean4export" "$BIN/lean4export"
fi

# --- landrun (Landlock sandbox helper; built from a pinned `main` commit) ------
# NOTE: comparator requires landrun built from `main` (per its README), NOT a
# release. The release assets are unusable here: the v0.1.14 asset actually
# reports 0.1.13, and BOTH the 0.1.13 asset and the tagged v0.1.15 commit fail
# with "permission denied" when comparator applies its Landlock ruleset. The
# pinned `main` commit below is the first that works end-to-end.
if [ ! -x "$BIN/landrun" ]; then
  command -v go >/dev/null 2>&1 || {
    echo "error: 'go' is required to build landrun from source" >&2
    exit 1
  }
  echo ">> building landrun @ $LANDRUN_REV from source"
  rm -rf "$SRC/landrun"
  git clone https://github.com/Zouuup/landrun.git "$SRC/landrun"
  git -C "$SRC/landrun" checkout -q "$LANDRUN_REV"
  ( cd "$SRC/landrun" && go build -o "$BIN/landrun" ./cmd/landrun )
fi

echo ">> comparator toolchain ready:"
ls -l "$BIN"

emit() {
  echo "$1=$2"
  if [ -n "${GITHUB_ENV:-}" ]; then echo "$1=$2" >> "$GITHUB_ENV"; fi
}
emit COMPARATOR_BIN         "$BIN/comparator"
emit COMPARATOR_LEAN4EXPORT "$BIN/lean4export"
emit COMPARATOR_LANDRUN     "$BIN/landrun"
