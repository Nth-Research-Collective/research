#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROJECT="$ROOT/formal/lean_project"
TOOLCHAIN="leanprover/lean4:v4.32.2"
ELAN="$HOME/.elan/bin/elan"

if [[ ! -x "$ELAN" ]]; then
  installer="$(mktemp)"
  trap 'rm -f "$installer"' EXIT
  curl --proto '=https' --tlsv1.2 -sSf \
    https://elan.lean-lang.org/elan-init.sh -o "$installer"
  sh "$installer" -y --default-toolchain "$TOOLCHAIN"
fi

case "$("$ELAN" toolchain list)" in
  *"$TOOLCHAIN"*) ;;
  *) "$ELAN" toolchain install "$TOOLCHAIN" ;;
esac
"$ELAN" default "$TOOLCHAIN"

LAKE="$HOME/.elan/bin/lake"
(cd "$PROJECT" && "$LAKE" update && "$LAKE" exe cache get)
(cd "$PROJECT" && "$LAKE" env lean TestMathlib.lean)

echo "PASS: Lean and pinned mathlib are ready"
