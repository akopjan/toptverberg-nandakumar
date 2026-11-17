#!/bin/sh
set -eu
cd "$(dirname "$0")/.."

printf '%s\n' 'Auditing Lean sources for forbidden proof placeholders...'
if grep -R -nE '^[[:space:]]*(axiom|sorry|admit|unsafe|opaque)([[:space:]]|$)' --include='*.lean' .; then
  echo 'Unexpected proof placeholder / unsound declaration found.' >&2
  exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
  echo 'Lean/Lake is not installed. Install elan and Lean 4.28.0 first.' >&2
  exit 2
fi

lake update
lake exe cache get
lake build
lake env lean Tverberg6/Audit.lean
printf '%s\n' 'Build and audit commands completed. IMPORTANT: MainGoal is still open.'
