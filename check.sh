#!/usr/bin/env bash
# Sound Agda verification for this repo — a REAL typecheck.
#
# ⚠️ Use THIS (raw agda), NOT the agda-mcp-server: that server was measured (2026-05-30) to
#    only scope-check and report "ok-complete" on code that does not type-check.
#
# Usage:  ./check.sh <path/to/Module.lagda.md>     (run from this repo root)
# Library flags (--without-K --exact-split ...) auto-apply from
# Codex-Homotopy-Group.agda-lib.
# Exit 0 + no "error:" + no remaining holes (?, {! !}) ⇒ verified.
#
# Prefers a plain `agda` binary (nix profile / PATH) so it needs NO Nix daemon at runtime —
# this is what lets it run inside Codex's sandbox. Falls back to `nix shell` if no binary found.
set -euo pipefail
file="${1:?usage: check.sh <Module.lagda.md>}"

repo_root="$(cd "$(dirname "$0")" && pwd)"
cd "$repo_root"

if [ ! -d agda-unimath/src ]; then
  echo "agda-unimath submodule is missing." >&2
  echo "Run: git submodule update --init --depth 1" >&2
  exit 1
fi

if command -v agda >/dev/null 2>&1; then
  exec agda +RTS -M8G -RTS "$file"
elif [ -x "$HOME/.nix-profile/bin/agda" ]; then
  exec "$HOME/.nix-profile/bin/agda" +RTS -M8G -RTS "$file"
else
  exec nix shell nixpkgs#agda -c agda +RTS -M8G -RTS "$file"
fi
