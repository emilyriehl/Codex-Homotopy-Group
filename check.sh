#!/usr/bin/env bash
# Sound Agda verification for this repo — a REAL typecheck.
#
# ⚠️ Use THIS (raw agda), NOT the agda-mcp-server: that server was measured (2026-05-30) to
#    only scope-check and report "ok-complete" on code that does not type-check.
#
# Usage:  ./check.sh [--fresh] <path/to/Module.lagda.md>     (run from this repo root)
# Library flags (--without-K --exact-split ...) auto-apply from
# Codex-Homotopy-Group.agda-lib.
# Exit 0 + no "error:" + no remaining holes (?, {! !}) ⇒ verified.
#
# Options:
#   --fresh  Pass --ignore-interfaces to Agda and re-typecheck from source.
#
# Environment:
#   AGDA_RTS_MAX  GHC RTS memory cap, without -M. Defaults to 8G.
#
# Prefers a plain `agda` binary (nix profile / PATH) so it needs NO Nix daemon at runtime —
# this is what lets it run inside the Codex sandbox. Falls back to `nix shell` if no binary found.
set -euo pipefail

usage() {
  echo "usage: check.sh [--fresh] <Module.lagda.md>" >&2
  exit 2
}

agda_args=(--no-allow-unsolved-metas)

if [ "${1:-}" = "--fresh" ]; then
  agda_args+=(--ignore-interfaces)
  shift
fi

if [ "$#" -ne 1 ]; then
  usage
fi

file="$1"
rts_max="${AGDA_RTS_MAX:-8G}"
rts_memory_arg="-M${rts_max#-M}"

repo_root="$(cd "$(dirname "$0")" && pwd)"
cd "$repo_root"

if [ ! -d agda-unimath/src ]; then
  echo "agda-unimath submodule is missing." >&2
  echo "Run: git submodule update --init --depth 1" >&2
  exit 1
fi

if command -v agda >/dev/null 2>&1; then
  exec agda +RTS "$rts_memory_arg" -RTS "${agda_args[@]}" "$file"
elif [ -x "$HOME/.nix-profile/bin/agda" ]; then
  exec "$HOME/.nix-profile/bin/agda" +RTS "$rts_memory_arg" -RTS "${agda_args[@]}" "$file"
else
  exec nix shell nixpkgs#agda -c agda +RTS "$rts_memory_arg" -RTS "${agda_args[@]}" "$file"
fi
