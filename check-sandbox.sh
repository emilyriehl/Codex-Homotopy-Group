#!/usr/bin/env bash
# Sound Agda verification for agda-unimath — a REAL typecheck.
#
# NOTE: This is the SANDBOX gate. codex-run.sh deploys it into the $HOME/agda-unimath
# working copy as ./check.sh, where it runs `agda` directly against agda-unimath.agda-lib.
# It is intentionally distinct from this repo's root ./check.sh, which is submodule-aware
# (it targets ./agda-unimath/src via Codex-Homotopy-Group.agda-lib) and is for LOCAL
# verification of artifacts brought back into this repo. Keep the two in step by content.
#
# ⚠️ Use THIS (raw agda), NOT the agda-mcp-server: that server was measured (2026-05-30) to
#    only scope-check and report "ok-complete" on code that does not type-check.
#
# Usage:  ./check.sh <path/to/Module.lagda.md>     (run from the agda-unimath repo root)
# Library flags (--without-K --exact-split ...) auto-apply from agda-unimath.agda-lib.
# Exit 0 + no "error:" + no remaining holes (?, {! !}) ⇒ verified.
#
# Prefers a plain `agda` binary (nix profile / PATH) so it needs NO Nix daemon at runtime —
# this is what lets it run inside Codex's sandbox. Falls back to `nix shell` if no binary found.
# Install agda into your nix profile (one-time):  nix profile install nixpkgs#agda
set -euo pipefail
file="${1:?usage: check.sh <Module.lagda.md>}"

if command -v agda >/dev/null 2>&1; then
  exec agda +RTS -M8G -RTS "$file"
elif [ -x "$HOME/.nix-profile/bin/agda" ]; then
  exec "$HOME/.nix-profile/bin/agda" +RTS -M8G -RTS "$file"
else
  exec nix shell nixpkgs#agda -c agda +RTS -M8G -RTS "$file"
fi
