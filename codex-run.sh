#!/usr/bin/env bash
# Launch Codex for the math team's π₃(S²) autoformalization, inside the agda-unimath working copy.
# Deploys the portable bundle (AGENTS.md + skill + check.sh) then runs the PLANNING step.
# Uses your global Codex config (gpt-5.5 / xhigh). PLAN ONLY — no proving, no library edits.
#
# Usage:  ./codex-run.sh            # planning run (default)
#         AGDA_UNIMATH=/path ./codex-run.sh   # override working-copy location
set -euo pipefail

REPO="${HOTT_REPO:-$HOME/projects6/HoTT-Auto}"   # deliverable source (this repo)
WORK="${AGDA_UNIMATH:-$HOME/agda-unimath}"       # agda-unimath working copy (Codex cwd)

[ -d "$WORK/src" ] || { echo "agda-unimath not found at $WORK (set AGDA_UNIMATH)"; exit 1; }

# 1) deploy the portable bundle into the working copy (idempotent — keeps it in sync)
cp "$REPO/AGENTS.md" "$WORK/AGENTS.md"
cp "$REPO/check.sh"  "$WORK/check.sh"; chmod +x "$WORK/check.sh"
mkdir -p "$WORK/.agent"
cp "$REPO/.claude/skills/agda-unimath-formalization/SKILL.md" "$WORK/.agent/agda-unimath-skill.md"

# 2) planning prompt (plan + dependency inventory; NO proving, NO library edits)
PROMPT="$(cat <<'PROMPT_EOF'
You are starting the math team's autoformalization project. FIRST read ./AGENTS.md and
./.agent/agda-unimath-skill.md in full and follow them.

TASK — PLANNING ONLY. Do NOT prove anything. Do NOT edit any file under src/. Do NOT add postulates.
Produce a formalization plan for **π₃(S²) = ℤ** (third homotopy group of the 2-sphere, as in the
HoTT book) targeting the agda-unimath library, and write it to ./FORMALIZATION-PLAN.md.

The plan MUST contain:
1. The mathematical route and its dependency chain (e.g. Hopf fibration, π_n(Sⁿ)=ℤ, the long exact
   sequence of a fibration, Freudenthal suspension — whatever the HoTT-book proof actually uses).
2. A DEPENDENCY INVENTORY table. For each prerequisite mark either
   EXISTS — with the concrete agda-unimath module path (find it with `rg` over src/), or
   MISSING — note where it could be ported from (e.g. the older HoTT-Agda library).
   Actually run ripgrep to check; do not guess.
3. Which agda-unimath namespaces/modules would need NEW additions; flag any high-fan-in targets
   (e.g. src/foundation) since extending them invalidates large caches.
4. A tractability/risk assessment and a recommended order of work (what to build first).

For any sanity typecheck use ./check.sh <file> (real agda); never trust scope-only tools.
End by printing a short summary: the route in one paragraph, and the EXISTS vs MISSING counts.
PROMPT_EOF
)"

# 3) pick codex (global on PATH, else via mise node 22)
if command -v codex >/dev/null 2>&1; then RUN=(codex); else RUN=(mise exec node@22 -- codex); fi

# 4) run headless; workspace-write lets it write the plan + run check.sh
cd "$WORK"
echo ">>> Codex planning run in $WORK (gpt-5.5/xhigh, sandbox=workspace-write). Plan → $WORK/FORMALIZATION-PLAN.md"
exec "${RUN[@]}" exec --sandbox workspace-write "$PROMPT"
