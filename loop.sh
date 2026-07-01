#!/usr/bin/env bash
# loop.sh — autoformalization driver (Layer 3).
#
# DESIGN (see technical-plan.md §4 and the loop-vs-workflow discussion):
#   • SERIAL BACKBONE: Codex proves ONE module at a time, in dependency order.
#   • SOUND GATE: the DRIVER (not Codex) verifies each module with raw `agda` (./check.sh)
#     + grep-no-postulate + no-holes + signature-unchanged. Codex's self-report is NEVER trusted.
#   • ATOMIC COMMIT per verified module (on a work branch) → durable, auditable, rollback-able.
#   • RESUMABLE: re-running skips modules already marked done.
#   • PER-MODULE BUDGET: MAX_ROUNDS driver re-invocations; MODULE_TIMEOUT per codex call.
#   • HUMAN CHECKPOINTS: pause on '*'-flagged modules and on budget busts.
#   • DORMANT best-of-N escalation (ESCALATE=1): on a bust, fan out N parallel attempts in
#     isolated git worktrees; the COMPILER picks the winner. Off by default.
#   • TELEMETRY: one JSONL line per codex attempt (tokens/pass/fail) → telemetry/runs/.
#
# PREREQUISITES before a real run:
#   1. The math team's decisions: chosen target module(s), confirmed signatures, billing path.
#   2. ./check.sh works in Codex's sandbox  → `nix profile install nixpkgs#agda` (see DECISION-BRIEF).
#   3. tasks/queue.txt populated (ordered) + a tasks/<id>.task.md spec per module (+ optional <id>.sig).
#
# Usage:  ./loop.sh                 # run the queue (resumable)
#         ESCALATE=1 ./loop.sh      # enable best-of-N rescue on busts
#         REASONING=xhigh ./loop.sh # bump effort (default: high)
set -uo pipefail   # deliberately NOT -e: per-module failures are handled, not fatal

# ---------- config (override via env) ----------
HOTT_REPO="${HOTT_REPO:-$(cd "$(dirname "$0")" && pwd)}"   # this repo (auto-located from the script path)
WORK="${AGDA_UNIMATH:-$HOME/agda-unimath}"          # agda-unimath working copy (Codex cwd)
WORK_BRANCH="${WORK_BRANCH:-math-team-autoformalization}"
MAX_ROUNDS="${MAX_ROUNDS:-3}"                        # driver re-invocations per module before pausing
MODULE_TIMEOUT="${MODULE_TIMEOUT:-1800}"            # seconds per codex exec
ESCALATE="${ESCALATE:-0}"                            # 0 = dormant; 1 = best-of-N on bust
ESCALATE_N="${ESCALATE_N:-3}"
REASONING="${REASONING:-high}"                       # xhigh = pricey; reserve for hard modules
CODEX_BIN="${CODEX_BIN:-codex}"

TASKS="$HOTT_REPO/tasks"
STATE="$HOTT_REPO/state"
TELEM="$HOTT_REPO/telemetry/runs"
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)"
LOG="$TELEM/loop-$RUN_ID.jsonl"
mkdir -p "$STATE" "$TELEM" "$TASKS"

say() { printf '\033[1m>>> %s\033[0m\n' "$*"; }
ts()  { date -u +%FT%TZ; }

with_timeout() { local t="$1"; shift
  if   command -v timeout  >/dev/null 2>&1; then timeout  "$t" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then gtimeout "$t" "$@"
  else "$@"; fi; }

# latest codex session's cumulative token total (best-effort)
codex_tokens() {
  local f; f="$(find "$HOME/.codex/sessions" -type f -name 'rollout-*.jsonl' 2>/dev/null | xargs ls -t 2>/dev/null | head -1)"
  [ -n "${f:-}" ] || { echo NA; return; }
  grep -oE '"total_tokens":[0-9]+' "$f" 2>/dev/null | tail -1 | grep -oE '[0-9]+' || echo NA
}

telem() { # module round verified gate tokens note
  printf '{"ts":"%s","run":"%s","module":"%s","round":%s,"reasoning":"%s","verified":%s,"gate":"%s","tokens":"%s","note":"%s"}\n' \
    "$(ts)" "$RUN_ID" "$1" "$2" "$REASONING" "$3" "$4" "$5" "${6:-}" >> "$LOG"; }

# ---------- the SOUND gate (independent of Codex) ----------
GATE_OUT=""   # populated with the failing detail for feedback
gate_verify() { # <relative-file>  -> 0 if fully verified
  local file="$1" out
  GATE_OUT=""
  # 1) real type-check
  out="$( cd "$WORK" && ./check.sh "$file" 2>&1 )"; local rc=$?
  if [ $rc -ne 0 ]; then GATE_OUT="typecheck FAILED (exit $rc):\n$(printf '%s' "$out" | grep -iE 'error|warning' | head -20)"; echo typecheck; return 1; fi
  if printf '%s' "$out" | grep -qiE 'unsolved (meta|constraint|interaction)'; then GATE_OUT="unsolved metas/constraints remain:\n$(printf '%s' "$out" | grep -iE 'unsolved' | head)"; echo metas; return 1; fi
  # 2) no open holes left in the file
  if grep -nE '\{!|(^|[[:space:]])\?([[:space:]]|$|\))' "$WORK/$file" >/dev/null 2>&1; then GATE_OUT="open holes ('?' / '{! !}') remain in $file"; echo holes; return 1; fi
  # 3) no postulate in authored code (anti-hallucination)
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)' "$WORK/$file" >/dev/null 2>&1; then GATE_OUT="forbidden 'postulate' present in $file"; echo postulate; return 1; fi
  # 4) target signature unchanged (anti goal-weakening) — if a pinned .sig exists
  local id; id="$(basename "${file%.lagda.md}")"
  if [ -f "$TASKS/$id.sig" ] && ! grep -Fqf "$TASKS/$id.sig" "$WORK/$file"; then GATE_OUT="pinned signature (tasks/$id.sig) NOT found verbatim in $file"; echo signature; return 1; fi
  echo ok; return 0
}

build_prompt() { # <file> <id> [feedback]   (bash-3.2 safe: no ${x:+} / no inline $() in heredoc)
  local file="$1" id="$2" fb="${3:-}" spec fbsection=""
  if [ -f "$TASKS/$id.task.md" ]; then spec="$(cat "$TASKS/$id.task.md")"; else spec="(no spec at tasks/$id.task.md — use AGENTS.md / FORMALIZATION-PLAN.md)"; fi
  if [ -n "$fb" ]; then fbsection="

YOUR PREVIOUS ATTEMPT FAILED THE DRIVER'S VERIFICATION. Fix it. Detail:
$fb"; fi
  cat <<EOF
FIRST read ./AGENTS.md and ./.agent/agda-unimath-skill.md and follow them.

TASK: implement and PROVE the module \`$file\` in the agda-unimath library.

$spec

RULES (hard):
- Verify ONLY with ./check.sh "$file" (real agda). Do NOT trust any MCP/scope-only "ok".
- Done means: ./check.sh exits 0, NO open holes (? / {! !}), NO unsolved metas, NO 'postulate'.
- Do NOT change the target type signature. Search the library (rg) before re-proving or importing.
- Write proper agda-unimath literate prose around every definition.$fbsection
EOF
}

run_codex() { # <prompt>  (cwd = WORK).  </dev/null so codex doesn't block on stdin when headless.
  ( cd "$WORK" && with_timeout "$MODULE_TIMEOUT" "$CODEX_BIN" exec --sandbox workspace-write \
      -c model_reasoning_effort="$REASONING" "$1" </dev/null ) 2>&1 | tail -40
}

prove_module() { # <file> <id>  -> 0 verified, 1 bust
  local file="$1" id="$2" round fb="" gate
  for round in $(seq 1 "$MAX_ROUNDS"); do
    say "[$id] round $round/$MAX_ROUNDS (reasoning=$REASONING)"
    run_codex "$(build_prompt "$file" "$id" "$fb")" >/dev/null
    gate="$(gate_verify "$file")"
    if [ "$gate" = ok ]; then telem "$id" "$round" true ok "$(codex_tokens)" "verified"; return 0; fi
    telem "$id" "$round" false "$gate" "$(codex_tokens)" "retry"
    fb="$(printf '%b' "$GATE_OUT")"
    say "[$id] not verified ($gate). $( [ "$round" -lt "$MAX_ROUNDS" ] && echo retrying || echo budget exhausted )"
  done
  return 1
}

# ---------- DORMANT: best-of-N rescue (ESCALATE=1), compiler picks the winner ----------
escalate_best_of_n() { # <file> <id>  -> 0 if some attempt verified (merged), 1 otherwise
  local file="$1" id="$2" i wt rc=1
  say "[$id] ESCALATION: $ESCALATE_N parallel attempts in isolated worktrees"
  for i in $(seq 1 "$ESCALATE_N"); do
    wt="$WORK.attempt$i"
    git -C "$WORK" worktree add -f --detach "$wt" >/dev/null 2>&1 || continue
    ( cd "$wt" && cp "$WORK/check.sh" . 2>/dev/null
      with_timeout "$MODULE_TIMEOUT" "$CODEX_BIN" exec --sandbox workspace-write \
        -c model_reasoning_effort="${ESCALATE_REASONING:-xhigh}" \
        "$(AGDA_UNIMATH="$wt" build_prompt "$file" "$id" "ESCALATED attempt $i — try a DIFFERENT strategy/decomposition.")" >/dev/null 2>&1 ) &
  done
  wait
  for i in $(seq 1 "$ESCALATE_N"); do
    wt="$WORK.attempt$i"
    if [ -f "$wt/$file" ] && ( cd "$wt" && ./check.sh "$file" >/dev/null 2>&1 ); then
      cp "$wt/$file" "$WORK/$file"; rc=0; say "[$id] winner: attempt $i"; fi
    git -C "$WORK" worktree remove --force "$wt" >/dev/null 2>&1
  done
  [ $rc -eq 0 ] && [ "$(gate_verify "$file")" = ok ]
}

commit_module() { # <file> <id>
  git -C "$WORK" add "$file"
  git -C "$WORK" commit -q -m "prove($1): verified by agda [AI, loop $RUN_ID]" || true
  : > "$STATE/$2.done"
}

pause() { say "PAUSED: $*"; printf '%s\n' "$*" > "$STATE/PAUSED"; say "review, then re-run ./loop.sh to resume"; exit 2; }

# ---------- preflight ----------
[ -d "$WORK/src" ]      || { echo "no agda-unimath at $WORK (set AGDA_UNIMATH)"; exit 1; }
[ -x "$WORK/check.sh" ] || { echo "deploy check.sh first (run ./codex-run.sh once, or cp check.sh)"; exit 1; }
command -v "$CODEX_BIN" >/dev/null 2>&1 || { echo "codex not on PATH (set CODEX_BIN)"; exit 1; }
[ -f "$TASKS/queue.txt" ] || { echo "populate $TASKS/queue.txt first (see comments in it)"; exit 1; }
( cd "$WORK" && ( ./check.sh src/foundation/equivalences.lagda.md >/dev/null 2>&1 || pause "check.sh cannot run here — apply the Codex-sandbox fix (nix profile install nixpkgs#agda)" ) )
[ -f "$STATE/PAUSED" ] && { say "clearing previous PAUSE ($(cat "$STATE/PAUSED"))"; rm -f "$STATE/PAUSED"; }
# work on a dedicated branch, never master
git -C "$WORK" rev-parse --verify "$WORK_BRANCH" >/dev/null 2>&1 \
  && git -C "$WORK" checkout -q "$WORK_BRANCH" \
  || git -C "$WORK" checkout -q -b "$WORK_BRANCH"

say "loop $RUN_ID | branch=$WORK_BRANCH | escalate=$ESCALATE | telemetry=$LOG"

# ---------- main: walk the ordered queue ----------
while IFS= read -r line; do
  line="${line%%#*}"; line="$(echo "$line" | xargs)"; [ -z "$line" ] && continue
  checkpoint=0; case "$line" in \** ) checkpoint=1; line="${line#\*}"; line="$(echo "$line" | xargs)";; esac
  file="$line"; id="$(basename "${file%.lagda.md}")"
  [ -f "$STATE/$id.done" ] && { say "[$id] already done — skip"; continue; }

  if prove_module "$file" "$id"; then
    commit_module "$file" "$id"; say "[$id] ✅ verified & committed"
    [ "$checkpoint" = 1 ] && pause "checkpoint after $id — human review this proof before continuing"
  else
    if [ "$ESCALATE" = 1 ] && escalate_best_of_n "$file" "$id"; then
      commit_module "$file" "$id"; say "[$id] ✅ verified via escalation & committed"
    else
      telem "$id" 0 false bust "$(codex_tokens)" "budget/escalation exhausted"
      pause "budget bust on $id — needs human help (or set ESCALATE=1). Detail: ${GATE_OUT}"
    fi
  fi
done < "$TASKS/queue.txt"

say "🎉 queue complete. Verified modules committed on $WORK_BRANCH. Next: make pre-commit + human PR review."
