# Using `codex-run.sh` and `loop.sh` in this repo

These two scripts drive the π₃(S²) autoformalization. They were carried over
from the **HoTT-Auto** repo and use the same architecture:

- **This repo is the deliverable source.** It holds the plan, the task queue,
  telemetry, and the portable bundle that gets deployed (`AGENTS.md`,
  `check-sandbox.sh`, the `.codex` skill).
- **Codex works in a separate agda-unimath checkout** — the "sandbox" — at
  `$HOME/agda-unimath` (override with `AGDA_UNIMATH=/path`). New modules are
  written and committed **there**, on a dedicated work branch, against
  agda-unimath's own `agda-unimath.agda-lib`.

> The submodule at `./agda-unimath` and the combined
> `Codex-Homotopy-Group.agda-lib` are a **separate** concern: they let you
> locally re-verify artifacts brought back into this repo with the repo-root
> `./check.sh`. They are **not** what the loop runs against.

## Status: proof of concept

This loop is a **proof of concept**, not a finished pipeline. Two known
limitations:

1. **The gate may not be strong enough.** `loop.sh`'s `gate_verify` enforces
   four checks — a real `agda` typecheck, no open holes, no `postulate`, and
   (only if a `.sig` is pinned) an unchanged target signature. That is a first
   cut and may not be sufficient to guarantee a faithful proof: it does not
   catch weakened/renamed statements without a pinned `.sig`, reliance on
   unproven lemmas defined elsewhere, unsolved-metas escapes, or trivially-true
   restatements. Expect to harden these checks before trusting the output.
2. **No MCP yet.** These bash scripts drive Codex directly. The intended
   direction is to replace this driver with an **MCP-based service**; the
   scripts are the interim mechanism, not the destination.

## What already differs from HoTT-Auto (already applied — nothing to do)

Only two path facts differ, and both scripts are already patched for them:

1. `HOTT_REPO` / `REPO` **auto-locate this repo from the script's own path**
   (`$(cd "$(dirname "$0")" && pwd)`) — no hard-coded local path, so it works
   wherever each collaborator clones it.
2. `codex-run.sh` deploys this repo's `.codex/skills/agda-unimath-skills/SKILL.md`
   (HoTT-Auto used `.claude/skills/...`) and deploys `check-sandbox.sh` as the
   sandbox's `./check.sh` (this repo's *root* `check.sh` is submodule-aware and
   would not run in the flat sandbox).

Everything else (`WORK=$HOME/agda-unimath`, the deploy target
`.agent/agda-unimath-skill.md`, in-sandbox paths like
`src/foundation/equivalences.lagda.md`) is **sandbox-side and correct as-is** —
do not repoint it at this repo.

**Shared repo / per-machine paths.** Nothing points at any one person's
machine. The repo locates itself (above); the sandbox defaults to `$HOME/agda-unimath`
— i.e. *each collaborator's own home* — and anyone who keeps it elsewhere just sets
`AGDA_UNIMATH=/their/path` (and, if desired, `WORK_BRANCH`). No edit to the
scripts is needed per person.

## Prerequisites

1. **A sandbox checkout** at `$HOME/agda-unimath` (or `AGDA_UNIMATH=/path`), on a
   dedicated work branch — never `master`. The loop uses `WORK_BRANCH`
   (default `math-team-autoformalization`).
2. **Agda on `PATH` in the sandbox** so the deployed `./check.sh` is a real
   typecheck, not the scope-only MCP server:
   ```sh
   nix profile install nixpkgs#agda
   ```
3. **For `loop.sh` only** — create in *this* repo:
   - `tasks/queue.txt` — ordered, one **sandbox-relative** module path per line
     (e.g. `src/synthetic-homotopy-theory/foo.lagda.md`, i.e. relative to the
     agda-unimath sandbox root). `*`-prefix forces a human checkpoint after that
     module; `#` starts a comment.
   - `tasks/<id>.task.md` — a spec per module, where `<id>` is the basename
     without `.lagda.md`. Optional `tasks/<id>.sig` pins the target signature
     (a verbatim substring the gate requires to survive).

## 1. Planning run — `codex-run.sh`

Deploys the bundle into the sandbox, then runs a **plan-only** Codex pass (no
proving, no edits under `src/`). Writes the plan to the **sandbox's**
`FORMALIZATION-PLAN.md`.

```sh
./codex-run.sh                      # from this repo root
AGDA_UNIMATH=/path ./codex-run.sh   # point at a different sandbox
```

Uses your global Codex config (gpt-5.5 / xhigh), sandbox `workspace-write`.
(A plan already exists in this repo as `FORMALIZATION-PLAN.md`, copied back from
an earlier run; a fresh planning pass overwrites only the sandbox's copy.)

## 2. Proving driver — `loop.sh`

Walks `tasks/queue.txt` one module at a time in the sandbox. The **driver**
(not Codex) verifies each module with the deployed `./check.sh` + no-postulate +
no-holes + unchanged-signature, then makes an **atomic commit per module** on the
sandbox work branch. Re-running skips modules with a `state/<id>.done` marker
(resumable); it pauses on `*` checkpoints and on budget busts.

```sh
./loop.sh                          # run the queue (resumable)
REASONING=xhigh ./loop.sh          # bump reasoning effort (default: high)
MAX_ROUNDS=5    ./loop.sh          # driver retries per module before pausing
MODULE_TIMEOUT=2700 ./loop.sh      # seconds per codex call (default 1800)
WORK_BRANCH=my-branch ./loop.sh    # default: math-team-autoformalization
ESCALATE=1      ./loop.sh          # dormant best-of-N rescue on a bust (off by default)
```

Outputs live in **this repo**: done-markers in `state/`, one JSONL telemetry
line per attempt in `telemetry/runs/loop-<RUN_ID>.jsonl`. Verified proofs are
committed in the **sandbox** on `$WORK_BRANCH` — bring finished modules back into
this repo's `src/` for archival and local re-verification with the repo-root
`./check.sh`.

## The two `check.sh` files (don't mix them up)

| File | Runs where | Library | Purpose |
|---|---|---|---|
| `./check.sh` (repo root) | this repo | `Codex-Homotopy-Group.agda-lib` (`src` + `agda-unimath/src` submodule) | local human verification of this repo's artifacts |
| `check-sandbox.sh` → deployed as sandbox `./check.sh` | `$HOME/agda-unimath` | `agda-unimath.agda-lib` | the loop's proving gate |

For the repo-root local check you also need the submodule initialized:
```sh
git submodule update --init --depth 1
```

## Optional: Agda MCP server

Agents may use the Agda MCP server for interactive proof development — see
`MCP-SETUP.md`. It is **not** the verification gate; final acceptance is always a
real `./check.sh <file>`.
