# Using `codex-run.sh` and `loop.sh` in this repo

Two scripts drive the π₃(S²) autoformalization, run from this repo root:
`codex-run.sh` makes a plan, and **`loop.sh` is the main driver** — it proves the
`tasks/queue.txt` modules one at a time. This repo is the source; Codex actually
works in a separate agda-unimath "sandbox" at `$HOME/agda-unimath` (override with
`AGDA_UNIMATH=/path`).

## How to use

**1. Plan** — deploy the bundle + run a plan-only Codex pass (writes the sandbox's
`FORMALIZATION-PLAN.md`):

```sh
./codex-run.sh
```

**2. Prove the queue** — the main driver; resumable, one atomic commit per verified
module on the sandbox work branch:

```sh
./loop.sh                          # run the queue (resumable)
REASONING=xhigh ./loop.sh          # bump reasoning effort (default: high)
MAX_ROUNDS=5    ./loop.sh          # driver retries per module before pausing
MODULE_TIMEOUT=2700 ./loop.sh      # seconds per codex call (default 1800)
WORK_BRANCH=my-branch ./loop.sh    # default: math-team-autoformalization
ESCALATE=1      ./loop.sh          # dormant best-of-N rescue on a bust (off by default)
```

> **First run?** Do the one-time **[Prerequisites](#prerequisites)** below first.

Outputs land in **this repo**: done-markers in `state/`, one JSONL telemetry line
per attempt in `telemetry/runs/loop-<RUN_ID>.jsonl`. Verified proofs are committed
in the **sandbox** on `$WORK_BRANCH`.

## Prerequisites

1. **A sandbox checkout** at `$HOME/agda-unimath` (or `AGDA_UNIMATH=/path`), on a
   dedicated work branch — never `master` (`WORK_BRANCH`, default
   `math-team-autoformalization`).
2. **Agda on `PATH` in the sandbox** so the deployed `./check.sh` is a real
   typecheck, not the scope-only MCP server:
   ```sh
   nix profile install nixpkgs#agda
   ```
3. **For `loop.sh` only** — create in *this* repo:
   - `tasks/queue.txt` — ordered, one **sandbox-relative** module path per line
     (e.g. `src/synthetic-homotopy-theory/foo.lagda.md`). `*`-prefix = human
     checkpoint after that module; `#` = comment.
   - `tasks/<id>.task.md` — a spec per module (`<id>` = basename without
     `.lagda.md`). Optional `tasks/<id>.sig` pins a target-signature substring the
     gate requires to survive.

## Inside `loop.sh` (key code)

- **`gate_verify <file>`** — the sound gate; the *driver*, not Codex, decides
  pass/fail. Four checks: real `./check.sh` typecheck (exit 0, no unsolved metas),
  no open holes (`?` / `{! !}`), no `postulate`, and — if `tasks/<id>.sig` is
  pinned — the target signature still present.
- **`build_prompt` / `run_codex`** — build one prompt (AGENTS.md + skill + the
  `tasks/<id>.task.md` spec + any retry feedback) and run `codex exec` headless in
  the sandbox, under `MODULE_TIMEOUT` at effort `REASONING`.
- **`prove_module`** — retry up to `MAX_ROUNDS`, feeding each gate failure back
  into the next prompt.
- **Main queue walk** — read `queue.txt` in order, skip `*.done` (resumable),
  atomic-commit each verified module, pause at `*` checkpoints / busts.
- **`escalate_best_of_n`** (`ESCALATE=1`, off by default) — N parallel attempts in
  isolated `git worktree`s; the compiler picks any that verifies.

## The two `check.sh` files (don't mix them up)

| File | Runs where | Library | Purpose |
|---|---|---|---|
| `./check.sh` (repo root) | this repo | `Codex-Homotopy-Group.agda-lib` (`src` + `agda-unimath/src` submodule) | local re-verification of artifacts brought back — **not** what the loop runs against |
| `check-sandbox.sh` → deployed as sandbox `./check.sh` | `$HOME/agda-unimath` | `agda-unimath.agda-lib` | the loop's proving gate |

For the repo-root local check, initialize the submodule first:
```sh
git submodule update --init --depth 1
```
