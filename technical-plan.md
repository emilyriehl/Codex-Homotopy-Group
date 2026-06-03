# Technical plan: a Codex-driven Agda autoformalization loop

> Goal: autoformalize known natural-language proofs from the HoTT book (first target:
> π₃(S²) = ℤ) into Agda / Agda-Unimath code (`.lagda.md`), filling in missing prerequisite
> lemmas first, with human experts in the loop, driven by Codex, while distilling reusable
> "agda-unimath skills."
>
> Default loop = **batch (whole-file write → check → feed-back iteration)**; interactive
> hole-filling is only a **point fallback**.
>
> Run host = **a single local machine (default: your Mac)**; Thor / k8s and other remote hosts
> are optional later extensions, **not a precondition**. The whole method is **host-agnostic** —
> the deliverable is a portable bundle, and switching machines just means redeploying the same
> bundle.

---

## 0. Positioning: this is AlphaProof Nexus's "Agent (A)" tier, not the whole picture

- **Task nature**: autoformalization — the proof is **known**; the difficulty is (1) engineering
  translation and (2) filling the library. This is *not* the open-conjecture solving (proof
  unknown) that AlphaProof Nexus headlines.
- **Corresponding tier**: equivalent to AlphaProof Nexus's **Agent (A)** — the naive loop of
  "LLM generates formal code → proof assistant checks → error feedback → iterate." Its Agent (A)
  uses "CoT + search-replace edits over a whole sketch, then compile," which is essentially
  **batch** (this is the basis for making batch the default here). It does not include B
  (dedicated RL solver) / C (evolutionary search) / D (autonomous fleet).
- **The endorsement and its boundary**:
  - AlphaProof Nexus: Agent (A) alone solved all 9 Erdős problems — the naive loop + compiler
    feedback was surprisingly sufficient.
  - The Megalodon experiment (arXiv:2601.03298): an isomorphic naive loop on a different proof
    system, 130k lines in two weeks for ~$100 — **corroborating reference** (different proof
    assistant; "same naive loop" is an inference, not a settled fact).
  - ⚠️ **The endorsement only covers the "translation" difficulty**: the paper limits Agent (A)'s
    success to the **mature-library** domain, whereas the **build-missing-prerequisites** half of
    π₃(S²) sits at the "immature library" frontier, outside the endorsement.
  - ⚠️ **The "needs a frontier LLM" evidence is Gemini-specific** (per the paper); **Codex/OpenAI's
    fit for Agda is unverified** and must be tested empirically.
- **Inference**: starting from the simplest batch loop is a validated correct starting point — no
  need to build a search engine up front; but the "build-prerequisites" sub-task needs its own
  budget and go/no-go gate.

---

## 1. Core decision: build a "Codex plugin layer," do not build a standalone agent

Do not build a complete agent from scratch. Extend Codex (it already natively supports MCP /
AGENTS.md / Skills / headless `codex exec`).

Split the project into **three layers, all model-independent** — it is both a "Codex plugin that
runs today" and a reusable foundation for "a complete in-house agent later." When B/C/D-tier
capabilities are needed, only the orchestration layer is augmented; the lower two layers stay put.

```
┌─────────────────────────────────────────────────────────────────────┐
│  Layer 3  Orchestration + telemetry  (codex exec wrapper / future    │  ← swappable; B·C·D added later
│           Agents SDK)                                                 │
├─────────────────────────────────────────────────────────────────────┤
│  Layer 2  Knowledge  (Codex Skills + AGENTS.md = agda-unimath skills) │  ← model-independent, a deliverable
├─────────────────────────────────────────────────────────────────────┤
│  Layer 1  Verification  (raw agda check script; the MCP server is     │  ← project core, reused across models
│           untrustworthy and has been retired)                         │
└─────────────────────────────────────────────────────────────────────┘
                                 ▲
            Codex (provides: planning / multi-turn tool calls / file editing / shell / error recovery)
```

- **Why not build a standalone agent**: Codex already provides the hardest parts for free
  (planning, multi-turn tool calls, file editing, shell, context management, error recovery); the
  naive loop is shown sufficient by two pieces of work; it fits the math team's constraints (use
  Codex, short-term, rough draft, human-in-the-loop); and the deliverables (skills, logs) are
  naturally Layers 2 and 3, surviving a "switch to an in-house model."
- **Why not use bare Codex either**: bare Codex does not understand Agda / Agda-Unimath / HoTT;
  without Layer-1 verification feedback and Layer-2 skills, the loop will not converge.

---

## 2. Layer 1 · Verification layer — **the only trustworthy verifier = raw `agda`** (not the MCP server)

> ⚠️ **Key measured finding (Thor + Mac, 2026-05-30)**: the stock `agda-mcp-server` 0.6.7 only does
> **scope-checking, not real type-checking**. On a file with a real type error injected,
> `agda_load` / `agda_typecheck` / `agda_load_no_metas` / `agda_proof_status` **all reported
> `ok-complete` with zero errors**, while raw `agda` errored precisely (`UnequalTerms: UU !=< A`).
> The source confirms it (full of "may not have been scope-checked"; reports `staleBeforeLoad: no`
> on just-edited files).
> **→ Never build the "is it proved?" gate on the MCP server, or the agent's false proofs will be
> accepted as "verified" — the project's most fatal failure mode.**

### Decision: Layer 1 = a check script that calls raw `agda`; the MCP server leaves the critical path
- **Trustworthy verification primitive**: `agda <agda-unimath flags> <file>.lagda.md` (flags
  auto-applied from the project `.agda-lib`). Exit code + stderr are the truth — raw agda gives
  `file:line:col + error message` and does **real** type-checking. Measured: precise error capture;
  cold 52s (128-module closure, Mac), warm re-check a few seconds.
- **Codex calls it directly in the shell** — the batch loop **does not need an MCP server at all**.
  Give Codex a `check.sh <file>` (= `nix shell nixpkgs#agda -c agda <flags> <file>`, already running
  on Mac/Thor). Codex's native "edit file → run command → read output" *is* this loop.
- **Disposition of the MCP server**: off the critical path, **not trustworthy for verification**;
  at most a later "for-reference-only, never a verification basis" interactive query (goal types,
  Mimer) — not used in this spike. → The earlier decision to "fork `agda-mcp-server`" is hereby
  **reversed**: not on the critical path, no need to fork, no need for `agda-language-server`.
- **The exploration was not wasted**: building the MCP server is exactly what **caught this fatal
  scope-check trap early** and produced the trustworthy raw-agda recipe + latency data.

### Default loop: batch (Codex + raw agda, no MCP)
- Codex edits a whole `.lagda.md` → runs `check.sh <file>` (raw agda, **real** type-check) → reads
  the real `file:line:col` errors → fixes → iterates. Error locations already point at the true
  line/column in the literate source. This is exactly the Megalodon / AlphaProof Agent (A) loop.
- **The gate ("is it proved?") = raw `agda` exit code 0 + no leftover holes `?`/`{! !}` in the file
  + agda reports no unsolved metas**; then `make pre-commit` before a PR.
- **Interactive hole-filling**: **not done** in this spike (MCP untrustworthy, and batch is already
  enough). Later, for goal types / Mimer, find a trustworthy source (agda's own interaction mode +
  careful verification), **never relying on a stock server's "ok."**
- **In-library lemma search**: first **ripgrep** the repo (by name/type) + human experts; encode
  "search the library before import/postulate" as a skill rule. **Do not build a full-library
  index** (one target + an expert team don't justify it).

### Anti-cheating gates (must be engineered — two distinct failure modes)

AlphaProof Nexus recorded two independent failure modes; this project (translating LaTeX statements
into Agda types) must especially guard against them:

1. **Goal-signature integrity**: **pin/hash** the target theorem's type signature at the start;
   **diff** on every reload; reject any change to the goal or its hypotheses (prevents silently
   weakening the goal). The paper's Validator responsibility of "unmodified statement" must land in
   this mechanism, not just in a risk column.
2. **Anti-hallucination lemmas**: ⚠️ in Agda, a false lemma written as a `postulate` **passes type
   checking cleanly** (zero unsolved metas). So: **grep to ban/flag `postulate` in agent-edited
   regions**; any reference claimed as "already in the library" must resolve to a **real module path
   that raw agda can type-check**.
3. **OEIS-style test-lemma**: a human first **signs off on the formalized "type"** and proves a few
   cheap corollaries before attacking the main proof.

### Speed plan (fast enough is fine; measure first, add later — do not pre-optimize)

> The math team is explicit: "do not optimize anything right now." So **first build only the
> necessary minimum, then measure real iteration latency before deciding whether to add a caching
> pipeline.**

> **✅ Measured (raw agda; Mac M-series + Thor aarch64, 2026-05-30)**: taking
> `foundation.equivalences` (24KB, 128-module closure) as an example — **cold build of the whole
> closure 52s (Mac) / 70s (Thor)**, producing 128 `.agdai`; **warm re-check of that active module
> ~2–4s**. Conclusion: **as long as the `_build/.agdai` cache is warm and the active proof is
> isolated into a small module, inner-loop latency is in seconds** — the original #1 risk is mild in
> practice. A cold closure of ~50–70s / 128 modules → warming the target prelude is a one-time
> bounded cost.

- **Must build (a precondition for convergence)**: ① a **precompiled, frozen prelude** (real
  type-check via raw agda / `make` into valid `.agdai`), which the active proof only `open import`s;
  ② **never run `make check` in the inner loop** (whole library ~15–33 min, peak ~4.4 GiB RAM).
- **Each raw agda call** loads the cached interfaces from disk (~2–3s startup) + re-checks the
  active module — seconds total when warm, entirely enough for a human-in-the-loop rough draft,
  **no long-lived process needed**.
- **Add only after measuring (if iteration is too slow)**: reuse `_build/*.agdai` caches as
  agda-unimath CI does (keyed by `hashFiles(src/**)`); **freeze the prelude** during proving, then
  deliberately re-warm after new prerequisites land in batch (editing the high-fan-in 583-file
  `src/foundation` invalidates a large area).

### What to reuse from where
- **agda-unimath itself**: the **exact flag set** from `.agda-lib` + the Makefile, the
  `make pre-commit` final gate, `make profile-module`/`make graph`, the `_build` cache pattern,
  `setup-agda` (how to install a precompiled Agda).
- **Nix**: `nix shell nixpkgs#agda` provides a version-locked Agda 2.8.0 (native Mac / Linux alike),
  the substrate of `check.sh`.
- **MCP server (off the critical path)**: if interactive goal types / Mimer are wanted later, the
  IOTCM wrapping approach can be a reference — but **any "ok" must be re-checked with raw agda**.

---

## 3. Layer 2 · Knowledge layer (Codex Skills + AGENTS.md) — the deliverable "agda-unimath skills"

Use SKILL.md modular skill packs + a repo-root AGENTS.md to encode domain knowledge. Pure Markdown,
model-independent, directly feedable to a co-PI's in-house model. Analogous to `leanprover/skills`
(agda-unimath has no ready equivalent — this is greenfield).

**Skill content that should be covered**
- Agda-Unimath naming conventions, directory structure, `import` habits, `.lagda.md` format rules.
- How to read goal state / advance via holes; common proof patterns; idiomatic constructions under
  `--without-K`/`--exact-split` and similar constraints.
- How to find and port prerequisite lemmas that exist in other HoTT libraries but are missing from
  Agda-Unimath.
- **Rule: ripgrep the library before any import/postulate** (prevents re-proving / hallucination).

**merge-readiness norms (the real bar for deliverable i)**
- Passing `make pre-commit` is **far from enough**. The library requires: explanatory mathematical
  prose per definition, descriptive naming, **source citations**, file templates, and
  `CONTRIBUTORS.toml` attribution.
- Add a human "**reads like a proper agda-unimath document**" sign-off gate (on top of
  `make pre-commit`).
- ✅ **Up-front confirmation (the math team can do this; not a build task)**: **Egbert Rijke is on
  the team** — directly confirm whether agda-unimath accepts AI-attributed PRs and how attribution
  works. This is a precondition for deliverable (i).

**Skill iteration loop (the mechanism producing deliverable iii)**
- Skills are **not static content** — the supervisor distills failure transcripts into SKILL.md
  increments, validated by regression, then merged. Every run feeds back into this loop, gradually
  growing the "agda-unimath skills."

---

## 4. Layer 3 · Orchestration + telemetry layer (codex exec wrapper) — the deliverable "report document"

A thin wrapper script that headlessly drives the batch loop with `codex exec`.

### Telemetry schema + USD ledger (deliverable ii; the math team flagged metrics twice)
- **One JSONL line per episode**: `timestamp, prompt, tokens_in/out, usd, tool_calls,
  typecheck_pass/fail, human_intervention{flag,type}, edit_author=AI|human`.
- **token × model unit-price → USD ledger**, with a **credit-burn alert** (the whole premise of
  using Codex is that OpenAI donation credit — don't burn it out).
- **Report metrics** (borrowing the paper's vocabulary): USD per proved lemma, episodes-to-
  convergence, first-pass type-check rate, AI/human step ratio, lines-per-dollar (Megalodon-style).
- **Specify what the June / August DARPA snapshots each contain** (which metrics + how far
  formalization progressed).

### Checkpoint protocol (human-in-the-loop + autonomy boundary)
- Define **which events pause the loop** (plan review, phase-artifact review, the go/no-go after
  dependency inventory).
- Specify the **autonomy boundary**: may the agent edit the frozen prelude unsupervised (default
  **no**).
- Pause/resume rules for headless `codex exec` runs vs forced human checkpoints.
- **Tag every edit with `author=AI|human`** (into the same telemetry log) — for honest PR
  attribution and the DARPA "human interaction" report.

### Budget cap + go/no-go
- Set a **USD / episode / wall-clock cap** per target.
- **A human go/no-go immediately after dependency inventory**: decide whether the target is doable,
  or trigger a pivot endorsed by the math team (a pivot is a first-class gate, not an afterthought).

### Forward compatibility (one line each, expand as needed)
- B/C/D (multiple parallel attempts, best-of-N, scoring/selection) are all added later in this
  layer; or use the OpenAI Agents SDK to orchestrate the Codex CLI as an MCP server. **Do not
  front-load these details in a short-term experiment.**

---

## 5. Run host: one machine, one filesystem (default = your Mac)

### The only real constraint: the files Codex edits and the files agda checks are on one filesystem
The deeper fact: Codex **edits** `.lagda.md`, and agda must **type-check the same files** (using the
`_build` cache). So **{Codex's file edits} + {raw agda} + {repo/cache}** must see **the same
filesystem**.
- Since verification = Codex running raw agda in its own shell (**no MCP server**), this is satisfied
  naturally: **one machine, one filesystem.**
- (Counter-example: putting agda on a remote and Codex local makes the files two copies that must be
  constantly synced — asking for trouble. Same machine is simplest.)
- **Conclusion: put it on one machine, the constraint is satisfied automatically at zero cost — and
  it binds to no particular machine.**

### Default host = your Mac (spike and early development)
The Mac is Apple Silicon (aarch64). Agda 2.8.0 has a macOS build in nixpkgs; Node 24 (one mise
line); the npm server and Codex both have macOS builds. Agda only uses ~4.4 GiB and **no GPU** — any
16GB+ Mac runs it easily, and **macOS has none of Ubuntu's userns restrictions**, so it's even less
hassle than remote Linux. Two paths:
- **Path A (native, no Docker)**: install Nix on the Mac (one `sudo`) → `nix shell nixpkgs#agda` +
  mise node24 + server + Codex.
- **Path B (zero learning cost)**: carry the ARM-verified "nixos/nix container" recipe onto the
  Mac's Docker Desktop, **1:1 identical**.

The resulting `.lagda.md` is platform-independent; same Agda 2.8.0 → matches agda-unimath's Linux CI
result. **So doing this locally on the Mac has no obstacle whatsoever.**

### Remote host (Thor / k8s) = optional, later, for scale — **not a precondition**
Moving to a shared / always-on host is **only for three scale needs** (none about correctness): ①
multi-supervisor collaboration (shared warm cache); ② always-on / unattended (long runs not tying up
a laptop); ③ more parallelism. **None of these apply now** (k8s is a week out, and the spike doesn't
need it).
- Because **the deliverable is a portable bundle** (AGENTS.md + skills + `check.sh` + Codex config),
  switching hosts = redeploying the same bundle on a new machine, **the method unchanged, fully
  reversible, near-zero cost**.
- **Thor**: a verified "optional always-on box" (Agda 2.8.0 + Codex working; the Nix-in-Docker recipe
  carries 1:1 to the Mac). Use it for long / laptop-free runs; otherwise unnecessary.
- **k8s**: the future home for team sharing / scaling, **not the current precondition**.

### Multi-supervisor shared repo = a later collaboration-phase concern (no issue in single-machine solo dev)
Relevant only when several people share one host: git branch-per-target-lemma, PRs into a **team
fork**, a unified log location; under concurrency, one session + working copy per supervisor (mirror
`sessionId` isolation), with the prelude / `_build` explicitly "shared read-only" or "one per
supervisor."

### Host selection: a CPU/memory workload, not GPU
Agda type-check uses **CPU + ~4.4 GiB RAM, no GPU**; Codex is an API call and uses no local GPU
either. So GPU dev kits (the GPU part of Spark/Thor) are useless for this workload — **any 16GB+
x86/ARM Linux or macOS machine works, and your Mac is exactly one.**

---

## 6. Workflow (end-to-end, batch-first)

1. **NL → plan**: have Codex make a formalization plan for the target (π₃(S²)=ℤ, per the HoTT book
   `homotopy.tex`), **inventorying the prerequisites missing from Agda-Unimath** (this step is itself
   a key artifact).
2. **Human review of the plan.**
3. **Dependency inventory → go/no-go gate**: clarify which prerequisites to build and in which
   modules (high fan-in?); set the budget cap; a human decides continue or pivot.
4. **Batch main loop**: Codex writes a whole `.lagda.md` → runs `check.sh` (raw agda, real type
   check) → feeds the real `file:line:col` errors back → iterates. **No interactive mode** (MCP
   untrustworthy).
5. **Build missing prerequisites**: first ripgrep + experts to find them in other HoTT libraries →
   port / re-prove → pass the anti-cheating gates → land in the library (mind the re-warming strategy
   for high-fan-in modules).
6. **Convergence** → raw `agda` exit 0 + no leftover holes / unsolved metas + `make pre-commit` +
   merge-readiness human sign-off → PR into the team fork; transcripts distilled back into Layer-2
   skills, telemetry rolled into the Layer-3 report.

---

## 7. Risk register

| Risk | Detail | Mitigation |
|------|--------|------------|
| **MCP-server verification is untrustworthy (measured, critical)** | stock `agda-mcp-server` 0.6.7 only scope-checks; on real type errors it still reports `ok-complete`, zero errors | **Verify with raw `agda`** (proven to catch errors precisely); MCP off the critical path; re-check any "ok" with raw agda |
| **Hallucinated lemmas / silently weakened goal** (two failure modes) | a `postulate` false lemma passes type-check cleanly; mistranslated / weakened goal type | pin + diff the goal signature; grep ban/flag `postulate` in agent regions; references must resolve to real type-checkable modules; OEIS-style test-lemma + human-approved type |
| Host setup (one-time, not "can't run") | any 16GB+ machine works (**including your Mac**); just install Agda 2.8.0 + Node 24 (for Codex) | native Nix on Mac (verified); warm the cache once on cold start; k8s arrives in a week, not a precondition |
| **Agda checking is slow** (measured, downgraded to mild) | whole library ~15–33 min; but **measured warm single-module re-check is only ~2–4s**, cold closure ~52s (Mac) / 70s (Thor) / 128 modules | freeze a precompiled prelude + isolate the active proof into a small module; never `make check` in the inner loop. Strategy validated in practice |
| **Flag inconsistency** | without the full flag set → passes locally, fails CI | `.agda-lib` auto-apply + everything-opts passed to `check.sh` (raw agda); `make pre-commit` final gate |
| Topology risk that only arises when splitting hosts (**absent by default on one machine**) | only if Codex and agda are on **different machines**: file sync needed; concurrency hazards when shared by many | **default single machine / one filesystem has no such issue**; handle splitting / multi-supervisor only if actually needed (see §5) |
| **merge-readiness underestimated** | passing `make pre-commit` ≠ mergeable; missing prose / naming / citations / attribution | skills encode library norms + a human "reads like a proper document" sign-off; **confirm AI-PR acceptance and attribution with Rijke first** |
| **The (A)-tier endorsement extrapolated too far** | the endorsement covers only "translation" difficulty; "build prerequisites" is at the immature-library frontier; the frontier-LLM evidence is Gemini-specific | separate the two sub-tasks; go/no-go + budget cap after dependency inventory; treat Codex-fit-for-Agda as unverified, spike first |
| Input format | NL proofs are in LaTeX/PDF; output must be `.lagda.md` | **use the LaTeX/text source (`homotopy.tex` is ready-made), not PDF**; skills spell out the LaTeX→lagda.md conventions |

---

## 8. In one sentence

Treat the project as the triad `raw agda check script + agda-unimath Skills + codex exec telemetry
wrapper` (one Codex plugin pack): **the batch loop (Codex edits → raw agda real verification → feed
back `file:line:col` errors) reproduces the AlphaProof Nexus Agent (A) that was shown to be
sufficient.** Verification **trusts only raw agda** (the stock MCP server was measured to only
scope-check, untrustworthy); all three layers are model-independent and form the foundation of a
future complete in-house agent — when stronger search is needed, just add B/C/D at the orchestration
layer. First spike on the **local Mac** to verify the naive loop converges, then invest in
infrastructure.
