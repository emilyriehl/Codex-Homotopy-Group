# The Math Team's Agda Autoformalization Experiment — Plan (for the math team)

> **Goal.** Use Codex to formalize a *known* HoTT proof — first target: π₃(S²) = ℤ from the
> HoTT book — into Agda / Agda-Unimath (`.lagda.md`), filling in the prerequisites that are
> missing from the library, with your experts in the loop. Produce three things: a PR-ready
> formalization, a documented record for DARPA, and reusable "agda-unimath skills."

*Audience: the math team (the lead, the postdoc, the PhD student — all mathematicians). The technical
Layer-1 details live in the appendix, labeled "for the DSAI engineer."*

---

## 1. What you actually do, step by step

1. **Ask Codex for a plan.** Prompt it to lay out how it would formalize π₃(S²) = ℤ following
   the HoTT book (`homotopy.tex`), and to **list which prerequisites are missing** from
   Agda-Unimath. This list is itself a valuable artifact.
2. **Review the plan** as a team; correct it.
3. **Dependency check → go/no-go.** Decide which prerequisites must be built and where they
   live in the library. Set a spending cap. **Then a human checkpoint decides:** proceed, or
   pivot to an easier target (your call — this is built in, not a failure).
4. **Run the loop (batch-first).** Codex edits a whole `.lagda.md` file → Agda type-checks it →
   the errors go back to Codex → it tries again. This "write → check → fix" loop is exactly the
   simple loop that DeepMind's AlphaProof Nexus and the Megalodon experiment both showed is
   surprisingly effective. *(When Codex gets stuck on one hard hole, the engineer's tooling can
   switch that single hole to Agda's interactive mode — but that's the fallback, not the default.)*
5. **Build the missing prerequisites:** search other HoTT libraries first, port/re-prove,
   pass the anti-cheating checks, add to the library.
6. **Finish → PR.** When it type-checks cleanly and reads like a proper Agda-Unimath document,
   open a PR (into a team fork first). Lessons from each run get distilled into the "skills";
   the cost/usage log becomes the DARPA report.

You drive this from your laptop as a terminal; the actual Agda checking runs on your team's
cloud machine (see appendix).

---

## 2. Why this shape (in one breath)

- **Don't build a custom AI system — extend Codex.** Codex already does the hard agent work
  (planning, editing files, running commands, recovering from errors). We add three thin,
  model-independent layers on top: (1) a tool that lets Codex type-check Agda and read the
  errors; (2) the "agda-unimath skills" that teach it the library's conventions; (3) a wrapper
  that runs it headless and logs everything. Layers (2) and (3) are exactly two of your three
  deliverables, and they survive the switch to your co-PIs' future in-house model.
- **Start simple, prove it converges, then invest.** Run the naive loop on a couple of real
  files *before* building any heavy infrastructure. Only add the fast-caching machinery if the
  loop is actually too slow to iterate.

---

## 3. The honest caveats (what the literature does and does *not* promise)

- The "simple loop works" evidence covers the **translation** difficulty. The other half —
  **building prerequisites missing from the library** — sits in territory the AlphaProof paper
  itself flags as harder (immature library). Budget and a go/no-go gate are there for this.
- The "you need a frontier model" evidence is **Gemini-specific**. **Whether Codex is good at
  Agda is unproven** — the first spike is partly a test of exactly that.
- **Cheating is a real risk and must be blocked by tooling, not trust.** In Agda, a *made-up*
  lemma written as a `postulate` type-checks cleanly — so "it compiles" is not "it's proved."
  We pin and diff the target statement (so the goal can't be silently weakened), forbid stray
  `postulate`s in AI-edited code, and require a human to sign off on the formalized *statement*
  (its type) before trusting the proof.

---

## 4. Decisions only your team can make

1. **Ask Egbert Rijke up front:** does Agda-Unimath accept AI-authored proofs as PRs, and how
   is authorship attributed (`CONTRIBUTORS.toml`)? He co-founded the library and is on the team —
   this is a quick conversation and a precondition for the "PR into the library" deliverable.
2. **Where does the checking machine live, and who maintains it?** You said your own cloud
   (Kubernetes). Good — note that Codex should run *on that same machine* (details in appendix).
   The plan's infrastructure assumes a DSAI engineer/grad student (the year-1 budget line) owns
   the tooling, not the three of you.
3. **A spending cap per target, and the objective trigger for declaring π₃(S²) "too hard"** and
   pivoting before the June DARPA report.
4. **What the June and August DARPA snapshots must contain** (which metrics, how much progress).

---

## 5. The three deliverables, and where each comes from

| Deliverable (from your email) | Where it's produced |
|---|---|
| (i) A formalization to clean up and PR into Agda-Unimath | The loop's output + a human "reads like a proper library document" sign-off |
| (ii) Documented prompts / resource use / human interactions for DARPA | The logging wrapper: a per-step record + a token→USD ledger |
| (iii) Prototypical "agda-unimath skills" | A skills file (modeled on `leanprover/skills`), grown by distilling each run's failures |

---

## Appendix — for the DSAI engineer

**Layer 1 (verification tool).** Fork the npm package `agda-mcp-server` (TypeScript, MIT,
InvariantHoldings). It drives a long-lived `agda --interaction-json` process over stdin/stdout
(IOTCM protocol) and — critically — already has literate `.lagda.md` code-block extraction,
which `faezs/agda-mcp` (Haskell) lacks. Fork to pin a known-good commit (bus-factor=1, pre-1.0)
and to add project-specific bits. Spike with the *stock* server first; only fork on a concrete
blocker.

- **Loop = batch by default**: edit whole `.lagda.md` → `Cmd_load` (chains `Cmd_metas`) → feed
  back the terminal `DisplayInfo` (`kind:Error`) whose ranges point at the literate source.
  No fence-splicing, no `InteractionId` bookkeeping. Interactive primitives
  (`agda_goal_type_context_infer`, `agda_auto`/Mimer, `agda_case_split`, `agda_refine`/`give`)
  are a per-hole fallback only.
- **Proof-complete gate**: `agda_load_no_metas`. **Anti-cheat gates**: pin+diff the target type
  signature on every reload; ban/flag `postulate` in AI-edited regions; require "already in the
  library" citations to resolve to a real type-checked module path.
- **Speed (only if iteration is too slow)**: keep ONE long-lived agda process (serialize
  commands — no pipelining); a pre-compiled, frozen prelude module the active proof imports;
  never run `make check` (whole library, ~15–33 min, ~4.4 GiB) in the inner loop. If still slow,
  snapshot `_build/*.agdai`, freeze the prelude during a run, tune RTS `-H/-M`.
- **Flags must match the library** (`--without-K --exact-split --no-import-sorts
  --auto-inline --no-require-unique-meta-solutions --no-postfix-projections` + everything-opts
  `--guardedness --cohesion --flat-split --rewriting`); `make pre-commit` is the final pre-PR gate.
- **Search**: start with `ripgrep` over the repo + expert knowledge; do **not** build a
  full-library semantic index for one target. `module_deps` is deferred (use `open import` scan
  / `make graph` if needed).

**Topology.** A stdio MCP server is a *child* of the Codex client and cannot reach Agda on a
different machine. So either (a) co-locate `agda` + the forked server + `codex exec` on the
Kubernetes host that owns the warm cache (Mac is just SSH), or (b) expose the fork over the
official `StreamableHTTPServerTransport` and set Codex `transport=streamable_http` + bearer token.
Agda type-checking is CPU/RAM-bound (no GPU) — so GPU dev kits (DGX Spark / Jetson Thor) are the
wrong tool; an x86 Linux node with ~4.4 GiB+ RAM and the prebuilt Agda 2.8.0 binary
(`setup-agda` + `agda --setup`) is what's needed.

**Multi-supervisor.** Branch-per-target-lemma; PRs into a team fork; a shared log location;
per-supervisor session + working copy (mirror the server's `sessionId` isolation); decide
whether the prelude/`_build` cache is shared-read-only or per-supervisor.

**Telemetry (deliverable ii).** Per-episode JSONL: `timestamp, prompt, tokens_in/out, usd,
tool_calls, typecheck_pass/fail, human_intervention{flag,type}, edit_author=AI|human`. Map
token usage × model price into a running USD ledger with credit-burn alerts. Report metrics:
USD per proved lemma, episodes-to-convergence, first-pass type-check rate, % AI vs human steps,
lines-per-dollar.

*Full technical plan with rationale and the source-level evaluation: `technical-plan.md`.*
