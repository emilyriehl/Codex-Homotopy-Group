---
name: agda-unimath-skills
description: Project-canonical workflows for Agda formalization in this agda-unimath-based repository. Use when Codex needs to inspect, write, repair, refactor, validate, or status-report Agda code; formalize homotopy type theory or univalent mathematics; search agda-unimath libraries; resolve Agda typechecking errors; or maintain the repository's formalization plan and status report.
---

# Agda UniMath Skills

## Canonical Copy

This repository-local skill is the master version for work in
`Codex-Homotopy-Group`. If a user-local skill with the same name also exists,
use this `.codex/skills/agda-unimath-skills` copy as authoritative for this
repository and treat user-local copies as disposable mirrors.

Use this workflow skill together with the repository-local
`agda-unimath-reference` skill. The workflow lives here; detailed library
reference material lives in `../agda-unimath-reference/references/`.

## Overview

Work like a careful Agda formalizer in agda-unimath-style projects. Prefer
small, typechecking changes, library reuse, and explicit validation over
speculative proof construction.

For command details and search patterns, read
[references/workflow.md](references/workflow.md) when you need project
commands, library navigation, or typechecking strategy.

## Core Workflow

1. Inspect the local project before editing.
   - Read `README*`, `.agda-lib`, `Makefile`, `agda-unimath.agda-lib`, and
     nearby modules when present.
   - Use `rg --files -g '*.agda' -g '*.lagda.md'` and `rg` searches to
     discover naming, imports, and existing lemmas.
   - Identify the module's import style and keep new imports minimal.

2. Reuse the library before proving from scratch.
   - Search for the target concept by several names: theorem statement words,
     constructor names, symbolic operators, and common agda-unimath prefixes.
   - Prefer existing equivalences, maps, `is-contr`, `is-equiv`, `is-prop`,
     `is-set`, path algebra, fiber, truncation, and identity-system lemmas over
     ad hoc proof terms.
   - If the proof seems long, pause and search again.

3. Make narrow edits.
   - Keep theorem names, statement shape, and universe levels consistent with
     surrounding code.
   - Follow the agda-unimath convention of one concept per file, organized by
     mathematical subject. If a module starts accumulating separable concepts,
     split them into descriptive files and import them where needed.
   - Avoid broad rewrites unless the user asked for a refactor.
   - Leave holes only when the user explicitly asks for partial progress or
     exploration.

4. Typecheck early and often.
   - Run the smallest Agda check that covers the edited module.
   - Use Agda errors as the source of truth.
   - After a failed check, fix the first relevant error and rerun.

5. Report the outcome concretely.
   - Name files changed, the checked command, and whether it passed.
   - If blocked, include the exact remaining Agda error and local definitions
     involved.

## Project Status Reports

- In any formalization repository with a `FORMALIZATION-PLAN.md`, create and
  maintain a `STATUS-REPORT.md` that links to the plan, summarizes the current
  status of the autoformalized Agda code, links to the files containing that
  code, and lists the tasks remaining to complete the plan.
- Update `STATUS-REPORT.md` whenever significant progress is made, such as
  proving a new theorem, formalizing an important definition, adding or
  removing a planned module, resolving a major blocker, or re-scoping a planned
  result.
- When updating the report, include relevant verification command results when
  practical, and distinguish completed code from partial infrastructure or
  remaining theorem statements.

## Formalization Heuristics

- Preserve universe-polymorphic generality unless nearby code specializes.
- Prefer named intermediate definitions when they match surrounding
  agda-unimath style or make goals reusable.
- Match local implicit argument conventions.
- Treat import changes as part of the proof. If a name is unavailable, search
  for the correct module rather than duplicating definitions.
- Avoid postulates, pragmas, disabled checks, unfinished metavariables, and
  commented-out failed attempts in final code.
- Use the repository-local reference skill for conventions, namespace lookup,
  foundational APIs, Agda error triage, and HoTT-specific practice.
- For HoTT exactness proofs, especially fiber-sequence and long-exact-sequence
  work, prove the smallest reusable adjacent exactness or comparison lemma
  first. A set-truncated image comparison against a canonical fiber sequence is
  often easier and more robust than trying to package the full iterated theorem
  in one step.

## Common Task Patterns

### Fix Typechecking

Read the failing command and module, reproduce the error, inspect the goal
context, then make the smallest correction. If the local command is unknown,
search for Makefile targets or use the `.agda-lib` file to run Agda on the
edited module.

### Fill Holes

Search surrounding modules first, then run Agda to inspect each hole. Fill one
hole at a time and keep proof terms close to local style. If a hole indicates a
missing lemma, search before creating a new lemma.

### Add A Lemma

Place the lemma near related results, choose a name consistent with nearby
naming, import only what is needed, and typecheck the module. Add helper lemmas
only when they simplify the main proof or match reusable patterns.

### Refactor Imports Or Names

Use `rg` to find all affected modules before editing. Keep public API changes
deliberate and validate every module touched by the rename or import change.

### Update Research Records

When making substantive formalization progress, update `STATUS-REPORT.md`.
When making a commit, also update `CHAT-LOG.md` with the request, actions,
verification, model context when visible, and commit hash or "This commit"
placeholder.

## Reference

Read [references/workflow.md](references/workflow.md) for:

- Agda command patterns
- agda-unimath search tactics
- error triage
- style checks before final response
