# Agda and agda-unimath Workflow

## First Pass

Run these inspections before substantive edits:

```bash
rg --files -g '*.agda' -g '*.lagda.md'
rg --files -g '*.agda-lib' -g 'Makefile' -g 'README*'
```

Read the relevant `.agda-lib` file to learn include paths and library names.
Read nearby modules to copy import style, section structure, naming, and
universe conventions.

For this repository, use the project wrapper:

```bash
./check.sh path/to/module.lagda.md
```

## Typechecking Commands

Prefer project-provided commands when available:

```bash
make
make <target>
./check.sh <file>
```

If no target is obvious, check the edited module directly with the local
library file:

```bash
agda -i . -i <library-root>/src <path/to/Module.lagda.md>
```

Adjust include paths from the `.agda-lib` file. If the repository uses Nix,
direnv, or a wrapper script, prefer the wrapper already documented in
`README*` or `Makefile`.

## Search Tactics

Use `rg` with multiple naming variants. Search both statements and definition
names.

Useful patterns:

```bash
rg "is-contr|is-equiv|is-prop|is-set|is-trunc"
rg "fiber|fib|total|Sigma|Σ"
rg "equiv|htpy|homotopy|retraction|section"
rg "identity-system|fundamental-theorem|encode-decode"
rg "ap |ap-|-ap|concat|inv|assoc|unit"
```

For a target theorem, search:

- the main noun phrase in kebab case
- the conclusion type former
- nearby concepts in the file's imports
- analogous lemmas for related structures

If a proof term becomes large or repetitive, search again for a more direct
lemma.

For fiber-sequence and long-exact-sequence work, also search for these APIs
before writing path algebra by hand:

```bash
rg "fiber-ap-eq-fiber|map-inv-fiber-ap-eq-fiber|triangle-fiber-ap-eq-fiber"
rg "naturality-unit-trunc-Set|apply-dependent-universal-property-trunc-Set'"
rg "tr-type-Ω|eq-conjugation-tr-type-Ω|pointed-map-Ω"
```

## Proof Patterns

### Exactness via canonical fiber sequences

When proving exactness of a long-exact-sequence segment, separate the problem
into layers:

1. Prove or reuse a pointed fiber-sequence comparison.
2. Apply set truncation and prove exactness as pointed sets.
3. Transport that exactness to the concrete homotopy-group maps only after the
   adjacent pointed-set theorem is stable.

For an adjacent triple that is not syntactically the canonical fiber sequence,
compare its image predicate with the image predicate of a canonical fiber
inclusion. Eliminate image witnesses with `apply-universal-property-trunc-Prop`,
then eliminate truncated preimages with
`apply-dependent-universal-property-trunc-Set'`. The path between set-truncated
maps is usually assembled from `naturality-unit-trunc-Set`, `ap unit-trunc-Set`,
and the relevant pointed homotopy or projection law.

### Equality in fibers under `--without-K`

Avoid pattern matching directly on equalities in fibers, such as reducing a
fiber element to `(q , refl)`, when the motive depends on the equality proof.
Agda may reject this as an illicit K-like split. Use
`foundation.equality-fibers-of-maps` instead: build paths with
`map-inv-fiber-ap-eq-fiber`, recover first-projection data with
`ap-pr1-map-inv-fiber-ap-eq-fiber`, and use `triangle-fiber-ap-eq-fiber` when
`fiber-ap-eq-fiber` is only propositionally aligned with `ap pr1`.

## Error Triage

When Agda fails:

1. Fix the first error that is caused by the current change.
2. Distinguish parse/scope errors from type errors.
3. For scope errors, search imports before inventing definitions.
4. For universe errors, compare nearby theorem levels and avoid unnecessary
   specialization.
5. For mismatch errors, inspect the expected and actual types; path
   orientation and implicit arguments are common causes.
6. Rerun the smallest check after each fix.

## Style Expectations

- Keep imports alphabetized or grouped only if the file already does so.
- Avoid adding global imports for one-off names when local qualification is
  clearer in nearby code.
- Match local section/module parameter style.
- Prefer existing agda-unimath naming conventions, usually descriptive
  kebab-case names.
- Do not introduce postulates or options that weaken checking.
- Do not leave holes, unfinished metavariables, or commented-out failed
  attempts in final code.
- Keep `STATUS-REPORT.md` current when formalization status changes.

## Final Verification

Before replying, run a check that covers every edited Agda module. In the final
response, state:

- the files changed
- the exact check command run
- pass/fail status
- any remaining holes or errors, if the user asked for partial work
