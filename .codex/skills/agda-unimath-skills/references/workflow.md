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
rg "connecting_map|connect_fiberseq|loops_les|isexact_connect_R"
```

## Proof Patterns

### Exactness via canonical fiber sequences

When proving exactness of a long-exact-sequence segment, separate the problem
into layers:

1. Prove or reuse a pointed fiber-sequence comparison.
2. Apply set truncation and prove exactness as pointed sets.
3. Transport that exactness to the concrete homotopy-group maps only after the
   adjacent pointed-set theorem is stable.

Prefer proofs that expose the native homotopy-theoretic structure expected in
agda-unimath. If an adjacent triple should itself be a pointed fiber sequence,
or should be obtained from a canonical one by a pointed equivalence, package
that structural theorem first. Image and kernel transports are useful when
extracting a consequence from a structural theorem, diagnosing a sign or
orientation mismatch, or bridging to an existing consumer; they should not
replace a canonical reusable construction merely because they close the current
hole faster.

For an adjacent triple that is not syntactically the canonical fiber sequence,
compare its image predicate with the image predicate of a canonical fiber
inclusion. Eliminate image witnesses with `apply-universal-property-trunc-Prop`,
then eliminate truncated preimages with
`apply-dependent-universal-property-trunc-Set'`. The path between set-truncated
maps is usually assembled from `naturality-unit-trunc-Set`, `ap unit-trunc-Set`,
and the relevant pointed homotopy or projection law.

### Iterated LES boundary maps

In iterated long-exact-sequence work, do not assume that the canonical shifted
boundary map is definitionally equal to the loop of a previously chosen
boundary map. The Coq-HoTT `loops_les` pattern defines each connecting map
freshly at each iterated-loop degree:

- the canonical shifted boundary is usually the right map for set-truncated
  exactness;
- the recursive looped boundary is often the right classifying pointed map for
  a concrete homotopy-group homomorphism;
- the bridge between them should be a named comparison or transport theorem,
  not a forced definitional equality.

If a group-level transport theorem expects maps of the form
`hom-trunc-Pointed-Set (pointed-map-Ω f)`, keep the recursive classifying map
available, but prove set-level exactness against the canonical boundary first.
The preferred upstreamable route is then to package the Coq-HoTT-style
`connect_fiberseq` analogue: the pointed fiber sequence
`Ω E ->* Ω B ->* F`, with comparison equivalence
`Ω E ≃* fiber (∂ : Ω B ->* F)`. After this structure is checked, derive the
recursive looped exactness from it. Use image/kernel transport between the
canonical and recursive boundary maps only as a secondary bridge or diagnostic,
for example to record an orientation or loop-inversion discrepancy. Do not
insert target-loop inversion or similar sign fixes unless there is an explicit
theorem transporting exactness across that equivalence.

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
