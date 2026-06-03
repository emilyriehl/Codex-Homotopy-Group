# Error & flag triage

How to read Agda's errors when typechecking `.lagda.md` against agda-unimath, and the fixes for the
ones that recur. The library flags (from `agda-unimath.agda-lib`, auto-applied — **don't fight
them**) are:

```
--without-K --exact-split --no-import-sorts --auto-inline
--no-require-unique-meta-solutions -WnoWithoutKFlagPrimEraseEquality --no-postfix-projections
```

Agda is **2.8.0**. Verification = a real `agda` run via `check.sh <file>` (exit 0, no `error:`, no
holes `?`/`{! !}`, no unsolved metas). Error locations point at the literate source
(`file:line:col`); the line is the line in the `.lagda.md`, counting prose and fences. This is
distinct from scope-checking — see the warning at the bottom.

## How to read an Agda error

- Agda reports the **first** hard error and stops elaborating that definition; fix top-down, one at a
  time, and re-run. A cascade of errors is usually one root cause.
- The message has three parts: the **location** (`Module.lagda.md:L:C-C`), the **kind** (`error:`
  followed by the category, e.g. `[UnsolvedMetas]`, `[ExactSplitError]`), and the **goal vs. actual**
  types. Read the goal/actual pair first — most fixes are "make the actual type equal the goal."
- "It compiles" ≠ "it's proved." A remaining hole `{! !}`/`?` or an unsolved metavariable means the
  proof is incomplete even if `agda` doesn't hard-error on the rest. Grep your file for `?` and `{!`
  before declaring done, and treat any `Unsolved` warning as a failure for our gates.

## Flag-specific errors (the ones the library's flags cause)

### `--without-K` — no axiom K / no uniqueness of identity proofs

You cannot pattern-match on `refl` in a way that would require K. Typical message:
`Cannot eliminate reflexivity proof … because K has been disabled` or a complaint that the index is
not a variable (failed "generalizing over the index").

- **Fix:** don't `match` the identity proof directly. Use the library's eliminators instead:
  `ind-Id`, `tr` (transport), `ap`, path induction packaged as named lemmas, or `J`-style helpers in
  `foundation.identity-types`. Search for an existing characterization (`rg 'tr ' …`,
  `rg 'equiv-tr'`) rather than hand-rolling a match.
- When you genuinely need "two paths are equal," that's a truncation/`is-set` statement — find or use
  `is-set`/`is-prop` machinery, don't try to match.

### `--exact-split` — every clause must hold definitionally

Message: `error: [ExactSplitError]` / "Exact splitting is enabled, and the following… clause could
not be preserved as definitional equalities". It fires when a `with`/pattern clause only holds
propositionally.

- **Fix:** make the clauses cover cases *explicitly* and reduce on the nose. Often this means
  matching on the constructor (e.g. `zero-ℕ`/`succ-ℕ`, `inl`/`inr`) rather than using a catch-all or
  a derived function, so each branch computes definitionally.
- If a definition legitimately can't be exact-split (genuinely only-propositional clauses, e.g. from
  a pattern-matching lambda), mark it `abstract` — the house style requires `abstract` on definitions
  containing `λ { … }` / `λ where` anyway.

### `--no-postfix-projections`

You can't write `t .pr1` postfix. Message about postfix projection or an unexpected parse.

- **Fix:** use prefix application: `pr1 t`, `pr2 t`, or (preferred by the style guide) the *named*
  projection of the structure (`vertex-Directed-Graph G`, not `pr1 G`).

### `--no-import-sorts` / `--auto-inline` / `--no-require-unique-meta-solutions`

These rarely surface as user-facing errors. `--no-import-sorts` means `Set`/`Prop` sort names aren't
auto-imported — the library uses `UU` from `foundation.universe-levels`; just import what you use.
`--no-require-unique-meta-solutions` loosens meta solving; it occasionally lets ambiguous code through
that bites later as a type mismatch, so still pin types explicitly.

## Common non-flag errors and fixes

| Symptom (error category) | Likely cause | Fix |
|---|---|---|
| `[UnsolvedMetas]` / yellow highlight, `_n : …` | Agda can't infer an implicit (often a `Level` or an implicit type) | Supply it explicitly: `{l = …}`, or annotate the term's type. Make the argument explicit at the call site. |
| `[UnsolvedConstraints]` | a metavariable's value is under-determined | Add a type annotation or give the implicit; check you imported the `foundation` (not `foundation-core`) version that adds the needed instance/lemma. |
| `… != … of type …` (type mismatch) | goal type and your term's type differ | Read goal-vs-actual; insert `tr`/`ap`/`inv`/`equiv-…` to bridge, or you used the wrong lemma — `rg` for one whose conclusion *is* the goal. |
| `Not in scope: foo` | missing import or wrong name | `rg '^foo' src/ -l` to find the real module; add `open import <module>` to the Imports block (not public unless re-exporting). Confirm the name's exact spelling. |
| `Ambiguous name foo` | same name from two opened modules | qualify it (`Module.foo`) or open only one. The library avoids overloading, so this usually means you opened too broadly. |
| `The identity type expects … ` / `= is a reserved` | you used ASCII `=` for identity | use the full-width `＝` (U+FF1D, input `\=`). ASCII `=` is the definition symbol only. |
| `Termination checking failed` | a recursive def Agda can't see as decreasing | restructure to recurse on a structurally smaller argument; or use an existing recursor (`ind-ℕ`, well-founded recursion lemmas). |
| `Failed to solve … constraints` about universe levels | level arithmetic doesn't unify | make each parameter's `Level` distinct and explicit; use `l1 ⊔ l2` in the result type; don't reuse one level where two are needed. |
| Coverage error / missing clause | `--exact-split` + incomplete cover | add the missing constructor case; for empty types use `ind-empty`/`ex-falso`. |
| `Cannot instantiate the metavariable … to … since it contains …` | a solution would capture a bound variable | reorder arguments / make the offending argument explicit. |

## Workflow that minimizes thrash

1. **Search before proving.** Most "mismatch" loops are really "I re-derived something the library
   already has, slightly wrong." `rg` the conclusion type first (see `references/namespace-map.md`
   §4).
2. **Fix the first error only, then re-run `check.sh`.** Don't speculatively fix downstream errors —
   they often vanish.
3. **Annotate aggressively** while debugging metas: give the term its full type, make implicits
   explicit; remove the noise once it's green.
4. **No `postulate` as an escape hatch.** A `postulate` typechecks but is rejected by the project's
   grep gate and defeats the point — if a lemma is missing, port it properly
   (see the `agda-unimath-formalization` skill).

## ⚠️ Scope-checking is not type-checking

Do **not** trust an `agda-mcp-server` "ok"/"ok-complete": it was measured (2026-05-30) to
*scope-check only* and reports success on code that real `agda` rejects. The truth is a raw `agda`
run (`check.sh <file>`) exiting 0 with no holes and no unsolved metas. Every claim of "this
typechecks" must be backed by a real run.
