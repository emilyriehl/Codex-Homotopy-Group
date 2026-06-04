---
name: agda-unimath-reference
description: Reference handbook for the agda-unimath library — house style/conventions, the src/ namespace & discovery map, a foundational API cheatsheet (UU, Σ, identity types ＝, equivalences, truncation, univalence), and an Agda error/flag triage table. Use this whenever writing, reading, reviewing, or porting agda-unimath `.lagda.md` code; when you need the module path or signature of a foundational construction; when deciding where a definition lives or how to search for an existing lemma before re-proving it; or when decoding an Agda error under `--without-K --exact-split`. Reach for it even if the user only says "agda-unimath", "unimath", "HoTT in Agda", "literate Agda proof", or names a construction like is-equiv / dependent-pair-types / synthetic-homotopy-theory without asking for "reference" explicitly. Complements (does not replace) the agda-unimath-formalization workflow skill.
---

# agda-unimath reference handbook

A look-up layer for working in the [agda-unimath](https://github.com/UniMath/agda-unimath) library:
the largest library of formalized univalent mathematics in Agda (~3000+ literate `.lagda.md` files
under `src/`, organized one concept per file by mathematical subject). This skill is the **reference**
half of the agda-unimath toolkit; the `agda-unimath-formalization` skill covers the *workflow*
(the type-check loop, porting prerequisites, PR/merge norms). Use them together.

The substance lives in five reference files under `references/`. **Don't try to recall agda-unimath
specifics from memory — load the relevant file and quote it.** The library is large and moves; every
name, path, and signature should be confirmed against the file (and ultimately against the source
clone) rather than guessed.

## When to load which reference

| You need to… | Load |
|---|---|
| Follow house style: file skeleton, prose requirements, naming, formatting, mixfix precedence, citations | `references/conventions.md` |
| Find where something lives / which namespace / how to search for an existing lemma | `references/namespace-map.md` |
| Get the module path & signature of a foundational construction (`UU`, `Σ`, `＝`, `is-equiv`, `is-trunc`, univalence, …) | `references/foundational-api.md` |
| Decode an Agda error, especially under `--without-K` / `--exact-split` | `references/error-triage.md` |
| Follow homotopy type theory formalization practice, especially for concrete groups and native homotopical definitions | `references/hott-skills.md` |

Read the whole relevant file when you start a task in its area — they're short and the cross-cutting
context matters. For a one-off lookup, jump to the named section.

## The five things that catch people out

These are load-bearing facts that the references expand on. Internalize them; they prevent the most
common mistakes.

1. **Verification is a real `agda` run, never a scope-check.** Done = `check.sh <file>` (raw `agda`
   with the library flags) exits 0, with no holes (`?`, `{! !}`) and no unsolved metas. An
   `agda-mcp-server` "ok"/"ok-complete" was measured to scope-check only and passes code that real
   `agda` rejects — do not trust it. (`error-triage.md`)

2. **The identity type is the full-width `＝` (U+FF1D), not ASCII `=`.** ASCII `=` is Agda's
   definition symbol and is reserved. This is the library's one deliberate unicode quirk; getting it
   wrong is an instant parse/type error. (`foundational-api.md`, `conventions.md`)

3. **Import from `foundation`, not `foundation-core`** — unless you *are* inside the foundation
   bootstrap. `foundation.X` publicly re-exports `foundation-core.X` and adds the
   univalence/funext-dependent results; `foundation-core` exists only to break dependency cycles.
   (`namespace-map.md` §2)

4. **Search before you prove or postulate.** `rg` the repo by name and especially by *conclusion
   type* before writing anything. If a lemma exists, import it; if it doesn't, port it properly —
   **never `postulate`** in authored code (a grep gate rejects it). (`namespace-map.md` §4)

5. **A typechecking file with no prose is not merge-ready.** agda-unimath files are math exposition:
   one concept per file, `## Idea`/`## Definitions`/`## Properties`, bolded defined term, hyperlinked
   technical terms, descriptive hyphenated names, cited sources. (`conventions.md`)

## Flags (auto-applied from `agda-unimath.agda-lib` — don't fight them)

```
--without-K --exact-split --no-import-sorts --auto-inline
--no-require-unique-meta-solutions -WnoWithoutKFlagPrimEraseEquality --no-postfix-projections
```

Implications you'll feel: no axiom K (don't match on `refl`; use `ind-Id`/`tr`/`ap`), exact-split
(cover cases so they reduce definitionally), no postfix projections (`pr1 t`, not `t .pr1`). The
error-triage reference maps each to its symptom and fix.

## Local clone

A clone is typically available at `/Users/eric/agda-unimath` (the authoritative `docs/`, `src/`, and
`check.sh` live there). The references distill it, but for anything load-bearing — an exact current
signature, the precise wording of a convention — open the source. Module `A.b-c` ⇔ file
`src/A/b-c.lagda.md`; each subject folder has an index file `src/A.lagda.md` that imports everything
in it.
