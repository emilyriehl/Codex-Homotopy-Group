# Namespace & discovery map

A navigation guide to the `agda-unimath` source tree (`src/`, literate Agda `.lagda.md`, one folder per mathematical subject). Use it to **find an existing definition or lemma before re-proving it** — search first, port second, never duplicate.

All commands below assume the repo root (where `src/` lives). File counts are approximate and drift over time; regenerate with the loop in §1.

## 1. Top-level namespaces under `src/`

Regenerate the counts with:

```sh
for d in src/*/; do n=$(find "$d" -name '*.lagda.md' | wc -l); echo "$n $d"; done | sort -rn
```

Ordered biggest-first. **★ marks the folders most relevant to HoTT / homotopy work.**

| Files | Namespace | Subject |
|------:|-----------|---------|
| 583 | **★ `foundation`** | The univalent foundations: types, equivalences, identity types, truncation, univalence, pullbacks, function extensionality. The big one. |
| 239 | `elementary-number-theory` | ℕ, ℤ, divisibility, primes, gcd, modular arithmetic. |
| 227 | `group-theory` | Groups, abelian groups, monoids, subgroups, concrete groups, group actions. |
| 176 | `category-theory` | Precategories, categories, functors, natural transformations, (co)limits. |
| 170 | `order-theory` | Posets, lattices, frames, suplattices, Galois connections. |
| 151 | `real-numbers` | Dedekind reals, rationals, inequalities. |
| 139 | **★ `synthetic-homotopy-theory`** | Spheres, circle, pushouts, suspensions, loop spaces, homotopy groups, descent. **Target area** (see §3). |
| 128 | `metric-spaces` | Metric spaces, premetric spaces, uniform structure. |
| 106 | `univalent-combinatorics` | Finite types, counting, standard finite types, decidable structure. |
| 96 | `linear-algebra` | Matrices, vectors over rings/fields. |
| 93 | `ring-theory` | Rings, ideals, localizations, modules. |
| 88 | `commutative-algebra` | Commutative rings, prime/maximal ideals, the Zariski locale. |
| 84 | **★ `structured-types`** | Pointed types, H-spaces, magmas, wild monoids, structured maps. Underpins pointed homotopy theory. |
| 79 | `graph-theory` | Directed/undirected graphs, trees, reflexive graphs. |
| 76 | **★ `orthogonal-factorization-systems`** | Modalities, factorization systems, reflective subuniverses, localizations, lifting. |
| 73 | **★ `foundation-core`** | Bootstrapping core of `foundation` (see §2). |
| 65 | `trees` | W-types, inductive/coinductive trees, multisets. |
| 55 | `globular-types` | Globular types, reflexive/transitive globular types. |
| 47 | `species` | Combinatorial species. |
| 39 | `lists` | Lists, vectors, sorting, permutations. |
| 29 | `logic` | Classical/constructive logic, propositional resizing. |
| 25 | `set-theory` | Cardinality, countable sets, Russell's paradox. |
| 25 | **★ `higher-group-theory`** | Higher groups (∞-groups as pointed connected types), deloopings, Eilenberg–Mac Lane spaces. |
| 24 | `finite-group-theory` | Finite groups, permutations, group tables. |
| 23 | `modal-type-theory` | Crisp type theory, flat/sharp modalities. |
| 18 | `complex-numbers` | Gaussian integers, complex arithmetic. |
| 17 | `universal-algebra` | Algebraic theories, models, terms. |
| 17 | `real-analysis` | Limits, continuity over the reals. |
| 14 | `reflection` | Agda reflection / metaprogramming utilities. |
| 10 | `type-theories`, `functional-analysis`, `finite-algebra`, `analysis` | Smaller specialist folders. |
| ≤9 | `domain-theory`, `wild-category-theory`, `synthetic-category-theory`, `organic-chemistry`, `literature`, `spectral-theory`, `primitives`, `polytopes` | Long tail. |

## 2. `foundation` vs `foundation-core`

This split is the one structural exception to the "one-concept-per-file, organize-by-topic" rule, and it trips up newcomers. Verbatim rationale from `docs/DESIGN-PRINCIPLES.md`:

> Towards the bottom of the library, we encounter a cluster of interdependent files, and Agda will report errors due to these cyclic dependencies… To resolve these cyclic dependencies, we created two folders… The `foundation-core` folder contains files that are paired with files of the same name in the `foundation` folder. The corresponding file in the `foundation` folder publicly imports the file from the `foundation-core` folder. **Users working in areas outside of the foundation can directly import files from the `foundation` folder** without worrying about potential file splits.

Precisely:

- `foundation-core/X` holds the minimal definitions/lemmas about `X` needed to break the bootstrapping cycle.
- `foundation/X` does `open import foundation-core.X public`, then adds everything else about `X` that depends on later machinery (e.g. univalence, function extensionality).
- **Rule for everyone outside `foundation`/`foundation-core`: import `foundation.X`, never `foundation-core.X`.** You get the core's contents transitively plus the rest, and you are insulated from future re-splits.

Verified example pair — `src/foundation/identity-types.lagda.md` opens with:

```agda
module foundation.identity-types where

open import foundation-core.identity-types public   -- re-exports the core file

open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
…
```

So `Id`, `refl`, `_∙_`, `inv`, `ap` come from `foundation-core.identity-types`; the extensionality-dependent results live in `foundation.identity-types`. Same naming pattern holds for `equivalences`, `homotopies`, `retractions`, `fibers-of-maps`, etc. (compare `ls src/foundation-core/` against `src/foundation/`).

## 3. `synthetic-homotopy-theory` contents (target area: π₃(S²) = ℤ)

Discover with:

```sh
ls src/synthetic-homotopy-theory/ | grep -iE 'sphere|circle|homotopy-group|loop|suspension|hopf|pushout|connected|join|smash|wedge'
```

**Homotopy groups & loop spaces**

| File | What it gives |
|------|---------------|
| `homotopy-groups.lagda.md` | `homotopy-group` / `concrete-homotopy-group`: `set-homotopy-group n A = trunc-Set (type-iterated-loop-space n A)`, packaged as a `Concrete-Group`. The π_n machinery. |
| `loop-spaces.lagda.md` | Ω of a pointed type, its group-like structure. |
| `double-loop-spaces.lagda.md`, `triple-loop-spaces.lagda.md`, `iterated-loop-spaces.lagda.md`, `multivariable-loop-spaces.lagda.md` | Ω², Ω³, Ωⁿ. `iterated-loop-spaces` is what `homotopy-groups` builds on. |
| `functoriality-loop-spaces.lagda.md`, `powers-of-loops.lagda.md`, `conjugation-loops.lagda.md`, `free-loops.lagda.md` | Functorial action, loop powers, conjugation, free loops (`free-loop` underlies the circle's universal property). |
| `groups-of-loops-in-1-types.lagda.md` | π₁ of a 1-type as an ordinary group. |

**Spaces**

| File | What it gives |
|------|---------------|
| `circle.lagda.md`, `universal-property-circle.lagda.md`, `universal-cover-circle.lagda.md`, `loop-homotopy-circle.lagda.md`, `multiplication-circle.lagda.md` | The circle S¹. `universal-cover-circle` proves the descent data is `ℤ` with `equiv-succ-ℤ` and gives `ℤ ≃ universal-cover-circle (base-free-loop l)` — i.e. the Ω S¹ ≃ ℤ result lives here. |
| `spheres.lagda.md`, `mere-spheres.lagda.md`, `tangent-spheres.lagda.md`, `sphere-prespectrum.lagda.md` | n-spheres (as iterated suspensions of S⁰). |
| `suspensions-of-types.lagda.md`, `suspensions-of-pointed-types.lagda.md`, `iterated-suspensions-of-pointed-types.lagda.md`, `suspension-structures.lagda.md`, `universal-property-suspensions.lagda.md`, `functoriality-suspensions.lagda.md` | Suspension Σ; `suspensions-of-types` is where the **Freudenthal suspension theorem** lives (`rg -il freudenthal src/`). |
| `pushouts.lagda.md`, `universal-property-pushouts.lagda.md`, `descent-data-pushouts.lagda.md`, `flattening-lemma-pushouts.lagda.md`, `pushout-products.lagda.md`, `cofibers-of-maps.lagda.md` | Pushouts and the full descent/flattening toolkit. |
| `joins-of-types.lagda.md`, `joins-of-maps.lagda.md`, `join-powers-of-types.lagda.md`, `smash-products-of-pointed-types.lagda.md`, `wedges-of-pointed-types.lagda.md`, `left-half-smash-products.lagda.md` | Joins, smash, wedge. |

**Connectedness / truncation tools**

`whitehead-principle-types.lagda.md`, `whitehead-principle-maps.lagda.md`, `truncated-acyclic-types.lagda.md`, `truncated-acyclic-maps.lagda.md`. General connectedness lives in `foundation` (e.g. `foundation.connected-types`, `foundation.truncations`).

**Present but elsewhere / partially present**

- **Hopf fibration:** no `hopf*` file in `synthetic-homotopy-theory/` — check before assuming it exists (`ls … | grep -i hopf` returns nothing). The Hopf construction / H-space machinery is in `structured-types` (H-spaces) and `higher-group-theory`.
- **Eilenberg–Mac Lane spaces & deloopings:** `src/higher-group-theory/eilenberg-mac-lane-spaces.lagda.md`, `deloopable-types.lagda.md`, `deloopable-groups.lagda.md`.
- **Missing for the π₃(S²) target:** no dedicated `pi-3-sphere`, `hopf-fibration`, or general "πₙ(Sⁿ) = ℤ" file. Ω S¹ ≃ ℤ exists (`universal-cover-circle`); the π₃(S²) chain (Hopf + Freudenthal + π_n machinery) must be assembled from the pieces above. Confirm any specific lemma with `rg` before relying on it.

## 4. How to discover a definition

**Module name ↔ file path** is mechanical: module `A.b-c` ⇔ file `src/A/b-c.lagda.md`. Dots separate folders; the last segment is the filename. So `foundation.dependent-pair-types` ⇒ `src/foundation/dependent-pair-types.lagda.md`. Reverse the mapping to turn any import line into a path to read.

**Per-subject index files.** Each folder `A/` has a sibling `src/A.lagda.md` that publicly imports every file in it (`src/foundation.lagda.md`, `src/synthetic-homotopy-theory.lagda.md`, `src/foundation-core.lagda.md`, …). Reading the index is the fastest way to scan everything a subject offers and to see exact module names to import.

**Search recipes** (all verified to return hits in this repo):

```sh
# 1. Which files even mention a name? (-l = list files)
rg 'is-equiv' src/ -l           # → 774 files

# 2. Definitions whose name STARTS with a token (anchor with ^):
rg '^is-equiv-' src/ --no-heading
#   e.g. src/group-theory/isomorphisms-abelian-groups.lagda.md:is-equiv-iso-eq-Ab :

# 3. Search by TYPE / conclusion, not just name — find the field that
#    extracts a proof of is-equiv from an equivalence:
rg 'is-equiv-map-equiv' src/foundation-core/equivalences.lagda.md
#   → is-equiv-map-equiv : is-equiv map-equiv

# 4. Locate the πₙ definition by its concept:
rg -n 'homotopy-group' src/synthetic-homotopy-theory/homotopy-groups.lagda.md
#   → set-homotopy-group, type-homotopy-group, concrete-homotopy-group …
```

More tactics:

- **Search for the goal's TYPE.** If you want "Ω S¹ ≃ ℤ", grep for the conclusion shape rather than a guessed name: `rg 'ℤ ≃' src/synthetic-homotopy-theory/` finds `ℤ ≃ universal-cover-circle …` in `universal-cover-circle.lagda.md`.
- **Concept annotations.** Definitions are tagged with `{{#concept "…" Agda=name}}`. Grep these for human-readable matches: `rg '{{#concept' src/synthetic-homotopy-theory/ -l`.
- **Naming convention is descriptive and predictable:** `is-`/`has-` for properties, `equiv-`/`iso-` for equivalences, `compute-` for computation rules, `eq-`/`Id` for equalities, suffix `-Group`, `-Set`, `-Pointed-Type` names the carrier structure. Guess the name from the convention, then confirm with `rg '^<guess>'`.
- **When a file is in an unexpected place** (the docs warn this happens), fall back to a repo-wide `rg <name> src/ -l` rather than assuming a folder.

**Always verify a path exists** (`ls src/<folder>/<file>.lagda.md`) before citing or importing it — do not trust a remembered name.
