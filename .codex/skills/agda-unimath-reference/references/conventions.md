# Library conventions (house style)

Distilled from the agda-unimath `docs/` (`CODINGSTYLE.md`, `DESIGN-PRINCIPLES.md`,
`FILE-CONVENTIONS.md`, `TEMPLATE.lagda.md`, `MIXFIX-OPERATORS.md`). These are the rules a
`.lagda.md` file must follow to "read like a proper agda-unimath document" — `make pre-commit`
passing is necessary but **not** sufficient; a human signs off on style. When in doubt, open the
real doc in the clone (`/Users/eric/agda-unimath/docs/`) for the authoritative wording and examples.

## File anatomy (the non-negotiable skeleton)

A file is literate Agda + markdown (`.lagda.md`); Agda lives in ```` ```agda ```` fences, prose lives
between them. Every file follows this exact order:

1. **Title** — a single `#` markdown header (`# The title of the file`). One line, may exceed 80 chars.
2. **Module block** — one ```` ```agda ```` block containing, *in this order*: option pragmas (if any),
   the `module <path> where` declaration, then any **public** imports (`open import … public`).
   The module name must match the file path under `src/` (e.g. file
   `src/foundation/dependent-pair-types.lagda.md` ⇒ `module foundation.dependent-pair-types where`).
3. **Imports block** — a collapsible block of all non-public imports, wrapped exactly:

   ````md
   <details><summary>Imports</summary>

   ```agda
   open import …
   ```

   </details>
   ````

   This is the *only* place non-public imports may appear; nothing imports after it. Imports are
   listed alphabetically — `make pre-commit` sorts them for you, so you don't sort by hand.
4. **Sections** — `## Idea`, `## Definitions`, `## Properties` are the canonical spine. `## Examples`,
   `## Theorem`, `## See also`, `## References` appear as needed. Use `###` for subsections, `####`
   to subdivide long ones. Reserve `#` for the title alone.

The minimal template (`docs/TEMPLATE.lagda.md`):

````md
# File title

```agda
{-# OPTIONS --safe #-}

module foundation.template where

open import foundation-core.template public
```

<details><summary>Imports</summary>

```agda
open import …
```

</details>

## Idea

A **concept** `C` is _abstract idea_, defined as _definition in words_.

## Definition

```agda
concept : …
concept = …
```

## Properties

### Concepts satisfy a property

```agda
satisfies-property-concept : …
satisfies-property-concept = …
```
````

## Prose is mandatory, not decorative

agda-unimath documents read as math exposition rendered on a website. **A file that typechecks but
has no prose around its definitions is not merge-ready.** Concretely:

- The `## Idea` section displays the defined concept in **bold** (`**galois connection**`) and
  hyperlinks technical terms to their own pages: `[large posets](order-theory.large-posets.md)`.
- Each code block is preceded by a descriptive `###` header and, where useful, a paragraph
  explaining the construction's purpose and method.
- Informal calculations go in ```` ```text ```` blocks (e.g. an equational-reasoning sketch before
  the formal proof).
- US English spelling throughout prose, comments, and names.

## Naming conventions

The cardinal rule: **a name describes the *type* of the term it names.** The proof that `succ-ℤ` is
an equivalence has type `is-equiv succ-ℤ`, so it is named `is-equiv-succ-ℤ`.

- **Lowercase, hyphen-separated**, reading as English math: `is-equiv`, `dependent-pair-types`,
  `universal-property-pushouts`.
- The **start of the name** describes what is constructed; a **trailing** part may describe the
  hypotheses, placed so the descriptor sits next to the variable it refers to. Example:
  `is-equiv-is-contr-map : is-contr-map f → is-equiv f` — `is-contr-map` (hypothesis) trails
  `is-equiv` (conclusion).
- **Names never reference variable names.** Prefer `commutative-product`, not `commutative-×` and
  not anything mentioning a bound `x`.
- **Capitalized suffix** names the ambient framework/structure: `Prop`, `Set`, `Group`, `Monoid`,
  `Poset`, `Precategory`, `Category`, `Directed-Graph`, `-Pointed-Type`. So a name is usually
  `all-lowercase-part` optionally followed by a `Capitalized-Structure`.
- **No namespace overloading** — names are unique across the library.
- **Abbreviations and unicode used sparingly** — clarity over brevity. Accepted abbreviations are
  widely-known math terms (`poset`). When a symbol isn't available, describe it in words.
- Prefer **prefix** names over infix: name the commutativity lemma `commutative-product`, not after
  the `×` operator.

The one deliberate unicode exception baked into the library: the identity type uses the **full-width
equals** `＝` (U+FF1D), because ASCII `=` is reserved in Agda.

## Code structure & definitions

- **Small, reusable entries.** Factor even tiny bits of logic into their own named definitions —
  most of the library looks like boilerplate *by design*. Small entries compile faster, break less,
  and become reusable knowledge.
- **Always give types.** No untyped definitions, even though Agda allows them — the type is the
  specification and aids navigation and maintenance.
- **Universe polymorphism**: give each assumed type/family its own `Level`.
- **Implicit arguments**: if an argument is inferable in most uses, make it implicit (`{…}`).
- **Reuse existing constructions** in both signatures and bodies — keeps naming consistent and code
  concise.
- **Anonymous modules** group constructions sharing parameters; declare module variables on a new
  line indented +2, with `where` on its own following line (also +2). Leave one blank line after a
  module declaration. Agda modules should not span multiple markdown sections or subsections; do not
  let a module cross `##`/`###` section headers — start a fresh one.
- **`where` blocks** are permitted but discouraged (their contents aren't reusable). Prefer them over
  `let`. If used: indent the `where` keyword +2 below the proof, type every helper, align contents
  with `where`. Better still, factor the helper into a top-level named lemma.
- **`pr1`/`pr2`**: avoid chains of raw projections — name the projections of a named `Σ`-type
  instead (more readable, more informative on jump-to-definition, easier to refactor).
- **Record types** are used rarely (they complicate characterizing the identity type); fine when the
  identity type isn't critical.
- The library does **not** use Agda's generalized `variable`s — all variables are module parameters
  or appear in a construction's type signature.
- **Lambdas**: wrap a lambda in parentheses when it's a function argument (even as the last arg).
  Avoid general pattern-matching lambdas (`λ { … }` / `λ where`); if one is needed, prefer the
  `where` form and mark the definition `abstract`. Recurring matching lambdas are a smell — factor
  them into named definitions.

## Formatting

- **80-character lines.** Exceptions: named `module` declarations, `open import` lines, and a line
  that is a single (possibly parenthesized) token optionally followed by `;`, `:`, `=`, or `→`.
  Markdown headers (including the title) are also exempt.
- **Two-space indentation**, always a multiple of two. Don't indent merely to "align" code neatly —
  it hurts maintainability.
- **Tree-structured line breaks.** Break at the *earliest* branching point when a definition spills
  past 80 chars. Each argument starts on a fresh line indented +2; mark branches with parentheses
  and put a space after the opening `(` of a branch. (See the `is-trunc-equiv-is-trunc` example in
  `CODINGSTYLE.md` §Formatting.)
- If a name + type signature don't fit one line, move the type to the next line, +2; break the type
  further at the same indentation if still too long.
- **Equational reasoning** is typeset as:

  ```text
  equational-reasoning
    term-1
    ＝ term-2
      by
      equation-1
    ＝ term-3
      by
      equation-2
  ```

  If `equation-n` is short enough to fit after `by` within 80 chars, keeping it on that line is fine.
- **Parenthesize mixfix expressions** whenever the association matters or could confuse a reader —
  don't make readers recall precedence/associativity.

## Mixfix operators & precedence

When introducing an operator (`MIXFIX-OPERATORS.md`):

- Precedence is a (preferably nonnegative integer) level; **higher binds tighter**. Agda's default
  is `20`. Reference points in the library: `_*ℕ_` = `40`, `_+ℕ_` = `35`, so `x +ℕ y *ℕ z` parses as
  `x +ℕ (y *ℕ z)`.
- **Nonparametric** operators (no universe-level argument, e.g. `_-ℤ_`, `_<-ℕ_`) bind *tighter* than
  **parametric** ones (those taking a `Level`, even implicitly: `_×_`, `_＝_`, `_,_`).
- Set associativity with `infixl`/`infixr` to avoid parenthesis noise — e.g. `_,_` is `infixr`, so
  `a , b , c` = `a , (b , c)`. Default (`infix`) associates to neither side.
- Common library fixities (verify against source): `infixr 3 _,_`, `infixl 15 _∙_`, `infix 6 _＝_`,
  `infix 6 _≃_`, `infix 6 _~_`, `infixr 10 _+_`, `infixr 15 _∘_`, `infixr 15 _×_`.

## Tables, links, and citations

- A reusable **table** goes in its own file under `docs/tables/` (descriptive name, table only) and
  is pulled in with `{{#include tables/<name>.md}}`. Pre-commit canonicalizes table formatting.
- **Cross-references** in prose:
  - by title: `[The univalence axiom](foundation.univalence.md)`
  - by module name: `` [`foundation.univalence`](foundation.univalence.md) ``
  - bare URL: `<https://unimath.github.io/agda-unimath/>`
- **Cite sources** for results (papers, HoTT book sections) in a `## References` / `## See also`
  section; the library uses an mdbook bibliography (`{{#cite Key}}` / `{{#bibliography}}`,
  `references.bib`). Mathematical content ported from elsewhere must credit its source.

## Design principles worth internalizing

- **One concept per file**, organized by mathematical subject (one folder per subject). File names
  *are* the index of the library — make them descriptive noun phrases, include prepositions
  (`fibers-of-maps`, not `fibers-maps`).
- The library is **constructive univalent mathematics**: assumes `--without-K` and `--exact-split`;
  postulates function extensionality, univalence, propositional truncation/truncations, replacement,
  pushouts, the interval, the circle (some redundantly — see `DESIGN-PRINCIPLES.md`). No LEM/AC in
  the developed theory. Higher inductive types have computation rules only **up to identification**.
- `foundation-core` exists solely to break bootstrapping cycles; everyone outside foundation imports
  from `foundation`. (See `references/namespace-map.md` §2.)
