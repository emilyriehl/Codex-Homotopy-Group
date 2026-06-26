# Long Exact Sequence Status

Last updated: 2026-06-26.

This note summarizes the current local state of the long exact sequence of a
fibration, with a critical eye toward what would still be needed before this
code should be considered library-quality `agda-unimath` material. It is meant
as a handoff file for the next agent; the authoritative checked code remains in
the Agda modules named below.

## Natural-Language Target

The usual HoTT Book and classical homotopy-theoretic statement is that a
pointed fibration or fiber sequence

```text
F -> E -> B
```

induces an infinite long exact sequence

```text
... -> pi_(n+1)(B) -> pi_n(F) -> pi_n(E) -> pi_n(B) -> pi_(n-1)(F) -> ...
```

with a boundary map `Omega B -> F` and exactness at every adjacent middle term.
In this repository's current indexing convention,
`concrete-homotopy-group n A` represents the ordinary group `pi_(n+1)(A)`, so
index shifts must be handled explicitly.

The natural-language proof route is structural:

1. construct the boundary map from loops in the base to the fiber;
2. identify the fiber of the fiber inclusion with the loop space of the base;
3. package the shifted connecting fiber sequence `Omega E -> Omega B -> F`;
4. iterate looping/connecting to obtain all adjacent triples;
5. prove set-truncated exactness of those triples;
6. transport this exactness to ordinary group exactness for homotopy groups.

The Coq-HoTT/Rocq `connect_fiberseq` style is the right comparison point: the
proof should expose a reusable shifted fiber sequence, not merely prove that
particular image and kernel predicates are equivalent after a sequence of local
transports.

## What Is Formalized Locally

### Fiber Sequences

`src/structured-types/fiber-sequences.lagda.md` defines general pointed fiber
sequences:

- `is-fiber-sequence-Pointed-Type`
- `fiber-sequence-Pointed-Type`
- accessors for the fiber, total, base, inclusion, fibration, and comparison
  with the canonical fiber of the fibration map
- the canonical fiber sequence of any pointed map

This is a useful structural base. The module is small compared with the later
LES code and is close in spirit to what should eventually be upstreamed, though
the namespace may need adjustment if merged into `synthetic-homotopy-theory`.

### Pointed-Set Exactness

`src/structured-types/exact-sequences-pointed-sets.lagda.md` defines exactness
for pointed sets:

- `is-exact-hom-Pointed-Set`
- image/kernel transport and invariance lemmas
- the canonical theorem
  `is-exact-trunc-fiber-inclusion-Pointed-Type`, stating that the set
  truncation of a canonical fiber sequence is exact

This is the current set-level exactness foundation for the LES. It is
mathematically appropriate, but several later proofs rely heavily on its
transport lemmas. For upstream code, those transport lemmas should be hidden
behind more conceptual LES-facing statements.

### Ordinary Group Exactness

`src/group-theory/exact-sequences-groups.lagda.md` defines
`is-exact-hom-Group` and proves that a fiber sequence of concrete-group
classifying maps gives exactness of the induced underlying group
homomorphisms. `src/group-theory/isomorphisms-from-exact-sequences-groups.lagda.md`
contains the algebraic exactness-to-isomorphism extraction used by the Hopf
applications.

Important caveat: the classifying-map fiber-sequence theorem is too strong for
general adjacent triples in a homotopy LES. Adjacent LES exactness should not
be reformulated as a short fiber sequence of concrete-group classifying maps.
The later group-level bridge correctly uses set-truncated exactness as the
source of truth instead.

### Boundary Maps And Initial LES Segments

`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`
contains the main structural and low-level LES work. It formalizes:

- `boundary-fiber-Pointed-Type : Omega B ->* fiber g`
- `pointed-equiv-loop-fiber-Pointed-Type`, identifying the fiber of a fiber
  inclusion with the loop space of the base
- the first boundary fiber sequence
  `fiber-sequence-boundary-fiber-Pointed-Type`
- the direct shifted sequence
  `fiber-sequence-boundary-map-Ω-direct-Pointed-Type`
- induced homomorphisms for a packaged fiber sequence:
  `hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence`,
  `hom-fibration-concrete-homotopy-group-fiber-sequence`, and
  `boundary-hom-concrete-homotopy-group-fiber-sequence`
- canonical boundary homomorphisms for pointed maps and for iterated packaged
  fiber sequences, including
  `canonical-boundary-hom-concrete-homotopy-group-fiber-sequence`
- `iterated-loop-fiber-sequence`
- set-truncated exactness for the initial adjacent triples
  `F -> E -> B`, `Omega B -> F -> E`, `Omega E -> Omega B -> F`,
  and `Omega F -> Omega E -> Omega B`
- a checked looped boundary/fiber-inclusion segment, including
  `is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence`

This module is the heart of the current LES formalization, but it is not yet
library-quality organization. It is very large and mixes boundary definitions,
fiber identifications, path algebra, exactness proofs, induced homomorphisms,
and comparison lemmas. A future upstream version should split this into
one-concept modules.

### Iterated Set-Truncated Exactness

`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
extends the LES exactness to arbitrary iterates for the two positions needed
most by the Hopf proof:

- all-index exactness at the total-space term, via
  `is-exact-set-truncation-iterated-loop-fiber-sequence`
- canonical shifted fibration-boundary exactness, via
  `is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence`
- direct shifted fibration-boundary exactness in the natural `Omega^n(Omega X)`
  indexing, via
  `is-exact-set-truncation-direct-iterated-loop-fibration-boundary-fiber-sequence`
- public all-index fibration-boundary exactness in the repository's iterated
  loop indexing, via
  `is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-direct`
- canonical all-index boundary/fiber-inclusion exactness, via
  `is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence`
- the checked set-level comparison target
  `coherence-square-loop-canonical-iterated-boundary-fiber-sequence`, which
  isolates the exact map comparison between `Ω` of the canonical boundary at
  index `n` and the fresh canonical boundary at index `succ n`
- transport wrappers for recursive boundary maps and pointed homotopies

The earlier induced-map reassociation blocker has been resolved in
`src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md`.
This is substantial progress: the fibration-boundary part is no longer only a
low-dimensional Hopf shortcut.

### Group-Level LES Bridge

`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`
transfers pointed-set exactness of set-truncated iterated loop maps to ordinary
group exactness. The key exports include:

- `is-exact-hom-Group-is-exact-hom-Pointed-Set`
- `is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type`
- the trivial-codomain variant
  `is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type-is-trivial-codomain`
- LES-specific wrappers for total-space and fibration-boundary exactness
- a canonical boundary/fiber-inclusion wrapper,
  `is-exact-hom-Group-is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence`

This is a useful and checked bridge, but it is adapter-heavy. It requires
explicit comparison maps, unit compatibility, injectivity data, and coherence
squares. For library-quality code, the public API should expose simple
homotopy-group exactness theorems and keep these comparison arguments internal.

### Current Group-Level Exactness Statements

`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`
exports the ordinary group exactness statements consumed by the Hopf
calculation:

- `is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence`
  gives all-index exactness at the total-space term
  `pi(F) -> pi(E) -> pi(B)`.
- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-direct`
  gives all-index exactness at the base term
  `pi(E) -> pi(B) -> pi(F)` using the direct shifted exactness route.
- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-second-direct`
  is the low-dimensional convenience instance used around the lower Hopf
  segment.
- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-pointed-htpy`
  transports fibration-boundary exactness across a pointed homotopy of boundary
  maps.
- `is-exact-hom-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence`
  gives a boundary/fiber-inclusion exactness statement, but only in the
  currently needed low-dimensional form.
- `is-exact-hom-canonical-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence`
  gives all-index boundary/fiber-inclusion exactness for the canonical
  boundary map of the corresponding iterated fiber sequence.

The remaining gap is now more precise: boundary/fiber-inclusion exactness is
available uniformly for canonical iterated boundary maps, while the existing
recursive boundary homomorphism used by the fibration-boundary direct theorem
has not yet been identified with those canonical boundaries in the fully
iterated form needed for a single polished LES package. The current checked
target for this identification is the set-truncated coherence square
`coherence-square-loop-canonical-iterated-boundary-fiber-sequence`; at the
concrete-group level the corresponding target is
`coherence-square-canonical-boundary-concrete-homotopy-group-fiber-sequence`.

### Hopf Consumers

The Hopf fibration and final `pi_3(S^2)` calculation now use enough LES
infrastructure to avoid the old trivial-codomain shortcut for the key
nontrivial fibration-boundary exactness input. The final Hopf comparisons are
checked, and the arbitrary-index fibration-boundary bridge exists at both the
set-truncated and group levels.

The algebraic isomorphism extraction still uses trivial outer groups where the
mathematics calls for zero endpoints. That is appropriate; the important point
is that exactness itself is no longer being faked by proving the target group
is trivial.

## What Is Still Missing For Library-Quality LES Code

### No Single Long Exact Sequence Package

There is no theorem or record that packages the whole infinite LES as a single
sequence of groups and homomorphisms with exactness at every adjacent term.
Instead, the current state is a collection of adjacent exactness lemmas, some
set-level and some group-level, spread across multiple files.

A library-quality result should probably provide a named object or theorem
whose surface resembles the natural-language statement:

```text
... -> pi_(n+1)(B) -> pi_n(F) -> pi_n(E) -> pi_n(B) -> pi_(n-1)(F) -> ...
```

with exactness projections for each middle term.

### Boundary/Fiber-Inclusion Exactness Still Needs A Boundary Comparison

The total-space and fibration-boundary group exactness statements are available
for all indices using the recursive/public boundary map. Boundary/fiber-
inclusion exactness is now also available for all indices, but for the
canonical boundary map of each iterated fiber sequence.

This is meaningful structural progress, but it is not yet the final
library-quality LES. A single package should use one boundary convention
consistently in the adjacent triples

```text
pi(E) -> pi(B) -> pi(F)
pi(B) -> pi(F) -> pi(E)
```

The next real theorem is therefore the set-truncated comparison
`coherence-square-loop-canonical-iterated-boundary-fiber-sequence`. Proving it
would compare `Ω` of the canonical boundary at index `n` with the fresh
canonical shifted boundary at index `succ n`; this is the pure pointed-set
part of making the canonical boundary convention usable consistently in both
adjacent positions.

### The Proof Shape Is Still Too Transport-Heavy

Much of the current code proves exactness by moving image and kernel predicates
through comparisons. This was effective for finishing the local Hopf
calculation, but it is not the ideal final proof.

For upstream, the preferred proof should first package the shifted connecting
fiber sequence

```text
Omega E -> Omega B -> F
```

and its iterates as reusable fiber sequences. Exactness of homotopy groups
should then be derived from those structural fiber sequences. Transport lemmas
should remain available, but not be the main public proof narrative.

### Boundary Map Conventions Need A Clear Public Story

The formalization currently has canonical boundary maps, recursive boundary
maps for packaged fiber sequences, direct shifted maps, and comparison
theorems between them. These distinctions were necessary to make the code
check, especially under `--without-K`, but they make the API hard to read.

Before upstreaming, there should be one documented boundary convention and
clear theorem names explaining:

- which boundary map is canonical;
- how the boundary associated to a chosen packaged fiber sequence compares with
  the canonical one;
- how looping/reindexing changes the displayed boundary map;
- whether the comparison is definitional, by pointed homotopy, or by transport.

### The Main LES Module Needs To Be Split

`long-exact-sequence-homotopy-groups.lagda.md` is doing too much. A plausible
upstream split would be:

- boundary maps of pointed maps;
- loop spaces of fibers and fibers of fiber inclusions;
- shifted connecting fiber sequences;
- exactness of set truncations of fiber sequences;
- iterated exactness of the homotopy LES;
- group-level exactness of homotopy groups;
- a final package exposing the long exact sequence.

This split matters for maintainability, discoverability, and review. The
current single-file organization makes it hard to tell which lemmas are core
definitions and which are proof-local adapters.

### The `pi_0` Tail Is Not Packaged

The natural-language long exact sequence of a fibration includes a pointed-set
tail involving lower homotopy groups/components. The current project was aimed
at concrete homotopy groups indexed from `pi_1` upward and at ordinary group
exactness, so it does not package the full low-dimensional pointed-set tail as
part of one LES theorem.

This is acceptable for the `pi_3(S^2)` project, but not for a complete
library-quality LES theorem.

### No Abelian-Group Refinement

The current group-level exactness is ordinary group exactness. Natural
statements often note that higher homotopy groups are abelian and that the LES
eventually lives in abelian groups. This is not needed for the Hopf calculation
as currently formalized, but it is another gap relative to a polished library
development.

### Naming Still Reflects The Project History

Some exports and wrappers are named around concrete homotopy groups, Hopf-facing
segments, direct variants, or low-dimensional convenience cases. That is fine
for local progress, but upstream names should emphasize the stable mathematical
construction rather than the route by which the blocker was cleared.

## Recommended Next Steps

1. Prove `coherence-square-loop-canonical-iterated-boundary-fiber-sequence`.
   This is now the most precise checked target for the boundary convention
   problem: it compares the set-truncated map induced by looping
   `canonical-pointed-map-iterated-boundary-fiber-sequence S n` with the fresh
   canonical boundary map of `iterated-loop-fiber-sequence S (succ-ℕ n)`.
   After this is proved, use naturality of the concrete homotopy-group
   underlying-type equivalence to establish
   `coherence-square-canonical-boundary-concrete-homotopy-group-fiber-sequence`.

2. Define a small LES indexing/package layer after the boundary comparison is
   checked. It does not need to be elaborate
   at first; even a record with three exactness projections for the repeating
   adjacent positions would make the current result far easier to consume.

3. Refactor the boundary map API. Choose a canonical public boundary, then make
   recursive/direct variants private or secondary corollaries with explicit
   comparison names.

4. Split `long-exact-sequence-homotopy-groups.lagda.md` into one-concept
   modules once the boundary comparison and package layer are checked. Splitting
   before that may make the remaining transport work harder.

5. Write short literate prose above the final structural theorems explaining
   the relationship with the HoTT Book LES proof and the Coq-HoTT
   `connect_fiberseq` decomposition. The code already contains the pieces, but
   a reviewer should not have to infer the proof architecture from transport
   lemmas.

6. Only after the group-level LES package is clean, consider adding the `pi_0`
   tail and abelian refinements. These are important for completeness but not
   the next blocker for the current local theorem stack.

## Verification State

The relevant Agda modules have been checked in recent sessions with
`./check.sh`, including:

```sh
./check.sh src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
```

On 2026-06-26, the canonical boundary/fiber-inclusion additions were checked
with the same five commands above.

At the time this handoff was written, Agda MCP tools were visible to the agent,
but `./check.sh <file>` remains the acceptance criterion. This file is a status
document only; it does not add or modify Agda proofs.
