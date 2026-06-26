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
contains the remaining structural and low-level LES work. It now imports the
standalone structural modules for the loop-fiber equivalence, the first
fiber-inclusion fiber sequence, and the connecting fiber sequence. It
formalizes:

- `boundary-fiber-Pointed-Type : Omega B ->* fiber g`
  as a compatibility name for `connecting-map-Pointed-Type`
- the direct shifted sequence
  `fiber-sequence-boundary-map-Ω-direct-Pointed-Type`
- induced homomorphisms for a packaged fiber sequence:
  `hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence`,
  `hom-fibration-concrete-homotopy-group-fiber-sequence`, and
  `boundary-hom-concrete-homotopy-group-fiber-sequence`
- canonical boundary homomorphisms for pointed maps and for iterated packaged
  fiber sequences, including
  `canonical-boundary-hom-concrete-homotopy-group-fiber-sequence`
- separate pointed-map names for the two canonical boundary roles:
  `canonical-pointed-map-iterated-loop-boundary-fiber-sequence` for the fresh
  shifted fibration-boundary map and
  `loop-canonical-pointed-map-iterated-boundary-fiber-sequence` for the loop of
  the canonical iterated boundary
- `iterated-loop-fiber-sequence`
- set-truncated exactness for the initial adjacent triples
  `F -> E -> B`, `Omega B -> F -> E`, `Omega E -> Omega B -> F`,
  and `Omega F -> Omega E -> Omega B`
- a checked looped boundary/fiber-inclusion segment, including
  `is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence`

This module is still the heart of the current LES formalization, but it is not
yet library-quality organization. It remains very large and mixes boundary
compatibility names, path algebra, exactness proofs, induced homomorphisms, and
comparison lemmas. The recent split has removed the first structural
fiber-identification blocks from this file; the remaining upstream cleanup
should continue moving boundary-comparison adapters and exactness packages into
one-concept modules.

### Connecting Fiber Sequences

`src/synthetic-homotopy-theory/connecting-fiber-sequences.lagda.md` is the
first extraction from the large LES module toward one-concept organization. It
gives library-facing names to the checked `connect_fiberseq`-style structures:

- `connecting-map-Pointed-Type : Omega B ->* fiber g`
- `fiber-sequence-connecting-map-Pointed-Type`, packaging
  `Omega E ->* Omega B ->* fiber g`
- `connecting-map-fiber-sequence-Pointed-Type` for a packaged fiber sequence
  `F ->* E ->* B`
- `fiber-sequence-connecting-map-fiber-sequence-Pointed-Type`, packaging
  `Omega E ->* Omega B ->* F`

This module is now standalone structural code rather than a facade over
`long-exact-sequence-homotopy-groups`. The long exact sequence file imports it
and keeps older boundary-map terminology as compatibility aliases.

### Loop Spaces Of Fibers

`src/synthetic-homotopy-theory/loop-spaces-fibers-of-pointed-maps.lagda.md`
is the extracted loop-fiber equivalence module. It proves:

- `pointed-equiv-loop-fiber-Pointed-Type`, identifying
  `Omega (fiber g)` with the fiber of `Omega E ->* Omega B`
- `pointed-htpy-loop-fiber-inclusion-Pointed-Type`, comparing the loop of the
  fiber inclusion with the canonical inclusion of the loop-map fiber

This is the structural ingredient used when iterating the LES and should be a
reasonable upstream candidate independent of the concrete LES exactness code.

### Loop Spaces Of Pointed Equivalences

`src/synthetic-homotopy-theory/loop-spaces-pointed-equivalences.lagda.md`
is a generic support module extracted from the LES comparison code. It records
explicit pointed homotopies showing that the loop-space functor preserves
inverses and composition of pointed equivalences, including the retraction
calculation used by the remaining loop-boundary comparison.

This is not LES-specific mathematics; it is reusable pointed-equivalence
algebra that should not live inside the main long exact sequence file.

### Fiber Sequences Of Fiber Inclusions

`src/synthetic-homotopy-theory/fiber-sequences-fiber-inclusions.lagda.md`
is the extracted first fiber-of-the-fiber module. For a pointed map
`g : E ->* B`, it identifies the fiber of the canonical fiber inclusion with
`Omega B` and packages

```text
Omega B ->* fiber g ->* E
```

as `fiber-sequence-boundary-fiber-Pointed-Type`. The construction uses the
standalone `connecting-map-Pointed-Type`, so it is aligned with the
`connect_fiberseq` route rather than the old local boundary-map block.

### Iterated Set-Truncated Exactness

`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
extends the LES exactness to arbitrary iterates for the two positions needed
most by the Hopf proof:

- all-index exactness at the total-space term, via
  `is-exact-set-truncation-iterated-loop-fiber-sequence`
- canonical shifted fibration-boundary exactness, via
  `is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence`
- connecting-sequence fibration-boundary exactness in the natural
  `Omega^n(Omega X)` indexing, via
  `is-exact-set-truncation-iterated-loop-connecting-fiber-sequence`, with the
  older direct name retained as a compatibility alias
- public all-index fibration-boundary exactness in the repository's iterated
  loop indexing, via
  `is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence`,
  with the older direct name retained as a compatibility alias
- canonical all-index boundary/fiber-inclusion exactness, via
  `is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence`
- a checked set-truncated canonical LES package,
  `Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence`,
  whose object
  `set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence`
  records the three repeating adjacent exactness positions while keeping the
  two canonical boundary maps for the fibration-boundary and
  boundary/fiber-inclusion positions as separate fields
- the checked all-index signed comparison
  `coherence-square-canonical-iterated-boundary-fiber-sequence-signed`,
  obtained by applying the first-loop comparison to each iterated loop fiber
  sequence
- the checked first-loop signed comparison
  `coherence-square-first-loop-canonical-iterated-boundary-fiber-sequence-signed`,
  which identifies the fresh canonical shifted boundary with the looped
  recursive boundary only after precomposing the recursive side by the
  double-loop inversion map induced by `ap inv`
- the checked all-index signed exactness transport
  `is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-signed`,
  which turns the all-index comparison into exactness for the looped canonical
  boundary while keeping the inversion adapter internal
- the checked first-loop signed exactness transport
  `is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-first-loop-signed`,
  retained as the base comparison reused by the all-index theorem
- transport wrappers for recursive boundary maps and pointed homotopies

The earlier induced-map reassociation blocker has been resolved in
`src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md`.
The first-loop sign calculation is also important negative information: the
naive unsigned recursive/canonical square is not the right target for the
current boundary definitions.

### Group-Level LES Bridge

`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`
transfers pointed-set exactness of set-truncated iterated loop maps to ordinary
group exactness. The key exports include:

- `is-exact-hom-Group-is-exact-hom-Pointed-Set`
- `is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type`
- the trivial-codomain variant
  `is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type-is-trivial-codomain`
- LES-specific wrappers for total-space and fibration-boundary exactness
- a looped-canonical fibration-boundary wrapper,
  `is-exact-hom-Group-is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence`
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
- `is-exact-hom-canonical-fibration-boundary-concrete-homotopy-group-fiber-sequence`
  gives all-index exactness at the base term using the canonical iterated
  boundary homomorphism.
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
- `Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence` packages the three
  repeating group-level exactness positions into a single checked record, and
  `long-exact-sequence-homotopy-groups-fiber-sequence` instantiates it for any
  packaged fiber sequence. The package now uses the canonical iterated boundary
  homomorphism in both boundary slots. The signed inversion adapter needed to
  compare the looped canonical boundary with the fresh shifted boundary is
  confined to the proof of the fibration-boundary exactness theorem.

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

### Natural-Language LES Surface Still Needs Polish

There is now a checked set-truncated canonical LES package for the repeating
adjacent pointed-set exactness positions, and a checked group-level record
packaging the three repeating ordinary group exactness positions for a fiber
sequence. The group-level package uses one canonical boundary homomorphism
convention in both boundary positions.

A library-quality result should probably provide a named object or theorem
whose surface resembles the natural-language statement:

```text
... -> pi_(n+1)(B) -> pi_n(F) -> pi_n(E) -> pi_n(B) -> pi_(n-1)(F) -> ...
```

with exactness projections for each middle term.

### Boundary Conventions Still Need Upstream API Polish

The total-space exactness statement is available for all indices. The
fibration-boundary and boundary/fiber-inclusion group exactness statements are
now also available for all indices using the canonical boundary map of each
iterated fiber sequence.

The new set-truncated canonical package deliberately follows the Coq-HoTT
`loops_les` style: each adjacent segment uses the fresh canonical connecting
map supplied by the relevant iterated fiber sequence. In particular, it records
two boundary fields with the same displayed source and target, one for
fibration-boundary exactness and one for boundary/fiber-inclusion exactness,
and does not assert that these are equal.

The public group-level package has chosen the latter convention: it exposes the
delooped canonical boundary homomorphism and hides the systematic signed
adapter in the proof that this boundary gives fibration-boundary exactness. A
direct unsigned comparison between `Ω` of the canonical boundary and the fresh
canonical shifted boundary is still not correct for the current definitions;
the checked all-index theorem records the necessary inversion internally.

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

1. Continue splitting `long-exact-sequence-homotopy-groups.lagda.md` into
   one-concept modules. The connecting fiber sequence has been extracted as a
   checked structural module, and the loop-fiber and first fiber-inclusion
   fiber-sequence equivalences have now been extracted. The next candidates are
   the remaining boundary-comparison adapters and the exactness packages that
   still live in the main LES file.

2. Write short literate prose above the final structural theorems explaining
   the relationship with the HoTT Book LES proof and the Coq-HoTT
   `connect_fiberseq` decomposition. The code already contains the pieces, but
   a reviewer should not have to infer the proof architecture from transport
   lemmas.

3. Only after the group-level LES package is clean, consider adding the `pi_0`
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
with the same five commands above. Later on 2026-06-26, the signed loop-boundary
comparison and set-truncated first-loop signed coherence were checked with:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
```

Both Agda checks passed, and the touched-file scan found no holes, unsolved
meta pragmas, or postulates.

Later on 2026-06-26, the approach-2 canonical set-truncated LES package and
the group-level LES package were checked with:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
```

All three checks passed. The set-level package keeps the fibration-boundary and
boundary/fiber-inclusion canonical boundary maps as separate fields, matching
the fresh-connecting-map approach rather than forcing a recursive/canonical
boundary equality. The group-level package now records the canonical iterated
boundary homomorphism in both boundary slots.

Later on 2026-06-26, the first-loop signed adapter was upgraded from a
comparison square to checked exactness transport. The structured pointed-set
exactness file now includes
`is-exact-hom-Pointed-Set-image-kernel-shift-right-inverse`; the set-truncated
iterated exactness file uses the pointed equivalence induced by loop inversion
to prove
`is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-first-loop-signed`;
this first-loop theorem is now the reusable seed for the all-index signed
comparison.
The checked commands were:

```sh
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
```

All four checks passed.

Later on 2026-06-26, the boundary API was refactored toward the canonical
public route. `long-exact-sequence-homotopy-groups` now names the fresh shifted
canonical boundary map and the loop of the canonical iterated boundary map as
separate pointed maps:

```text
canonical-pointed-map-iterated-loop-boundary-fiber-sequence
loop-canonical-pointed-map-iterated-boundary-fiber-sequence
```

The set-truncated canonical LES package now defines its two boundary fields
through these names, making the fresh-connecting-map convention explicit.
The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
```

All three checks passed.

Later on 2026-06-26, the first-loop comparison was lifted to all indices by
applying it to the iterated loop fiber sequence. This proved
`coherence-square-canonical-iterated-boundary-fiber-sequence-signed` and
`is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-signed`,
added the group-level converter
`is-exact-hom-Group-is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence`,
and switched the group-level LES package to the canonical boundary
homomorphism in both boundary slots. The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All five checks passed. The signed transport is now hidden inside the
canonical fibration-boundary exactness proof rather than exposed as public LES
data.

Later on 2026-06-26, the first two API-cleanup tasks were completed as checked
code. The module
`synthetic-homotopy-theory.connecting-fiber-sequences` is no longer a facade
over `long-exact-sequence-homotopy-groups`: it defines the connecting map of a
pointed map, proves the pointed fiber sequence

```text
Omega E ->* Omega B ->* fiber g
```

and transports it across a packaged fiber sequence to prove

```text
Omega E ->* Omega B ->* F.
```

The long exact sequence module now imports this structural module. Its
`boundary-fiber-Pointed-Type` and `boundary-pointed-map-fiber-sequence` names
are compatibility names for the connecting maps, and the generic
`fiber-sequence-boundary-map-Ω-direct-Pointed-Type` package is an alias of the
structural connecting fiber sequence. The older packaged direct proof package
remains in the LES file because later comparison lemmas use its exact proof
components; it is now documented as compatibility infrastructure rather than
the reviewer-facing construction.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/connecting-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All seven checks passed. The touched-file scan found no holes, postulates,
unsafe termination pragmas, rewrite-rule dependency, or unsolved-meta options,
and `git diff --check` passed.

Later on 2026-06-26, the loop-fiber and first fiber-inclusion structural
blocks were split out of `long-exact-sequence-homotopy-groups`. The new module
`loop-spaces-fibers-of-pointed-maps` contains the pointed equivalence
`Omega (fiber g) ~=* fiber (Omega g)` and its fiber-inclusion compatibility.
The new module `fiber-sequences-fiber-inclusions` contains the pointed
equivalence identifying the fiber of `fiber g -> E` with `Omega B` and packages
`Omega B ->* fiber g ->* E` as a pointed fiber sequence. The main LES module
now imports those modules instead of defining the blocks inline, and the
set-truncated iterated exactness file imports the loop-fiber module directly.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/loop-spaces-fibers-of-pointed-maps.lagda.md
./check.sh src/synthetic-homotopy-theory/fiber-sequences-fiber-inclusions.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All eight checks passed. A touched-file scan found no holes, postulates,
unsafe termination pragmas, rewrite-rule dependency, or unsolved-meta options,
and `git diff --check` passed.

Later on 2026-06-26, the generic pointed-equivalence algebra used by the LES
comparison code was also extracted to
`loop-spaces-pointed-equivalences`. The main LES file now imports this module
instead of carrying the loop-of-inverse and inverse-of-composite pointed
homotopies inline.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/loop-spaces-pointed-equivalences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All six checks passed.

At the time this handoff was written, Agda MCP tools were visible to the agent,
but `./check.sh <file>` remains the acceptance criterion. This file is a status
document only; it does not add or modify Agda proofs.
