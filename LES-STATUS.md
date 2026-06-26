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

### Long Exact Sequence Coordination Module

`src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md`
is now a thin coordination/documentation module. The definition-level LES maps,
boundary maps, and homomorphisms have been split into standalone modules, and
this file points readers to them:

- `iterated-loop-fiber-sequences`
- `iterated-boundary-maps-fiber-sequences`
- `homomorphisms-homotopy-groups-fiber-sequences`

The old large main-file organization has therefore been cleared as a blocker.
Remaining library-quality cleanup should focus on the larger exactness
packages and the final public long-exact-sequence surface.

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
`long-exact-sequence-homotopy-groups`. Later boundary-map terminology is now
kept in dedicated boundary modules rather than in the long exact sequence
coordination file.

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

### Fibers Of Boundary Maps

`src/synthetic-homotopy-theory/fibers-boundary-maps-pointed-maps.lagda.md`
is the extracted boundary-adapter module. It gives LES-facing terminology for
the connecting map of a pointed map,

```text
Omega B ->* fiber g,
```

and contains the direct comparison between `Omega E` and the fiber of this
boundary map. It also records the compatibility between this direct
fiber-of-boundary comparison and the fiber-inclusion-of-the-fiber-inclusion
sequence, plus the looped-boundary first-projection/path adapters used by the
iterated exactness layer.

### Base Set-Truncated Exactness

`src/synthetic-homotopy-theory/set-truncated-exactness-homotopy-groups-fiber-sequences.lagda.md`
is the extracted base exactness module. It proves set-truncated exactness for:

- canonical and packaged `F ->* E ->* B` fiber-sequence triples;
- the boundary segment `Omega B ->* F ->* E`;
- the shifted connecting segment `Omega E ->* Omega B ->* F`;
- the looped packaged segment `Omega F ->* Omega E ->* Omega B`;
- the looped boundary/fiber-inclusion segment
  `Omega^2 B ->* Omega F ->* Omega E`;
- the initial four-triple set-truncated LES segment package.

This file is still proof-heavy, but it now separates the set-level exactness
layer from the definition-level homotopy-group maps in the main LES file.

### Iterated Loop Fiber Sequences

`src/synthetic-homotopy-theory/iterated-loop-fiber-sequences.lagda.md`
contains the checked iteration of a packaged fiber sequence. For a fiber
sequence `F ->* E ->* B`, it defines:

- `pointed-equiv-iterated-loop-fiber-fiber-sequence`, identifying `Omega^n F`
  with the fiber of `Omega^n E ->* Omega^n B`;
- `pointed-htpy-iterated-loop-fiber-inclusion-fiber-sequence`, comparing the
  iterated fiber inclusion with the canonical inclusion of that fiber;
- `iterated-loop-fiber-sequence`, packaging
  `Omega^n F ->* Omega^n E ->* Omega^n B`.

### Iterated Boundary Maps Of Fiber Sequences

`src/synthetic-homotopy-theory/iterated-boundary-maps-fiber-sequences.lagda.md`
contains the recursive and canonical boundary maps of a packaged fiber
sequence. It owns:

- `boundary-pointed-map-fiber-sequence`;
- `pointed-map-iterated-boundary-fiber-sequence`;
- reassociation lemmas for recursive iterated boundaries;
- `canonical-pointed-map-iterated-boundary-fiber-sequence`;
- `canonical-pointed-map-iterated-loop-boundary-fiber-sequence`;
- `loop-canonical-pointed-map-iterated-boundary-fiber-sequence`;
- the direct shifted boundary fiber sequence
  `fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type`.

This keeps the Coq-HoTT/Rocq-style distinction between fresh canonical
connecting maps and recursive looped boundary maps visible at the pointed-map
level.

### Homomorphisms Induced By Fiber Sequences

`src/synthetic-homotopy-theory/homomorphisms-homotopy-groups-fiber-sequences.lagda.md`
contains the concrete homotopy-group homomorphisms induced by a packaged fiber
sequence:

- `hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence`;
- `hom-fibration-concrete-homotopy-group-fiber-sequence`;
- `boundary-hom-concrete-homotopy-group-fiber-sequence`;
- `canonical-boundary-hom-concrete-homotopy-group-fiber-sequence`;
- `canonical-boundary-hom-concrete-homotopy-group-Pointed-Type`.

The group-level exactness files now import these homomorphisms directly
instead of obtaining them through the main LES module.

### Iterated Set-Truncated Maps

`src/synthetic-homotopy-theory/set-truncated-iterated-maps-homotopy-groups-fiber-sequences.lagda.md`
is the extracted map layer for the iterated set-truncated LES. It owns the
pointed-set homomorphisms induced by the fiber inclusion, fibration, recursive
boundary, canonical shifted boundary, looped canonical boundary, and shifted
connecting sequence. This gives later exactness modules stable names for the
maps without carrying the proof-heavy transport layer.

### Canonical Iterated Set-Truncated Exactness

`src/synthetic-homotopy-theory/set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
owns the structural exactness theorems that do not involve the recursive
signed boundary comparison:

- all-index exactness at the total-space term;
- canonical shifted fibration-boundary exactness;
- canonical shifted boundary/fiber-inclusion exactness.

These are the theorem inputs for the checked set-truncated canonical LES
package.

### Signed Boundary Comparisons

`src/synthetic-homotopy-theory/signed-boundary-comparisons-fiber-sequences.lagda.md`
owns the inversion/sign adapter comparing looped canonical boundaries with
fresh shifted canonical boundaries. The all-index signed comparison and the
corresponding exactness transport now live here, keeping the systematic
double-loop inversion machinery out of the public LES packages.

### Iterated Set-Truncated Exactness Wrapper

`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
now imports the extracted map, canonical exactness, and signed comparison
modules as public theorem providers. It retains the remaining compatibility
wrappers and transport lemmas that connect the structural route to older local
names:

- connecting-sequence fibration-boundary exactness in the natural
  `Omega^n(Omega X)` indexing, via
  `is-exact-set-truncation-iterated-loop-connecting-fiber-sequence`, with the
  older direct name retained as a compatibility alias
- public all-index fibration-boundary exactness in the repository's iterated
  loop indexing, via
  `is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence`,
  with the older direct name retained as a compatibility alias
- theorem inputs for the checked set-truncated canonical LES package in
  `src/synthetic-homotopy-theory/set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md`,
  whose record
  `Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence`
  and object
  `set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence`
  expose the three repeating adjacent exactness positions while keeping the
  two canonical boundary maps for the fibration-boundary and
  boundary/fiber-inclusion positions as separate fields
- transport wrappers for recursive boundary maps and pointed homotopies

The earlier induced-map reassociation blocker has been resolved in
`src/synthetic-homotopy-theory/reassociation-iterated-loop-spaces.lagda.md`.
The first-loop sign calculation is also important negative information: the
naive unsigned recursive/canonical square is not the right target for the
current boundary definitions.

### Generic Group-Level Exactness Bridge

`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md`
transfers pointed-set exactness to ordinary group exactness. The key exports
include:

- `is-exact-hom-Group-is-exact-hom-Pointed-Set`
- `is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type`
- the trivial-codomain variant
  `is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type-is-trivial-codomain`

This is still an adapter, since it requires explicit comparison maps, unit
compatibility, injectivity data, and coherence squares. It is now independent
of fiber sequences and set-truncated LES modules, which makes it a reusable
ordinary-group transport theorem.

### Fiber-Sequence Group-Level Exactness Bridge

`src/synthetic-homotopy-theory/group-exactness-from-set-truncated-exactness-fiber-sequences.lagda.md`
specializes the generic bridge to the set-truncated adjacent triples in a
fiber sequence. It owns the group-level converters for:

- all-index total-space exactness;
- canonical boundary/fiber-inclusion exactness;
- recursive fibration-boundary exactness;
- looped-canonical fibration-boundary exactness.

This module is still proof- and adapter-heavy, but it is no longer mixed into
the generic pointed-set-to-group transport theorem.

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
- `src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md`
  defines `Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence` and
  instantiates it as `long-exact-sequence-homotopy-groups-fiber-sequence` for
  any packaged fiber sequence. The package uses the canonical iterated boundary
  homomorphism in both boundary slots. The signed inversion adapter needed to
  compare the looped canonical boundary with the fresh shifted boundary is
  confined to the imported proof of the fibration-boundary exactness theorem.

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

### The Remaining Exactness Packages Need To Be Split

`long-exact-sequence-homotopy-groups.lagda.md` is now only a thin coordination
module. Completed splits include:

- loop spaces of fibers and fibers of fiber inclusions;
- shifted connecting fiber sequences;
- boundary maps of pointed maps and their fiber comparisons;
- exactness of set truncations of fiber sequences;
- iterated loop fiber sequences;
- recursive and canonical iterated boundary maps;
- homomorphisms induced on concrete homotopy groups by fiber sequences;
- the set-truncated canonical LES package;
- the group-level LES package.

A plausible remaining upstream split would be:

- the transport-heavy support lemmas inside iterated exactness of the homotopy
  LES;
- the signed boundary comparison support layer;
- the group-level exactness support wrappers below the final package.

This split matters for maintainability, discoverability, and review. The
current exactness files still contain many adapters and transport theorems
beside the public exactness statements.

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

1. Continue cleaning the public group-level exactness statement layer into
   reviewer-facing modules. The main LES file, final package modules, iterated
   set-truncated map layer, canonical set-truncated exactness layer, signed
   boundary comparison layer, generic group bridge, and fiber-sequence-specific
   group bridge are now split; the next candidate is the theorem statement
   layer in `exactness-homotopy-groups-fiber-sequences`.

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

All six checks passed. A touched-file scan found no holes, postulates, unsafe
termination pragmas, rewrite-rule dependency, or unsolved-meta options, and
`git diff --check` passed.

Later on 2026-06-26, the boundary-map adapters and the base
set-truncated exactness package were split out of
`long-exact-sequence-homotopy-groups`. The new module
`fibers-boundary-maps-pointed-maps` owns the LES-facing boundary terminology,
the direct fiber-of-boundary comparison, the comparison with the
fiber-inclusion-of-the-fiber-inclusion sequence, and the looped-boundary
adapters. The new module
`set-truncated-exactness-homotopy-groups-fiber-sequences` owns the base
set-truncated exactness proofs for canonical, packaged, boundary, shifted
connecting, looped packaged, and looped boundary/fiber-inclusion segments. The
main LES module now imports those modules and keeps only definition-level
homotopy-group maps, recursive boundary maps, and compatibility prose.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/fibers-boundary-maps-pointed-maps.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All eight checks passed.

Later on 2026-06-26, the remaining definition-level contents of
`long-exact-sequence-homotopy-groups` were split into three checked modules:
`iterated-loop-fiber-sequences`, `iterated-boundary-maps-fiber-sequences`, and
`homomorphisms-homotopy-groups-fiber-sequences`. Downstream set-level,
group-level, and Hopf consumers now import these modules directly. The old
long exact sequence file is now a thin coordination module.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/iterated-loop-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/iterated-boundary-maps-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/homomorphisms-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md
```

All eleven checks passed.

Later on 2026-06-26, the public LES package layer was split out of the
proof-heavy exactness modules. The new module
`set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences`
owns the checked set-truncated canonical LES record and object, while
`long-exact-sequence-homotopy-groups-fiber-sequences` owns the checked
group-level LES record and object. The proof modules
`set-truncated-iterated-exactness-homotopy-groups-fiber-sequences` and
`exactness-homotopy-groups-fiber-sequences` now provide the exactness theorems
imported by those packages instead of defining the final package surface
inline.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All five checks passed. A touched-file scan found no holes, postulates,
unsafe termination pragmas, rewrite-rule dependency, or unsolved-meta options,
and `git diff --check` passed.

Later on 2026-06-26, the iterated set-truncated exactness support layer was
split into three checked modules. The new module
`set-truncated-iterated-maps-homotopy-groups-fiber-sequences` owns the
set-truncated iterated LES maps. The new module
`set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences`
owns the structural canonical exactness theorems. The new module
`signed-boundary-comparisons-fiber-sequences` owns the loop-inversion signed
comparison and exactness transport. The original iterated exactness module now
re-exports these pieces and retains compatibility wrappers for the direct and
recursive routes.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-maps-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/signed-boundary-comparisons-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All ten checks passed. A touched-file scan found no holes, postulates, unsafe
termination pragmas, rewrite-rule dependency, or unsolved-meta options, and
`git diff --check` passed.

Later on 2026-06-26, the group-level exactness bridge was split into a generic
transport theorem module and a fiber-sequence-specific specialization module.
The existing module
`group-exactness-from-set-truncated-homotopy-group-exactness` now owns only the
generic pointed-set-to-group and loop-truncation transport theorems. The new
module `group-exactness-from-set-truncated-exactness-fiber-sequences` owns the
LES-specific converters from set-truncated fiber-sequence exactness to ordinary
group exactness. The public exactness module imports both.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-exactness-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequence-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All six checks passed.

At the time this handoff was written, Agda MCP tools were visible to the agent,
but `./check.sh <file>` remains the acceptance criterion. This file is a status
document only; it does not add or modify Agda proofs.
