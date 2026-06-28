# Long Exact Sequence Status

Last updated: 2026-06-27.

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

`src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md`
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
`long-exact-sequences-homotopy-groups`. Later boundary-map terminology is now
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

### Direct Iterated Set-Truncated Exactness

`src/synthetic-homotopy-theory/set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
owns the direct connecting-map route and reassociation transports:

- connecting-sequence fibration-boundary exactness in the natural
  `Omega^n(Omega X)` indexing, via
  `is-exact-set-truncation-iterated-loop-connecting-fiber-sequence`, with the
  older direct name retained as a compatibility alias
- public all-index fibration-boundary exactness in the repository's iterated
  loop indexing, via
  `is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence`,
  with the older direct name retained as a compatibility alias

### Recursive Iterated Set-Truncated Exactness

`src/synthetic-homotopy-theory/set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
owns the recursive-boundary compatibility transports:

- kernel-comparison transport from canonical shifted boundary exactness;
- pointwise homotopy transport from canonical shifted boundary exactness;
- pointed-homotopy transport from the recursive looped boundary map to the
  fresh boundary map of the iterated loop fiber sequence.

### Iterated Set-Truncated Exactness Wrapper

`src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md`
is now only the compatibility facade re-exporting the extracted maps,
canonical exactness, signed comparison, direct exactness, and recursive
exactness modules. This preserves older downstream imports while making each
proof route explicit.

The checked set-truncated LES display is in
`src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md`:

- theorem inputs for the checked set-truncated LES display are imported through
  the iterated exactness facade;
- it instantiates
  `Long-Exact-Sequence-Pointed-Set` as
  `set-truncated-long-exact-sequence-fiber-sequence`;
- its public boundary is
  `hom-trunc-loop-canonical-iterated-boundary-fiber-sequence`, while the signed
  comparison with the fresh shifted boundary remains theorem-provider machinery.


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

`src/synthetic-homotopy-theory/canonical-exactness-homotopy-groups-fiber-sequences.lagda.md`
owns the canonical group-level exactness statements used by the public LES
package:

- `is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence`
  gives all-index exactness at the total-space term
  `pi(F) -> pi(E) -> pi(B)`.
- `is-exact-hom-canonical-fibration-boundary-concrete-homotopy-group-fiber-sequence`
  gives all-index exactness at the base term using the canonical iterated
  boundary homomorphism.
- `is-exact-hom-canonical-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence`
  gives all-index boundary/fiber-inclusion exactness for the canonical
  boundary map of the corresponding iterated fiber sequence.
- `src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md`
  now imports this canonical theorem provider directly.

`src/synthetic-homotopy-theory/direct-exactness-homotopy-groups-fiber-sequences.lagda.md`
owns the direct shifted connecting-map group-level exactness statements:

- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-direct`
  gives all-index exactness at the base term
  `pi(E) -> pi(B) -> pi(F)` using the direct shifted exactness route.
- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-second-direct`
  is the low-dimensional convenience instance used around the lower Hopf
  segment.
- `is-exact-hom-fibration-connecting-map-concrete-homotopy-group-fiber-sequence`
  exposes the direct connecting-map theorem before the historical boundary
  alias.

`src/synthetic-homotopy-theory/recursive-exactness-homotopy-groups-fiber-sequences.lagda.md`
owns the recursive and transport compatibility statements consumed by the Hopf
calculation:

- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-pointed-htpy`
  transports fibration-boundary exactness across a pointed homotopy of boundary
  maps.
- `is-exact-hom-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence`
  gives a boundary/fiber-inclusion exactness statement, but only in the
  currently needed low-dimensional form.
- `is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-is-trivial-codomain`
  is the older trivial-target fallback retained for downstream compatibility.

`src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md`
is now only the compatibility facade re-exporting the canonical, direct, and
recursive theorem-provider modules. This preserves older downstream imports
while making each proof route explicit.

The group-level LES package defines
`Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence` and instantiates it as
`long-exact-sequence-homotopy-groups-fiber-sequence` for any packaged fiber
sequence. Its single public boundary field is the canonical iterated boundary
homomorphism, and that field is used in both adjacent exactness positions. The
signed inversion adapter needed to compare the looped canonical boundary with
the fresh shifted boundary is confined to the imported proof of the canonical
fibration-boundary exactness theorem.

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

## Library-Quality LES Status

### Public Surface

The checked public LES surface now has package layers with record projections as
its API:

- `structured-types.exact-sequences-pointed-sets` defines
  `Exact-Triple-Pointed-Set`, a reusable package for three pointed sets, two
  pointed maps, and exactness at the middle term.
- `structured-types.long-exact-sequences-pointed-sets` defines the reusable
  three-periodic pointed-set LES display and derives the three adjacent exact
  triples at each index: fiber-inclusion/fibration, fibration/boundary, and
  boundary/fiber-inclusion.
- `set-truncated-long-exact-sequences-fiber-sequences` instantiates that display
  for iterated loops of a fiber sequence, using one looped canonical public
  boundary convention, and re-exposes the three adjacent exact triples for that
  instance.
- `long-exact-sequences-homotopy-groups-fiber-sequences` exposes the standard
  group-level fiber-inclusion, fibration, boundary, and exactness projections as
  fields of `Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence`.
- `pointed-set-tail-long-exact-sequences-fiber-sequences` exposes the low-degree
  pointed-set tail maps and exactness projections as fields.
- `abelian-long-exact-sequences-homotopy-groups-fiber-sequences` exposes the
  abelian-range LES arrows and exactness projections as fields.

The display-layer question is now resolved. A long exact sequence remains the
minimal three-periodic record, while the textbook adjacent-triple view is an
additive derived API over that record. The public set-truncated package has one
boundary convention; signed comparisons, recursive boundaries, direct shifted
maps, and image/kernel transports remain theorem-provider machinery outside the
headline LES packages.

### Remaining Upstream Integration Decisions

There are no remaining proof-search, file-splitting, or display-layer blockers
for a library-quality local LES. The remaining decisions are upstream extraction
and review decisions:

- choose final upstream module names and namespaces for the exact-triple,
  pointed-set display, set-truncated, group-level, abelian, and pointed-set tail
  packages;
- decide whether older downstream names deserve separate migration facades,
  without putting compatibility aliases back into the main LES packages;
- keep route-specific names such as direct, recursive, signed, and
  low-dimensional convenience variants out of the main narrative unless a user
  explicitly asks for those comparison theorems;
- prepare the upstream extraction so structural modules, exactness-provider
  modules, public packages, and any migration facades stay separate.

For handoff: the next agent should not re-split exactness providers, re-prove the
LES, add another boundary convention to the public set-truncated package, or
reintroduce compatibility aliases in the main packages. A further single
ordinal/indexed rendering should only be added if an upstream reviewer asks for
that specific presentation; the current derived exact-triple view covers the
standard adjacent display.

## Verification State

The relevant Agda modules have been checked in recent sessions with
`./check.sh`, including:

```sh
./check.sh src/synthetic-homotopy-theory/functoriality-iterated-loop-spaces.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
```

On 2026-06-26, the canonical boundary/fiber-inclusion additions were checked
with the same five commands above. Later on 2026-06-26, the signed loop-boundary
comparison and set-truncated first-loop signed coherence were checked with:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
rg -n "\{!!\}|allow-unsolved-metas|postulate" src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
```

Both Agda checks passed, and the touched-file scan found no holes, unsolved
meta pragmas, or postulates.

Later on 2026-06-26, the approach-2 canonical set-truncated LES display package and
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
public route. `long-exact-sequences-homotopy-groups` now names the fresh shifted
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
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
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
over `long-exact-sequences-homotopy-groups`: it defines the connecting map of a
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
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
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
blocks were split out of `long-exact-sequences-homotopy-groups`. The new module
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
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
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
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
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
`long-exact-sequences-homotopy-groups`. The new module
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
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All eight checks passed.

Later on 2026-06-26, the remaining definition-level contents of
`long-exact-sequences-homotopy-groups` were split into three checked modules:
`iterated-loop-fiber-sequences`, `iterated-boundary-maps-fiber-sequences`, and
`homomorphisms-homotopy-groups-fiber-sequences`. Downstream set-level,
group-level, and Hopf consumers now import these modules directly. The old
long exact sequence file is now a thin coordination module.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/iterated-loop-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/iterated-boundary-maps-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/homomorphisms-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
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
`set-truncated-long-exact-sequences-fiber-sequences`
owns the checked set-truncated canonical LES record and object, while
`long-exact-sequences-homotopy-groups-fiber-sequences` owns the checked
group-level LES record and object. The proof modules
`set-truncated-iterated-exactness-homotopy-groups-fiber-sequences` and
`exactness-homotopy-groups-fiber-sequences` now provide the exactness theorems
imported by those packages instead of defining the final package surface
inline.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
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
./check.sh src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-homotopy-group-exactness.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
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
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
```

All six checks passed. A touched-file scan found no holes, postulates, unsafe
termination pragmas, rewrite-rule dependency, or unsolved-meta options, and
`git diff --check` passed.

Later on 2026-06-26, the canonical group-level exactness statements were split
out of the compatibility exactness module. The new module
`canonical-exactness-homotopy-groups-fiber-sequences` owns the all-index
total-space, canonical fibration-boundary, and canonical
boundary/fiber-inclusion exactness theorems. The public group-level LES
package now imports this canonical theorem provider directly. The older
`exactness-homotopy-groups-fiber-sequences` module re-exports the canonical
module and retains only the direct, recursive, low-dimensional, and
trivial-codomain compatibility wrappers.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/canonical-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
```

All six checks passed.

Later on 2026-06-26, the remaining group-level compatibility wrappers were
split by route. The new module
`direct-exactness-homotopy-groups-fiber-sequences` owns the direct
connecting-map and historical direct-boundary aliases. The new module
`recursive-exactness-homotopy-groups-fiber-sequences` owns the recursive
set-level-to-group wrapper, pointed-homotopy transport, the low-dimensional
boundary/fiber-inclusion statement, and the trivial-codomain fallback. The
older `exactness-homotopy-groups-fiber-sequences` module is now a thin public
facade re-exporting the canonical, direct, and recursive providers.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/recursive-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/direct-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
```

All seven checks passed.

Later on 2026-06-26, the set-truncated iterated exactness compatibility layer
was split by route. The new module
`set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences` owns
the connecting-map route, direct aliases, and reassociation transports from
`Omega^n(Omega X)` to the public shifted indexing. The new module
`set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences`
owns kernel, pointwise-homotopy, and pointed-homotopy transport from canonical
shifted boundary exactness to recursive boundary exactness. The older
`set-truncated-iterated-exactness-homotopy-groups-fiber-sequences` module is
now a thin public facade re-exporting maps, canonical exactness, signed
comparison, direct exactness, and recursive exactness providers.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/set-truncated-direct-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-iterated-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/group-exactness-from-set-truncated-exactness-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/canonical-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/direct-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/recursive-exactness-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-second-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/hopf-long-exact-sequence-third-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
```

All eleven checks passed.

At the time this handoff was written, Agda MCP tools were visible to the agent,
but `./check.sh <file>` remains the acceptance criterion. This file is a status
document only; it does not add or modify Agda proofs.


## 2026-06-27 Public LES Completion Pass

Codex implemented the planned public LES completion pass. The group-level LES record now has one public canonical boundary field, with compatibility aliases for the two adjacent boundary positions. New checked packages were added for abelian exactness, abelian homotopy groups via Eckmann-Hilton, the abelian-range long exact sequence, and the low-degree pointed-set tail.

The checked commands were:

```sh
./check.sh src/group-theory/exact-sequences-abelian-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/pointed-set-tail-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/abelian-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/abelian-long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
```

All six Agda checks passed. `git diff --check` passed, and a touched-file scan found no holes, postulates, unsafe termination pragmas, rewrite-rule dependency, or unsolved-meta options.


## 2026-06-27 Public LES API And Prose Polish Pass

Codex implemented the remaining public API and prose pass over the checked LES packages. The group-level, set-truncated, abelian, and pointed-set tail packages now expose shorter reviewer-facing aliases for the standard maps and exactness positions, while the public prose records the canonical boundary convention and the structural connecting-fiber-sequence proof narrative.

The checked commands were:

```sh
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/abelian-long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/pointed-set-tail-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
```

All five Agda checks passed. `git diff --check` passed, and the touched-file safety scan produced no matches.


## 2026-06-27 Aggressive LES Display And Rename Pass

Codex implemented the aggressive LES cleanup plan. The public LES file names are
pluralized consistently, the old compatibility aliases were removed from the main
packages, and the concise reviewer-facing names are now the actual record field
projections. A reusable generic display record
`Long-Exact-Sequence-Pointed-Set` was added in
`structured-types.long-exact-sequences-pointed-sets`, and the set-truncated LES
package now instantiates it with one looped canonical public boundary map. Agda
accepted the same looped canonical boundary in both adjacent exactness slots, so
no extra boundary-transport lemma was needed.

The checked commands were:

```sh
./check.sh src/structured-types/long-exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/abelian-long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/pointed-set-tail-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md
```

All seven Agda checks passed. `git diff --check` passed, and the touched-file safety scan produced no matches.


## 2026-06-28 Exact-Triple Display Completion Pass

Codex completed the remaining display-layer cleanup for the library-quality LES surface. The pointed-set exactness layer now includes `Exact-Triple-Pointed-Set`, and the generic `Long-Exact-Sequence-Pointed-Set` derives the three adjacent exact triples at every index. The set-truncated fiber-sequence LES re-exposes those three exact triples for its checked instance, so the usual textbook adjacent-triple rendering is available without adding another proof route or a second boundary convention.

The checked commands were:

```sh
./check.sh src/structured-types/exact-sequences-pointed-sets.lagda.md
./check.sh src/structured-types/long-exact-sequences-pointed-sets.lagda.md
./check.sh src/synthetic-homotopy-theory/set-truncated-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/abelian-long-exact-sequences-homotopy-groups-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/pointed-set-tail-long-exact-sequences-fiber-sequences.lagda.md
./check.sh src/synthetic-homotopy-theory/long-exact-sequences-homotopy-groups.lagda.md
./check.sh src/synthetic-homotopy-theory/classifying-fiber-sequences-homotopy-groups.lagda.md
```

All eight Agda checks passed. At this point the local LES code and documentation are library-quality modulo upstream naming, namespace placement, and extraction review.
