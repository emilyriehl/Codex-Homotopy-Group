# Long exact sequences of homotopy groups

```agda
module synthetic-homotopy-theory.long-exact-sequence-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import synthetic-homotopy-theory.abelian-homotopy-groups
open import synthetic-homotopy-theory.abelian-long-exact-sequence-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences
```

</details>

## Idea

A [fiber sequence](structured-types.fiber-sequences.md)

```text
  F →∗ E →∗ B
```

has induced homomorphisms on homotopy groups. The remaining extra datum needed
to state the long exact sequence is the family of boundary homomorphisms

```text
  π(n+2) B → π(n+1) F.
```

In the indexing convention of
[homotopy groups](synthetic-homotopy-theory.homotopy-groups.md),
`concrete-homotopy-group n` denotes `π(n+1)`.

The public group-level boundary convention is the canonical iterated boundary
homomorphism. The shifted sequence `Ω E →∗ Ω B →∗ F` is provided structurally by
the connecting fiber sequence module. The public proof route first constructs
connecting and iterated-loop fiber sequences, proves set-truncated exactness for
the resulting standard segments, and then transports those exactness statements
to concrete homotopy-group exactness. Recursive boundary maps, direct shifted
boundary adapters, signed comparisons, and image/kernel transports remain
separate theorem-provider machinery rather than the headline LES API.

The public surface now has three checked package layers: the concrete group-level
long exact sequence, the abelian long exact sequence in dimensions `2` and
higher, and the low-degree pointed-set tail
`||ΩE||₀ -> ||ΩB||₀ -> ||F||₀ -> ||E||₀ -> ||B||₀`. These
packages expose shorter `hom-...-long-exact-sequence` and
`exact-at-...-long-exact-sequence` aliases for the standard arrows and
exactness terms while keeping the underlying checked record fields available.

## Definitions

### Iterated loop fiber sequences of a fiber sequence

Iterated loop fiber sequences are defined in
[`iterated-loop-fiber-sequences`](synthetic-homotopy-theory.iterated-loop-fiber-sequences.md).

### Iterated boundary maps of fiber sequences

Recursive and canonical iterated boundary maps, together with their direct
shifted boundary fiber sequence, are defined in
[`iterated-boundary-maps-fiber-sequences`](synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences.md).

### Homomorphisms induced by fiber sequences

The homomorphisms on concrete homotopy groups induced by the fiber inclusion,
fibration, and boundary maps of a fiber sequence are defined in
[`homomorphisms-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences.md).

### Set-truncated canonical long exact sequence

The set-truncated canonical long exact sequence package is defined in
[`set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences.md).

### Group-level long exact sequence

The group-level long exact sequence package is defined in
[`long-exact-sequence-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.long-exact-sequence-homotopy-groups-fiber-sequences.md).

### Abelian homotopy groups and abelian long exact sequence

The higher homotopy groups are packaged as abelian groups in
[`abelian-homotopy-groups`](synthetic-homotopy-theory.abelian-homotopy-groups.md).
The abelian-range long exact sequence package is defined in
[`abelian-long-exact-sequence-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.abelian-long-exact-sequence-homotopy-groups-fiber-sequences.md).

### Pointed-set tail

The low-degree pointed-set tail is defined in
[`pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.pointed-set-tail-long-exact-sequence-homotopy-groups-fiber-sequences.md).

## Properties

The set-truncated exactness statements for canonical, packaged, boundary, and
looped boundary fiber-sequence segments are defined in
[`set-truncated-exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences.md).
