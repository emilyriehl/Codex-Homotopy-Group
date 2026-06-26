# The Hopf long exact sequence and second homotopy groups

```agda
module synthetic-homotopy-theory.hopf-long-exact-sequence-second-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.isomorphisms-from-exact-sequences-groups
open import group-theory.isomorphisms-groups
open import group-theory.trivial-underlying-groups-concrete-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.pointed-homotopies

open import synthetic-homotopy-theory.exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups-sphere-3
open import synthetic-homotopy-theory.hopf-fiber-sequence
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The Hopf fiber sequence `S¹ → S³ → S²` gives an exact segment

```text
π₂(S³) → π₂(S²) → π₁(S¹) → π₁(S³).
```

Since the two outer groups are trivial, exactness identifies the boundary
homomorphism `π₂(S²) → π₁(S¹)` as an isomorphism.

## Theorems

### Exactness of the boundary/fiber-inclusion segment

```agda
is-exact-second-homotopy-hopf-boundary-fiber-inclusion :
  is-exact-hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 3)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2))
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
      ( boundary-hom-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 0)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 3))
      ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 0)))
is-exact-second-homotopy-hopf-boundary-fiber-inclusion =
  is-exact-hom-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence
    ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
```

### Exactness of the lower Hopf segment identifies `π₂(S²)` and `π₁(S¹)`

```agda
iso-second-homotopy-group-is-exact-hopf-segment :
  is-exact-hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 3))
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2))
      ( hom-fibration-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 1)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2))
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
      ( boundary-hom-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 0))) →
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
iso-second-homotopy-group-is-exact-hopf-segment H1 =
  ( hom-group-hom-Concrete-Group
    ( concrete-homotopy-group 1 (sphere-Pointed-Type 2))
    ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
    ( boundary-hom-concrete-homotopy-group-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 0)) ,
    is-iso-is-exact-is-trivial-outer-groups
      ( group-Concrete-Group
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 3)))
      ( group-Concrete-Group
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
      ( group-Concrete-Group
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
      ( group-Concrete-Group
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 3)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 3))
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 2))
        ( hom-fibration-concrete-homotopy-group-fiber-sequence
          ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
          ( 1)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 2))
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence
          ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
          ( 0)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 3))
        ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence
          ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
          ( 0)))
      ( is-trivial-group-is-trivial-Concrete-Group
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 3))
        ( is-trivial-concrete-homotopy-group-one-sphere-3))
      ( is-trivial-group-is-trivial-Concrete-Group
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 3))
        ( is-trivial-concrete-homotopy-group-zero-sphere-3))
      ( H1)
      ( is-exact-second-homotopy-hopf-boundary-fiber-inclusion))
```

### The recursive set-level exactness input for the lower Hopf segment

```agda
is-exact-set-truncation-second-homotopy-hopf-fibration-boundary :
  is-exact-hom-Pointed-Set
    ( trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space 1 (sphere-Pointed-Type 3))))
    ( trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space 1 (sphere-Pointed-Type 2))))
    ( trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space 0 (sphere-Pointed-Type 1))))
    ( hom-trunc-iterated-loop-fibration-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 1))
    ( hom-trunc-iterated-loop-boundary-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 0))
is-exact-set-truncation-second-homotopy-hopf-fibration-boundary =
  is-exact-set-truncation-loop-fiber-sequence
    ( fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))
```

### The lower Hopf comparison from recursive set-level exactness

```agda
iso-second-homotopy-group-is-exact-set-truncation-hopf-segment :
  is-exact-hom-Pointed-Set
    ( trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space 1 (sphere-Pointed-Type 3))))
    ( trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space 1 (sphere-Pointed-Type 2))))
    ( trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space 0 (sphere-Pointed-Type 1))))
    ( hom-trunc-iterated-loop-fibration-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 1))
    ( hom-trunc-iterated-loop-boundary-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 0)) →
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
iso-second-homotopy-group-is-exact-set-truncation-hopf-segment H =
  iso-second-homotopy-group-is-exact-hopf-segment
    ( is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 0)
      ( H))
```

### The lower Hopf comparison from a pointed boundary homotopy

```agda
iso-second-homotopy-group-pointed-htpy-hopf-segment :
  ( pointed-map-Ω
    ( pointed-map-iterated-boundary-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 0))) ~∗
  ( boundary-pointed-map-fiber-sequence
    ( iterated-loop-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( succ-ℕ 0))) →
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
iso-second-homotopy-group-pointed-htpy-hopf-segment H =
  iso-second-homotopy-group-is-exact-hopf-segment
    ( is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-pointed-htpy
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 0)
      ( H))
```
