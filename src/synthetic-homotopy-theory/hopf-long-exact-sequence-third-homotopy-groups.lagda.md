# The Hopf long exact sequence and third homotopy groups

```agda
module synthetic-homotopy-theory.hopf-long-exact-sequence-third-homotopy-groups where
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
open import group-theory.trivial-groups
open import group-theory.trivial-underlying-groups-concrete-groups

open import synthetic-homotopy-theory.exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups-circle
open import synthetic-homotopy-theory.hopf-fiber-sequence
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The Hopf fiber sequence `S¹ → S³ → S²` gives an exact segment

```text
π₃(S¹) → π₃(S³) → π₃(S²) → π₂(S¹).
```

Since the two outer groups are trivial, the middle homomorphism is an
isomorphism.

## Definitions

### The two exact Hopf segments

```agda
is-exact-third-homotopy-hopf-fiber-inclusion-fibration :
  is-exact-hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( hom-fibration-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
is-exact-third-homotopy-hopf-fiber-inclusion-fibration =
  is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence
    ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
    ( 2)

is-exact-third-homotopy-hopf-fibration-boundary :
  is-exact-hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( hom-fibration-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1))
      ( boundary-hom-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 1)))
is-exact-third-homotopy-hopf-fibration-boundary =
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-second-direct
    ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
```

## Theorem

### Exactness of the Hopf segment identifies `π₃(S³)` and `π₃(S²)`

```agda
iso-third-homotopy-group-is-exact-hopf-segment :
  is-exact-hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( hom-fibration-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2))) →
  is-exact-hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( hom-fibration-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1))
      ( boundary-hom-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 1))) →
  is-trivial-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1))) →
  is-trivial-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1))) →
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
pr1 (iso-third-homotopy-group-is-exact-hopf-segment H1 H2 T1 T2) =
  hom-group-hom-Concrete-Group
    ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
    ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
    ( hom-fibration-concrete-homotopy-group-fiber-sequence
      ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
      ( 2))
pr2 (iso-third-homotopy-group-is-exact-hopf-segment H1 H2 T1 T2) =
  is-iso-is-exact-is-trivial-outer-groups
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3))
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( hom-fibration-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 2)))
    ( hom-group-hom-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2))
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1))
      ( boundary-hom-concrete-homotopy-group-fiber-sequence
        ( hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)
        ( 1)))
    ( T1)
    ( T2)
    ( H1)
    ( H2)

iso-third-homotopy-group-hopf-fiber-sequence :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
iso-third-homotopy-group-hopf-fiber-sequence =
  iso-third-homotopy-group-is-exact-hopf-segment
    ( is-exact-third-homotopy-hopf-fiber-inclusion-fibration)
    ( is-exact-third-homotopy-hopf-fibration-boundary)
    ( is-trivial-group-is-trivial-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 1))
      ( is-trivial-positive-concrete-homotopy-group-sphere-1 1))
    ( is-trivial-group-is-trivial-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 1))
      ( is-trivial-positive-concrete-homotopy-group-sphere-1 0))
```
