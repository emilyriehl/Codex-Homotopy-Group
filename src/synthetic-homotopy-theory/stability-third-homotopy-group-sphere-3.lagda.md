# Stability for the third homotopy group of the 3-sphere

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.stability-third-homotopy-group-sphere-3 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.freudenthal-suspension-theorem
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups-sphere-3
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.stabilization-homotopy-groups
```

</details>

## Idea

Freudenthal suspension and stability for spheres identify the second homotopy
group of `S²` with the third homotopy group of `S³`.

## Definitions

### The special connected-map consequence of Freudenthal for `S²`

```agda
is-connected-map-Freudenthal-suspension-sphere-2 :
  is-connected-map-Freudenthal-suspension 0 (sphere-Pointed-Type 2) →
  is-connected-map
    ( truncation-level-ℕ 2)
    ( map-Freudenthal-suspension (sphere-Pointed-Type 2))
is-connected-map-Freudenthal-suspension-sphere-2 H =
  H is-1-connected-sphere-2
```

### The canonical stabilization homomorphism from `π₂(S²)` to `π₃(S³)`

```agda
hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3 :
  hom-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3 =
  hom-group-stabilization-concrete-homotopy-group 1 (sphere-Pointed-Type 2)

is-iso-hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3 :
  is-iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3)
is-iso-hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3 =
  {!!}
```

## Theorem

### The stable suspension comparison from `π₂(S²)` to `π₃(S³)`

```agda
iso-suspension-second-third-homotopy-group-sphere-2-sphere-3 :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
iso-suspension-second-third-homotopy-group-sphere-2-sphere-3 =
  pair
    ( hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3)
    ( is-iso-hom-group-suspension-second-third-homotopy-group-sphere-2-sphere-3)
```
