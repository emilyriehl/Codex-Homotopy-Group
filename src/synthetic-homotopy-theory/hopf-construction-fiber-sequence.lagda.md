# The canonical fiber sequence of the Hopf construction

```agda
module synthetic-homotopy-theory.hopf-construction-fiber-sequence where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.h-spaces
open import structured-types.pointed-types

open import synthetic-homotopy-theory.h-space-structure-circle
open import synthetic-homotopy-theory.hopf-construction
open import synthetic-homotopy-theory.hopf-construction-circle
open import synthetic-homotopy-theory.join-powers-of-types
open import synthetic-homotopy-theory.joins-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [Hopf construction](synthetic-homotopy-theory.hopf-construction.md) of an
H-space `A` gives a pointed map

```text
A * A →∗ suspension A.
```

Every pointed map has a canonical fiber sequence whose fiber is its pointed
fiber. This file records that canonical fiber sequence for the Hopf
construction. The geometric Hopf fibration `S¹ → S³ → S²` is obtained from this
source by identifying the Hopf-construction fiber with `S¹` and the total space
`S¹ * S¹` with `S³`.

## Definition

### The canonical fiber sequence of the Hopf construction

```agda
module _
  {l : Level} (A : H-Space l)
  where

  fiber-hopf-construction-H-Space : Pointed-Type l
  fiber-hopf-construction-H-Space =
    fiber-Pointed-Type (pointed-map-hopf-construction-H-Space A)

  fiber-sequence-hopf-construction-H-Space :
    fiber-sequence-Pointed-Type l l l
  fiber-sequence-hopf-construction-H-Space =
    fiber-sequence-fiber-Pointed-Type
      ( pointed-map-hopf-construction-H-Space A)
```

### The canonical fiber sequence of the Hopf construction on the 1-sphere

```agda
fiber-hopf-construction-sphere-1 : Pointed-Type lzero
fiber-hopf-construction-sphere-1 =
  fiber-hopf-construction-H-Space sphere-1-H-Space

fiber-sequence-hopf-construction-sphere-1 :
  fiber-sequence-Pointed-Type lzero lzero lzero
fiber-sequence-hopf-construction-sphere-1 =
  fiber-sequence-hopf-construction-H-Space sphere-1-H-Space
```

### The total-space comparison with the join-power model

```agda
equiv-total-space-fiber-sequence-hopf-construction-sphere-1-join-power-Fin-2 :
  type-Pointed-Type
    ( total-space-fiber-sequence-Pointed-Type
      fiber-sequence-hopf-construction-sphere-1) ≃
  join-power 2 (Fin 2) * join-power 2 (Fin 2)
equiv-total-space-fiber-sequence-hopf-construction-sphere-1-join-power-Fin-2 =
  equiv-total-space-hopf-construction-sphere-1-join-power-Fin-2
```
