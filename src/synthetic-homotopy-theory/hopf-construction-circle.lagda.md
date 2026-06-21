# The Hopf construction on the circle

```agda
module synthetic-homotopy-theory.hopf-construction-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.h-space-structure-circle
open import synthetic-homotopy-theory.hopf-construction
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The [Hopf construction](synthetic-homotopy-theory.hopf-construction.md) applied
to the checked [H-space](structured-types.h-spaces.md) structure on the
`1`-sphere gives a pointed map from the join `S¹ * S¹` to `S²`.

This is the fibration map of the Hopf fiber sequence before replacing the join
total space by `S³`.

## Definitions

### The Hopf construction total space for the 1-sphere

```agda
total-space-hopf-construction-sphere-1 : UU lzero
total-space-hopf-construction-sphere-1 =
  total-space-hopf-construction-H-Space sphere-1-H-Space

pointed-total-space-hopf-construction-sphere-1 : Pointed-Type lzero
pointed-total-space-hopf-construction-sphere-1 =
  pointed-total-space-hopf-construction-H-Space sphere-1-H-Space
```

### The Hopf map from `S¹ * S¹` to `S²`

```agda
hopf-map-sphere-1 : total-space-hopf-construction-sphere-1 → sphere 2
hopf-map-sphere-1 =
  hopf-map-H-Space sphere-1-H-Space

pointed-map-hopf-construction-sphere-1 :
  pointed-total-space-hopf-construction-sphere-1 →∗ sphere-Pointed-Type 2
pointed-map-hopf-construction-sphere-1 =
  pointed-map-hopf-construction-H-Space sphere-1-H-Space
```
