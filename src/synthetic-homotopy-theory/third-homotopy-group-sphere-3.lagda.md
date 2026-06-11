# The third homotopy group of the 3-sphere

```agda
module synthetic-homotopy-theory.third-homotopy-group-sphere-3 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.natural-numbers

open import group-theory.concrete-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.fundamental-group-sphere-1
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.second-homotopy-group-sphere-2
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.stability-third-homotopy-group-sphere-3
```

</details>

## Idea

The diagonal computation of the [homotopy groups of
spheres](synthetic-homotopy-theory.spheres.md) gives `πₙ(Sⁿ) ≅ ℤ`. At `n = 3`,
this identifies the third homotopy group of `S³` with the additive group of
integers.

This file now delegates the calculation to the next layer: stability identifies
`π₂(S²)` with `π₃(S³)`, the Hopf fibration identifies `π₂(S²)` with `π₁(S¹)`,
and the loop-space computation of the circle identifies `π₁(S¹)` with `ℤ`.

In the current indexing convention for
[`concrete-homotopy-group`](synthetic-homotopy-theory.homotopy-groups.md),
the index `2` denotes the ordinary third homotopy group.

## Theorem

### The third homotopy group of the 3-sphere is the integers

```agda
iso-third-homotopy-group-sphere-3-ℤ :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( ℤ-Group)
iso-third-homotopy-group-sphere-3-ℤ =
  comp-iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
    ( ℤ-Group)
    ( iso-fundamental-group-sphere-1-ℤ)
    ( comp-iso-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
      ( group-Concrete-Group
        ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
      ( group-Concrete-Group
        ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
      ( iso-second-homotopy-group-sphere-2-fundamental-group-sphere-1)
      ( inv-iso-Group
        ( group-Concrete-Group
          ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
        ( group-Concrete-Group
          ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
        ( iso-suspension-second-third-homotopy-group-sphere-2-sphere-3)))
```
