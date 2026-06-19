# The fundamental group of the 1-sphere

```agda
module synthetic-homotopy-theory.fundamental-group-sphere-1 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types

open import group-theory.concrete-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups-circle
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.underlying-type-fundamental-group-sphere-1
```

</details>

## Idea

The loop space of the 1-sphere is equivalent to the integers. This file records
the group-level packaging of that calculation as an isomorphism from the
fundamental group of `S¹` to the additive group of integers.

## Theorem

### The fundamental group of `S¹` is the integers

```agda
iso-fundamental-group-sphere-1-ℤ :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
    ( ℤ-Group)
iso-fundamental-group-sphere-1-ℤ =
  iso-equiv-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
    ( ℤ-Group)
    ( pair
      ( equiv-type-fundamental-group-sphere-1-ℤ)
      ( λ {x} {y} →
        ( ap
          ( map-equiv compute-loop-space-sphere-1)
          ( preserves-mul-equiv-type-fundamental-group-sphere-1-loop-space
            ( x)
            ( y))) ∙
        ( preserves-mul-compute-loop-space-sphere-1
          ( map-equiv equiv-type-fundamental-group-sphere-1-loop-space x)
          ( map-equiv equiv-type-fundamental-group-sphere-1-loop-space y))))
```
