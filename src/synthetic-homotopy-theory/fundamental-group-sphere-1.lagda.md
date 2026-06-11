# The fundamental group of the 1-sphere

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.fundamental-group-sphere-1 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.natural-numbers

open import group-theory.concrete-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups-circle
open import synthetic-homotopy-theory.spheres
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
iso-fundamental-group-sphere-1-ℤ = {!!}
```
