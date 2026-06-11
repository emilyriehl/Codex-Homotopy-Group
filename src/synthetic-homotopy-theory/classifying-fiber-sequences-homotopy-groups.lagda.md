# Classifying fiber sequences of homotopy groups of fiber sequences

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.classifying-fiber-sequences-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
```

</details>

## Idea

The concrete homotopy group `π(n+1) X` is represented as the concrete group of
the pointed type `Ωⁿ X`. Therefore exactness of the homotopy-group maps can be
deduced from the stronger statement that the corresponding classifying pointed
maps of concrete groups form fiber sequences.

This file records those stronger HoTT-book fiber-sequence obligations. They are
the homotopical bridge needed before the existing concrete-group theorem
`is-exact-is-fiber-sequence-hom-Concrete-Group` can be applied.

## Theorems

### The fiber-inclusion/fibration classifying sequence

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-fiber-sequence-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    is-fiber-sequence-Pointed-Type
      ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S n)
      ( hom-fibration-concrete-homotopy-group-fiber-sequence S n)
  is-fiber-sequence-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence =
    {!!}
```

### The fibration/boundary classifying sequence

```agda
  is-fiber-sequence-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    is-fiber-sequence-Pointed-Type
      ( hom-fibration-concrete-homotopy-group-fiber-sequence S (succ-ℕ n))
      ( boundary-hom-concrete-homotopy-group-fiber-sequence S n)
  is-fiber-sequence-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence =
    {!!}
```
