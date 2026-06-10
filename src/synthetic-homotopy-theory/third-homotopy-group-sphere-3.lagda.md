# The third homotopy group of the 3-sphere

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.third-homotopy-group-sphere-3 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.natural-numbers

open import group-theory.concrete-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

This file is an intentional theorem stub. The `--allow-unsolved-metas` option
marks the proof below as unfinished so that the top-level assembly file can
import and compose the stated result while lower-level proofs are developed.

The diagonal computation of the [homotopy groups of
spheres](synthetic-homotopy-theory.spheres.md) gives `πₙ(Sⁿ) ≅ ℤ`. At `n = 3`,
this identifies the third homotopy group of `S³` with the additive group of
integers.

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
iso-third-homotopy-group-sphere-3-ℤ = {!!}
```
