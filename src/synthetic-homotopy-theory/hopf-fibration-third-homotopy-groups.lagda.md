# The Hopf fibration and the third homotopy groups of spheres

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.hopf-fibration-third-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
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

The Hopf fibration has fiber `S¹`, total space `S³`, and base `S²`. The long
exact sequence of homotopy groups, together with the vanishing of the higher
homotopy groups of `S¹`, identifies the third homotopy group of `S³` with the
third homotopy group of `S²`.

## Theorem

### The Hopf fibration identifies the third homotopy groups of `S³` and `S²`

```agda
iso-third-homotopy-group-sphere-3-sphere-2 :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
iso-third-homotopy-group-sphere-3-sphere-2 = {!!}
```
