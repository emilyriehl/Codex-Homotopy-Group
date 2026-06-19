# The second homotopy group of the 2-sphere

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.second-homotopy-group-sphere-2 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import group-theory.concrete-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.hopf-long-exact-sequence-second-homotopy-groups
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The Hopf fibration and the long exact sequence identify the second homotopy
group of `S²` with the fundamental group of `S¹`.

## Theorem

### The second homotopy group of `S²` is the fundamental group of `S¹`

```agda
iso-second-homotopy-group-sphere-2-fundamental-group-sphere-1 :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)))
iso-second-homotopy-group-sphere-2-fundamental-group-sphere-1 =
  iso-second-homotopy-group-is-exact-set-truncation-hopf-segment
    ( {!!})
```
