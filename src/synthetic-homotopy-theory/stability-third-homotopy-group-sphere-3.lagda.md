# Stability for the third homotopy group of the 3-sphere

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.stability-third-homotopy-group-sphere-3 where
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

Freudenthal suspension and stability for spheres identify the second homotopy
group of `S²` with the third homotopy group of `S³`.

## Theorem

### The stable suspension comparison from `π₂(S²)` to `π₃(S³)`

```agda
iso-suspension-second-third-homotopy-group-sphere-2-sphere-3 :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 1 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
iso-suspension-second-third-homotopy-group-sphere-2-sphere-3 = {!!}
```
