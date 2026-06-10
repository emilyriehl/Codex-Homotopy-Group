# The third homotopy group of the 2-sphere

```agda
module synthetic-homotopy-theory.third-homotopy-group-sphere-2 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.natural-numbers

open import group-theory.concrete-groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.hopf-fibration-third-homotopy-groups
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.third-homotopy-group-sphere-3
```

</details>

## Idea

The third [homotopy group](synthetic-homotopy-theory.homotopy-groups.md) of
the [2-sphere](synthetic-homotopy-theory.spheres.md) is computed by combining
the Hopf fibration `S¹ → S³ → S²`, the long exact sequence of homotopy groups,
the vanishing of the higher homotopy groups of `S¹`, and the diagonal
calculation `πₙ(Sⁿ) ≅ ℤ`.

The proof composes the inverse of the Hopf-fibration comparison
`π₃(S³) ≅ π₃(S²)` with the diagonal computation `π₃(S³) ≅ ℤ`.

In the current indexing convention for
[`concrete-homotopy-group`](synthetic-homotopy-theory.homotopy-groups.md),
the index `2` denotes the ordinary third homotopy group.

## Theorem

### The third homotopy group of the 2-sphere is the integers

```agda
iso-third-homotopy-group-sphere-2-ℤ :
  iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( ℤ-Group)
iso-third-homotopy-group-sphere-2-ℤ =
  comp-iso-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
    ( group-Concrete-Group
      ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
    ( ℤ-Group)
    ( iso-third-homotopy-group-sphere-3-ℤ)
    ( inv-iso-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group 2 (sphere-Pointed-Type 3)))
      ( group-Concrete-Group
        ( concrete-homotopy-group 2 (sphere-Pointed-Type 2)))
      ( iso-third-homotopy-group-sphere-3-sphere-2))
```
