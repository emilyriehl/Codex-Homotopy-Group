# Diagonal homotopy groups of spheres

```agda
module synthetic-homotopy-theory.diagonal-homotopy-groups-spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.isomorphisms-groups

open import synthetic-homotopy-theory.fundamental-group-sphere-1
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.second-homotopy-group-sphere-2
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.stability-diagonal-homotopy-groups-spheres
```

</details>

## Idea

The positive diagonal homotopy groups of spheres are computed from the base
calculation `π₁(S¹) ≅ ℤ`, the Hopf-fibration calculation `π₂(S²) ≅ π₁(S¹)`,
and the Freudenthal stabilization isomorphisms on the diagonal.

In the current indexing convention for
[`concrete-homotopy-group`](synthetic-homotopy-theory.homotopy-groups.md), the
index `n` denotes the ordinary `(n+1)`-st homotopy group. Thus the theorem below
computes the ordinary groups `πₙ₊₁(Sⁿ⁺¹)`.

## Definitions

### The diagonal concrete homotopy groups of spheres

```agda
diagonal-homotopy-group-sphere-succ : ℕ → Group lzero
diagonal-homotopy-group-sphere-succ n =
  group-Concrete-Group
    ( concrete-homotopy-group n (sphere-Pointed-Type (succ-ℕ n)))

diagonal-homotopy-group-sphere-succ-succ : ℕ → Group lzero
diagonal-homotopy-group-sphere-succ-succ n =
  group-Concrete-Group
    ( concrete-homotopy-group
      ( succ-ℕ n)
      ( sphere-Pointed-Type (succ-ℕ (succ-ℕ n))))
```

## Theorem

### The second homotopy group of `S²` is the integers

```agda
iso-second-homotopy-group-sphere-2-ℤ :
  iso-Group (diagonal-homotopy-group-sphere-succ-succ zero-ℕ) ℤ-Group
iso-second-homotopy-group-sphere-2-ℤ =
  comp-iso-Group
    ( diagonal-homotopy-group-sphere-succ-succ zero-ℕ)
    ( diagonal-homotopy-group-sphere-succ zero-ℕ)
    ( ℤ-Group)
    ( iso-fundamental-group-sphere-1-ℤ)
    ( iso-second-homotopy-group-sphere-2-fundamental-group-sphere-1)
```

### The diagonal homotopy groups of spheres are the integers

```agda
iso-diagonal-homotopy-group-sphere-succ-succ-ℤ :
  (n : ℕ) → iso-Group (diagonal-homotopy-group-sphere-succ-succ n) ℤ-Group
iso-diagonal-homotopy-group-sphere-succ-succ-ℤ zero-ℕ =
  iso-second-homotopy-group-sphere-2-ℤ
iso-diagonal-homotopy-group-sphere-succ-succ-ℤ (succ-ℕ n) =
  comp-iso-Group
    ( diagonal-homotopy-group-sphere-succ-succ (succ-ℕ n))
    ( diagonal-homotopy-group-sphere-succ-succ n)
    ( ℤ-Group)
    ( iso-diagonal-homotopy-group-sphere-succ-succ-ℤ n)
    ( inv-iso-Group
      ( diagonal-homotopy-group-sphere-succ-succ n)
      ( diagonal-homotopy-group-sphere-succ-succ (succ-ℕ n))
      ( iso-stabilization-diagonal-homotopy-group-sphere-succ-succ n))

iso-diagonal-homotopy-group-sphere-succ-ℤ :
  (n : ℕ) → iso-Group (diagonal-homotopy-group-sphere-succ n) ℤ-Group
iso-diagonal-homotopy-group-sphere-succ-ℤ zero-ℕ =
  iso-fundamental-group-sphere-1-ℤ
iso-diagonal-homotopy-group-sphere-succ-ℤ (succ-ℕ n) =
  iso-diagonal-homotopy-group-sphere-succ-succ-ℤ n
```
