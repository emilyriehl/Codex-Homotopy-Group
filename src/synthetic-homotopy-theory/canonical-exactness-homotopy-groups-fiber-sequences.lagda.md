# Canonical exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.canonical-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.group-exactness-from-set-truncated-exactness-fiber-sequences
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **canonical exactness statements** for homotopy groups of a fiber sequence
are the all-index group-level exactness theorems that use the canonical
iterated boundary homomorphism in the boundary positions. The direct and
recursive boundary compatibility wrappers are kept in
[`exactness-homotopy-groups-fiber-sequences`](synthetic-homotopy-theory.exactness-homotopy-groups-fiber-sequences.md).

This module is the theorem provider used by the public group-level long exact
sequence package.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S n))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( base-fiber-sequence-Pointed-Type S))
        ( hom-fibration-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence n =
    is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fiber-sequence
      ( S)
      ( n)
      ( is-exact-set-truncation-iterated-loop-fiber-sequence S n)

  is-exact-hom-canonical-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence S n))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-canonical-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence
    n =
    is-exact-hom-Group-is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
      ( S)
      ( n)
      ( is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
        ( S)
        ( n))

  is-exact-hom-canonical-fibration-boundary-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( hom-fibration-concrete-homotopy-group-fiber-sequence S (succ-ℕ n)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-canonical-fibration-boundary-concrete-homotopy-group-fiber-sequence
    n =
    is-exact-hom-Group-is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence
      ( S)
      ( n)
      ( is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-signed
        ( S)
        ( n))
```
