# Long exact sequence of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.long-exact-sequence-homotopy-groups-fiber-sequences where
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

open import synthetic-homotopy-theory.canonical-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homotopy-groups
```

</details>

## Idea

The group-level package records the canonical iterated boundary homomorphism
in both adjacent boundary positions. Internally, the fibration-boundary
exactness proof compares the looped canonical boundary with the fresh shifted
boundary by an all-index signed equivalence, but the signed transport is not
part of the public long exact sequence data.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  record Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence :
    UU (l1 ⊔ l2 ⊔ l3)
    where
    constructor make-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    field
      hom-fiber-inclusion-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Concrete-Group
          ( concrete-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
          ( concrete-homotopy-group
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))
      hom-fibration-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Concrete-Group
          ( concrete-homotopy-group
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))
          ( concrete-homotopy-group
            ( n)
            ( base-fiber-sequence-Pointed-Type S))
      hom-fibration-boundary-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Concrete-Group
          ( concrete-homotopy-group
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))
          ( concrete-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
      hom-boundary-fiber-inclusion-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Concrete-Group
          ( concrete-homotopy-group
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))
          ( concrete-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
      is-exact-fiber-inclusion-fibration-long-exact-sequence-homotopy-groups-fiber-sequence :
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
            ( hom-fiber-inclusion-long-exact-sequence-homotopy-groups-fiber-sequence
              ( n)))
          ( hom-group-hom-Concrete-Group
            ( concrete-homotopy-group
              ( n)
              ( total-space-fiber-sequence-Pointed-Type S))
            ( concrete-homotopy-group
              ( n)
              ( base-fiber-sequence-Pointed-Type S))
            ( hom-fibration-long-exact-sequence-homotopy-groups-fiber-sequence
              ( n)))
      is-exact-fibration-boundary-long-exact-sequence-homotopy-groups-fiber-sequence :
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
            ( hom-fibration-long-exact-sequence-homotopy-groups-fiber-sequence
              ( succ-ℕ n)))
          ( hom-group-hom-Concrete-Group
            ( concrete-homotopy-group
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))
            ( concrete-homotopy-group
              ( n)
              ( fiber-fiber-sequence-Pointed-Type S))
            ( hom-fibration-boundary-long-exact-sequence-homotopy-groups-fiber-sequence
              ( n)))
      is-exact-boundary-fiber-inclusion-long-exact-sequence-homotopy-groups-fiber-sequence :
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
            ( hom-boundary-fiber-inclusion-long-exact-sequence-homotopy-groups-fiber-sequence
              ( n)))
          ( hom-group-hom-Concrete-Group
            ( concrete-homotopy-group
              ( n)
              ( fiber-fiber-sequence-Pointed-Type S))
            ( concrete-homotopy-group
              ( n)
              ( total-space-fiber-sequence-Pointed-Type S))
            ( hom-fiber-inclusion-long-exact-sequence-homotopy-groups-fiber-sequence
              ( n)))

  open Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence public

  long-exact-sequence-homotopy-groups-fiber-sequence :
    Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
  long-exact-sequence-homotopy-groups-fiber-sequence =
    make-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
      ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S)
      ( hom-fibration-concrete-homotopy-group-fiber-sequence S)
      ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence S)
      ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence S)
      ( is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence
        S)
      ( is-exact-hom-canonical-fibration-boundary-concrete-homotopy-group-fiber-sequence
        S)
      ( is-exact-hom-canonical-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence
        S)
```
