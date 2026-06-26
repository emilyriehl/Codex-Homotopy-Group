# Direct exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.direct-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.recursive-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

This module contains the direct connecting-map route to group-level exactness
at the base homotopy group of a fiber sequence. It is separated from the
recursive bridge so downstream files can distinguish whether a theorem is a
direct shifted exactness result or a compatibility wrapper around a supplied
set-truncated proof.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-hom-fibration-connecting-map-concrete-homotopy-group-fiber-sequence :
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
        ( hom-fibration-concrete-homotopy-group-fiber-sequence
          S
          ( succ-ℕ n)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-fibration-connecting-map-concrete-homotopy-group-fiber-sequence n =
    is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence
      ( S)
      ( n)
      ( is-exact-set-truncation-iterated-loop-fibration-connecting-map-fiber-sequence
        ( S)
        ( n))

  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-direct :
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
        ( hom-fibration-concrete-homotopy-group-fiber-sequence
          S
          ( succ-ℕ n)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-direct =
    is-exact-hom-fibration-connecting-map-concrete-homotopy-group-fiber-sequence

  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-second-direct :
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( 2)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( 2)
          ( base-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( 1)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( 2)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( 2)
          ( base-fiber-sequence-Pointed-Type S))
        ( hom-fibration-concrete-homotopy-group-fiber-sequence S 2))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( 2)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( 1)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S 1))
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-second-direct =
    is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-direct
      ( 1)
```
