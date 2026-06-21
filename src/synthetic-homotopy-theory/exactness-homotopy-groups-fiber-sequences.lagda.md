# Group exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-homotopies
open import structured-types.pointed-sets

open import synthetic-homotopy-theory.group-exactness-from-set-truncated-homotopy-group-exactness
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The current long-exact-sequence development proves adjacent exactness for
set-truncated pointed sets. To extract Hopf-fibration isomorphisms, those
adjacent exactness statements must be compared with exactness of the ordinary
groups underlying concrete homotopy groups.

The tempting route through fiber sequences of concrete-group classifying maps
is too strong in general: such a fiber sequence would impose short-exact-style
conditions, while the homotopy long exact sequence only gives adjacent
exactness, with the next boundary map measuring the cokernel.

This file records the group-level exactness statements for the two adjacent
triples needed by the Hopf comparison.

## Theorems

### Exactness at the total-space homotopy group

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
```

### Exactness at the fiber homotopy group after the boundary

```agda
  is-exact-hom-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence :
    is-exact-hom-Group
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( 1)
          ( base-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( 0)
          ( fiber-fiber-sequence-Pointed-Type S)))
      ( group-Concrete-Group
        ( concrete-homotopy-group
          ( 0)
          ( total-space-fiber-sequence-Pointed-Type S)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( 1)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( 0)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S 0))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( 0)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( 0)
          ( total-space-fiber-sequence-Pointed-Type S))
        ( hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence S 0))
  is-exact-hom-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
      ( Ω (base-fiber-sequence-Pointed-Type S))
      ( fiber-fiber-sequence-Pointed-Type S)
      ( total-space-fiber-sequence-Pointed-Type S)
      ( boundary-pointed-map-fiber-sequence S)
      ( fiber-inclusion-fiber-sequence-Pointed-Type S)
      ( is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence S)
```

### Exactness at the base homotopy group from recursive set-level exactness

```agda
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S (succ-ℕ n))
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n) →
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
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence n =
    is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence
      ( S)
      ( n)

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
    is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence
      ( 1)
      ( is-exact-set-truncation-second-iterated-loop-fibration-boundary-fiber-sequence-direct
        ( S))

  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-pointed-htpy :
    (n : ℕ) →
    ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)) ~∗
    ( boundary-pointed-map-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))) →
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
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-pointed-htpy
    n H =
    is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence
      ( n)
      ( is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-pointed-htpy
        ( S)
        ( n)
        ( H))
```

### Exactness at the base homotopy group with trivial target

```agda
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-is-trivial-codomain :
    (n : ℕ) →
    is-contr
      ( type-Group
        ( group-Concrete-Group
          ( concrete-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S)))) →
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
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-fibration-boundary-concrete-homotopy-group-fiber-sequence-is-trivial-codomain
    n is-trivial-target =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type-is-trivial-codomain
      ( iterated-loop-space
        ( succ-ℕ n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( succ-ℕ n)
        ( fibration-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-boundary-fiber-sequence S n)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S n))
      ( is-trivial-target)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        ( S)
        ( n))
```
