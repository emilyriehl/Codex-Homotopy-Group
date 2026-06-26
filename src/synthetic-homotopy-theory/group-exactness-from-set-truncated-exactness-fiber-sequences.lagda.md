# Group exactness from set-truncated exactness of fiber sequences

```agda
module synthetic-homotopy-theory.group-exactness-from-set-truncated-exactness-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homomorphisms-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-maps
open import structured-types.pointed-sets

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.group-exactness-from-set-truncated-homotopy-group-exactness
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups
open import synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups
```

</details>

## Idea

The generic bridge from pointed-set exactness to ordinary group exactness is
defined in
[`group-exactness-from-set-truncated-homotopy-group-exactness`](synthetic-homotopy-theory.group-exactness-from-set-truncated-homotopy-group-exactness.md).
This file specializes that bridge to the set-truncated adjacent triples in the
long exact sequence of a fiber sequence.

Keeping these fiber-sequence-specific adapters separate makes the generic
transport theorem reusable while hiding the comparison maps, unit coherences,
and signed boundary transports from the public long exact sequence package.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( base-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S n) →
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
  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fiber-sequence n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( n)
        ( fiber-inclusion-fiber-sequence-Pointed-Type S))
      ( pointed-map-iterated-loop-space
        ( n)
        ( fibration-fiber-sequence-Pointed-Type S))

  is-exact-hom-Group-is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
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
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
        ( S)
        ( n))
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S n) →
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
  is-exact-hom-Group-is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
    n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
      ( iterated-loop-space
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( iterated-loop-space
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( canonical-pointed-map-iterated-boundary-fiber-sequence S n)
      ( pointed-map-iterated-loop-space
        ( n)
        ( fiber-inclusion-fiber-sequence-Pointed-Type S))

  coherence-square-canonical-boundary-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) → UU (l1 ⊔ l3)
  coherence-square-canonical-boundary-concrete-homotopy-group-fiber-sequence n =
    (x :
      type-Group
        ( group-Concrete-Group
          ( concrete-homotopy-group
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S)))) →
    map-underlying-type-concrete-group-Pointed-Type
      ( iterated-loop-space
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( map-hom-Group
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
            ( base-fiber-sequence-Pointed-Type S))
          ( concrete-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
          ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence
            S
            n))
        ( x)) ＝
    map-pointed-map
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( map-underlying-type-concrete-group-Pointed-Type
        ( iterated-loop-space
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( x))

  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence :
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
        ( hom-fibration-concrete-homotopy-group-fiber-sequence S (succ-ℕ n)))
      ( hom-group-hom-Concrete-Group
        ( concrete-homotopy-group
          ( succ-ℕ n)
          ( base-fiber-sequence-Pointed-Type S))
        ( concrete-homotopy-group
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S))
        ( boundary-hom-concrete-homotopy-group-fiber-sequence S n))
  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
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

  is-exact-hom-Group-is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence :
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
      ( hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S n) →
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
  is-exact-hom-Group-is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence n =
    is-exact-hom-Group-is-exact-loop-truncation-hom-Pointed-Type
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
      ( canonical-pointed-map-iterated-boundary-fiber-sequence S n)

```
