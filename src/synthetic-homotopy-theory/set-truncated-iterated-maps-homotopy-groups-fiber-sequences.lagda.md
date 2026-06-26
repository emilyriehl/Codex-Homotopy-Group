# Set-truncated iterated maps of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.set-truncations
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **set-truncated iterated maps of the long exact sequence** are the
pointed-set homomorphisms obtained by applying set truncation to looped and
iterated-looped maps in a fiber sequence. This module contains only the maps,
leaving exactness proofs and comparison transports to separate modules.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( fiber-inclusion-fiber-sequence-Pointed-Type S)))

  hom-trunc-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-iterated-loop-fibration-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( fibration-fiber-sequence-Pointed-Type S)))

  hom-trunc-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-iterated-loop-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n))

  hom-trunc-canonical-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( canonical-pointed-map-iterated-loop-boundary-fiber-sequence S n)

  hom-trunc-loop-canonical-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-loop-canonical-iterated-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( loop-canonical-pointed-map-iterated-boundary-fiber-sequence S n)

  hom-trunc-direct-iterated-loop-fibration-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (total-space-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
  hom-trunc-direct-iterated-loop-fibration-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))))

  hom-trunc-direct-iterated-loop-boundary-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
  hom-trunc-direct-iterated-loop-boundary-fiber-sequence n =
    hom-trunc-Pointed-Set
      ( pointed-map-Ω
        ( pointed-map-iterated-loop-space
          ( n)
          ( boundary-pointed-map-fiber-sequence S)))

  hom-trunc-iterated-loop-connecting-fibration-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (total-space-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
  hom-trunc-iterated-loop-connecting-fibration-fiber-sequence =
    hom-trunc-direct-iterated-loop-fibration-fiber-sequence

  hom-trunc-iterated-loop-connecting-map-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( Ω (base-fiber-sequence-Pointed-Type S)))))
      ( trunc-Pointed-Set
        ( Ω
          ( iterated-loop-space
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))))
  hom-trunc-iterated-loop-connecting-map-fiber-sequence =
    hom-trunc-direct-iterated-loop-boundary-fiber-sequence

  hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
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
  hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
    n =
    hom-trunc-loop-boundary-fiber-sequence-Pointed-Type
      ( iterated-loop-fiber-sequence S n)
```
