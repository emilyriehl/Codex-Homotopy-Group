# Set-truncated canonical long exact sequence of homotopy groups

```agda
module synthetic-homotopy-theory.set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.set-truncations
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **set-truncated canonical long exact sequence** package records the two
adjacent uses of the boundary map separately. The fibration-boundary segment
uses the fresh boundary map of the shifted iterated loop fiber sequence, while
the boundary-fiber-inclusion segment uses the loop-boundary map of the current
iterated loop fiber sequence. These have the same displayed source and target,
but this package does not assert that they are equal.

The exactness proofs are imported from the iterated set-truncated exactness
module. This file is the public package layer that hides the signed comparison
and transport machinery. The aliases below name the two boundary appearances as
the shifted boundary and the loop boundary, which is the distinction needed by
the structural `connect_fiberseq` proof route.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  record Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence :
    UU (l1 ⊔ l2 ⊔ l3)
    where
    constructor
      make-Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    field
      hom-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      hom-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      hom-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      hom-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
      is-exact-fiber-inclusion-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
          ( hom-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
          ( hom-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
      is-exact-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
          ( hom-fibration-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( succ-ℕ n))
          ( hom-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
      is-exact-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
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
          ( hom-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
          ( hom-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))

  open Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    public

  hom-shifted-boundary-set-truncated-homotopy-group-long-exact-sequence :
    Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence →
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
  hom-shifted-boundary-set-truncated-homotopy-group-long-exact-sequence =
    hom-fibration-boundary-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence

  hom-loop-boundary-set-truncated-homotopy-group-long-exact-sequence :
    Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence →
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
  hom-loop-boundary-set-truncated-homotopy-group-long-exact-sequence =
    hom-boundary-fiber-inclusion-set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence

  set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence :
    Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
  set-truncated-canonical-long-exact-sequence-homotopy-groups-fiber-sequence =
    make-Set-Truncated-Canonical-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S)
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
        S)
      ( is-exact-set-truncation-iterated-loop-fiber-sequence S)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        S)
      ( is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
        S)
```
