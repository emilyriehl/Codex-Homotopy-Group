# Set-truncated recursive iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-recursive-iterated-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.set-truncations
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-boundary-maps-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **recursive set-truncated iterated exactness statements** transport the
canonical shifted boundary exactness theorem to a recursively looped boundary
map. They are compatibility wrappers: callers supply either a kernel
comparison, a pointwise homotopy of set-truncated maps, or a pointed homotopy
of the classifying pointed maps.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-kernel :
    (n : ℕ) →
    ((x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
      is-in-kernel-hom-Pointed-Set
        { A =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( succ-ℕ n)
                ( base-fiber-sequence-Pointed-Type S)))}
        { B =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))}
        ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
        ( x) ↔
      is-in-kernel-hom-Pointed-Set
        { A =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( succ-ℕ n)
                ( base-fiber-sequence-Pointed-Type S)))}
        { B =
          trunc-Pointed-Set
            ( Ω
              ( iterated-loop-space
                ( n)
                ( fiber-fiber-sequence-Pointed-Type S)))}
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
        ( x)) →
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
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-kernel
    n K =
    is-exact-hom-Pointed-Set-iff-kernel-right
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
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
      ( K)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        S
        ( n))

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence :
    (n : ℕ) →
    ((x :
      type-Pointed-Set
        ( trunc-Pointed-Set
          ( Ω
            ( iterated-loop-space
              ( succ-ℕ n)
              ( base-fiber-sequence-Pointed-Type S))))) →
      map-pointed-map (hom-trunc-iterated-loop-boundary-fiber-sequence S n) x ＝
      map-pointed-map
        ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
        ( x)) →
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
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence n H =
    is-exact-hom-Pointed-Set-htpy-right
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
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
      ( H)
      ( is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
        S
        ( n))

  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-pointed-htpy :
    (n : ℕ) →
    ( pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)) ~∗
    ( boundary-pointed-map-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))) →
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
      ( hom-trunc-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence-pointed-htpy
    n H =
    is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence
      ( n)
      ( htpy-hom-trunc-Pointed-Set
        { f = pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence S n)}
        { g =
          boundary-pointed-map-fiber-sequence
            ( iterated-loop-fiber-sequence S (succ-ℕ n))}
        ( htpy-pointed-htpy H))
```
