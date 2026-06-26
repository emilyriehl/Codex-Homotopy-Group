# Set-truncated canonical iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-canonical-iterated-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.set-truncations
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.iterated-loop-fiber-sequences
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.set-truncated-iterated-maps-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **canonical iterated exactness statements** are the exactness theorems for
the iterated fiber sequence and for the fresh canonical shifted boundary maps.
They are the theorem inputs for the public canonical long exact sequence
package and for the internal signed comparison layer.

## Theorems

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  is-exact-set-truncation-iterated-loop-fiber-sequence :
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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence S n)
  is-exact-set-truncation-iterated-loop-fiber-sequence zero-ℕ =
    is-exact-set-truncation-loop-fiber-sequence S
  is-exact-set-truncation-iterated-loop-fiber-sequence (succ-ℕ n) =
    is-exact-set-truncation-loop-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))

  is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence :
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
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S n)
  is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
    n =
    is-exact-set-truncation-loop-boundary-fiber-inclusion-fiber-sequence
      ( iterated-loop-fiber-sequence S n)

  is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence :
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
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence S n)
  is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence
    n =
    is-exact-set-truncation-loop-boundary-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))
```
