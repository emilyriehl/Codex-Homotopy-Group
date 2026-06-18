# Set-truncated iterated exactness of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The group-level long exact sequence of homotopy groups needs exactness after
applying set truncation to the loop spaces of iterated loop spaces. This file
records that set-level iterated exactness separately from the later transport to
ordinary group exactness.

For a fiber sequence `F ->* E ->* B`, the first target says that the maps

```text
  Ω Ω^n F ->* Ω Ω^n E ->* Ω Ω^n B
```

are exact after set truncation. The second checked target says that the maps

```text
  Ω Ω^(n+1) E ->* Ω Ω^(n+1) B ->* Ω Ω^n F
```

are exact after set truncation when the final map is the canonical shifted
boundary map of the iterated loop fiber sequence. The recursive looped
boundary map is retained separately because it is the map classifying the
concrete homotopy-group homomorphism; comparing these two boundary maps is the
remaining bridge from this set-level theorem to the group-level LES statement.

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
    hom-trunc-boundary-fiber-sequence-Pointed-Type
      ( iterated-loop-fiber-sequence S (succ-ℕ n))
```

## Theorems

```agda
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
      ( hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence n)
      ( hom-trunc-iterated-loop-fibration-fiber-sequence n)
  is-exact-set-truncation-iterated-loop-fiber-sequence zero-ℕ =
    is-exact-set-truncation-loop-fiber-sequence S
  is-exact-set-truncation-iterated-loop-fiber-sequence (succ-ℕ n) =
    is-exact-set-truncation-loop-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))

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
      ( hom-trunc-iterated-loop-fibration-fiber-sequence (succ-ℕ n))
      ( hom-trunc-canonical-iterated-loop-boundary-fiber-sequence n)
  is-exact-set-truncation-canonical-iterated-loop-fibration-boundary-fiber-sequence n =
    is-exact-set-truncation-loop-boundary-fiber-sequence
      ( iterated-loop-fiber-sequence S (succ-ℕ n))
```
