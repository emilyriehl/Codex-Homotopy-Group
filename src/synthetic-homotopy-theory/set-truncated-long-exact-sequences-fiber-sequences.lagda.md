# Set-truncated long exact sequence of a fiber sequence

```agda
module synthetic-homotopy-theory.set-truncated-long-exact-sequences-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.set-truncations
open import foundation.universe-levels

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.long-exact-sequences-pointed-sets
open import structured-types.pointed-maps
open import structured-types.pointed-sets

open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The **set-truncated long exact sequence** of a fiber sequence is the generic
three-periodic pointed-set display obtained from the iterated loop sequence.
Its public boundary map is the looped canonical iterated boundary. The signed
comparison with the fresh shifted boundary remains internal to the imported
exactness facade.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence :
    ℕ → Pointed-Set l1
  fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n =
    trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space
          ( n)
          ( fiber-fiber-sequence-Pointed-Type S)))

  total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence :
    ℕ → Pointed-Set l2
  total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n =
    trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space
          ( n)
          ( total-space-fiber-sequence-Pointed-Type S)))

  base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence :
    ℕ → Pointed-Set l3
  base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n =
    trunc-Pointed-Set
      ( Ω
        ( iterated-loop-space
          ( n)
          ( base-fiber-sequence-Pointed-Type S)))

  hom-fiber-inclusion-set-truncated-long-exact-sequence-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
      ( total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        n)
  hom-fiber-inclusion-set-truncated-long-exact-sequence-fiber-sequence =
    hom-trunc-iterated-loop-fiber-inclusion-fiber-sequence S

  hom-fibration-set-truncated-long-exact-sequence-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        n)
      ( base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
  hom-fibration-set-truncated-long-exact-sequence-fiber-sequence =
    hom-trunc-iterated-loop-fibration-fiber-sequence S

  hom-boundary-set-truncated-long-exact-sequence-fiber-sequence :
    (n : ℕ) →
    hom-Pointed-Set
      ( base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        (succ-ℕ n))
      ( fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
  hom-boundary-set-truncated-long-exact-sequence-fiber-sequence =
    hom-trunc-loop-canonical-iterated-boundary-fiber-sequence S

  is-exact-at-total-space-set-truncated-long-exact-sequence-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
      ( total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        n)
      ( base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
      ( hom-fiber-inclusion-set-truncated-long-exact-sequence-fiber-sequence n)
      ( hom-fibration-set-truncated-long-exact-sequence-fiber-sequence n)
  is-exact-at-total-space-set-truncated-long-exact-sequence-fiber-sequence =
    is-exact-set-truncation-iterated-loop-fiber-sequence S

  is-exact-at-base-set-truncated-long-exact-sequence-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        (succ-ℕ n))
      ( base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        (succ-ℕ n))
      ( fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
      ( hom-fibration-set-truncated-long-exact-sequence-fiber-sequence
        (succ-ℕ n))
      ( hom-boundary-set-truncated-long-exact-sequence-fiber-sequence n)
  is-exact-at-base-set-truncated-long-exact-sequence-fiber-sequence =
    is-exact-set-truncation-loop-canonical-iterated-boundary-fiber-sequence-signed
      S

  is-exact-at-fiber-set-truncated-long-exact-sequence-fiber-sequence :
    (n : ℕ) →
    is-exact-hom-Pointed-Set
      ( base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        (succ-ℕ n))
      ( fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence n)
      ( total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence
        n)
      ( hom-boundary-set-truncated-long-exact-sequence-fiber-sequence n)
      ( hom-fiber-inclusion-set-truncated-long-exact-sequence-fiber-sequence n)
  is-exact-at-fiber-set-truncated-long-exact-sequence-fiber-sequence =
    is-exact-set-truncation-canonical-iterated-loop-boundary-fiber-inclusion-fiber-sequence
      S

  set-truncated-long-exact-sequence-fiber-sequence :
    Long-Exact-Sequence-Pointed-Set l1 l2 l3
  set-truncated-long-exact-sequence-fiber-sequence =
    make-Long-Exact-Sequence-Pointed-Set
      ( fiber-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence)
      ( total-space-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence)
      ( base-Pointed-Set-set-truncated-long-exact-sequence-fiber-sequence)
      ( hom-fiber-inclusion-set-truncated-long-exact-sequence-fiber-sequence)
      ( hom-fibration-set-truncated-long-exact-sequence-fiber-sequence)
      ( hom-boundary-set-truncated-long-exact-sequence-fiber-sequence)
      ( is-exact-at-total-space-set-truncated-long-exact-sequence-fiber-sequence)
      ( is-exact-at-base-set-truncated-long-exact-sequence-fiber-sequence)
      ( is-exact-at-fiber-set-truncated-long-exact-sequence-fiber-sequence)
```

## Adjacent Exact Triples

The generic display record renders the set-truncated long exact sequence as the
three standard adjacent exact triples at each index.

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  fiber-inclusion-fibration-Exact-Triple-set-truncated-long-exact-sequence-fiber-sequence :
    ℕ → Exact-Triple-Pointed-Set l1 l2 l3
  fiber-inclusion-fibration-Exact-Triple-set-truncated-long-exact-sequence-fiber-sequence =
    fiber-inclusion-fibration-Exact-Triple-Long-Exact-Sequence-Pointed-Set
      ( set-truncated-long-exact-sequence-fiber-sequence S)

  fibration-boundary-Exact-Triple-set-truncated-long-exact-sequence-fiber-sequence :
    ℕ → Exact-Triple-Pointed-Set l2 l3 l1
  fibration-boundary-Exact-Triple-set-truncated-long-exact-sequence-fiber-sequence =
    fibration-boundary-Exact-Triple-Long-Exact-Sequence-Pointed-Set
      ( set-truncated-long-exact-sequence-fiber-sequence S)

  boundary-fiber-inclusion-Exact-Triple-set-truncated-long-exact-sequence-fiber-sequence :
    ℕ → Exact-Triple-Pointed-Set l3 l1 l2
  boundary-fiber-inclusion-Exact-Triple-set-truncated-long-exact-sequence-fiber-sequence =
    boundary-fiber-inclusion-Exact-Triple-Long-Exact-Sequence-Pointed-Set
      ( set-truncated-long-exact-sequence-fiber-sequence S)
```
