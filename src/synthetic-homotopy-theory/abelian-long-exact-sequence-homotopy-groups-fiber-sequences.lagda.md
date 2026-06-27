# Abelian long exact sequence of homotopy groups of fiber sequences

```agda
module synthetic-homotopy-theory.abelian-long-exact-sequence-homotopy-groups-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.exact-sequences-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.abelian-homotopy-groups
open import synthetic-homotopy-theory.canonical-exactness-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homomorphisms-homotopy-groups-fiber-sequences
open import synthetic-homotopy-theory.homotopy-groups
```

</details>

## Idea

In dimensions `2` and higher, homotopy groups are abelian. This file packages
the long exact sequence of a fiber sequence in that abelian range. The boundary
map is indexed so that

```text
  π_{n+3} B -> π_{n+2} F
```

is represented as a homomorphism

```text
  abelian-homotopy-group (succ-ℕ n) B -> abelian-homotopy-group n F.
```

Exactness is inherited from the concrete-group long exact sequence at index
`succ-ℕ n`.

## Definitions

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  record Abelian-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence :
    UU (l1 ⊔ l2 ⊔ l3)
    where
    constructor make-Abelian-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
    field
      hom-fiber-inclusion-abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Ab
          ( abelian-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))
      hom-fibration-abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Ab
          ( abelian-homotopy-group
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( base-fiber-sequence-Pointed-Type S))
      hom-boundary-abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        hom-Ab
          ( abelian-homotopy-group
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
      is-exact-fiber-inclusion-fibration-abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        is-exact-hom-Ab
          ( abelian-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( base-fiber-sequence-Pointed-Type S))
          ( hom-fiber-inclusion-abelian-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
          ( hom-fibration-abelian-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
      is-exact-fibration-boundary-abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        is-exact-hom-Ab
          ( abelian-homotopy-group
            ( succ-ℕ n)
            ( total-space-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
          ( hom-fibration-abelian-long-exact-sequence-homotopy-groups-fiber-sequence
            ( succ-ℕ n))
          ( hom-boundary-abelian-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
      is-exact-boundary-fiber-inclusion-abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
        (n : ℕ) →
        is-exact-hom-Ab
          ( abelian-homotopy-group
            ( succ-ℕ n)
            ( base-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( fiber-fiber-sequence-Pointed-Type S))
          ( abelian-homotopy-group
            ( n)
            ( total-space-fiber-sequence-Pointed-Type S))
          ( hom-boundary-abelian-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))
          ( hom-fiber-inclusion-abelian-long-exact-sequence-homotopy-groups-fiber-sequence
            ( n))

  open Abelian-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence public

  hom-canonical-boundary-abelian-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Ab
      ( abelian-homotopy-group
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( abelian-homotopy-group
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  hom-canonical-boundary-abelian-homotopy-group-fiber-sequence n =
    hom-group-hom-Concrete-Group
      ( concrete-homotopy-group
        ( succ-ℕ (succ-ℕ n))
        ( base-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( succ-ℕ n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( canonical-boundary-hom-concrete-homotopy-group-fiber-sequence
        ( S)
        ( succ-ℕ n))

  abelian-long-exact-sequence-homotopy-groups-fiber-sequence :
    Abelian-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
  abelian-long-exact-sequence-homotopy-groups-fiber-sequence =
    make-Abelian-Long-Exact-Sequence-Homotopy-Groups-Fiber-Sequence
      ( λ n →
        hom-abelian-homotopy-group
          ( n)
          ( fiber-inclusion-fiber-sequence-Pointed-Type S))
      ( λ n →
        hom-abelian-homotopy-group
          ( n)
          ( fibration-fiber-sequence-Pointed-Type S))
      ( hom-canonical-boundary-abelian-homotopy-group-fiber-sequence)
      ( λ n →
        is-exact-hom-fiber-inclusion-fibration-concrete-homotopy-group-fiber-sequence
          ( S)
          ( succ-ℕ n))
      ( λ n →
        is-exact-hom-canonical-fibration-boundary-concrete-homotopy-group-fiber-sequence
          ( S)
          ( succ-ℕ n))
      ( λ n →
        is-exact-hom-canonical-boundary-fiber-inclusion-concrete-homotopy-group-fiber-sequence
          ( S)
          ( succ-ℕ n))
```
