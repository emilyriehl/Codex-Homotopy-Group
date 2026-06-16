# Group exactness from set-truncated homotopy-group exactness

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module synthetic-homotopy-theory.group-exactness-from-set-truncated-homotopy-group-exactness where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.exact-sequences-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.set-truncated-iterated-exactness-homotopy-groups-fiber-sequences
```

</details>

## Idea

The set-truncated long exact sequence gives exactness for pointed sets built
from loop spaces. The final Hopf comparison needs exactness for the ordinary
groups underlying concrete homotopy groups. This file isolates that transport
step, keeping it separate from the construction of the set-level exactness
statements.

The missing proof will use the underlying-type equivalences for concrete
homotopy groups and the naturality squares for the induced maps to transport
image and kernel membership between the two exactness formulations.

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
  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fiber-sequence =
    {!!}

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
  is-exact-hom-Group-is-exact-set-truncation-iterated-loop-fibration-boundary-fiber-sequence =
    {!!}
```
