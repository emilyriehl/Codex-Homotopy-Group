# Long exact sequences of homotopy groups

```agda
module synthetic-homotopy-theory.long-exact-sequence-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.functoriality-homotopy-automorphism-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.exact-sequences-pointed-sets
open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A [fiber sequence](structured-types.fiber-sequences.md)

```text
  F →∗ E →∗ B
```

has induced homomorphisms on homotopy groups. The remaining extra datum needed
to state the long exact sequence is the family of boundary homomorphisms

```text
  π(n+2) B → π(n+1) F.
```

In the indexing convention of
[homotopy groups](synthetic-homotopy-theory.homotopy-groups.md),
`concrete-homotopy-group n` denotes `π(n+1)`.

## Definitions

### The boundary pointed map of a pointed map

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  boundary-fiber-Pointed-Type : Ω B →∗ fiber-Pointed-Type g
  pr1 boundary-fiber-Pointed-Type p =
    ( point-Pointed-Type E , preserves-point-pointed-map g ∙ p)
  pr2 boundary-fiber-Pointed-Type =
    eq-pair-Σ refl right-unit
```

### Induced maps on the homotopy groups of a fiber sequence

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
  hom-fiber-inclusion-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-homotopy-group
      ( n)
      ( fiber-inclusion-fiber-sequence-Pointed-Type S)

  hom-fibration-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( n)
        ( total-space-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( base-fiber-sequence-Pointed-Type S))
  hom-fibration-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-homotopy-group
      ( n)
      ( fibration-fiber-sequence-Pointed-Type S)
```

### The boundary map of a fiber sequence

```agda
  boundary-pointed-map-fiber-sequence : Ω (base-fiber-sequence-Pointed-Type S) →∗
    fiber-fiber-sequence-Pointed-Type S
  boundary-pointed-map-fiber-sequence =
    pointed-map-inv-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type S) ∘∗
    boundary-fiber-Pointed-Type
      ( fibration-fiber-sequence-Pointed-Type S)

  pointed-map-iterated-boundary-fiber-sequence :
    (n : ℕ) →
    iterated-loop-space
      ( succ-ℕ n)
      ( base-fiber-sequence-Pointed-Type S) →∗
    iterated-loop-space
      ( n)
      ( fiber-fiber-sequence-Pointed-Type S)
  pointed-map-iterated-boundary-fiber-sequence zero-ℕ =
    boundary-pointed-map-fiber-sequence
  pointed-map-iterated-boundary-fiber-sequence (succ-ℕ n) =
    pointed-map-Ω (pointed-map-iterated-boundary-fiber-sequence n)

  boundary-hom-concrete-homotopy-group-fiber-sequence :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group
        ( succ-ℕ n)
        ( base-fiber-sequence-Pointed-Type S))
      ( concrete-homotopy-group
        ( n)
        ( fiber-fiber-sequence-Pointed-Type S))
  boundary-hom-concrete-homotopy-group-fiber-sequence n =
    hom-concrete-group-Pointed-Type
      ( pointed-map-iterated-boundary-fiber-sequence n)
```

### The canonical boundary homomorphism of a pointed map

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  canonical-boundary-hom-concrete-homotopy-group-Pointed-Type :
    (n : ℕ) →
    hom-Concrete-Group
      ( concrete-homotopy-group (succ-ℕ n) B)
      ( concrete-homotopy-group n (fiber-Pointed-Type g))
  canonical-boundary-hom-concrete-homotopy-group-Pointed-Type n =
    boundary-hom-concrete-homotopy-group-fiber-sequence
      ( fiber-sequence-fiber-Pointed-Type g)
      ( n)
```

## Properties

### Set-truncated canonical fiber sequences are exact

This is the first substantive step in the proof of the
[long exact sequence](#idea): the `0`-truncation of any adjacent canonical
fiber-projection triple

```text
  fiber g →∗ E →∗ B
```

is exact as a sequence of pointed sets.

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  is-exact-set-truncation-fiber-sequence-Pointed-Type :
    is-exact-hom-Pointed-Set
      ( trunc-Pointed-Set (fiber-Pointed-Type g))
      ( trunc-Pointed-Set E)
      ( trunc-Pointed-Set B)
      ( hom-trunc-Pointed-Set (inclusion-fiber-Pointed-Type g))
      ( hom-trunc-Pointed-Set g)
  is-exact-set-truncation-fiber-sequence-Pointed-Type =
    is-exact-trunc-fiber-inclusion-Pointed-Type g
```
