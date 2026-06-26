# Connecting fiber sequences

```agda
module synthetic-homotopy-theory.connecting-fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.long-exact-sequence-homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **connecting fiber sequence** of a pointed map `g : E →∗ B` is the
fiber sequence

```text
  Ω E →∗ Ω B →∗ fiber g
```

whose second map is the connecting map of `g`. For a packaged fiber sequence
`F →∗ E →∗ B`, the corresponding connecting fiber sequence is

```text
  Ω E →∗ Ω B →∗ F.
```

This module gives those structures library-facing names. The proofs are the
checked `connect_fiberseq`-style constructions currently developed in
`long-exact-sequence-homotopy-groups`; this module separates their public
mathematical meaning from the older proof-route-specific names.

## Definitions

### Connecting fiber sequence of a pointed map

```agda
module _
  {l1 l2 : Level}
  {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  connecting-map-Pointed-Type :
    Ω B →∗ fiber-Pointed-Type g
  connecting-map-Pointed-Type =
    boundary-fiber-Pointed-Type g

  pointed-equiv-fiber-connecting-map-Pointed-Type :
    Ω E ≃∗ fiber-Pointed-Type connecting-map-Pointed-Type
  pointed-equiv-fiber-connecting-map-Pointed-Type =
    pointed-equiv-fiber-boundary-map-Ω-direct-Pointed-Type g

  pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type :
    pointed-map-Ω g ~∗
    ( inclusion-fiber-Pointed-Type connecting-map-Pointed-Type ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-connecting-map-Pointed-Type)
  pointed-htpy-inclusion-fiber-connecting-map-Pointed-Type =
    pointed-htpy-inclusion-fiber-boundary-map-Ω-direct-Pointed-Type g

  is-fiber-sequence-connecting-map-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( pointed-map-Ω g)
      ( connecting-map-Pointed-Type)
  is-fiber-sequence-connecting-map-Pointed-Type =
    is-fiber-sequence-boundary-map-Ω-direct-Pointed-Type g

  fiber-sequence-connecting-map-Pointed-Type :
    fiber-sequence-Pointed-Type l1 l2 (l1 ⊔ l2)
  fiber-sequence-connecting-map-Pointed-Type =
    fiber-sequence-boundary-map-Ω-direct-Pointed-Type g
```

### Connecting fiber sequence of a packaged fiber sequence

```agda
module _
  {l1 l2 l3 : Level}
  (S : fiber-sequence-Pointed-Type l1 l2 l3)
  where

  connecting-map-fiber-sequence-Pointed-Type :
    Ω (base-fiber-sequence-Pointed-Type S) →∗
    fiber-fiber-sequence-Pointed-Type S
  connecting-map-fiber-sequence-Pointed-Type =
    boundary-pointed-map-fiber-sequence S

  pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type :
    Ω (total-space-fiber-sequence-Pointed-Type S) ≃∗
    fiber-Pointed-Type connecting-map-fiber-sequence-Pointed-Type
  pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type =
    pointed-equiv-fiber-boundary-fiber-sequence-direct-Pointed-Type S

  pointed-htpy-inclusion-fiber-connecting-map-fiber-sequence-Pointed-Type :
    pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S) ~∗
    ( inclusion-fiber-Pointed-Type
      ( connecting-map-fiber-sequence-Pointed-Type) ∘∗
      pointed-map-pointed-equiv
        pointed-equiv-fiber-connecting-map-fiber-sequence-Pointed-Type)
  pointed-htpy-inclusion-fiber-connecting-map-fiber-sequence-Pointed-Type =
    pointed-htpy-inclusion-fiber-boundary-fiber-sequence-direct-Pointed-Type S

  is-fiber-sequence-connecting-map-fiber-sequence-Pointed-Type :
    is-fiber-sequence-Pointed-Type
      ( pointed-map-Ω (fibration-fiber-sequence-Pointed-Type S))
      ( connecting-map-fiber-sequence-Pointed-Type)
  is-fiber-sequence-connecting-map-fiber-sequence-Pointed-Type =
    is-fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S

  fiber-sequence-connecting-map-fiber-sequence-Pointed-Type :
    fiber-sequence-Pointed-Type l2 l3 l1
  fiber-sequence-connecting-map-fiber-sequence-Pointed-Type =
    fiber-sequence-boundary-fiber-sequence-direct-Pointed-Type S
```
