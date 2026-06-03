# Fiber sequences

```agda
module synthetic-homotopy-theory.fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A **fiber sequence** of [pointed types](structured-types.pointed-types.md)
consists of a pair of composable
[pointed maps](structured-types.pointed-maps.md)

```text
  F →∗ E →∗ B
```

such that `F` is identified with the
[pointed fiber](structured-types.fibers-of-pointed-maps.md) of the second map
over the base point of `B`, compatibly with the first map.

## Definitions

### The inclusion of the pointed fiber

The pointed fiber of a pointed map `g : E →∗ B` comes equipped with its
canonical pointed map into `E`.

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  (g : E →∗ B)
  where

  map-inclusion-fiber-Pointed-Type :
    type-Pointed-Type (fiber-Pointed-Type g) → type-Pointed-Type E
  map-inclusion-fiber-Pointed-Type = pr1

  preserves-point-inclusion-fiber-Pointed-Type :
    map-inclusion-fiber-Pointed-Type
      ( point-Pointed-Type (fiber-Pointed-Type g)) ＝
    point-Pointed-Type E
  preserves-point-inclusion-fiber-Pointed-Type = refl

  inclusion-fiber-Pointed-Type : fiber-Pointed-Type g →∗ E
  pr1 inclusion-fiber-Pointed-Type = map-inclusion-fiber-Pointed-Type
  pr2 inclusion-fiber-Pointed-Type =
    preserves-point-inclusion-fiber-Pointed-Type
```

### Fiber sequences of pointed types

```agda
module _
  {l1 l2 l3 : Level}
  {F : Pointed-Type l1} {E : Pointed-Type l2} {B : Pointed-Type l3}
  (f : F →∗ E) (g : E →∗ B)
  where

  is-fiber-sequence-Pointed-Type : UU (l1 ⊔ l2 ⊔ l3)
  is-fiber-sequence-Pointed-Type =
    Σ ( F ≃∗ fiber-Pointed-Type g)
      ( λ e →
        ( inclusion-fiber-Pointed-Type g ∘∗ pointed-map-pointed-equiv e) ~∗
        f)

  fiber-sequence-Pointed-Type : UU (l1 ⊔ l2 ⊔ l3)
  fiber-sequence-Pointed-Type = is-fiber-sequence-Pointed-Type
```

## Properties

### Accessors for fiber sequences

```agda
module _
  {l1 l2 l3 : Level}
  {F : Pointed-Type l1} {E : Pointed-Type l2} {B : Pointed-Type l3}
  {f : F →∗ E} {g : E →∗ B}
  (s : fiber-sequence-Pointed-Type f g)
  where

  pointed-equiv-fiber-fiber-sequence-Pointed-Type :
    F ≃∗ fiber-Pointed-Type g
  pointed-equiv-fiber-fiber-sequence-Pointed-Type = pr1 s

  pointed-map-fiber-fiber-sequence-Pointed-Type :
    F →∗ fiber-Pointed-Type g
  pointed-map-fiber-fiber-sequence-Pointed-Type =
    pointed-map-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type)

  is-pointed-equiv-pointed-map-fiber-fiber-sequence-Pointed-Type :
    is-pointed-equiv pointed-map-fiber-fiber-sequence-Pointed-Type
  is-pointed-equiv-pointed-map-fiber-fiber-sequence-Pointed-Type =
    is-equiv-map-pointed-equiv
      ( pointed-equiv-fiber-fiber-sequence-Pointed-Type)

  pointed-htpy-inclusion-fiber-fiber-sequence-Pointed-Type :
    ( inclusion-fiber-Pointed-Type g ∘∗
      pointed-map-fiber-fiber-sequence-Pointed-Type) ~∗
    f
  pointed-htpy-inclusion-fiber-fiber-sequence-Pointed-Type = pr2 s
```
