# Pointed sets

```agda
module structured-types.pointed-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A **pointed set** is a [set](foundation.sets.md) equipped with a specified
base point.

Pointed sets are the set-level analogue of
[pointed types](structured-types.pointed-types.md), and their morphisms are
[pointed maps](structured-types.pointed-maps.md) between their underlying
pointed types.

## Definitions

### Pointed sets

```agda
Pointed-Set : (l : Level) → UU (lsuc l)
Pointed-Set l = Σ (Set l) (type-Set)

module _
  {l : Level} (A : Pointed-Set l)
  where

  set-Pointed-Set : Set l
  set-Pointed-Set = pr1 A

  type-Pointed-Set : UU l
  type-Pointed-Set = type-Set set-Pointed-Set

  is-set-type-Pointed-Set : is-set type-Pointed-Set
  is-set-type-Pointed-Set = is-set-type-Set set-Pointed-Set

  point-Pointed-Set : type-Pointed-Set
  point-Pointed-Set = pr2 A

  pointed-type-Pointed-Set : Pointed-Type l
  pr1 pointed-type-Pointed-Set = type-Pointed-Set
  pr2 pointed-type-Pointed-Set = point-Pointed-Set
```

### Pointed maps of pointed sets

```agda
module _
  {l1 l2 : Level} (A : Pointed-Set l1) (B : Pointed-Set l2)
  where

  hom-Pointed-Set : UU (l1 ⊔ l2)
  hom-Pointed-Set =
    pointed-type-Pointed-Set A →∗ pointed-type-Pointed-Set B
```

### Set truncation as a pointed set

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  trunc-Pointed-Set : Pointed-Set l
  pr1 trunc-Pointed-Set = trunc-Set (type-Pointed-Type A)
  pr2 trunc-Pointed-Set = unit-trunc-Set (point-Pointed-Type A)
```

### Set truncation of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  hom-trunc-Pointed-Set :
    hom-Pointed-Set (trunc-Pointed-Set A) (trunc-Pointed-Set B)
  pr1 hom-trunc-Pointed-Set =
    map-trunc-Set (map-pointed-map f)
  pr2 hom-trunc-Pointed-Set =
    ( naturality-unit-trunc-Set
      ( map-pointed-map f)
      ( point-Pointed-Type A)) ∙
    ( ap unit-trunc-Set (preserves-point-pointed-map f))
```

## Properties

### Set truncation of pointed maps transports along identifications

```agda
module _
  {l1 l2 : Level}
  {A A' : Pointed-Type l1} {B B' : Pointed-Type l2}
  where

  tr-hom-trunc-Pointed-Set :
    (pA : A' ＝ A) (pB : B' ＝ B) (f' : A' →∗ B') →
    tr
      (λ X → hom-Pointed-Set X (trunc-Pointed-Set B))
      (ap trunc-Pointed-Set pA)
      ( tr
        (λ Y → hom-Pointed-Set (trunc-Pointed-Set A') Y)
        (ap trunc-Pointed-Set pB)
        (hom-trunc-Pointed-Set f')) ＝
    hom-trunc-Pointed-Set
      ( tr
        (λ X → X →∗ B)
        (pA)
        ( tr
          (λ Y → A' →∗ Y)
          (pB)
          (f')))
  tr-hom-trunc-Pointed-Set refl refl f = refl
```
