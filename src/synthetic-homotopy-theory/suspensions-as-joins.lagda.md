# Suspensions as joins with the two-point type

```agda
module synthetic-homotopy-theory.suspensions-as-joins where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The suspension of a type `X` can be modeled as the join of the standard
two-element type with `X`. The forward map

```text
Fin 2 * X → suspension X
```

sends the two points of `Fin 2` to the north and south poles and sends the
right copy of `X` to the south pole, using the meridians for the join paths.
The reverse map

```text
suspension X → Fin 2 * X
```

sends the poles to the two points of `Fin 2` and sends each meridian through
the corresponding point of the right copy of `X`.

These maps are the first reusable layer toward identifying spheres with join
powers of `Fin 2`.

## Definitions

### The map from `Fin 2 * X` to the suspension of `X`

```agda
module _
  {l : Level} (X : UU l)
  where

  cocone-map-suspension-join-Fin-2 :
    cocone
      ( pr1 {A = Fin 2} {B = λ _ → X})
      ( pr2 {A = Fin 2} {B = λ _ → X})
      ( suspension X)
  pr1 cocone-map-suspension-join-Fin-2 (inl (inr star)) =
    north-suspension
  pr1 cocone-map-suspension-join-Fin-2 (inr star) =
    south-suspension
  pr1 (pr2 cocone-map-suspension-join-Fin-2) x =
    south-suspension
  pr2 (pr2 cocone-map-suspension-join-Fin-2) ((inl (inr star)) , x) =
    meridian-suspension x
  pr2 (pr2 cocone-map-suspension-join-Fin-2) ((inr star) , x) =
    refl

  map-suspension-join-Fin-2 : Fin 2 * X → suspension X
  map-suspension-join-Fin-2 =
    cogap-join
      ( suspension X)
      ( cocone-map-suspension-join-Fin-2)
```

### The map from the suspension of `X` to `Fin 2 * X`

```agda
  suspension-structure-map-join-Fin-2-suspension :
    suspension-structure X (Fin 2 * X)
  pr1 suspension-structure-map-join-Fin-2-suspension =
    inl-join (zero-Fin 1)
  pr1 (pr2 suspension-structure-map-join-Fin-2-suspension) =
    inl-join (one-Fin 1)
  pr2 (pr2 suspension-structure-map-join-Fin-2-suspension) x =
    ( glue-join (zero-Fin 1 , x)) ∙
    ( inv (glue-join (one-Fin 1 , x)))

  map-join-Fin-2-suspension : suspension X → Fin 2 * X
  map-join-Fin-2-suspension =
    cogap-suspension suspension-structure-map-join-Fin-2-suspension
```

## Properties

### Computation rules for the map from the join to the suspension

```agda
  compute-inl-zero-map-suspension-join-Fin-2 :
    map-suspension-join-Fin-2 (inl-join (zero-Fin 1)) ＝
    north-suspension
  compute-inl-zero-map-suspension-join-Fin-2 =
    compute-inl-cogap-join
      ( cocone-map-suspension-join-Fin-2)
      ( zero-Fin 1)

  compute-inl-one-map-suspension-join-Fin-2 :
    map-suspension-join-Fin-2 (inl-join (one-Fin 1)) ＝
    south-suspension
  compute-inl-one-map-suspension-join-Fin-2 =
    compute-inl-cogap-join
      ( cocone-map-suspension-join-Fin-2)
      ( one-Fin 1)

  compute-inr-map-suspension-join-Fin-2 :
    (x : X) →
    map-suspension-join-Fin-2 (inr-join x) ＝ south-suspension
  compute-inr-map-suspension-join-Fin-2 =
    compute-inr-cogap-join cocone-map-suspension-join-Fin-2
```

### Computation rules for the map from the suspension to the join

```agda
  compute-north-map-join-Fin-2-suspension :
    map-join-Fin-2-suspension north-suspension ＝ inl-join (zero-Fin 1)
  compute-north-map-join-Fin-2-suspension =
    compute-north-cogap-suspension
      ( suspension-structure-map-join-Fin-2-suspension)

  compute-south-map-join-Fin-2-suspension :
    map-join-Fin-2-suspension south-suspension ＝ inl-join (one-Fin 1)
  compute-south-map-join-Fin-2-suspension =
    compute-south-cogap-suspension
      ( suspension-structure-map-join-Fin-2-suspension)

  compute-meridian-map-join-Fin-2-suspension :
    (x : X) →
    ( ( ap map-join-Fin-2-suspension (meridian-suspension x)) ∙
      compute-south-map-join-Fin-2-suspension) ＝
    ( compute-north-map-join-Fin-2-suspension ∙
      ( glue-join (zero-Fin 1 , x) ∙
        inv (glue-join (one-Fin 1 , x))))
  compute-meridian-map-join-Fin-2-suspension =
    compute-meridian-cogap-suspension
      ( suspension-structure-map-join-Fin-2-suspension)
```
