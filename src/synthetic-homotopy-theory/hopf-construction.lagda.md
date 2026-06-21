# The Hopf construction

```agda
module synthetic-homotopy-theory.hopf-construction where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The **Hopf construction** of an [H-space](structured-types.h-spaces.md) `A`
begins with a map

```text
A * A → suspension A.
```

On the left copy of `A` this map is constantly the north pole, on the right
copy it is constantly the south pole, and on the join path indexed by
`(x , y)` it uses the meridian indexed by the product `x · y`.

This map is the fibration map in the Hopf fiber sequence once the total space
and fiber comparison proofs are supplied.

## Definitions

### The Hopf map of an H-space

```agda
module _
  {l : Level} (A : H-Space l)
  where

  total-space-hopf-construction-H-Space : UU l
  total-space-hopf-construction-H-Space =
    type-H-Space A * type-H-Space A

  base-hopf-construction-H-Space : UU l
  base-hopf-construction-H-Space =
    suspension (type-H-Space A)

  pointed-total-space-hopf-construction-H-Space : Pointed-Type l
  pr1 pointed-total-space-hopf-construction-H-Space =
    total-space-hopf-construction-H-Space
  pr2 pointed-total-space-hopf-construction-H-Space =
    inl-join (unit-H-Space A)

  pointed-base-hopf-construction-H-Space : Pointed-Type l
  pr1 pointed-base-hopf-construction-H-Space =
    base-hopf-construction-H-Space
  pr2 pointed-base-hopf-construction-H-Space =
    north-suspension

  cocone-hopf-construction-H-Space :
    cocone
      ( pr1 {A = type-H-Space A} {B = λ _ → type-H-Space A})
      ( pr2 {A = type-H-Space A} {B = λ _ → type-H-Space A})
      ( base-hopf-construction-H-Space)
  pr1 cocone-hopf-construction-H-Space x =
    north-suspension
  pr1 (pr2 cocone-hopf-construction-H-Space) y =
    south-suspension
  pr2 (pr2 cocone-hopf-construction-H-Space) (x , y) =
    meridian-suspension (mul-H-Space A x y)

  hopf-map-H-Space :
    total-space-hopf-construction-H-Space → base-hopf-construction-H-Space
  hopf-map-H-Space =
    cogap-join
      ( base-hopf-construction-H-Space)
      ( cocone-hopf-construction-H-Space)

  pointed-map-hopf-construction-H-Space :
    pointed-total-space-hopf-construction-H-Space →∗
    pointed-base-hopf-construction-H-Space
  pr1 pointed-map-hopf-construction-H-Space =
    hopf-map-H-Space
  pr2 pointed-map-hopf-construction-H-Space =
    compute-inl-cogap-join
      ( cocone-hopf-construction-H-Space)
      ( unit-H-Space A)
```
