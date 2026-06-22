# The Hopf family over the 2-sphere

```agda
module synthetic-homotopy-theory.hopf-family-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.h-space-structure-circle
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The Hopf fibration can be presented as a type family over the suspension of the
circle. Both pole fibers are the circle, and the meridian indexed by `x : S¹`
is classified by the equivalence given by left multiplication by `x`.

This file records that structural family over `S²`. Its total space is the
object that the flattening argument should identify with the total space of the
Hopf construction.

## Definitions

### The family over the 2-sphere

```agda
suspension-structure-hopf-family-sphere-1 :
  suspension-structure (sphere 1) (UU lzero)
pr1 suspension-structure-hopf-family-sphere-1 =
  sphere 1
pr1 (pr2 suspension-structure-hopf-family-sphere-1) =
  sphere 1
pr2 (pr2 suspension-structure-hopf-family-sphere-1) x =
  eq-equiv (equiv-left-mul-sphere-1 x)

hopf-family-sphere-1 : sphere 2 → UU lzero
hopf-family-sphere-1 =
  cogap-suspension suspension-structure-hopf-family-sphere-1
```

### Pole and meridian computations

```agda
compute-north-hopf-family-sphere-1 :
  hopf-family-sphere-1 (north-sphere 2) ＝ sphere 1
compute-north-hopf-family-sphere-1 =
  compute-north-cogap-suspension suspension-structure-hopf-family-sphere-1

compute-south-hopf-family-sphere-1 :
  hopf-family-sphere-1 (south-sphere 2) ＝ sphere 1
compute-south-hopf-family-sphere-1 =
  compute-south-cogap-suspension suspension-structure-hopf-family-sphere-1

compute-meridian-hopf-family-sphere-1 :
  (x : sphere 1) →
  ( ( ap hopf-family-sphere-1 (meridian-sphere 1 x)) ∙
    ( compute-south-hopf-family-sphere-1)) ＝
  ( ( compute-north-hopf-family-sphere-1) ∙
    ( eq-equiv (equiv-left-mul-sphere-1 x)))
compute-meridian-hopf-family-sphere-1 =
  compute-meridian-cogap-suspension suspension-structure-hopf-family-sphere-1
```

### The total space of the Hopf family

```agda
total-space-hopf-family-sphere-1 : UU lzero
total-space-hopf-family-sphere-1 =
  Σ (sphere 2) hopf-family-sphere-1
```

### The projection from the total space of the Hopf family

```agda
point-hopf-family-sphere-1 :
  hopf-family-sphere-1 (north-sphere 2)
point-hopf-family-sphere-1 =
  map-inv-equiv
    ( equiv-eq compute-north-hopf-family-sphere-1)
    ( north-sphere 1)

pointed-total-space-hopf-family-sphere-1 : Pointed-Type lzero
pr1 pointed-total-space-hopf-family-sphere-1 =
  total-space-hopf-family-sphere-1
pr2 pointed-total-space-hopf-family-sphere-1 =
  north-sphere 2 , point-hopf-family-sphere-1

projection-hopf-family-sphere-1 :
  total-space-hopf-family-sphere-1 → sphere 2
projection-hopf-family-sphere-1 =
  pr1

pointed-map-projection-hopf-family-sphere-1 :
  pointed-total-space-hopf-family-sphere-1 →∗ sphere-Pointed-Type 2
pr1 pointed-map-projection-hopf-family-sphere-1 =
  projection-hopf-family-sphere-1
pr2 pointed-map-projection-hopf-family-sphere-1 =
  refl
```

### The fiber over the north pole

```agda
equiv-fiber-projection-hopf-family-sphere-1 :
  type-Pointed-Type
    ( fiber-Pointed-Type pointed-map-projection-hopf-family-sphere-1) ≃
  sphere 1
equiv-fiber-projection-hopf-family-sphere-1 =
  ( equiv-eq compute-north-hopf-family-sphere-1) ∘e
  ( equiv-fiber-pr1 hopf-family-sphere-1 (north-sphere 2))

pointed-equiv-fiber-projection-hopf-family-sphere-1 :
  fiber-Pointed-Type pointed-map-projection-hopf-family-sphere-1 ≃∗
  sphere-Pointed-Type 1
pr1 pointed-equiv-fiber-projection-hopf-family-sphere-1 =
  equiv-fiber-projection-hopf-family-sphere-1
pr2 pointed-equiv-fiber-projection-hopf-family-sphere-1 =
  is-section-map-inv-equiv
    ( equiv-eq compute-north-hopf-family-sphere-1)
    ( north-sphere 1)

pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1 :
  sphere-Pointed-Type 1 ≃∗
  fiber-Pointed-Type pointed-map-projection-hopf-family-sphere-1
pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1 =
  inv-pointed-equiv pointed-equiv-fiber-projection-hopf-family-sphere-1
```

### The fiber sequence of the Hopf family

```agda
fiber-inclusion-hopf-family-sphere-1 :
  sphere-Pointed-Type 1 →∗ pointed-total-space-hopf-family-sphere-1
fiber-inclusion-hopf-family-sphere-1 =
  ( inclusion-fiber-Pointed-Type
    ( pointed-map-projection-hopf-family-sphere-1)) ∘∗
  ( pointed-map-pointed-equiv
    ( pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1))

is-fiber-sequence-hopf-family-sphere-1 :
  is-fiber-sequence-Pointed-Type
    ( fiber-inclusion-hopf-family-sphere-1)
    ( pointed-map-projection-hopf-family-sphere-1)
pr1 is-fiber-sequence-hopf-family-sphere-1 =
  pointed-equiv-sphere-1-fiber-projection-hopf-family-sphere-1
pr2 is-fiber-sequence-hopf-family-sphere-1 =
  refl-pointed-htpy fiber-inclusion-hopf-family-sphere-1

fiber-sequence-hopf-family-sphere-1 :
  fiber-sequence-Pointed-Type lzero lzero lzero
pr1 fiber-sequence-hopf-family-sphere-1 =
  sphere-Pointed-Type 1
pr1 (pr2 fiber-sequence-hopf-family-sphere-1) =
  pointed-total-space-hopf-family-sphere-1
pr1 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1)) =
  sphere-Pointed-Type 2
pr1 (pr2 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1))) =
  fiber-inclusion-hopf-family-sphere-1
pr1 (pr2 (pr2 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1)))) =
  pointed-map-projection-hopf-family-sphere-1
pr2 (pr2 (pr2 (pr2 (pr2 fiber-sequence-hopf-family-sphere-1)))) =
  is-fiber-sequence-hopf-family-sphere-1
```
