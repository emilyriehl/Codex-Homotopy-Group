# The Hopf family over the 2-sphere

```agda
module synthetic-homotopy-theory.hopf-family-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

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
