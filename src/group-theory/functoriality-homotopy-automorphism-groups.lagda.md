# Functoriality of homotopy automorphism groups

```agda
module group-theory.functoriality-homotopy-automorphism-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.subtypes

open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homotopy-automorphism-groups

open import higher-group-theory.automorphism-groups

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

The concrete
[homotopy automorphism group](group-theory.homotopy-automorphism-groups.md) of
a [pointed type](structured-types.pointed-types.md) is classified by the
connected component of the base point in the `1`-truncation of that pointed
type. Therefore every pointed map induces a homomorphism of concrete homotopy
automorphism groups by functoriality of `1`-truncation and functoriality of
connected components.

## Definitions

### The pointed map on classifying types induced by a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  map-classifying-type-concrete-group-Pointed-Type :
    classifying-type-Concrete-Group (concrete-group-Pointed-Type A) →
    classifying-type-Concrete-Group (concrete-group-Pointed-Type B)
  pr1 (map-classifying-type-concrete-group-Pointed-Type X) =
    map-trunc one-𝕋 (map-pointed-map f) (pr1 X)
  pr2 (map-classifying-type-concrete-group-Pointed-Type X) =
    transitive-mere-eq
      ( map-trunc one-𝕋 (map-pointed-map f) (pr1 X))
      ( map-trunc
        ( one-𝕋)
        ( map-pointed-map f)
        ( unit-trunc (point-Pointed-Type A)))
      ( unit-trunc (point-Pointed-Type B))
      ( mere-eq-eq
        ( ( coherence-square-map-trunc
            ( one-𝕋)
            ( map-pointed-map f)
            ( point-Pointed-Type A)) ∙
          ( ap unit-trunc (preserves-point-pointed-map f))))
      ( map-trunc-Prop
        ( ap (map-trunc one-𝕋 (map-pointed-map f)))
        ( pr2 X))

  preserves-point-map-classifying-type-concrete-group-Pointed-Type :
    map-classifying-type-concrete-group-Pointed-Type
      ( shape-Concrete-Group (concrete-group-Pointed-Type A)) ＝
    shape-Concrete-Group (concrete-group-Pointed-Type B)
  preserves-point-map-classifying-type-concrete-group-Pointed-Type =
    eq-Eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type B))
      ( map-classifying-type-concrete-group-Pointed-Type
        ( shape-Concrete-Group (concrete-group-Pointed-Type A)))
      ( shape-Concrete-Group (concrete-group-Pointed-Type B))
      ( ( coherence-square-map-trunc
          ( one-𝕋)
          ( map-pointed-map f)
          ( point-Pointed-Type A)) ∙
        ( ap unit-trunc (preserves-point-pointed-map f)))

  classifying-pointed-map-concrete-group-Pointed-Type :
    classifying-pointed-type-Concrete-Group (concrete-group-Pointed-Type A) →∗
    classifying-pointed-type-Concrete-Group (concrete-group-Pointed-Type B)
  pr1 classifying-pointed-map-concrete-group-Pointed-Type =
    map-classifying-type-concrete-group-Pointed-Type
  pr2 classifying-pointed-map-concrete-group-Pointed-Type =
    preserves-point-map-classifying-type-concrete-group-Pointed-Type
```

### The induced homomorphism of concrete homotopy automorphism groups

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  hom-concrete-group-Pointed-Type :
    A →∗ B →
    hom-Concrete-Group
      ( concrete-group-Pointed-Type A)
      ( concrete-group-Pointed-Type B)
  hom-concrete-group-Pointed-Type =
    classifying-pointed-map-concrete-group-Pointed-Type
```
