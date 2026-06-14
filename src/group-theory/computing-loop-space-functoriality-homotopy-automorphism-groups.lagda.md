# Computing loop-space functoriality of homotopy automorphism groups

```agda
module group-theory.computing-loop-space-functoriality-homotopy-automorphism-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.functoriality-homotopy-automorphism-groups
open import group-theory.homotopy-automorphism-groups

open import higher-group-theory.automorphism-groups
open import higher-group-theory.computing-identity-types-automorphism-infinity-groups

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The first-component equality obtained by applying the classifying map of a
pointed map to a path in a connected component is just the action of the
truncated underlying map on first-component equalities.

## Theorem

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  compute-Eq-eq-ap-map-classifying-type-concrete-group-Pointed-Type :
    (Y : classifying-type-Concrete-Group (concrete-group-Pointed-Type A)) →
    (p : shape-Concrete-Group (concrete-group-Pointed-Type A) ＝ Y) →
    Eq-eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type B))
      ( map-classifying-type-concrete-group-Pointed-Type f
        ( shape-Concrete-Group (concrete-group-Pointed-Type A)))
      ( map-classifying-type-concrete-group-Pointed-Type f Y)
      ( ap (map-classifying-type-concrete-group-Pointed-Type f) p) ＝
    ap
      ( map-trunc one-𝕋 (map-pointed-map f))
      ( Eq-eq-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Concrete-Group (concrete-group-Pointed-Type A))
        ( Y)
        ( p))
  compute-Eq-eq-ap-map-classifying-type-concrete-group-Pointed-Type
    .(shape-Concrete-Group (concrete-group-Pointed-Type A)) refl =
    refl

  compute-Eq-eq-preserves-point-map-classifying-type-concrete-group-Pointed-Type :
    Eq-eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type B))
      ( map-classifying-type-concrete-group-Pointed-Type f
        ( shape-Concrete-Group (concrete-group-Pointed-Type A)))
      ( shape-Concrete-Group (concrete-group-Pointed-Type B))
      ( preserves-point-map-classifying-type-concrete-group-Pointed-Type f) ＝
    ( coherence-square-map-trunc
      ( one-𝕋)
      ( map-pointed-map f)
      ( point-Pointed-Type A)) ∙
    ( ap unit-trunc (preserves-point-pointed-map f))
  compute-Eq-eq-preserves-point-map-classifying-type-concrete-group-Pointed-Type =
    compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type B))
      ( map-classifying-type-concrete-group-Pointed-Type f
        ( shape-Concrete-Group (concrete-group-Pointed-Type A)))
      ( shape-Concrete-Group (concrete-group-Pointed-Type B))
      ( ( coherence-square-map-trunc
          ( one-𝕋)
          ( map-pointed-map f)
          ( point-Pointed-Type A)) ∙
        ( ap unit-trunc (preserves-point-pointed-map f)))

  compute-Eq-eq-map-Ω-classifying-pointed-map-concrete-group-Pointed-Type :
    (p :
      Eq-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Concrete-Group (concrete-group-Pointed-Type A))
        ( shape-Concrete-Group (concrete-group-Pointed-Type A))) →
    Eq-eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type B))
      ( shape-Concrete-Group (concrete-group-Pointed-Type B))
      ( shape-Concrete-Group (concrete-group-Pointed-Type B))
      ( map-Ω
        ( classifying-pointed-map-concrete-group-Pointed-Type f)
        ( eq-Eq-classifying-type-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A))
          ( shape-Concrete-Group (concrete-group-Pointed-Type A))
          ( shape-Concrete-Group (concrete-group-Pointed-Type A))
          ( p))) ＝
    tr-type-Ω
      ( ( coherence-square-map-trunc
          ( one-𝕋)
          ( map-pointed-map f)
          ( point-Pointed-Type A)) ∙
        ( ap unit-trunc (preserves-point-pointed-map f)))
      ( ap (map-trunc one-𝕋 (map-pointed-map f)) p)
  compute-Eq-eq-map-Ω-classifying-pointed-map-concrete-group-Pointed-Type p =
    ( compute-Eq-eq-tr-type-Ω-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type B))
      ( preserves-point-map-classifying-type-concrete-group-Pointed-Type f)
      ( ap (map-classifying-type-concrete-group-Pointed-Type f) s)) ∙
    ( ap
      ( λ r →
        tr-type-Ω r
          ( Eq-eq-classifying-type-Automorphism-∞-Group
            ( unit-trunc (point-Pointed-Type B))
            ( map-classifying-type-concrete-group-Pointed-Type f
              ( shape-Concrete-Group (concrete-group-Pointed-Type A)))
            ( map-classifying-type-concrete-group-Pointed-Type f
              ( shape-Concrete-Group (concrete-group-Pointed-Type A)))
            ( ap (map-classifying-type-concrete-group-Pointed-Type f) s)))
      ( compute-Eq-eq-preserves-point-map-classifying-type-concrete-group-Pointed-Type)) ∙
    ( ap
      ( tr-type-Ω η)
      ( ( compute-Eq-eq-ap-map-classifying-type-concrete-group-Pointed-Type
          ( shape-Concrete-Group (concrete-group-Pointed-Type A))
          ( s)) ∙
        ( ap
          ( ap (map-trunc one-𝕋 (map-pointed-map f)))
          ( compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group
            ( unit-trunc (point-Pointed-Type A))
            ( shape-Concrete-Group (concrete-group-Pointed-Type A))
            ( shape-Concrete-Group (concrete-group-Pointed-Type A))
            ( p)))))
    where
    s =
      eq-Eq-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Concrete-Group (concrete-group-Pointed-Type A))
        ( shape-Concrete-Group (concrete-group-Pointed-Type A))
        ( p)

    η =
      ( coherence-square-map-trunc
        ( one-𝕋)
        ( map-pointed-map f)
        ( point-Pointed-Type A)) ∙
      ( ap unit-trunc (preserves-point-pointed-map f))
```
