# Underlying maps of concrete homotopy groups

```agda
module synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-truncation
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import group-theory.computing-loop-space-functoriality-homotopy-automorphism-groups
open import group-theory.concrete-groups
open import group-theory.functoriality-homotopy-automorphism-groups
open import group-theory.homomorphisms-concrete-groups
open import group-theory.homotopy-automorphism-groups

open import higher-group-theory.automorphism-groups
open import higher-group-theory.computing-identity-types-automorphism-infinity-groups

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.naturality-effectiveness-loop-spaces
open import synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups
```

</details>

## Idea

The equivalence from the ordinary underlying type of a concrete homotopy group
to the set truncation of the next iterated loop space should be natural in
pointed maps. The full naturality proof is the next coherence step. This file
records the two maps whose compatibility must be proved: the ordinary
underlying map of the concrete-group homomorphism and the set-truncated loop
map.

## Definitions for pointed types

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  map-underlying-hom-concrete-group-Pointed-Type :
    type-Concrete-Group (concrete-group-Pointed-Type A) →
    type-Concrete-Group (concrete-group-Pointed-Type B)
  map-underlying-hom-concrete-group-Pointed-Type =
    map-hom-Concrete-Group
      ( concrete-group-Pointed-Type A)
      ( concrete-group-Pointed-Type B)
      ( hom-concrete-group-Pointed-Type f)

  map-set-trunc-loop-map-Pointed-Type :
    type-trunc-Set (type-Ω A) → type-trunc-Set (type-Ω B)
  map-set-trunc-loop-map-Pointed-Type =
    map-trunc-Set (map-Ω f)

  coherence-square-map-underlying-type-concrete-group-Pointed-Type :
    UU (l1 ⊔ l2)
  coherence-square-map-underlying-type-concrete-group-Pointed-Type =
    (x : type-Concrete-Group (concrete-group-Pointed-Type A)) →
    map-underlying-type-concrete-group-Pointed-Type B
      ( map-underlying-hom-concrete-group-Pointed-Type x) ＝
    map-set-trunc-loop-map-Pointed-Type
      ( map-underlying-type-concrete-group-Pointed-Type A x)

  coherence-square-map-inv-underlying-type-concrete-group-Pointed-Type :
    UU (l1 ⊔ l2)
  coherence-square-map-inv-underlying-type-concrete-group-Pointed-Type =
    (x : type-trunc-Set (type-Ω A)) →
    map-underlying-hom-concrete-group-Pointed-Type
      ( map-inv-underlying-type-concrete-group-Pointed-Type A x) ＝
    map-inv-underlying-type-concrete-group-Pointed-Type B
      ( map-set-trunc-loop-map-Pointed-Type x)
```

## Inverse laws for pointed types

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  is-section-map-inv-underlying-type-concrete-group-Pointed-Type :
    (x : type-trunc-Set (type-Ω A)) →
    map-underlying-type-concrete-group-Pointed-Type A
      ( map-inv-underlying-type-concrete-group-Pointed-Type A x) ＝ x
  is-section-map-inv-underlying-type-concrete-group-Pointed-Type x =
    ( ap
      ( map-inv-equiv
        ( effectiveness-trunc
          ( zero-𝕋)
          ( point-Pointed-Type A)
          ( point-Pointed-Type A)))
      ( compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A)))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A)))
        ( map-effectiveness-trunc
          ( zero-𝕋)
          ( point-Pointed-Type A)
          ( point-Pointed-Type A)
          ( x)))) ∙
    ( is-retraction-map-inv-equiv
      ( effectiveness-trunc
        ( zero-𝕋)
        ( point-Pointed-Type A)
        ( point-Pointed-Type A))
      ( x))

  is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type :
    (x : type-Concrete-Group (concrete-group-Pointed-Type A)) →
    map-inv-underlying-type-concrete-group-Pointed-Type A
      ( map-underlying-type-concrete-group-Pointed-Type A x) ＝ x
  is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type x =
    is-injective-equiv
      ( extensionality-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A)))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A))))
      ( ( compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A))
          ( shape-Automorphism-∞-Group
            ( unit-trunc (point-Pointed-Type A)))
          ( shape-Automorphism-∞-Group
            ( unit-trunc (point-Pointed-Type A)))
          ( map-effectiveness-trunc
            ( zero-𝕋)
            ( point-Pointed-Type A)
            ( point-Pointed-Type A)
            ( map-underlying-type-concrete-group-Pointed-Type A x))) ∙
        ( is-section-map-inv-equiv
          ( effectiveness-trunc
            ( zero-𝕋)
            ( point-Pointed-Type A)
            ( point-Pointed-Type A))
          ( Eq-eq-classifying-type-Automorphism-∞-Group
            ( unit-trunc (point-Pointed-Type A))
            ( shape-Automorphism-∞-Group
              ( unit-trunc (point-Pointed-Type A)))
            ( shape-Automorphism-∞-Group
              ( unit-trunc (point-Pointed-Type A)))
            ( x))))

  compute-map-inv-underlying-type-concrete-group-unit-Pointed-Type :
    map-inv-underlying-type-concrete-group-Pointed-Type A
      ( unit-trunc-Set refl) ＝
    unit-Concrete-Group (concrete-group-Pointed-Type A)
  compute-map-inv-underlying-type-concrete-group-unit-Pointed-Type =
    ( ap
      ( eq-Eq-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A)))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A))))
      ( refl-effectiveness-trunc zero-𝕋 (point-Pointed-Type A))) ∙
    ( is-retraction-map-inv-equiv
      ( extensionality-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A)))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A))))
      ( refl))

  preserves-unit-map-underlying-type-concrete-group-Pointed-Type :
    map-underlying-type-concrete-group-Pointed-Type A
      ( unit-Concrete-Group (concrete-group-Pointed-Type A)) ＝
    unit-trunc-Set refl
  preserves-unit-map-underlying-type-concrete-group-Pointed-Type =
    ( ap
      ( map-underlying-type-concrete-group-Pointed-Type A)
      ( inv compute-map-inv-underlying-type-concrete-group-unit-Pointed-Type)) ∙
    ( is-section-map-inv-underlying-type-concrete-group-Pointed-Type
      ( unit-trunc-Set refl))

  equiv-map-inv-underlying-type-concrete-group-Pointed-Type :
    type-trunc-Set (type-Ω A) ≃
    type-Concrete-Group (concrete-group-Pointed-Type A)
  pr1 equiv-map-inv-underlying-type-concrete-group-Pointed-Type =
    map-inv-underlying-type-concrete-group-Pointed-Type A
  pr2 equiv-map-inv-underlying-type-concrete-group-Pointed-Type =
    is-equiv-is-invertible
      ( map-underlying-type-concrete-group-Pointed-Type A)
      ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type)
      ( is-section-map-inv-underlying-type-concrete-group-Pointed-Type)

  preserves-mul-map-underlying-type-concrete-group-Pointed-Type :
    (x y : type-Concrete-Group (concrete-group-Pointed-Type A)) →
    map-underlying-type-concrete-group-Pointed-Type A
      ( mul-Concrete-Group (concrete-group-Pointed-Type A) x y) ＝
    binary-map-trunc-Set (mul-Ω A)
      ( map-underlying-type-concrete-group-Pointed-Type A x)
      ( map-underlying-type-concrete-group-Pointed-Type A y)
  preserves-mul-map-underlying-type-concrete-group-Pointed-Type x y =
    is-injective-equiv
      ( equiv-map-inv-underlying-type-concrete-group-Pointed-Type)
      ( ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
          ( mul-Concrete-Group (concrete-group-Pointed-Type A) x y)) ∙
        ( inv
          ( ( preserves-mul-map-inv-underlying-type-concrete-group-Pointed-Type
              ( A)
              ( map-underlying-type-concrete-group-Pointed-Type A x)
              ( map-underlying-type-concrete-group-Pointed-Type A y)) ∙
            ( ap-binary
              ( mul-Concrete-Group (concrete-group-Pointed-Type A))
              ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
                ( x))
              ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
                ( y))))))
```

## Properties for pointed types

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  naturality-map-inv-underlying-type-concrete-group-Pointed-Type :
    (f : A →∗ B) →
    coherence-square-map-inv-underlying-type-concrete-group-Pointed-Type f
  naturality-map-inv-underlying-type-concrete-group-Pointed-Type
    (pair f' refl) =
    apply-dependent-universal-property-trunc-Set'
      ( λ x →
        set-Prop
          ( Id-Prop
            ( set-Concrete-Group (concrete-group-Pointed-Type B))
            ( map-underlying-hom-concrete-group-Pointed-Type
              ( pair f' refl)
              ( map-inv-underlying-type-concrete-group-Pointed-Type A x))
            ( map-inv-underlying-type-concrete-group-Pointed-Type B
              ( map-set-trunc-loop-map-Pointed-Type (pair f' refl) x))))
      ( λ p →
        is-injective-equiv
          ( extensionality-classifying-type-Automorphism-∞-Group
            ( unit-trunc (point-Pointed-Type B))
            ( shape-Automorphism-∞-Group
              ( unit-trunc (point-Pointed-Type B)))
            ( shape-Automorphism-∞-Group
              ( unit-trunc (point-Pointed-Type B))))
          ( ( compute-Eq-eq-map-Ω-classifying-pointed-map-concrete-group-Pointed-Type
              ( pair f' refl)
              ( map-effectiveness-trunc
                ( zero-𝕋)
                ( point-Pointed-Type A)
                ( point-Pointed-Type A)
                ( unit-trunc p))) ∙
            ( tr-naturality-map-effectiveness-trunc
              ( zero-𝕋)
              ( f')
              ( unit-trunc p)) ∙
            ( inv
              ( compute-Eq-eq-eq-Eq-classifying-type-Automorphism-∞-Group
                ( unit-trunc (point-Pointed-Type B))
                ( shape-Automorphism-∞-Group
                  ( unit-trunc (point-Pointed-Type B)))
                ( shape-Automorphism-∞-Group
                  ( unit-trunc (point-Pointed-Type B)))
                ( map-effectiveness-trunc
                  ( zero-𝕋)
                  ( point-Pointed-Type B)
                  ( point-Pointed-Type B)
                  ( map-trunc zero-𝕋 (ap f') (unit-trunc p)))))))

  naturality-map-underlying-type-concrete-group-Pointed-Type :
    (f : A →∗ B) →
    coherence-square-map-underlying-type-concrete-group-Pointed-Type f
  naturality-map-underlying-type-concrete-group-Pointed-Type f x =
    ( ap
      ( λ y →
        map-underlying-type-concrete-group-Pointed-Type B
          ( map-underlying-hom-concrete-group-Pointed-Type f y))
      ( inv
        ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type A x))) ∙
    ( ap
      ( map-underlying-type-concrete-group-Pointed-Type B)
      ( naturality-map-inv-underlying-type-concrete-group-Pointed-Type f
        ( map-underlying-type-concrete-group-Pointed-Type A x))) ∙
    ( is-section-map-inv-underlying-type-concrete-group-Pointed-Type B
      ( map-set-trunc-loop-map-Pointed-Type f
        ( map-underlying-type-concrete-group-Pointed-Type A x)))

  is-equiv-map-underlying-hom-concrete-group-Pointed-Type-is-equiv-map-set-trunc-loop-map-Pointed-Type :
    (f : A →∗ B) →
    is-equiv (map-set-trunc-loop-map-Pointed-Type f) →
    is-equiv (map-underlying-hom-concrete-group-Pointed-Type f)
  is-equiv-map-underlying-hom-concrete-group-Pointed-Type-is-equiv-map-set-trunc-loop-map-Pointed-Type
    f =
    is-equiv-equiv
      ( equiv-underlying-type-concrete-group-Pointed-Type A)
      ( equiv-underlying-type-concrete-group-Pointed-Type B)
      ( naturality-map-underlying-type-concrete-group-Pointed-Type f)
```

## Definitions for homotopy groups

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (n : ℕ) (f : A →∗ B)
  where

  map-underlying-hom-concrete-homotopy-group :
    type-Concrete-Group (concrete-homotopy-group n A) →
    type-Concrete-Group (concrete-homotopy-group n B)
  map-underlying-hom-concrete-homotopy-group =
    map-hom-Concrete-Group
      ( concrete-homotopy-group n A)
      ( concrete-homotopy-group n B)
      ( hom-concrete-homotopy-group n f)

  map-set-trunc-loop-map-concrete-homotopy-group :
    type-homotopy-group (succ-ℕ n) A →
    type-homotopy-group (succ-ℕ n) B
  map-set-trunc-loop-map-concrete-homotopy-group =
    map-trunc-Set (map-Ω (pointed-map-iterated-loop-space n f))

  coherence-square-map-underlying-type-concrete-homotopy-group :
    UU (l1 ⊔ l2)
  coherence-square-map-underlying-type-concrete-homotopy-group =
    coherence-square-map-underlying-type-concrete-group-Pointed-Type
      ( pointed-map-iterated-loop-space n f)

  coherence-square-map-inv-underlying-type-concrete-homotopy-group :
    UU (l1 ⊔ l2)
  coherence-square-map-inv-underlying-type-concrete-homotopy-group =
    coherence-square-map-inv-underlying-type-concrete-group-Pointed-Type
      ( pointed-map-iterated-loop-space n f)
```

## Properties for homotopy groups

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  preserves-mul-map-underlying-type-concrete-homotopy-group :
    (x y : type-Concrete-Group (concrete-homotopy-group n A)) →
    map-underlying-type-concrete-homotopy-group n A
      ( mul-Concrete-Group (concrete-homotopy-group n A) x y) ＝
    binary-map-trunc-Set (mul-Ω (iterated-loop-space n A))
      ( map-underlying-type-concrete-homotopy-group n A x)
      ( map-underlying-type-concrete-homotopy-group n A y)
  preserves-mul-map-underlying-type-concrete-homotopy-group =
    preserves-mul-map-underlying-type-concrete-group-Pointed-Type
      ( iterated-loop-space n A)
```
