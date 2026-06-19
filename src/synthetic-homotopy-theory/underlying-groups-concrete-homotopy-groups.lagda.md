# Underlying groups of concrete homotopy groups

```agda
module synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.computing-binary-functoriality-set-truncation
open import foundation.equivalences
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.naturality-effectiveness-truncation
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homotopy-automorphism-groups

open import higher-group-theory.automorphism-groups
open import higher-group-theory.computing-identity-types-automorphism-infinity-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The concrete homotopy group `concrete-homotopy-group n A` is the concrete group
classified by the pointed type `Ωⁿ A`. Its ordinary underlying group is the
loop group of the connected component of the base point in the `1`-truncation
of `Ωⁿ A`. By effectiveness of truncation, this underlying type agrees with
the set truncation of the next iterated loop space.

This comparison is the bridge needed to translate set-truncated adjacent
exactness in the homotopy long exact sequence into ordinary group exactness of
concrete homotopy groups.

## Theorem

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  equiv-underlying-type-concrete-group-Pointed-Type :
    type-Concrete-Group (concrete-group-Pointed-Type A) ≃
    type-trunc-Set (type-Ω A)
  equiv-underlying-type-concrete-group-Pointed-Type =
    ( inv-equiv
      ( effectiveness-trunc
        ( zero-𝕋)
        ( point-Pointed-Type A)
        ( point-Pointed-Type A))) ∘e
    ( extensionality-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type A))
      ( shape-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A)))
      ( shape-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))))

  map-underlying-type-concrete-group-Pointed-Type :
    type-Concrete-Group (concrete-group-Pointed-Type A) →
    type-trunc-Set (type-Ω A)
  map-underlying-type-concrete-group-Pointed-Type =
    map-equiv equiv-underlying-type-concrete-group-Pointed-Type

  map-inv-underlying-type-concrete-group-Pointed-Type :
    type-trunc-Set (type-Ω A) →
    type-Concrete-Group (concrete-group-Pointed-Type A)
  map-inv-underlying-type-concrete-group-Pointed-Type x =
    eq-Eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type A))
      ( shape-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A)))
      ( shape-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A)))
      ( map-effectiveness-trunc
        ( zero-𝕋)
        ( point-Pointed-Type A)
        ( point-Pointed-Type A)
        ( x))

  compute-mul-map-inv-underlying-type-concrete-group-unit-trunc-Pointed-Type :
    (p q : type-Ω A) →
    map-inv-underlying-type-concrete-group-Pointed-Type
      ( unit-trunc-Set (mul-Ω A p q)) ＝
    mul-Concrete-Group (concrete-group-Pointed-Type A)
      ( map-inv-underlying-type-concrete-group-Pointed-Type
        ( unit-trunc-Set p))
      ( map-inv-underlying-type-concrete-group-Pointed-Type
        ( unit-trunc-Set q))
  compute-mul-map-inv-underlying-type-concrete-group-unit-trunc-Pointed-Type
    p q =
    ( ap
      ( eq-Eq-classifying-type-Automorphism-∞-Group
        ( unit-trunc (point-Pointed-Type A))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A)))
        ( shape-Automorphism-∞-Group
          ( unit-trunc (point-Pointed-Type A))))
      ( preserves-concat-map-effectiveness-trunc-unit-trunc
        ( zero-𝕋)
        ( p)
        ( q))) ∙
    ( preserves-concat-eq-Eq-classifying-type-Automorphism-∞-Group
      ( unit-trunc (point-Pointed-Type A))
      ( map-effectiveness-trunc
        ( zero-𝕋)
        ( point-Pointed-Type A)
        ( point-Pointed-Type A)
        ( unit-trunc-Set p))
      ( map-effectiveness-trunc
        ( zero-𝕋)
        ( point-Pointed-Type A)
        ( point-Pointed-Type A)
        ( unit-trunc-Set q)))

  preserves-mul-map-inv-underlying-type-concrete-group-Pointed-Type :
    (x y : type-trunc-Set (type-Ω A)) →
    map-inv-underlying-type-concrete-group-Pointed-Type
      ( binary-map-trunc-Set (mul-Ω A) x y) ＝
    mul-Concrete-Group (concrete-group-Pointed-Type A)
      ( map-inv-underlying-type-concrete-group-Pointed-Type x)
      ( map-inv-underlying-type-concrete-group-Pointed-Type y)
  preserves-mul-map-inv-underlying-type-concrete-group-Pointed-Type =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ x y →
        set-Prop
          ( Id-Prop
            ( set-Concrete-Group (concrete-group-Pointed-Type A))
            ( map-inv-underlying-type-concrete-group-Pointed-Type
              ( binary-map-trunc-Set (mul-Ω A) x y))
            ( mul-Concrete-Group (concrete-group-Pointed-Type A)
              ( map-inv-underlying-type-concrete-group-Pointed-Type x)
              ( map-inv-underlying-type-concrete-group-Pointed-Type y))))
      ( λ p q →
        ( ap
          ( map-inv-underlying-type-concrete-group-Pointed-Type)
          ( compute-binary-map-trunc-Set-unit-trunc-Set
            ( mul-Ω A)
            ( p)
            ( q))) ∙
        ( compute-mul-map-inv-underlying-type-concrete-group-unit-trunc-Pointed-Type
          ( p)
          ( q)))

module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  equiv-underlying-type-concrete-homotopy-group :
    type-Concrete-Group (concrete-homotopy-group n A) ≃
    type-homotopy-group (succ-ℕ n) A
  equiv-underlying-type-concrete-homotopy-group =
    equiv-underlying-type-concrete-group-Pointed-Type (iterated-loop-space n A)

  map-underlying-type-concrete-homotopy-group :
    type-Concrete-Group (concrete-homotopy-group n A) →
    type-homotopy-group (succ-ℕ n) A
  map-underlying-type-concrete-homotopy-group =
    map-equiv equiv-underlying-type-concrete-homotopy-group

  map-inv-underlying-type-concrete-homotopy-group :
    type-homotopy-group (succ-ℕ n) A →
    type-Concrete-Group (concrete-homotopy-group n A)
  map-inv-underlying-type-concrete-homotopy-group =
    map-inv-underlying-type-concrete-group-Pointed-Type
      ( iterated-loop-space n A)

  preserves-mul-map-inv-underlying-type-concrete-homotopy-group :
    (x y : type-homotopy-group (succ-ℕ n) A) →
    map-inv-underlying-type-concrete-homotopy-group
      ( binary-map-trunc-Set (mul-Ω (iterated-loop-space n A)) x y) ＝
    mul-Concrete-Group (concrete-homotopy-group n A)
      ( map-inv-underlying-type-concrete-homotopy-group x)
      ( map-inv-underlying-type-concrete-homotopy-group y)
  preserves-mul-map-inv-underlying-type-concrete-homotopy-group =
    preserves-mul-map-inv-underlying-type-concrete-group-Pointed-Type
      ( iterated-loop-space n A)
```
