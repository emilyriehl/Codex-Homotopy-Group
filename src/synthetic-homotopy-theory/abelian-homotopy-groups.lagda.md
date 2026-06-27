# Abelian homotopy groups

```agda
module synthetic-homotopy-theory.abelian-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.computing-binary-functoriality-set-truncation
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-set-truncation
open import foundation.identity-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.concrete-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-concrete-groups

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.functoriality-homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups
open import synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups
```

</details>

## Idea

The concrete homotopy group `concrete-homotopy-group (succ-ℕ n) A` is the
ordinary group associated to the loop space on an iterated loop space. Its
multiplication is transported from concatenation of double loops, which is
commutative by the Eckmann-Hilton argument. This file packages the resulting
higher homotopy groups as abelian groups.

## Properties

### Set-truncated double loop multiplication is commutative

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  commutative-binary-map-trunc-Set-mul-Ω-Ω :
    (x y : type-trunc-Set (type-Ω (Ω A))) →
    binary-map-trunc-Set (mul-Ω (Ω A)) x y ＝
    binary-map-trunc-Set (mul-Ω (Ω A)) y x
  commutative-binary-map-trunc-Set-mul-Ω-Ω =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ x y →
        set-Prop
          ( Id-Prop
            ( trunc-Set (type-Ω (Ω A)))
            ( binary-map-trunc-Set (mul-Ω (Ω A)) x y)
            ( binary-map-trunc-Set (mul-Ω (Ω A)) y x)))
      ( λ α β →
        ( compute-binary-map-trunc-Set-unit-trunc-Set
          ( mul-Ω (Ω A))
          ( α)
          ( β)) ∙
        ( ap unit-trunc-Set (eckmann-hilton-Ω² α β)) ∙
        ( inv
          ( compute-binary-map-trunc-Set-unit-trunc-Set
            ( mul-Ω (Ω A))
            ( β)
            ( α))))
```

### Higher concrete homotopy groups are abelian

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  commutative-mul-map-inv-underlying-type-concrete-homotopy-group-succ :
    (x y : type-homotopy-group (succ-ℕ (succ-ℕ n)) A) →
    mul-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A)
      ( map-inv-underlying-type-concrete-homotopy-group
        ( succ-ℕ n)
        ( A)
        ( x))
      ( map-inv-underlying-type-concrete-homotopy-group
        ( succ-ℕ n)
        ( A)
        ( y)) ＝
    mul-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A)
      ( map-inv-underlying-type-concrete-homotopy-group
        ( succ-ℕ n)
        ( A)
        ( y))
      ( map-inv-underlying-type-concrete-homotopy-group
        ( succ-ℕ n)
        ( A)
        ( x))
  commutative-mul-map-inv-underlying-type-concrete-homotopy-group-succ x y =
    ( inv
      ( preserves-mul-map-inv-underlying-type-concrete-homotopy-group
        ( succ-ℕ n)
        ( A)
        ( x)
        ( y))) ∙
    ( ap
      ( map-inv-underlying-type-concrete-homotopy-group (succ-ℕ n) A)
      ( commutative-binary-map-trunc-Set-mul-Ω-Ω
        ( iterated-loop-space n A)
        ( x)
        ( y))) ∙
    ( preserves-mul-map-inv-underlying-type-concrete-homotopy-group
      ( succ-ℕ n)
      ( A)
      ( y)
      ( x))

  is-abelian-concrete-homotopy-group-succ :
    is-abelian-Group
      ( group-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A))
  is-abelian-concrete-homotopy-group-succ x y =
    ( inv
      ( ap-binary
        ( mul-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A))
        ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
          ( iterated-loop-space (succ-ℕ n) A)
          ( x))
        ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
          ( iterated-loop-space (succ-ℕ n) A)
          ( y)))) ∙
    ( commutative-mul-map-inv-underlying-type-concrete-homotopy-group-succ
      ( map-underlying-type-concrete-homotopy-group (succ-ℕ n) A x)
      ( map-underlying-type-concrete-homotopy-group (succ-ℕ n) A y)) ∙
    ( ap-binary
      ( mul-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A))
      ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
        ( iterated-loop-space (succ-ℕ n) A)
        ( y))
      ( is-retraction-map-inv-underlying-type-concrete-group-Pointed-Type
        ( iterated-loop-space (succ-ℕ n) A)
        ( x)))
```

## Definitions

```agda
module _
  {l : Level} (n : ℕ) (A : Pointed-Type l)
  where

  abelian-homotopy-group : Ab l
  pr1 abelian-homotopy-group =
    group-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A)
  pr2 abelian-homotopy-group =
    is-abelian-concrete-homotopy-group-succ n A

module _
  {l1 l2 : Level} (n : ℕ) {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  hom-abelian-homotopy-group :
    hom-Ab
      ( abelian-homotopy-group n A)
      ( abelian-homotopy-group n B)
  hom-abelian-homotopy-group =
    hom-group-hom-Concrete-Group
      ( concrete-homotopy-group (succ-ℕ n) A)
      ( concrete-homotopy-group (succ-ℕ n) B)
      ( hom-concrete-homotopy-group (succ-ℕ n) f)
```
