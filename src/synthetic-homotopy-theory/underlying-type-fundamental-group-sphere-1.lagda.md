# The underlying type of the fundamental group of the 1-sphere

```agda
module synthetic-homotopy-theory.underlying-type-fundamental-group-sphere-1 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.computing-binary-functoriality-set-truncation
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.set-truncations
open import foundation.universe-levels

open import group-theory.concrete-groups

open import structured-types.pointed-equivalences
open import structured-types.pointed-types

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.computing-loop-space-circle
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.homotopy-groups-circle
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups
open import synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups
open import synthetic-homotopy-theory.universal-cover-circle
```

</details>

## Idea

The ordinary underlying type of the concrete fundamental group of the
1-sphere is the set truncation of its loop space. Since the loop space of the
1-sphere is already a set and is equivalent to the integers, this underlying
type is equivalent to the integers.

## Theorem

### The underlying type of the fundamental group of `S¹` is the integers

```agda
equiv-type-fundamental-group-sphere-1-loop-space :
  type-Concrete-Group
    ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)) ≃
  type-Ω (sphere-Pointed-Type 1)
equiv-type-fundamental-group-sphere-1-loop-space =
  inv-equiv
    ( equiv-unit-trunc-Set
      ( pair
        ( type-Ω (sphere-Pointed-Type 1))
        ( is-set-loop-space-sphere-1))) ∘e
  equiv-underlying-type-concrete-homotopy-group
    ( 0)
    ( sphere-Pointed-Type 1)

equiv-type-fundamental-group-sphere-1-ℤ :
  type-Concrete-Group
    ( concrete-homotopy-group 0 (sphere-Pointed-Type 1)) ≃ ℤ
equiv-type-fundamental-group-sphere-1-ℤ =
  compute-loop-space-sphere-1 ∘e
  equiv-type-fundamental-group-sphere-1-loop-space
```

### The equivalence to the loop space preserves multiplication

```agda
preserves-mul-equiv-type-fundamental-group-sphere-1-loop-space :
  (x y :
    type-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))) →
  map-equiv equiv-type-fundamental-group-sphere-1-loop-space
    ( mul-Concrete-Group
      ( concrete-homotopy-group 0 (sphere-Pointed-Type 1))
      ( x)
      ( y)) ＝
  mul-Ω (sphere-Pointed-Type 1)
    ( map-equiv equiv-type-fundamental-group-sphere-1-loop-space x)
    ( map-equiv equiv-type-fundamental-group-sphere-1-loop-space y)
preserves-mul-equiv-type-fundamental-group-sphere-1-loop-space x y =
  ( ap
    ( map-inv-equiv
      ( equiv-unit-trunc-Set
        ( pair
          ( type-Ω (sphere-Pointed-Type 1))
          ( is-set-loop-space-sphere-1))))
    ( preserves-mul-map-underlying-type-concrete-homotopy-group
      ( 0)
      ( sphere-Pointed-Type 1)
      ( x)
      ( y))) ∙
  ( preserves-binary-map-map-inv-equiv-unit-trunc-Set
    ( pair
      ( type-Ω (sphere-Pointed-Type 1))
      ( is-set-loop-space-sphere-1))
    ( pair
      ( type-Ω (sphere-Pointed-Type 1))
      ( is-set-loop-space-sphere-1))
    ( pair
      ( type-Ω (sphere-Pointed-Type 1))
      ( is-set-loop-space-sphere-1))
    ( mul-Ω (sphere-Pointed-Type 1))
    ( map-underlying-type-concrete-homotopy-group
      ( 0)
      ( sphere-Pointed-Type 1)
      ( x))
    ( map-underlying-type-concrete-homotopy-group
      ( 0)
      ( sphere-Pointed-Type 1)
      ( y)))
```

### The loop-space computation preserves multiplication

```agda
preserves-mul-map-inv-equiv-Ω-pointed-equiv :
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B) (p q : type-Ω B) →
  map-inv-equiv (equiv-Ω-pointed-equiv e) (p ∙ q) ＝
  map-inv-equiv (equiv-Ω-pointed-equiv e) p ∙
  map-inv-equiv (equiv-Ω-pointed-equiv e) q
preserves-mul-map-inv-equiv-Ω-pointed-equiv e p q =
  is-injective-equiv
    ( equiv-Ω-pointed-equiv e)
    ( ( is-section-map-inv-equiv (equiv-Ω-pointed-equiv e) (p ∙ q)) ∙
      ( inv
        ( ( preserves-mul-map-Ω
            ( pointed-map-pointed-equiv e)
            { map-inv-equiv (equiv-Ω-pointed-equiv e) p}
            { map-inv-equiv (equiv-Ω-pointed-equiv e) q}) ∙
          ( ap-binary
            ( mul-Ω _)
            ( is-section-map-inv-equiv (equiv-Ω-pointed-equiv e) p)
            ( is-section-map-inv-equiv (equiv-Ω-pointed-equiv e) q)))))

preserves-mul-compute-loop-space-sphere-1 :
  (p q : type-Ω (sphere-Pointed-Type 1)) →
  map-equiv compute-loop-space-sphere-1 (p ∙ q) ＝
  map-equiv compute-loop-space-sphere-1 p +ℤ
  map-equiv compute-loop-space-sphere-1 q
preserves-mul-compute-loop-space-sphere-1 p q =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( preserves-mul-map-inv-equiv-Ω-pointed-equiv
      ( pointed-equiv-sphere-1-circle)
      ( p)
      ( q))) ∙
  ( preserves-mul-compute-loop-space-𝕊¹
    ( map-inv-equiv
      ( equiv-Ω-pointed-equiv pointed-equiv-sphere-1-circle)
      ( p))
    ( map-inv-equiv
      ( equiv-Ω-pointed-equiv pointed-equiv-sphere-1-circle)
      ( q)))
```

### The underlying-type equivalence preserves the unit element

```agda
compute-refl-compute-loop-space-𝕊¹ :
  map-equiv compute-loop-space-𝕊¹ refl ＝ zero-ℤ
compute-refl-compute-loop-space-𝕊¹ =
  is-retraction-map-inv-equiv
    ( compute-fiber-universal-cover-circle
      ( free-loop-𝕊¹)
      ( dependent-universal-property-𝕊¹))
    ( zero-ℤ)

compute-refl-compute-loop-space-sphere-1 :
  map-equiv compute-loop-space-sphere-1 refl ＝ zero-ℤ
compute-refl-compute-loop-space-sphere-1 =
  ( ap
    ( map-equiv compute-loop-space-𝕊¹)
    ( preserves-point-map-inv-pointed-equiv
      ( pointed-equiv-Ω-pointed-equiv pointed-equiv-sphere-1-circle))) ∙
  compute-refl-compute-loop-space-𝕊¹

compute-unit-trunc-compute-loop-space-sphere-1 :
  map-equiv
    ( compute-loop-space-sphere-1 ∘e
      inv-equiv
        ( equiv-unit-trunc-Set
          ( pair
            ( type-Ω (sphere-Pointed-Type 1))
            ( is-set-loop-space-sphere-1))))
    ( unit-trunc-Set refl) ＝ zero-ℤ
compute-unit-trunc-compute-loop-space-sphere-1 =
  ( ap
    ( map-equiv compute-loop-space-sphere-1)
    ( is-retraction-map-inv-equiv
      ( equiv-unit-trunc-Set
        ( pair
          ( type-Ω (sphere-Pointed-Type 1))
          ( is-set-loop-space-sphere-1)))
      ( refl))) ∙
  compute-refl-compute-loop-space-sphere-1
```
