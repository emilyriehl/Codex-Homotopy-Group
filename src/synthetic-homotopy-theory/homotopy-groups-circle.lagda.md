# Homotopy groups of the circle

```agda
module synthetic-homotopy-theory.homotopy-groups-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation-core.truncation-levels

open import group-theory.concrete-groups
open import group-theory.trivial-concrete-groups
open import group-theory.trivial-groups
open import group-theory.trivial-underlying-groups-concrete-groups

open import structured-types.pointed-equivalences

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.higher-homotopy-groups-truncated-types
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.universal-cover-circle
```

</details>

## Idea

The [universal cover of the circle](synthetic-homotopy-theory.universal-cover-circle.md)
computes the loop space of the [circle](synthetic-homotopy-theory.circle.md)
as the type of [integers](elementary-number-theory.integers.md).

## Theorem

### The loop space of the circle is the integers

```agda
compute-loop-space-𝕊¹ : type-Ω 𝕊¹-Pointed-Type ≃ ℤ
compute-loop-space-𝕊¹ =
  compute-loop-space-circle
    ( free-loop-𝕊¹)
    ( dependent-universal-property-𝕊¹)
```

### The circle is pointed equivalent to the 1-sphere

```agda
pointed-equiv-sphere-1-circle : 𝕊¹-Pointed-Type ≃∗ sphere-Pointed-Type 1
pr1 pointed-equiv-sphere-1-circle =
  equiv-sphere-1-circle
pr2 pointed-equiv-sphere-1-circle =
  sphere-1-circle-base-𝕊¹-eq-north-sphere-1
```

### The loop space of the 1-sphere is the integers

```agda
compute-loop-space-sphere-1 : type-Ω (sphere-Pointed-Type 1) ≃ ℤ
compute-loop-space-sphere-1 =
  compute-loop-space-𝕊¹ ∘e
  inv-equiv (equiv-Ω-pointed-equiv pointed-equiv-sphere-1-circle)
```

### The circle is a 1-type

```agda
is-set-loop-space-𝕊¹ : is-set (type-Ω 𝕊¹-Pointed-Type)
is-set-loop-space-𝕊¹ =
  is-set-equiv ℤ compute-loop-space-𝕊¹ is-set-ℤ

is-1-type-𝕊¹ : is-1-type 𝕊¹
is-1-type-𝕊¹ =
  apply-dependent-universal-property-is-0-connected
    ( base-𝕊¹)
    ( is-0-connected-𝕊¹)
    ( λ x →
      ( (y : 𝕊¹) → is-set (x ＝ y)) ,
      ( is-prop-Π (λ y → is-prop-is-set (x ＝ y))))
    ( apply-dependent-universal-property-is-0-connected
      ( base-𝕊¹)
      ( is-0-connected-𝕊¹)
      ( λ y → is-set-Prop (base-𝕊¹ ＝ y))
      ( is-set-loop-space-𝕊¹))
```

### The 1-sphere is a 1-type

```agda
is-set-loop-space-sphere-1 : is-set (type-Ω (sphere-Pointed-Type 1))
is-set-loop-space-sphere-1 =
  is-set-equiv ℤ compute-loop-space-sphere-1 is-set-ℤ

is-1-type-sphere-1 : is-1-type (sphere 1)
is-1-type-sphere-1 =
  is-trunc-equiv' one-𝕋 𝕊¹ equiv-sphere-1-circle is-1-type-𝕊¹
```

### The second concrete homotopy group of the circle is trivial

```agda
is-trivial-concrete-homotopy-group-one-𝕊¹ :
  is-trivial-Concrete-Group (concrete-homotopy-group 1 𝕊¹-Pointed-Type)
is-trivial-concrete-homotopy-group-one-𝕊¹ =
  is-trivial-positive-concrete-homotopy-group-is-1-type
    0
    𝕊¹-Pointed-Type
    is-1-type-𝕊¹

is-trivial-concrete-homotopy-group-one-sphere-1 :
  is-trivial-Concrete-Group
    ( concrete-homotopy-group 1 (sphere-Pointed-Type 1))
is-trivial-concrete-homotopy-group-one-sphere-1 =
  is-trivial-positive-concrete-homotopy-group-is-1-type
    0
    ( sphere-Pointed-Type 1)
    is-1-type-sphere-1

is-trivial-positive-concrete-homotopy-group-𝕊¹ :
  (n : ℕ) →
  is-trivial-Concrete-Group
    ( concrete-homotopy-group (succ-ℕ n) 𝕊¹-Pointed-Type)
is-trivial-positive-concrete-homotopy-group-𝕊¹ n =
  is-trivial-positive-concrete-homotopy-group-is-1-type
    n
    𝕊¹-Pointed-Type
    is-1-type-𝕊¹

is-trivial-positive-concrete-homotopy-group-sphere-1 :
  (n : ℕ) →
  is-trivial-Concrete-Group
    ( concrete-homotopy-group (succ-ℕ n) (sphere-Pointed-Type 1))
is-trivial-positive-concrete-homotopy-group-sphere-1 n =
  is-trivial-positive-concrete-homotopy-group-is-1-type
    n
    ( sphere-Pointed-Type 1)
    is-1-type-sphere-1

is-trivial-group-positive-concrete-homotopy-group-𝕊¹ :
  (n : ℕ) →
  is-trivial-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group (succ-ℕ n) 𝕊¹-Pointed-Type))
is-trivial-group-positive-concrete-homotopy-group-𝕊¹ n =
  is-trivial-group-is-trivial-Concrete-Group
    ( concrete-homotopy-group (succ-ℕ n) 𝕊¹-Pointed-Type)
    ( is-trivial-positive-concrete-homotopy-group-𝕊¹ n)

is-trivial-group-positive-concrete-homotopy-group-sphere-1 :
  (n : ℕ) →
  is-trivial-Group
    ( group-Concrete-Group
      ( concrete-homotopy-group (succ-ℕ n) (sphere-Pointed-Type 1)))
is-trivial-group-positive-concrete-homotopy-group-sphere-1 n =
  is-trivial-group-is-trivial-Concrete-Group
    ( concrete-homotopy-group (succ-ℕ n) (sphere-Pointed-Type 1))
    ( is-trivial-positive-concrete-homotopy-group-sphere-1 n)
```
