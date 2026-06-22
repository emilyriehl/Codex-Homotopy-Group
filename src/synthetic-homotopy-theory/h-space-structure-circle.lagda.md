# The H-space structure on the circle

```agda
module synthetic-homotopy-theory.h-space-structure-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.h-spaces

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.multiplication-circle
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The [circle](synthetic-homotopy-theory.circle.md) is an
[H-space](structured-types.h-spaces.md). The multiplication is the standard
multiplication on the circle, and the unit laws are the left and right unit
laws of that multiplication.

The Hopf construction is naturally phrased for a connected H-space. Since the
local Hopf fiber sequence is stated using the `1`-sphere rather than the circle,
we also transport the multiplication across the equivalence between the circle
and the `1`-sphere.

## Definitions

### The H-space structure on the circle

```agda
coherent-unital-mul-𝕊¹-Pointed-Type :
  coherent-unital-mul-Pointed-Type 𝕊¹-Pointed-Type
pr1 coherent-unital-mul-𝕊¹-Pointed-Type =
  mul-𝕊¹
pr2 coherent-unital-mul-𝕊¹-Pointed-Type =
  coherent-unit-laws-unit-laws
    ( mul-𝕊¹)
    ( left-unit-law-mul-𝕊¹ , right-unit-law-mul-𝕊¹)

𝕊¹-H-Space : H-Space lzero
𝕊¹-H-Space =
  make-H-Space
    ( 𝕊¹-Pointed-Type)
    ( coherent-unital-mul-𝕊¹-Pointed-Type)
```

### Left and right translations on the circle

```agda
is-equiv-left-mul-𝕊¹ : (x : 𝕊¹) → is-equiv (mul-𝕊¹ x)
is-equiv-left-mul-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → is-equiv (mul-𝕊¹ x))
    ( is-equiv-htpy-id left-unit-law-mul-𝕊¹)
    ( eq-is-prop (is-property-is-equiv (mul-𝕊¹ base-𝕊¹)))

is-equiv-right-mul-𝕊¹ :
  (x : 𝕊¹) → is-equiv (λ y → mul-𝕊¹ y x)
is-equiv-right-mul-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → is-equiv (λ y → mul-𝕊¹ y x))
    ( is-equiv-htpy-id right-unit-law-mul-𝕊¹)
    ( eq-is-prop (is-property-is-equiv (λ y → mul-𝕊¹ y base-𝕊¹)))

equiv-left-mul-𝕊¹ : 𝕊¹ → 𝕊¹ ≃ 𝕊¹
pr1 (equiv-left-mul-𝕊¹ x) = mul-𝕊¹ x
pr2 (equiv-left-mul-𝕊¹ x) = is-equiv-left-mul-𝕊¹ x

equiv-right-mul-𝕊¹ : 𝕊¹ → 𝕊¹ ≃ 𝕊¹
pr1 (equiv-right-mul-𝕊¹ x) = λ y → mul-𝕊¹ y x
pr2 (equiv-right-mul-𝕊¹ x) = is-equiv-right-mul-𝕊¹ x
```

### The transported multiplication on the 1-sphere

```agda
mul-sphere-1 : sphere 1 → sphere 1 → sphere 1
mul-sphere-1 x y =
  sphere-1-circle (mul-𝕊¹ (circle-sphere-1 x) (circle-sphere-1 y))

left-unit-law-mul-sphere-1 :
  (x : sphere 1) → mul-sphere-1 (north-sphere 1) x ＝ x
left-unit-law-mul-sphere-1 x =
  ( ap
    ( λ t → sphere-1-circle (mul-𝕊¹ t (circle-sphere-1 x)))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( ap
    ( sphere-1-circle)
    ( left-unit-law-mul-𝕊¹ (circle-sphere-1 x))) ∙
  ( pr2 sphere-1-circle-sphere-1 x)

right-unit-law-mul-sphere-1 :
  (x : sphere 1) → mul-sphere-1 x (north-sphere 1) ＝ x
right-unit-law-mul-sphere-1 x =
  ( ap
    ( λ t → sphere-1-circle (mul-𝕊¹ (circle-sphere-1 x) t))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( ap
    ( sphere-1-circle)
    ( right-unit-law-mul-𝕊¹ (circle-sphere-1 x))) ∙
  ( pr2 sphere-1-circle-sphere-1 x)
```

### Left and right translations on the 1-sphere

```agda
is-equiv-left-mul-sphere-1 :
  (x : sphere 1) → is-equiv (mul-sphere-1 x)
is-equiv-left-mul-sphere-1 x =
  is-equiv-comp
    ( sphere-1-circle)
    ( mul-𝕊¹ (circle-sphere-1 x) ∘ circle-sphere-1)
    ( is-equiv-comp
      ( mul-𝕊¹ (circle-sphere-1 x))
      ( circle-sphere-1)
      ( is-equiv-map-inv-equiv equiv-sphere-1-circle)
      ( is-equiv-left-mul-𝕊¹ (circle-sphere-1 x)))
    ( is-equiv-map-equiv equiv-sphere-1-circle)

is-equiv-right-mul-sphere-1 :
  (x : sphere 1) → is-equiv (λ y → mul-sphere-1 y x)
is-equiv-right-mul-sphere-1 x =
  is-equiv-comp
    ( sphere-1-circle)
    ( (λ y → mul-𝕊¹ y (circle-sphere-1 x)) ∘ circle-sphere-1)
    ( is-equiv-comp
      ( λ y → mul-𝕊¹ y (circle-sphere-1 x))
      ( circle-sphere-1)
      ( is-equiv-map-inv-equiv equiv-sphere-1-circle)
      ( is-equiv-right-mul-𝕊¹ (circle-sphere-1 x)))
    ( is-equiv-map-equiv equiv-sphere-1-circle)

equiv-left-mul-sphere-1 : sphere 1 → sphere 1 ≃ sphere 1
pr1 (equiv-left-mul-sphere-1 x) = mul-sphere-1 x
pr2 (equiv-left-mul-sphere-1 x) = is-equiv-left-mul-sphere-1 x

equiv-right-mul-sphere-1 : sphere 1 → sphere 1 ≃ sphere 1
pr1 (equiv-right-mul-sphere-1 x) = λ y → mul-sphere-1 y x
pr2 (equiv-right-mul-sphere-1 x) = is-equiv-right-mul-sphere-1 x
```

### The H-space structure on the 1-sphere

```agda
coherent-unital-mul-sphere-1-Pointed-Type :
  coherent-unital-mul-Pointed-Type (sphere-Pointed-Type 1)
pr1 coherent-unital-mul-sphere-1-Pointed-Type =
  mul-sphere-1
pr2 coherent-unital-mul-sphere-1-Pointed-Type =
  coherent-unit-laws-unit-laws
    ( mul-sphere-1)
    ( left-unit-law-mul-sphere-1 , right-unit-law-mul-sphere-1)

sphere-1-H-Space : H-Space lzero
sphere-1-H-Space =
  make-H-Space
    ( sphere-Pointed-Type 1)
    ( coherent-unital-mul-sphere-1-Pointed-Type)
```
