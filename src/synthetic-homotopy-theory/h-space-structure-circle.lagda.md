# The H-space structure on the circle

```agda
module synthetic-homotopy-theory.h-space-structure-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
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
