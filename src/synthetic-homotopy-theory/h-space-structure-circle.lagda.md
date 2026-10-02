# The H-space structure on the circle

```agda
module synthetic-homotopy-theory.h-space-structure-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.equality-pointed-maps
open import structured-types.h-spaces
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.multiplication-circle
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

The [circle](synthetic-homotopy-theory.circle.md) is an
[H-space](structured-types.h-spaces.md). The multiplication is the standard
multiplication on the circle, and the unit laws are the left and right unit
laws of that multiplication. Their coherence follows directly from the base
point computation rule of the circle's dependent eliminator, which is an
identification of pointed maps.

The Hopf construction is naturally phrased for a connected H-space. Since the
local Hopf fiber sequence is stated using the `1`-sphere rather than the circle,
we also transport the multiplication across the equivalence between the circle
and the `1`-sphere.

## Definitions

### Coherence of the given unit laws on the circle

The circle multiplication is constructed as a dependent family of pointed
maps `(mul-𝕊¹ x , right-unit-law-mul-𝕊¹ x)`. At `base-𝕊¹`, the computation
rule `pr1 (pr2 mul-Π-𝕊¹)` identifies this pointed map with the identity
pointed map. The induced homotopy of underlying maps is exactly
`left-unit-law-mul-𝕊¹`. Its base point coherence says

```text
right-unit-law-mul-𝕊¹ base-𝕊¹ ＝ left-unit-law-mul-𝕊¹ base-𝕊¹ ∙ refl.
```

Removing the concatenation with `refl` and inverting gives the required
coherence of the original unit laws.

```agda
coh-unit-laws-mul-𝕊¹ :
  left-unit-law-mul-𝕊¹ base-𝕊¹ ＝ right-unit-law-mul-𝕊¹ base-𝕊¹
coh-unit-laws-mul-𝕊¹ =
  inv
    ( coherence-point-htpy-eq-pointed-map
      ( pr1 mul-Π-𝕊¹ base-𝕊¹)
      ( id-pointed-map)
      ( pr1 (pr2 mul-Π-𝕊¹)) ∙
      right-unit)
```

### The H-space structure on the circle

```agda
coherent-unital-mul-𝕊¹-Pointed-Type :
  coherent-unital-mul-Pointed-Type 𝕊¹-Pointed-Type
pr1 coherent-unital-mul-𝕊¹-Pointed-Type =
  mul-𝕊¹
pr2 coherent-unital-mul-𝕊¹-Pointed-Type =
  ( left-unit-law-mul-𝕊¹ , right-unit-law-mul-𝕊¹ , coh-unit-laws-mul-𝕊¹)

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

### The Hopf shear on the product of two 1-spheres

```agda
equiv-hopf-shear-sphere-1 : (sphere 1 × sphere 1) ≃ (sphere 1 × sphere 1)
equiv-hopf-shear-sphere-1 =
  ( equiv-tot (λ y → equiv-right-mul-sphere-1 y)) ∘e
  ( commutative-product)

hopf-shear-sphere-1 : sphere 1 × sphere 1 → sphere 1 × sphere 1
hopf-shear-sphere-1 =
  map-equiv equiv-hopf-shear-sphere-1

compute-pr1-hopf-shear-sphere-1 :
  (t : sphere 1 × sphere 1) →
  pr1 (hopf-shear-sphere-1 t) ＝ pr2 t
compute-pr1-hopf-shear-sphere-1 t =
  refl

compute-pr2-hopf-shear-sphere-1 :
  (t : sphere 1 × sphere 1) →
  pr2 (hopf-shear-sphere-1 t) ＝ mul-sphere-1 (pr1 t) (pr2 t)
compute-pr2-hopf-shear-sphere-1 t =
  refl
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
