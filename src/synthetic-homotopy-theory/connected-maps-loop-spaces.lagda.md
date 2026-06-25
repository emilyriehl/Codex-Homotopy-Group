# Connected maps and loop spaces

```agda
module synthetic-homotopy-theory.connected-maps-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
```

</details>

## Idea

Looping a pointed map lowers the connectivity of the map by one. The basic
case follows by identifying the fiber of the induced loop map over the base
loop with an identity type in the fiber of the original map.

## Theorem

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  equiv-fiber-ap-Eq-fiber :
    (f : type-Pointed-Type A → type-Pointed-Type B)
    (q : f (point-Pointed-Type A) ＝ f (point-Pointed-Type A)) →
    fiber
      ( ap f {point-Pointed-Type A} {point-Pointed-Type A})
      ( q) ≃
    Eq-fiber
      ( f)
      ( f (point-Pointed-Type A))
      ( point-Pointed-Type A , refl)
      ( point-Pointed-Type A , inv q)
  equiv-fiber-ap-Eq-fiber f q =
    equiv-tot
      ( λ p → equiv-right-transpose-eq-concat' (ap f p) refl q)

  is-connected-map-map-Ω :
    (f : A →∗ B) →
    is-connected-map (succ-𝕋 k) (map-pointed-map f) →
    is-connected-map k (map-Ω f)
  is-connected-map-map-Ω (f , refl) H q =
    is-connected-equiv'
      ( ( inv-equiv (equiv-fiber-ap-Eq-fiber f q)) ∘e
        ( equiv-Eq-eq-fiber f (f (point-Pointed-Type A))))
      ( is-connected-eq-is-connected
        ( H (f (point-Pointed-Type A)))
        { point-Pointed-Type A , refl}
        { point-Pointed-Type A , inv q})
```
