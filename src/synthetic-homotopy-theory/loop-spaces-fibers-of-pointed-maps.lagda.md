# Loop spaces of fibers of pointed maps

```agda
module synthetic-homotopy-theory.loop-spaces-fibers-of-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.fibers-of-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The **loop space of the fiber** of a pointed map `g : E →∗ B` is equivalent to
the fiber of the induced loop map `Ω E →∗ Ω B`. This is the looped form of the
canonical fiber sequence and is used repeatedly when iterating the long exact
sequence.

## Definitions

```agda
module _
  {l1 l2 : Level} {E : Pointed-Type l1} {B : Pointed-Type l2}
  where

  map-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    type-Ω (fiber-Pointed-Type g) →
    type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))
  map-loop-fiber-Pointed-Type (g , refl) x =
    fiber-ap-eq-fiber
      ( g)
      ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
      ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
      ( x)

  map-inv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g)) →
    type-Ω (fiber-Pointed-Type g)
  map-inv-loop-fiber-Pointed-Type (g , refl) =
    map-inv-equiv
      ( equiv-fiber-ap-eq-fiber
        ( g)
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl))))

  is-section-map-inv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    (x : type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))) →
    map-loop-fiber-Pointed-Type g (map-inv-loop-fiber-Pointed-Type g x) ＝ x
  is-section-map-inv-loop-fiber-Pointed-Type (g , refl) =
    is-section-map-inv-equiv
      ( equiv-fiber-ap-eq-fiber
        ( g)
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl))))

  is-retraction-map-inv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    (x : type-Ω (fiber-Pointed-Type g)) →
    map-inv-loop-fiber-Pointed-Type g (map-loop-fiber-Pointed-Type g x) ＝ x
  is-retraction-map-inv-loop-fiber-Pointed-Type (g , refl) =
    is-retraction-map-inv-equiv
      ( equiv-fiber-ap-eq-fiber
        ( g)
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
        ( point-Pointed-Type (fiber-Pointed-Type (g , refl))))

  is-equiv-map-loop-fiber-Pointed-Type :
    (g : E →∗ B) → is-equiv (map-loop-fiber-Pointed-Type g)
  is-equiv-map-loop-fiber-Pointed-Type g =
    is-equiv-is-invertible
      ( map-inv-loop-fiber-Pointed-Type g)
      ( is-section-map-inv-loop-fiber-Pointed-Type g)
      ( is-retraction-map-inv-loop-fiber-Pointed-Type g)

  equiv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    type-Ω (fiber-Pointed-Type g) ≃
    type-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))
  pr1 (equiv-loop-fiber-Pointed-Type g) = map-loop-fiber-Pointed-Type g
  pr2 (equiv-loop-fiber-Pointed-Type g) = is-equiv-map-loop-fiber-Pointed-Type g

  preserves-point-map-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    map-equiv (equiv-loop-fiber-Pointed-Type g) refl ＝
    point-Pointed-Type (fiber-Pointed-Type (pointed-map-Ω g))
  preserves-point-map-loop-fiber-Pointed-Type (g , refl) =
    refl

  pointed-equiv-loop-fiber-Pointed-Type :
    (g : E →∗ B) →
    Ω (fiber-Pointed-Type g) ≃∗ fiber-Pointed-Type (pointed-map-Ω g)
  pr1 (pointed-equiv-loop-fiber-Pointed-Type g) = equiv-loop-fiber-Pointed-Type g
  pr2 (pointed-equiv-loop-fiber-Pointed-Type g) =
    preserves-point-map-loop-fiber-Pointed-Type g

  pointed-htpy-loop-fiber-inclusion-Pointed-Type :
    (g : E →∗ B) →
    pointed-map-Ω (inclusion-fiber-Pointed-Type g) ~∗
    ( inclusion-fiber-Pointed-Type (pointed-map-Ω g) ∘∗
      pointed-map-pointed-equiv (pointed-equiv-loop-fiber-Pointed-Type g))
  pr1 (pointed-htpy-loop-fiber-inclusion-Pointed-Type (g , refl)) x =
    inv
      ( ap pr1
        ( triangle-fiber-ap-eq-fiber
          ( g)
          ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
          ( point-Pointed-Type (fiber-Pointed-Type (g , refl)))
          ( x)))
  pr2 (pointed-htpy-loop-fiber-inclusion-Pointed-Type (g , refl)) =
    refl
```
