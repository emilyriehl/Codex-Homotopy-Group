# The Hopf fiber sequence

```agda
module synthetic-homotopy-theory.hopf-fiber-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.fiber-sequences
open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.hopf-family-circle
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.spheres-as-join-powers
```

</details>

## Idea

The Hopf fibration gives a fiber sequence

```text
S¹ → S³ → S².
```

This file records the packaged pointed fiber sequence with its fiber, total
space, and base fields fixed definitionally to the pointed spheres used by the
homotopy-group calculation.

## Theorem

### The Hopf fiber sequence

```agda
pointed-equiv-total-space-hopf-family-sphere-1-sphere-3 :
  pointed-total-space-hopf-family-sphere-1 ≃∗ sphere-Pointed-Type 3
pr1 pointed-equiv-total-space-hopf-family-sphere-1-sphere-3 =
  equiv-total-space-hopf-family-sphere-1-sphere-3
pr2 pointed-equiv-total-space-hopf-family-sphere-1-sphere-3 =
  ( ap
    ( λ y →
      map-equiv equiv-sphere-3-join-power-Fin-2
        ( map-equiv equiv-join-power-two-two-Fin-2 y))
    ( compute-point-equiv-total-space-hopf-family-sphere-1-join-power-Fin-2)) ∙
  ( ap
    ( map-equiv equiv-sphere-3-join-power-Fin-2)
    ( compute-point-equiv-join-power-two-two-Fin-2)) ∙
  compute-point-equiv-sphere-join-power-Fin-2 3

hopf-fiber-sequence-data-sphere-1-sphere-3-sphere-2 :
  Σ ( sphere-Pointed-Type 1 →∗ sphere-Pointed-Type 3)
    ( λ i →
      Σ ( sphere-Pointed-Type 3 →∗ sphere-Pointed-Type 2)
        ( λ p → is-fiber-sequence-Pointed-Type i p))
hopf-fiber-sequence-data-sphere-1-sphere-3-sphere-2 =
  tr
    ( λ E →
      Σ ( sphere-Pointed-Type 1 →∗ E)
        ( λ i →
          Σ ( E →∗ sphere-Pointed-Type 2)
            ( λ p → is-fiber-sequence-Pointed-Type i p)))
    ( eq-pointed-equiv
      ( pointed-total-space-hopf-family-sphere-1)
      ( sphere-Pointed-Type 3)
      ( pointed-equiv-total-space-hopf-family-sphere-1-sphere-3))
    ( fiber-inclusion-hopf-family-sphere-1 ,
      pointed-map-projection-hopf-family-sphere-1 ,
      is-fiber-sequence-hopf-family-sphere-1)

hopf-fiber-sequence-sphere-1-sphere-3-sphere-2 :
  fiber-sequence-Pointed-Type lzero lzero lzero
pr1 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2 =
  sphere-Pointed-Type 1
pr1 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2) =
  sphere-Pointed-Type 3
pr1 (pr2 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)) =
  sphere-Pointed-Type 2
pr1 (pr2 (pr2 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))) =
  pr1 hopf-fiber-sequence-data-sphere-1-sphere-3-sphere-2
pr1 (pr2 (pr2 (pr2 (pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2)))) =
  pr1 (pr2 hopf-fiber-sequence-data-sphere-1-sphere-3-sphere-2)
pr1
  ( pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))))) =
  pr1 (pr2 (pr2 hopf-fiber-sequence-data-sphere-1-sphere-3-sphere-2))
pr2
  ( pr2
    ( pr2
      ( pr2
        ( pr2
          ( pr2 hopf-fiber-sequence-sphere-1-sphere-3-sphere-2))))) =
  pr2 (pr2 (pr2 hopf-fiber-sequence-data-sphere-1-sphere-3-sphere-2))
```
