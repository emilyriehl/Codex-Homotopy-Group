# Isomorphisms of homotopy groups

```agda
module synthetic-homotopy-theory.isomorphisms-homotopy-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-iterated-loop-spaces
open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.underlying-groups-concrete-homotopy-groups
open import synthetic-homotopy-theory.underlying-maps-concrete-homotopy-groups
```

</details>

## Idea

The ordinary underlying type of a concrete homotopy group agrees naturally with
the set truncation of the next iterated loop space. Therefore, if a pointed map
induces an equivalence on those set-truncated loop spaces, then the underlying
map of the induced homomorphism of concrete homotopy groups is an equivalence.

## Theorem

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (n : ℕ) (f : A →∗ B)
  where

  equiv-map-set-trunc-loop-map-concrete-homotopy-group :
    is-equiv (map-set-trunc-loop-map-concrete-homotopy-group n f) →
    type-homotopy-group (succ-ℕ n) A ≃
    type-homotopy-group (succ-ℕ n) B
  pr1 (equiv-map-set-trunc-loop-map-concrete-homotopy-group H) =
    map-set-trunc-loop-map-concrete-homotopy-group n f
  pr2 (equiv-map-set-trunc-loop-map-concrete-homotopy-group H) = H

  is-equiv-map-underlying-hom-concrete-homotopy-group-is-equiv-map-set-trunc-loop-map :
    is-equiv (map-set-trunc-loop-map-concrete-homotopy-group n f) →
    is-equiv (map-underlying-hom-concrete-homotopy-group n f)
  is-equiv-map-underlying-hom-concrete-homotopy-group-is-equiv-map-set-trunc-loop-map =
    is-equiv-map-underlying-hom-concrete-group-Pointed-Type-is-equiv-map-set-trunc-loop-map-Pointed-Type
      ( pointed-map-iterated-loop-space n f)
```
