# Higher homotopy groups of truncated types

```agda
module synthetic-homotopy-theory.higher-homotopy-groups-truncated-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.1-types
open import foundation.connected-components
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncations
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels
open import foundation-core.equality-dependent-pair-types
open import foundation-core.truncation-levels

open import group-theory.automorphism-groups
open import group-theory.homotopy-automorphism-groups
open import group-theory.trivial-concrete-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

If a pointed type is a `1`-type, then its loop space is a set. Iterating loop
spaces preserves being a set, so all positive concrete homotopy groups of a
pointed `1`-type are trivial.

## Theorem

### Connected components of sets are contractible

```agda
abstract
  is-contr-connected-component-is-set :
    {l : Level} {A : UU l} (is-set-A : is-set A) (a : A) →
    is-contr (connected-component A a)
  pr1 (is-contr-connected-component-is-set is-set-A a) =
    point-connected-component _ a
  pr2 (is-contr-connected-component-is-set is-set-A a) (x , p) =
    apply-universal-property-trunc-Prop
      ( p)
      ( Id-Prop
        ( connected-component _ a , is-trunc-connected-component _ a is-set-A)
        ( point-connected-component _ a)
        ( x , p))
      ( λ q →
        eq-pair-Σ
          ( inv q)
          ( all-elements-equal-type-trunc-Prop _ p))

abstract
  is-set-type-trunc-one-is-set :
    {l : Level} {A : UU l} → is-set A → is-set (type-trunc one-𝕋 A)
  is-set-type-trunc-one-is-set {A = A} is-set-A =
    is-set-equiv'
      ( A)
      ( equiv-unit-trunc (A , is-1-type-is-set is-set-A))
      ( is-set-A)

  is-trivial-Automorphism-Group-Set :
    {l : Level} (A : Set l) (a : type-Set A) →
    is-trivial-Concrete-Group
      ( Automorphism-Group
        ( type-Set A , is-1-type-is-set (is-set-type-Set A))
        ( a))
  is-trivial-Automorphism-Group-Set A a =
    is-prop-is-contr
      ( is-contr-connected-component-is-set (is-set-type-Set A) a)
      ( point-connected-component _ a)
      ( point-connected-component _ a)

abstract
  is-trivial-concrete-group-Pointed-Type-is-set :
    {l : Level} (A : Pointed-Type l) →
    is-set (type-Pointed-Type A) →
    is-trivial-Concrete-Group (concrete-group-Pointed-Type A)
  is-trivial-concrete-group-Pointed-Type-is-set A is-set-A =
    is-prop-is-contr
      ( is-contr-connected-component-is-set
        ( is-set-type-trunc-one-is-set is-set-A)
        ( unit-trunc (point-Pointed-Type A)))
      ( point-connected-component _ (unit-trunc (point-Pointed-Type A)))
      ( point-connected-component _ (unit-trunc (point-Pointed-Type A)))
```

### Positive iterated loop spaces of `1`-types are sets

```agda
is-set-loop-space-is-1-type :
  {l : Level} (A : Pointed-Type l) →
  is-1-type (type-Pointed-Type A) → is-set (type-Ω A)
is-set-loop-space-is-1-type A =
  is-trunc-Ω zero-𝕋 A

is-set-Ω-is-set :
  {l : Level} (A : Pointed-Type l) →
  is-set (type-Pointed-Type A) → is-set (type-Ω A)
is-set-Ω-is-set A is-set-A =
  is-set-is-prop (is-trunc-Ω neg-one-𝕋 A is-set-A)

is-set-positive-iterated-loop-space-is-1-type :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  is-1-type (type-Pointed-Type A) →
  is-set (type-iterated-loop-space (succ-ℕ n) A)
is-set-positive-iterated-loop-space-is-1-type zero-ℕ A is-1-type-A =
  is-set-loop-space-is-1-type A is-1-type-A
is-set-positive-iterated-loop-space-is-1-type (succ-ℕ n) A is-1-type-A =
  is-set-Ω-is-set
    ( iterated-loop-space (succ-ℕ n) A)
    ( is-set-positive-iterated-loop-space-is-1-type n A is-1-type-A)
```

### Positive concrete homotopy groups of `1`-types are trivial

```agda
is-trivial-positive-concrete-homotopy-group-is-1-type :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  is-1-type (type-Pointed-Type A) →
  is-trivial-Concrete-Group (concrete-homotopy-group (succ-ℕ n) A)
is-trivial-positive-concrete-homotopy-group-is-1-type n A is-1-type-A =
  is-trivial-concrete-group-Pointed-Type-is-set
    ( iterated-loop-space (succ-ℕ n) A)
    ( is-set-positive-iterated-loop-space-is-1-type n A is-1-type-A)
```
