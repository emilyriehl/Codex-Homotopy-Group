# Low homotopy groups of the 3-sphere

```agda
module synthetic-homotopy-theory.homotopy-groups-sphere-3 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-components
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import group-theory.homotopy-automorphism-groups
open import group-theory.trivial-concrete-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.homotopy-groups
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [3-sphere](synthetic-homotopy-theory.spheres.md) is obtained by three
successive suspensions of the inhabited 0-sphere. Since suspension raises
connectedness, `S³` is 2-connected. This implies that its first two concrete
homotopy groups are trivial.

## Lemmas

### Inhabited types are `(-1)`-connected

```agda
is-neg-one-connected-is-inhabited :
  {l : Level} {A : UU l} → A → is-connected neg-one-𝕋 A
pr1 (is-neg-one-connected-is-inhabited a) = unit-trunc-Prop a
pr2 (is-neg-one-connected-is-inhabited a) =
  all-elements-equal-type-trunc-Prop (unit-trunc-Prop a)
```

### Connected components of contractible types are contractible

```agda
is-contr-connected-component-is-contr :
  {l : Level} {A : UU l} → is-contr A → (a : A) →
  is-contr (connected-component A a)
is-contr-connected-component-is-contr H a =
  is-contr-Σ-is-prop
    ( a)
    ( refl-mere-eq a)
    ( λ x → is-prop-mere-eq x a)
    ( λ x _ → eq-is-contr H)
```

### `1`-connected pointed types have trivial concrete group

```agda
is-trivial-concrete-group-Pointed-Type-is-1-connected :
  {l : Level} (A : Pointed-Type l) →
  is-connected one-𝕋 (type-Pointed-Type A) →
  is-trivial-Concrete-Group (concrete-group-Pointed-Type A)
is-trivial-concrete-group-Pointed-Type-is-1-connected A H =
  is-prop-is-contr
    ( is-contr-connected-component-is-contr
      ( H)
      ( unit-trunc (point-Pointed-Type A)))
    ( point-connected-component _ (unit-trunc (point-Pointed-Type A)))
    ( point-connected-component _ (unit-trunc (point-Pointed-Type A)))

is-trivial-concrete-homotopy-group-is-1-connected :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  is-connected
    ( one-𝕋)
    ( type-Pointed-Type (iterated-loop-space n A)) →
  is-trivial-Concrete-Group (concrete-homotopy-group n A)
is-trivial-concrete-homotopy-group-is-1-connected n A =
  is-trivial-concrete-group-Pointed-Type-is-1-connected
    ( iterated-loop-space n A)
```

## Connectivity of `S³`

```agda
is-neg-one-connected-sphere-0 :
  is-connected neg-one-𝕋 (sphere 0)
is-neg-one-connected-sphere-0 =
  is-neg-one-connected-is-inhabited (north-sphere 0)

is-0-connected-sphere-1 :
  is-connected zero-𝕋 (sphere 1)
is-0-connected-sphere-1 =
  is-connected-succ-suspension-is-connected is-neg-one-connected-sphere-0

is-1-connected-sphere-2 :
  is-connected one-𝕋 (sphere 2)
is-1-connected-sphere-2 =
  is-connected-succ-suspension-is-connected is-0-connected-sphere-1

is-2-connected-sphere-3 :
  is-connected (succ-𝕋 one-𝕋) (sphere 3)
is-2-connected-sphere-3 =
  is-connected-succ-suspension-is-connected is-1-connected-sphere-2

is-1-connected-sphere-3 :
  is-connected one-𝕋 (sphere 3)
is-1-connected-sphere-3 =
  is-connected-is-connected-succ-𝕋 one-𝕋 is-2-connected-sphere-3

is-1-connected-loop-space-sphere-3 :
  is-connected one-𝕋 (type-Ω (sphere-Pointed-Type 3))
is-1-connected-loop-space-sphere-3 =
  is-connected-eq-is-connected is-2-connected-sphere-3
```

## Theorem

### The first two concrete homotopy groups of `S³` are trivial

```agda
is-trivial-concrete-homotopy-group-zero-sphere-3 :
  is-trivial-Concrete-Group
    ( concrete-homotopy-group 0 (sphere-Pointed-Type 3))
is-trivial-concrete-homotopy-group-zero-sphere-3 =
  is-trivial-concrete-homotopy-group-is-1-connected
    ( 0)
    ( sphere-Pointed-Type 3)
    ( is-1-connected-sphere-3)

is-trivial-concrete-homotopy-group-one-sphere-3 :
  is-trivial-Concrete-Group
    ( concrete-homotopy-group 1 (sphere-Pointed-Type 3))
is-trivial-concrete-homotopy-group-one-sphere-3 =
  is-trivial-concrete-homotopy-group-is-1-connected
    ( 1)
    ( sphere-Pointed-Type 3)
    ( is-1-connected-loop-space-sphere-3)
```
