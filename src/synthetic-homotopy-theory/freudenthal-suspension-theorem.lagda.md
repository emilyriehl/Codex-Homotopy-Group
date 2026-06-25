# The Freudenthal suspension theorem

```agda
module synthetic-homotopy-theory.freudenthal-suspension-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.connected-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types
```

</details>

## Idea

The unit of the suspension-loop adjunction

```text
  A → ΩΣA
```

is the map appearing in the Freudenthal suspension theorem. If `A` is
`(n+1)`-connected, Freudenthal says that this unit is `(2n+2)`-connected. In
the natural-number-indexed part of agda-unimath's truncation levels, the two
bounds are recorded by the following functions.

## Definitions

### The connectivity range in the Freudenthal suspension theorem

```agda
freudenthal-domain-connectivity-level-ℕ : ℕ → ℕ
freudenthal-domain-connectivity-level-ℕ n = succ-ℕ n

freudenthal-connectivity-level-ℕ : ℕ → ℕ
freudenthal-connectivity-level-ℕ n = succ-ℕ (succ-ℕ (n +ℕ n))
```

### The suspension stabilization map

```agda
pointed-map-Freudenthal-suspension :
  {l : Level} (A : Pointed-Type l) →
  A →∗ Ω (suspension-Pointed-Type A)
pointed-map-Freudenthal-suspension =
  pointed-map-unit-suspension-loop-adjunction

map-Freudenthal-suspension :
  {l : Level} (A : Pointed-Type l) →
  type-Pointed-Type A → type-Ω (suspension-Pointed-Type A)
map-Freudenthal-suspension A =
  map-pointed-map (pointed-map-Freudenthal-suspension A)
```

### The Freudenthal suspension theorem as a reusable target statement

```agda
is-connected-map-Freudenthal-suspension :
  {l : Level} (n : ℕ) (A : Pointed-Type l) → UU l
is-connected-map-Freudenthal-suspension n A =
  is-connected
    ( truncation-level-ℕ (freudenthal-domain-connectivity-level-ℕ n))
    ( type-Pointed-Type A) →
  is-connected-map
    ( truncation-level-ℕ (freudenthal-connectivity-level-ℕ n))
    ( map-Freudenthal-suspension A)
```
