# Connectedness of spheres

```agda
module synthetic-homotopy-theory.connectedness-spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The spheres are defined as iterated suspensions of the inhabited `0`-sphere.
Since suspension raises connectedness, `Sⁿ` is `(n-1)`-connected.

## Lemmas

### Inhabited types are `(-1)`-connected

```agda
is-neg-one-connected-is-inhabited :
  {l : Level} {A : UU l} → A → is-connected neg-one-𝕋 A
pr1 (is-neg-one-connected-is-inhabited a) = unit-trunc-Prop a
pr2 (is-neg-one-connected-is-inhabited a) =
  all-elements-equal-type-trunc-Prop (unit-trunc-Prop a)
```

## Theorem

### The `n`-sphere is `(n-1)`-connected

```agda
is-connected-sphere :
  (n : ℕ) → is-connected (truncation-level-minus-one-ℕ n) (sphere n)
is-connected-sphere zero-ℕ =
  is-neg-one-connected-is-inhabited (north-sphere 0)
is-connected-sphere (succ-ℕ n) =
  is-connected-succ-suspension-is-connected (is-connected-sphere n)

is-connected-sphere-succ :
  (n : ℕ) → is-connected (truncation-level-ℕ n) (sphere (succ-ℕ n))
is-connected-sphere-succ n = is-connected-sphere (succ-ℕ n)

is-connected-sphere-succ-succ :
  (n : ℕ) →
  is-connected (truncation-level-ℕ (succ-ℕ n))
    ( sphere (succ-ℕ (succ-ℕ n)))
is-connected-sphere-succ-succ n =
  is-connected-sphere (succ-ℕ (succ-ℕ n))
```
