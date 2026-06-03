# Functoriality of iterated loop spaces

```agda
module synthetic-homotopy-theory.functoriality-iterated-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.iterated-loop-spaces
```

</details>

## Idea

A [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` induces pointed
maps on all [iterated loop spaces](synthetic-homotopy-theory.iterated-loop-spaces.md)
by iterating the functorial action of the [loop space](synthetic-homotopy-theory.loop-spaces.md)
operation.

## Definitions

### The functorial action of iterated loop spaces on pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  pointed-map-iterated-loop-space :
    (n : ℕ) → A →∗ B → iterated-loop-space n A →∗ iterated-loop-space n B
  pointed-map-iterated-loop-space zero-ℕ f = f
  pointed-map-iterated-loop-space (succ-ℕ n) f =
    pointed-map-Ω (pointed-map-iterated-loop-space n f)
```
