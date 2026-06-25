# Connectivity of codiagonals of maps

```agda
module synthetic-homotopy-theory.connectivity-codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [codiagonal](synthetic-homotopy-theory.codiagonals-of-maps.md) of a map
`f : A → B` has fibers equivalent to the
[suspensions](synthetic-homotopy-theory.suspensions-of-types.md) of the fibers
of `f`. Therefore, if `f` is `k`-connected, then its codiagonal is
`(k+1)`-connected.

## Theorem

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-codiagonal-map-is-connected-map :
    is-connected-map k f →
    is-connected-map (succ-𝕋 k) (codiagonal-map f)
  is-connected-map-codiagonal-map-is-connected-map H b =
    is-connected-equiv'
      ( equiv-fiber-codiagonal-map-suspension-fiber f b)
      ( is-connected-succ-suspension-is-connected (H b))
```
