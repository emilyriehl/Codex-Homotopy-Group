# Equality of pointed maps

```agda
module structured-types.equality-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-extensionality-axiom
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

An [identification](foundation.identity-types.md) of
[pointed maps](structured-types.pointed-maps.md) induces a homotopy between
their underlying maps. This homotopy has a **base point coherence**: its value
at the base point commutes with the paths witnessing preservation of base
points.

## Properties

### The homotopy induced by an identification of pointed maps preserves the base point

For `p : f ＝ g`, the underlying homotopy is
`htpy-eq (ap map-pointed-map p)`. Its base point coherence follows by path
induction on `p`.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  coherence-point-htpy-eq-pointed-map :
    (g : A →∗ B) (p : f ＝ g) →
    coherence-point-unpointed-htpy-pointed-Π f g
      ( htpy-eq (ap map-pointed-map p))
  coherence-point-htpy-eq-pointed-map .f refl = refl
```
