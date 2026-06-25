# Gap maps of pushout squares

```agda
module synthetic-homotopy-theory.gap-maps-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

Every [cocone](synthetic-homotopy-theory.cocones-under-spans.md) under a span

```text
  A <- S -> B
```

determines a square

```text
  S ---> B
  |      |
  v      v
  A ---> X.
```

The **gap map** of this square is the induced map from `S` to the standard
pullback of the two maps into `X`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {X : UU l4} (f : S → A) (g : S → B) (c : cocone f g X)
  where

  cone-gap-pushout :
    cone
      ( horizontal-map-cocone f g c)
      ( vertical-map-cocone f g c)
      ( S)
  pr1 cone-gap-pushout = f
  pr1 (pr2 cone-gap-pushout) = g
  pr2 (pr2 cone-gap-pushout) = coherence-square-cocone f g c

  gap-pushout :
    S →
    standard-pullback
      ( horizontal-map-cocone f g c)
      ( vertical-map-cocone f g c)
  gap-pushout =
    gap
      ( horizontal-map-cocone f g c)
      ( vertical-map-cocone f g c)
      ( cone-gap-pushout)
```
